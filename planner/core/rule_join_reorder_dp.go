// Copyright 2018 PingCAP, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// See the License for the specific language governing permissions and
// limitations under the License.

package core

import (
	"math/bits"

	"github.com/pingcap/tidb/expression"
	"github.com/pingcap/tidb/parser/ast"
)

type joinReorderDPSolver struct {
	*baseSingleGroupJoinOrderSolver
	newJoin func(lChild, rChild LogicalPlan, eqConds []*expression.ScalarFunction, otherConds []expression.Expression) LogicalPlan
}

type joinGroupEqEdge struct {
	nodeIDs []int
	edge    *expression.ScalarFunction
}

type joinGroupNonEqEdge struct {
	// Why is this struct defined in this way?
	nodeIDs    []int
	nodeIDMask uint
	expr       expression.Expression
}

func (s *joinReorderDPSolver) solve(joinGroup []LogicalPlan, eqConds []expression.Expression) (LogicalPlan, error) {
	// TODO: You need to implement the join reorder algo based on DP.

	// The pseudo code can be found in README.
	// And there's some common struct and method like `baseNodeCumCost`, `calcJoinCumCost` you can use in `rule_join_reorder.go`.
	// Also, you can take a look at `rule_join_reorder_greedy.go`, this file implement the join reorder algo based on greedy algorithm.
	// You'll see some common usages in the greedy version.

	// Note that the join tree may be disconnected. i.e. You need to consider the case `select * from t, t1, t2`.
	for _, node := range joinGroup {
		_, err := node.recursiveDeriveStats()
		if err != nil {
			return nil, err
		}
		// Each entry is a logical plan with associated cost
		s.curJoinGroup = append(s.curJoinGroup, &jrNode{
			p:       node,
			cumCost: s.baseNodeCumCost(node),
		})
	}

	// Build a graph that is used for dp
	adjacents := make([][]int, len(s.curJoinGroup))
	totalEqEdges := make([]joinGroupEqEdge, 0, len(eqConds))
	addEqEdge := func(node1, node2 int, edgeContent *expression.ScalarFunction) {
		totalEqEdges = append(totalEqEdges, joinGroupEqEdge{
			nodeIDs: []int{node1, node2},
			edge:    edgeContent,
		})
		adjacents[node1] = append(adjacents[node1], node2)
		adjacents[node2] = append(adjacents[node2], node1)
	}
	for _, cond := range eqConds {
		sf := cond.(*expression.ScalarFunction)
		args := sf.GetArgs()
		lCol := args[0].(*expression.Column)
		rCol := args[1].(*expression.Column)
		lIdx, err := findNodeIndexInGroup(joinGroup, lCol)
		if err != nil {
			return nil, err
		}
		rIdx, err := findNodeIndexInGroup(joinGroup, rCol)
		if err != nil {
			return nil, err
		}
		addEqEdge(lIdx, rIdx, sf)
	}

	// What is the purpose of this?
	totalNonEqEdges := make([]joinGroupNonEqEdge, 0, len(s.otherConds))
	// For each condition in s.otherConds, find the columns that related with the condition.
	// Then iterate through all the columns to store all the index information for the condition.
	for _, cond := range s.otherConds {
		cols := expression.ExtractColumns(cond)
		mask := uint(0)
		ids := make([]int, 0, len(cols))
		for _, col := range cols {
			idx, err := findNodeIndexInGroup(joinGroup, col)
			if err != nil {
				return nil, err
			}
			ids = append(ids, idx)
			mask |= 1 << uint(idx)
		}
		// Looks like ids and mask both contains the index information, so why are both of them needed?
		// nodeIDMask is used to quickly match the subset of the node set. nodeIDs only contains nodeID.
		totalNonEqEdges = append(totalNonEqEdges, joinGroupNonEqEdge{
			nodeIDs:    ids,
			nodeIDMask: mask,
			expr:       cond,
		})
	}
	visited := make([]bool, len(joinGroup))
	// What is nodeID2VisitID used for?
	// The reason why using nodeID2VisitID and visitID2nodeID to map the relationship between nodeID and visitID
	// is that in bfs not every nodes will be visited, so len(#visitID) <= len(#nodeID).
	// nodeID2VisitID stores the order of each node being visited in bfs. This is
	// used in dpGrpah to translate the nodeID mask to visitID mask.
	nodeID2VisitID := make([]int, len(joinGroup))
	var joins []LogicalPlan
	// For each joinGroup[i], traverse all the reachable nodes. And then combine all the associated otherConds
	// to generate a new join.
	for i := 0; i < len(joinGroup); i++ {
		if visited[i] {
			continue
		}
		visitID2NodeID := s.bfsGraph(i, visited, adjacents, nodeID2VisitID)
		// All the nodes that are visited in dfs, which means all the nodes that are reachable from joinGroup[i]
		nodeIDMask := uint(0)
		for _, nodeID := range visitID2NodeID {
			nodeIDMask |= 1 << uint(nodeID)
		}
		var subNonEqEdges []joinGroupNonEqEdge
		// Iterating by reverse order to remove nonEqEdge from totalNonEqEdges faster.
		for i := len(totalNonEqEdges) - 1; i >= 0; i-- {
			// Filter out the totalNonEqEdge that is not a subset of nodes that are reachable from joinGroup[i]
			if totalNonEqEdges[i].nodeIDMask&nodeIDMask != totalNonEqEdges[i].nodeIDMask {
				continue
			}
			// newMask stores the visitID information, but what is the purpose to transform the ID?
			newMask := uint(0)
			for _, nodeID := range totalNonEqEdges[i].nodeIDs {
				newMask |= 1 << uint(nodeID2VisitID[nodeID])
			}
			totalNonEqEdges[i].nodeIDMask = newMask
			subNonEqEdges = append(subNonEqEdges, totalNonEqEdges[i])
			totalNonEqEdges = append(totalNonEqEdges[:i], totalNonEqEdges[i+1:]...)
		}
		join, err := s.dpGraph(visitID2NodeID, nodeID2VisitID, joinGroup, totalEqEdges, subNonEqEdges)
		if err != nil {
			return nil, err
		}
		joins = append(joins, join)
	}
	remainedOtherConds := make([]expression.Expression, 0, len(totalNonEqEdges))
	for _, edge := range totalNonEqEdges {
		remainedOtherConds = append(remainedOtherConds, edge.expr)
	}
	return s.makeBushyJoin(joins, remainedOtherConds), nil
}

// bfsGraph traverses the graph and finds the information regarding the order of each node being visited.
func (s *joinReorderDPSolver) bfsGraph(startNode int, visited []bool, adjacents [][]int, nodeID2VisitID []int) []int {
	queue := []int{startNode}
	visited[startNode] = true
	var visitID2NodeID []int
	for len(queue) > 0 {
		// Pop the first element from the queue
		curNodeID := queue[0]
		queue = queue[1:]
		// So nodeID2VisitID is just recording the order of each node being visited,
		// and visitID2NodeID is the same relationship in the reverse direction.
		nodeID2VisitID[curNodeID] = len(visitID2NodeID)
		visitID2NodeID = append(visitID2NodeID, curNodeID)
		for _, adjNodeID := range adjacents[curNodeID] {
			if visited[adjNodeID] {
				continue
			}
			queue = append(queue, adjNodeID)
			visited[adjNodeID] = true
		}
	}
	return visitID2NodeID
}

func (s *joinReorderDPSolver) dpGraph(visitID2NodeID, nodeID2VisitID []int, joinGroup []LogicalPlan,
	totalEqEdges []joinGroupEqEdge, totalNonEqEdges []joinGroupNonEqEdge) (LogicalPlan, error) {
	// Recursion function: dp[group] = min{join{dp[sub], dp[group ^ sub]}}, which
	// is the minimum of cost of sub group join with other conds.
	nodeCnt := uint(len(visitID2NodeID))
	bestPlan := make([]*jrNode, 1<<nodeCnt)
	for i := uint(0); i < nodeCnt; i++ {
		bestPlan[1<<i] = s.curJoinGroup[visitID2NodeID[i]]
	}
	for nodeBitmap := uint(1); nodeBitmap < (1 << nodeCnt); nodeBitmap++ {
		if bits.OnesCount(nodeBitmap) == 1 {
			continue
		}
		// The way to enumerate through all possible subset is interesting.
		for sub := (nodeBitmap - 1) & nodeBitmap; sub > 0; sub = (sub - 1) & nodeBitmap {
			remain := nodeBitmap ^ sub
			// Why should skip the case sub > remain?
			if sub > remain {
				continue
			}
			if bestPlan[sub] == nil || bestPlan[remain] == nil {
				continue
			}
			usedEdges, otherConds := s.nodesAreConnected(sub, remain, totalEqEdges, totalNonEqEdges, nodeID2VisitID)
			if len(usedEdges) == 0 {
				continue
			}
			join, err := s.newJoinWithEdge(bestPlan[sub].p, bestPlan[remain].p, usedEdges, otherConds)
			if err != nil {
				return nil, err
			}
			curCost := s.calcJoinCumCost(join, bestPlan[sub], bestPlan[remain])
			if bestPlan[nodeBitmap] == nil {
				bestPlan[nodeBitmap] = &jrNode{
					p:       join,
					cumCost: curCost,
				}
			} else if bestPlan[nodeBitmap].cumCost > curCost {
				bestPlan[nodeBitmap].p = join
				bestPlan[nodeBitmap].cumCost = curCost
			}
		}
	}
	// Return the best plan in this connected join group
	return bestPlan[(1<<nodeCnt)-1].p, nil
}

func (s *joinReorderDPSolver) nodesAreConnected(subMask, remainMask uint, totalEqEdges []joinGroupEqEdge,
	totalNonEqEdges []joinGroupNonEqEdge, oldPos2NewPos []int) ([]joinGroupEqEdge, []expression.Expression) {
	var (
		eqEdges    []joinGroupEqEdge
		otherConds []expression.Expression
	)
	for _, edge := range totalEqEdges {
		// Translate nodeID to visitID
		lIdx := uint(oldPos2NewPos[edge.nodeIDs[0]])
		rIdx := uint(oldPos2NewPos[edge.nodeIDs[1]])
		if (subMask&(1<<lIdx)) > 0 && (remainMask&(1<<rIdx)) > 0 || ((subMask&(1<<rIdx)) > 0 && (remainMask&(1<<lIdx)) > 0) {
			eqEdges = append(eqEdges, edge)
		}
	}
	for _, edge := range totalNonEqEdges {
		// If edge.nodeIDMask is not a subset of nodeBitmap
		if edge.nodeIDMask&(subMask|remainMask) != edge.nodeIDMask {
			continue
		}
		// If edge.nodeIDMask does not overlap with either subMask or remainMask
		if edge.nodeIDMask&subMask == 0 || edge.nodeIDMask&remainMask == 0 {
			continue
		}
		otherConds = append(otherConds, edge.expr)
	}
	return eqEdges, otherConds
}

func (s *joinReorderDPSolver) newJoinWithEdge(leftPlan, rightPlan LogicalPlan, edges []joinGroupEqEdge, otherConds []expression.Expression) (LogicalPlan, error) {
	var eqConds []*expression.ScalarFunction
	for _, edge := range edges {
		lCol := edge.edge.GetArgs()[0].(*expression.Column)
		rCol := edge.edge.GetArgs()[1].(*expression.Column)
		if leftPlan.Schema().Contains(lCol) {
			eqConds = append(eqConds, edge.edge)
		} else {
			newSf := expression.NewFunctionInternal(s.ctx, ast.EQ, edge.edge.GetType(), rCol, lCol).(*expression.ScalarFunction)
			eqConds = append(eqConds, newSf)
		}
	}
	join := s.newJoin(leftPlan, rightPlan, eqConds, otherConds)
	_, err := join.recursiveDeriveStats()
	return join, err
}

// Make cartesian join as bushy tree.
func (s *joinReorderDPSolver) makeBushyJoin(cartesianJoinGroup []LogicalPlan, otherConds []expression.Expression) LogicalPlan {
	for len(cartesianJoinGroup) > 1 {
		resultJoinGroup := make([]LogicalPlan, 0, len(cartesianJoinGroup))
		for i := 0; i < len(cartesianJoinGroup); i += 2 {
			if i+1 == len(cartesianJoinGroup) {
				resultJoinGroup = append(resultJoinGroup, cartesianJoinGroup[i])
				break
			}
			// TODO:Since the other condition may involve more than two tables, e.g. t1.a = t2.b+t3.c.
			//  So We'll need a extra stage to deal with it.
			// Currently, we just add it when building cartesianJoinGroup.
			mergedSchema := expression.MergeSchema(cartesianJoinGroup[i].Schema(), cartesianJoinGroup[i+1].Schema())
			var usedOtherConds []expression.Expression
			otherConds, usedOtherConds = expression.FilterOutInPlace(otherConds, func(expr expression.Expression) bool {
				return expression.ExprFromSchema(expr, mergedSchema)
			})
			resultJoinGroup = append(resultJoinGroup, s.newJoin(cartesianJoinGroup[i], cartesianJoinGroup[i+1], nil, usedOtherConds))
		}
		cartesianJoinGroup = resultJoinGroup
	}
	return cartesianJoinGroup[0]
}

func findNodeIndexInGroup(group []LogicalPlan, col *expression.Column) (int, error) {
	for i, plan := range group {
		if plan.Schema().Contains(col) {
			return i, nil
		}
	}
	return -1, ErrUnknownColumn.GenWithStackByArgs(col, "JOIN REORDER RULE")
}
