/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.util.collection.SetQueue;

import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;
    //public DataflowResult<Node, Fact> result;
    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    public DataflowResult<Node, Fact> getResult(){
        return result;
    }

    public void addWorkList(Node node) {
            workList.add(node);
    }

    private void initialize() {
        // TODO - finish me
        Set<Node> entryNodes = new HashSet<>();

        // set boundary fact for nodes of entry methods
        for (Method method : icfg.entryMethods().toList()){
            Node entry = icfg.getEntryOf(method);
            entryNodes.add(entry);
            result.setInFact(entry, analysis.newBoundaryFact(entry));
            result.setOutFact(entry, analysis.newBoundaryFact(entry));
        }

        for (Node node : icfg) {
            if (entryNodes.contains(node)) continue;
            result.setInFact(node, analysis.newInitialFact());
            result.setOutFact(node, analysis.newInitialFact());
        }

        workList = new SetQueue<>();
    }

    private void doSolve() {
        // TODO - finish me
        for (Node node : icfg) {
            workList.add(node);
        }

        while (!workList.isEmpty()) {
            Node node = workList.remove();

            Fact out_fact = result.getOutFact(node);
            Fact in_fact = result.getInFact(node);

            for (ICFGEdge<Node> predEdge : icfg.getInEdgesOf(node)) {
                Fact pred_fact = result.getOutFact(predEdge.getSource());
                analysis.meetInto(analysis.transferEdge(predEdge, pred_fact), in_fact);
            }

            boolean change = analysis.transferNode(node, in_fact, out_fact);

            if (change) {
                for (Node succ : icfg.getSuccsOf(node))
                    workList.add(succ);
            }

        }
    }
}
