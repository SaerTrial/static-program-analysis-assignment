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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.HashSet;
import java.util.Set;
import java.util.ArrayList;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me

        Set<Node> worklist = new HashSet<Node>();

        for (Node node : cfg) {
            worklist.add(node);
        }

        while (worklist.size() > 0) {
            Node node = worklist.iterator().next();
            worklist.remove(node);

            Fact out_fact = result.getOutFact(node);
            Fact in_fact = result.getInFact(node);

            boolean change = false;

            for (Node pred : cfg.getPredsOf(node)) {
                Fact pred_fact = result.getOutFact(pred);
                // union
                analysis.meetInto(pred_fact, in_fact);
            }

            change = analysis.transferNode(node, in_fact, out_fact);
            if (change) {
                for (Node succ : cfg.getSuccsOf(node)) {
                    worklist.add(succ);
                }
            }
        }

        System.out.println("done");
    }



    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }
}
