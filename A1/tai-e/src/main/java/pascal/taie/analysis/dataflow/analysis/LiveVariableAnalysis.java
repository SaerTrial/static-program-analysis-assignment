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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.Return;

import java.util.Collection;

/**
 * Implementation of classic live variable analysis.
 */
public class LiveVariableAnalysis extends
        AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return false;
    }

    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        // FIXME: find the exit point - may not be necessary!
        SetFact<Var> fact = new SetFact<Var>();
        fact.clear();
        return fact;
    }

    @Override
    public SetFact<Var> newInitialFact() {
        // TODO - finish me
        SetFact<Var> fact = new SetFact<Var>();
        fact.clear();
        return fact;
    }

    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
        // TODO - finish me

        // union method from SetFact class
        target.union(fact);
    }

    @Override
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        // TODO - finish me

        SetFact<Var> old_in = in.copy();

        // clear in set each time
        in.clear();
        // trick: avoid a copy of the out fact set
        in.union(out);

        // if redefinition found, kill it from the set
        if (stmt.getDef().isPresent() && (stmt.getDef().get().getClass() == Var.class)){

            // kill
            in.remove((Var) stmt.getDef().get());
        }

        // if any use of a var is found, gen it in the set

        if (stmt.getClass() == Return.class){
            Var val = ((Return) stmt).getValue();
            if (val != null && val.getClass() == Var.class){
                if (!in.contains(val)) {
                    // gen
                    in.add(val);
                }
            }
        }

        for (int i = 0; i < stmt.getUses().size(); i++){
            if (stmt.getUses().get(i).getClass() == Var.class){
                // pass if the var has already been added in the in set
                if (!in.contains((Var) stmt.getUses().get(i))) {
                    // gen
                    in.add((Var) stmt.getUses().get(i));
                }
            }
        }

        if (old_in.equals(in)){
            return false;
        }
        else {
            return true;
        }
    }
}
