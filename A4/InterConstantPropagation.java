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

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import java.util.List;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me

        // directly make out equals to in
        if (in.equals(out)) return false;

        out.copyFrom(in);
        return true;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me

        // evaluate
        if (!stmt.getDef().isPresent() || !(stmt.getDef().get() instanceof Var)) {
            if (in.equals(out))
                return false;

            out.clear();
            out.copyFrom(in);
            return true;
        }

        if(!cp.canHoldInt((Var) stmt.getDef().get())) {
            if (in.equals(out))
                return false;

            out.clear();
            out.copyFrom(in);
            return true;
        }

        DefinitionStmt def = (DefinitionStmt) stmt;

        CPFact old_out = out.copy();
        out.copyFrom(in);

        out.update((Var) def.getLValue(), cp.evaluate(def.getRValue(), in));

        if (old_out.equals(out)) return false;

        return true;
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        Stmt curStmt = edge.getSource();

        // left-handed val does not exist, directly remains the same
        if (!curStmt.getDef().isPresent())  return out;

        // if left-handed val is not Var
        if(!(curStmt.getDef().get() instanceof Var)) return out;

        // kill the left-handed val in the copy of out fact, then return it
        CPFact new_out = out.copy();
        new_out.remove((Var) curStmt.getDef().get());
        return new_out;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me

        CPFact transferedOut = new CPFact();

        // arguments
        Invoke sourceStmt = (Invoke) edge.getSource();

        if (!(sourceStmt instanceof Invoke)) throw new RuntimeException("wrong!");

        List<Var> ArgsList = sourceStmt.getInvokeExp().getArgs();
        List<Var> ParamList = edge.getCallee().getIR().getParams();

        for (int idx = 0; idx < ArgsList.size(); idx++) {
            // from left to right
            Var arg = ArgsList.get(idx);
            Var param = ParamList.get(idx);

            transferedOut.update(param, callSiteOut.get(arg));
        }

        return transferedOut;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact transferedOut = new CPFact();

        // if no left-handed var, return an empty fact
        if (!edge.getCallSite().getDef().isPresent())  return transferedOut;

        // no Var
        if(!(((Invoke) edge.getCallSite()).getLValue() instanceof Var)) return transferedOut;

        // if more than one return var, which holds a different value, then return NAC to the receiver var
        boolean holdOne = true;
        Value prev = null;
        for (Var returnVar : edge.getReturnVars()){
            if (prev == null) prev = returnOut.get(returnVar);
            else if (prev != returnOut.get(returnVar)){
                holdOne = false;
                break;
            }
        }

        // check left-handed val
        if (holdOne)
            transferedOut.update((Var) ((Invoke) edge.getCallSite()).getLValue(), prev);
        else
            transferedOut.update((Var) ((Invoke) edge.getCallSite()).getLValue(), Value.getNAC());

        return transferedOut;
    }
}
