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

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private PointerAnalysisResult ptaResult;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here
        ptaResult = pta;

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

        if (in.equals(out)) return false;

        out.copyFrom(in);
        return true;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me

        if (stmt instanceof StoreField storeField && cp.canHoldInt(storeField.getRValue())){
            if (!in.equals(out)) {
                if (!storeField.isStatic()) {
                    InstanceFieldAccess instanceFieldAccess = (InstanceFieldAccess) storeField.getLValue();
                    Var curInstanceBase = instanceFieldAccess.getBase();
                    Set<Obj> tmpSet = null;
                    // put all load field stmts into worklist to avoid order-dependent propagation
                    for (Var var : ptaResult.getVars()) {
                        for (LoadField loadField : var.getLoadFields()) {

                            tmpSet = new HashSet<>(ptaResult.getPointsToSet(var));
                            tmpSet.retainAll(ptaResult.getPointsToSet(curInstanceBase));

                            // without intersection, then this is not an alias
                            if (tmpSet.isEmpty()) continue;

                            solver.addWorkList(loadField);
                        }
                    }
                } else {
                    for (Stmt node : icfg){
                        if (node instanceof LoadField && ((LoadField) node).isStatic()){
                            // same static field and declaring class
                            if ( ((LoadField) node).getFieldAccess().getFieldRef().resolve().equals(
                                    storeField.getFieldAccess().getFieldRef().resolve()) ) {
                                solver.addWorkList(node);
                            }
                        }
                    }
                }
            }

            if (in.equals(out))
                return false;

            out.copyFrom(in);
            return true;
        }

        if (stmt instanceof StoreArray storeArray && cp.canHoldInt(storeArray.getRValue())){
            ArrayAccess arrayAccess = storeArray.getArrayAccess();
            Set<Obj> tmpSet = null;

            // search for alias
            for (Var var : ptaResult.getVars()) {
                for (LoadArray loadArray : var.getLoadArrays()) {
                    // check base
                    tmpSet = new HashSet<>(ptaResult.getPointsToSet(loadArray.getArrayAccess().getBase()));
                    tmpSet.retainAll(ptaResult.getPointsToSet(arrayAccess.getBase()));

                    if (tmpSet.isEmpty()) continue;

                    // check index
                    Value candidate = solver.getResult().getInFact(loadArray).get(loadArray.getArrayAccess().getIndex());
                    Value host = solver.getResult().getInFact(storeArray).get(arrayAccess.getIndex());

                    // alias checking
                    boolean isAlias = false;

                    if (host.isUndef()){
                        // i == UNDEF
                        isAlias = false;
                    } else if (host.isNAC()) {
                        // i == NAC
                        if (candidate.isNAC()){
                            // j == NAC
                            isAlias = true;
                        } else if (candidate.isUndef()) {
                            // j == UNDEF
                            isAlias = false;
                        } else if (candidate.isConstant()) {
                            // j == c
                            isAlias = true;
                        }
                    } else if (host.isConstant()) {
                        // i == c
                        if (candidate.isNAC()){
                            // j == NAC
                            isAlias = true;
                        } else if (candidate.isUndef()) {
                            // j == UNDEF
                            isAlias = false;
                        } else if (candidate.isConstant()) {
                            // j == c
                            if (candidate.getConstant() == host.getConstant())
                                isAlias = true;
                            else
                                isAlias = false;
                        }
                    }

                    if (isAlias)
                        solver.addWorkList(loadArray);
                }
            }
            if (in.equals(out))
                return false;

            out.copyFrom(in);
            return true;
        }

    if (stmt instanceof LoadField loadField && cp.canHoldInt(loadField.getLValue())) {
        Value newValue = Value.getUndef();

        // deal with static field access
        if (loadField.isStatic()) {
            // go through all static field store
            for (Stmt node : icfg){
                if (node instanceof StoreField && ((StoreField) node).isStatic()){
                    // same static field and declaring class
                    if ( ((StoreField) node).getFieldAccess().getFieldRef().resolve().equals(
                            loadField.getFieldAccess().getFieldRef().resolve()) )
                        // check IN fact of the right var
                        newValue = cp.meetValue(newValue,
                                solver.getResult().getInFact(node).get(((StoreField) node).getRValue()));
                }
            }
        }else {
            // y = o.f;
            InstanceFieldAccess instanceFieldAccess = (InstanceFieldAccess) loadField.getRValue();
            Var curInstanceBase = instanceFieldAccess.getBase();
            Set<Obj> tmpSet = null;

            // alias
            for (Var var : ptaResult.getVars()) {
                for (StoreField storeField : var.getStoreFields()) {
                    // o.f = x;
                    tmpSet = new HashSet<>(ptaResult.getPointsToSet(var));
                    tmpSet.retainAll(ptaResult.getPointsToSet(curInstanceBase));

                    // without intersection, then this is not an alias
                    if (tmpSet.isEmpty()) continue;

                    // TODO: I forgot to add this checking such that 10 stmts (4 methods) were analyzed wrong
                    if (instanceFieldAccess.getFieldRef().resolve().equals(storeField.getFieldRef().resolve()))
                        newValue = cp.meetValue(newValue,
                            solver.getResult().getInFact(storeField).get(storeField.getRValue()));
                }
            }
        }

        if (newValue.isConstant() || newValue.isNAC()) {
            if (in.get(loadField.getLValue()).equals(newValue))
                return false;

            out.copyFrom(in);
            out.update(loadField.getLValue(), newValue);
            return true;
        }

        if (in.equals(out))
            return false;

        out.copyFrom(in);
        return true;
    }


    if (stmt instanceof LoadArray loadArray && cp.canHoldInt(loadArray.getLValue())){

        ArrayAccess arrayAccess = loadArray.getRValue();
        Set<Obj> tmpSet = null;
        Value newValue = Value.getUndef();

        // search for alias
        for (Var var : ptaResult.getVars()) {
            for (StoreArray storeArray : var.getStoreArrays()) {

                // check base
                tmpSet = new HashSet<>(ptaResult.getPointsToSet(storeArray.getArrayAccess().getBase()));
                tmpSet.retainAll(ptaResult.getPointsToSet(arrayAccess.getBase()));

                if (tmpSet.isEmpty()) continue;

                // check index
                Value candidate = solver.getResult().getInFact(storeArray).get(storeArray.getArrayAccess().getIndex());
                Value host = solver.getResult().getInFact(stmt).get(arrayAccess.getIndex());

                // alias checking
                boolean isAlias = false;

                if (host.isUndef()){
                    // i == UNDEF
                    isAlias = false;
                } else if (host.isNAC()) {
                    // i == NAC
                    if (candidate.isNAC()){
                        // j == NAC
                        isAlias = true;
                    } else if (candidate.isUndef()) {
                        // j == UNDEF
                        isAlias = false;
                    } else if (candidate.isConstant()) {
                        // j == c
                        isAlias = true;
                    }
                } else if (host.isConstant()) {
                    // i == c
                    if (candidate.isNAC()){
                        // j == NAC
                        isAlias = true;
                    } else if (candidate.isUndef()) {
                        // j == UNDEF
                        isAlias = false;
                    } else if (candidate.isConstant()) {
                        // j == c
                        if (candidate.getConstant() == host.getConstant())
                            isAlias = true;
                        else
                            isAlias = false;
                    }
                }

                // meet a value of field store of the current var
                if (isAlias)
                    newValue = cp.meetValue(newValue,
                            solver.getResult().getInFact(storeArray).get(storeArray.getRValue()));
            }
        }

        if (newValue.isConstant() || newValue.isNAC()) {
            if (in.get(((LoadArray) stmt).getLValue()).equals(newValue))
                return false;

            out.copyFrom(in);
            out.update(((LoadArray) stmt).getLValue(), newValue);
            return true;
        }

        if (in.equals(out))
            return false;

        out.copyFrom(in);
        return true;
    }


    return cp.transferNode(stmt, in, out);
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
        // FIXME: ignore this checking since we deal with field access and array access
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
        if (!edge.getCallSite().getDef().isPresent())
            return transferedOut;

        // no Var
        // if(!(((Invoke) edge.getCallSite()).getLValue() instanceof Var)) return transferedOut;

        // if more than one return var, which holds a different value, then return NAC to the receiver var
        Value newValue = null;

        // pretty fancy approach that I have seen in one's solution, would like to apply here
        List<Value> values = edge.getReturnVars().stream().map(returnOut::get).toList();

        for (Value value : values){
            if (newValue == null)
                newValue = value;
            else
                newValue = cp.meetValue(newValue, value);
        }

        if (newValue == null) newValue = Value.getUndef();

        transferedOut.update((Var) ((Invoke) edge.getCallSite()).getLValue(), newValue);

        return transferedOut;
    }
}
