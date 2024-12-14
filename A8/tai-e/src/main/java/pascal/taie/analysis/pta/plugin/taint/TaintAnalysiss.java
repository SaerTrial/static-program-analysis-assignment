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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    private class RecordCSCallsite {
        CSCallSite csCallSite;
        JMethod jMethod;

        RecordCSCallsite(CSCallSite csCallSite, JMethod jMethod) {
            this.csCallSite = csCallSite;
            this.jMethod = jMethod;
        }
    };

    private class RecordTransferCalls {

        CSCallSite csCallSite;
        TaintTransfer taintTransfer;
        Type type;
        CSVar base;

        RecordTransferCalls(CSCallSite csCallSite, TaintTransfer taintTransfer, Type type, CSVar base) {
            this.csCallSite = csCallSite;
            this.taintTransfer = taintTransfer;
            this.type = type;
            this.base = base;
        }

    }

    private Set<RecordCSCallsite> sinkCalls;
    private Set<RecordTransferCalls> argToBaseSet;
    private Set<RecordTransferCalls> argToResultSet;


    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
        sinkCalls = new HashSet<>();
        argToBaseSet = new HashSet<>();
        argToResultSet = new HashSet<>();
    }

    // TODO - finish me
    public CSObj getTaintObj(Invoke sourceCall, Type type) {
        if (sourceCall.getResult() == null) return null;

        for (Source source : config.getSources()){
            if (source.method().equals(sourceCall.getMethodRef().resolve()))
                return csManager.getCSObj(emptyContext, manager.makeTaint(sourceCall, type));
        }

        return null;
    }

    public CSObj transferTaintObj(CSObj old, Type receiverType) {
        return csManager.getCSObj(emptyContext, manager.makeTaint(manager.getSourceCall(old.getObject()), receiverType));
    }

    public boolean isTaintObj(CSObj taintObj) {
        if (taintObj == null)
            return false;

        return manager.isTaint(taintObj.getObject());
    }

    public boolean isSinkCall(JMethod sinkMethod) {
        for (Sink sink : config.getSinks()){
            if (sink.method().equals(sinkMethod)) return true;
        }
        return false;
    }

    // -1 base, -2 result
    public void aggregateArgToResult(CSCallSite csCallSite, Type type) {
        if (csCallSite.getCallSite().getResult() == null) throw new RuntimeException("no receiver var");

        for (TaintTransfer taintTransfer : config.getTransfers()){
            if (taintTransfer.method().equals(csCallSite.getCallSite().getMethodRef().resolve()) && taintTransfer.from() >= 0 && taintTransfer.to() == -2
                    && taintTransfer.type().equals(type)) {
                boolean isExisting = false;

                for (RecordTransferCalls recordTransferCalls : argToResultSet) {
                    if (recordTransferCalls.csCallSite.equals(csCallSite) && recordTransferCalls.taintTransfer.equals(taintTransfer) && recordTransferCalls.type.equals(type)) {
                        isExisting = true;
                    }
                }
                if (!isExisting) argToResultSet.add(new RecordTransferCalls(csCallSite, taintTransfer, type, null));
            }
        }
    }

    public void transfer(){
        // argToResult
        for (RecordTransferCalls recordArgToResult : argToResultSet) {
            int idx = recordArgToResult.taintTransfer.from();

            csManager.getCSVar(recordArgToResult.csCallSite.getContext(), recordArgToResult.csCallSite.getCallSite().getInvokeExp().getArgs().get(idx)).getPointsToSet().forEach(csObj -> {
                if (isTaintObj(csObj)) {
                    CSObj transfer = transferTaintObj(csObj, recordArgToResult.csCallSite.getCallSite().getResult().getType());
                    CSVar receiverVar = csManager.getCSVar(recordArgToResult.csCallSite.getContext(), recordArgToResult.csCallSite.getCallSite().getResult());
                    if (transfer != null)
                        if (!receiverVar.getPointsToSet().contains(transfer))
                            solver.addWorkListEntry(receiverVar, transfer);
                }
            });
        }

        // argToBase
        for (RecordTransferCalls recordArgToBase : argToBaseSet){
            int idx = recordArgToBase.taintTransfer.from();
            csManager.getCSVar(recordArgToBase.csCallSite.getContext(), recordArgToBase.csCallSite.getCallSite().getInvokeExp().getArgs().get(idx)).getPointsToSet().forEach(csObj -> {
                if (isTaintObj(csObj)) {
                    CSObj transfer = transferTaintObj(csObj, recordArgToBase.base.getType());
                    if (transfer != null)
                        if (!recordArgToBase.base.getPointsToSet().contains(transfer))
                            solver.addWorkListEntry(recordArgToBase.base, transfer);
                }
            });
        }

    }

    public void aggregateArgToBase(CSCallSite csCallSite, Type type, CSVar base) {
        for (TaintTransfer taintTransfer : config.getTransfers()){
            if (taintTransfer.method().equals(csCallSite.getCallSite().getMethodRef().resolve()) && taintTransfer.from() >= 0 && taintTransfer.to() == -1
                    && taintTransfer.type().equals(type)) {
                boolean isExisting = false;

                for (RecordTransferCalls recordTransferCalls : argToBaseSet) {
                    if (recordTransferCalls.csCallSite.equals(csCallSite) && recordTransferCalls.taintTransfer.equals(taintTransfer) && recordTransferCalls.type.equals(type)) {
                        isExisting = true;
                    }
                }

                if (!isExisting) argToBaseSet.add(new RecordTransferCalls(csCallSite, taintTransfer, type, base));
            }
        }
    }

    public boolean isBaseToResult(Invoke sourceCall, Type type){
        for (TaintTransfer taintTransfer : config.getTransfers()){
            if (taintTransfer.method().equals(sourceCall.getMethodRef().resolve()) && taintTransfer.from() == -1 && taintTransfer.to() == -2
                    && taintTransfer.type().equals(type))
                return true;
        }
        return false;
    }

    public Set<RecordCSCallsite> addSink(CSCallSite csCallSite, JMethod jMethod){
        sinkCalls.add(new RecordCSCallsite(csCallSite, jMethod));
        return sinkCalls;
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.

        for (RecordCSCallsite recordCSCallsite : sinkCalls) {
            for (Sink sink : config.getSinks()) {
                if (sink.method().equals(recordCSCallsite.jMethod)) {
                    for (CSObj csObj : csManager.getCSVar(recordCSCallsite.csCallSite.getContext(), recordCSCallsite.csCallSite.getCallSite().getInvokeExp().getArgs().get(sink.index())).getPointsToSet()) {
                        if (isTaintObj(csObj)) taintFlows.add(new TaintFlow(manager.getSourceCall(csObj.getObject()),
                                recordCSCallsite.csCallSite.getCallSite(), sink.index()));
                    }
                }
            }
        }

        return taintFlows;
    }
}
