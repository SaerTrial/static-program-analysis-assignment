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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.checkerframework.checker.units.qual.C;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;
import polyglot.ast.Call;
import soot.jimple.InvokeExpr;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    private Obj curObj = null;
    private Var curVar = null;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (!callGraph.contains(method)) {
            callGraph.addReachableMethod(method);

            for (Stmt stmt : method.getIR().getStmts()) {
                if (stmt instanceof New)
                    stmt.accept(stmtProcessor);

                if (stmt instanceof Copy)
                    stmt.accept(stmtProcessor);

                // static call
                if (stmt instanceof Invoke && ((Invoke) stmt).isStatic())
                    stmt.accept(stmtProcessor);

                // static field store
                if (stmt instanceof StoreField && ((StoreField) stmt).isStatic())
                    stmt.accept(stmtProcessor);

                // static field load
                if (stmt instanceof LoadField && ((LoadField) stmt).isStatic())
                    stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        // via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            if (!stmt.getDef().isPresent()) return null;

            workList.addEntry(pointerFlowGraph.getVarPtr((Var) stmt.getDef().get()), new PointsToSet(heapModel.getObj(stmt)));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            // x = y
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(LoadArray stmt) {
            // y = x[i]
            addPFGEdge(pointerFlowGraph.getArrayIndex(curObj), pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(StoreArray stmt) {
            // x[i] = y
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getArrayIndex(curObj));
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {

            if (stmt.isStatic()){
                // T.f = y
                addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getStaticField(stmt.getFieldAccess().getFieldRef().resolve()));
            }else {
                // x.f = y
                addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getInstanceField(curObj, stmt.getFieldRef().resolve()));
            }

            return null;
        }

        @Override
        public Void visit(LoadField stmt) {

            if (stmt.isStatic()){
                // y = T.f
                addPFGEdge(pointerFlowGraph.getStaticField(stmt.getFieldAccess().getFieldRef().resolve()), pointerFlowGraph.getVarPtr(stmt.getLValue()));
            }else {
                // y = x.f
                addPFGEdge(pointerFlowGraph.getInstanceField(curObj, stmt.getFieldRef().resolve()), pointerFlowGraph.getVarPtr(stmt.getLValue()));
            }

            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            // TODO: check if this invoke is static
            JMethod m  = null;

            if (!stmt.isStatic()) {
                // FIXME: how to locate an obj for a var
                // current solution: processCall passes current var and obj through class member
                m = resolveCallee(curObj, stmt);
                workList.addEntry(pointerFlowGraph.getVarPtr(m.getIR().getThis()), new PointsToSet(curObj));
            } else {
                // static call
                m = stmt.getMethodRef().resolve();
                // m = resolveCallee(null, stmt); also works
            }

            // l -> G not available in CG
            // callGraph.getCallSitesIn() makes judgement in failure by about 20 test cases
            // since this approach will fail if there are two callsites on one function, e.g., l@10 -> func1, l@20 -> func1
            // func1 is added to CallSitesIn for the first time, then this checking will pass and do nothing, missing an edge that should have been added

            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt), stmt, m))) {
            //if (!callGraph.getCallSitesIn(m).contains(stmt)) {
                //callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt), stmt, m));
                addReachable(m);

                for (int idx = 0; idx < m.getIR().getParams().size(); idx++) {
                    addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getInvokeExp().getArgs().get(idx)),
                            pointerFlowGraph.getVarPtr(m.getIR().getParams().get(idx)));
                }

                if (stmt.getDef().isPresent()) {
                    for (Var returnVar : m.getIR().getReturnVars()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(returnVar),
                                pointerFlowGraph.getVarPtr((Var) stmt.getDef().get()));
                    }
                }
            }

            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me

        if (!pointerFlowGraph.getSuccsOf(source).contains(target)){
            pointerFlowGraph.addEdge(source, target);
            if (!source.getPointsToSet().isEmpty())
                workList.addEntry(target, source.getPointsToSet());
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry cur = workList.pollEntry();
            PointsToSet diff = propagate(cur.pointer(), cur.pointsToSet());

            if (cur.pointer() instanceof VarPtr) {
                Var n = ((VarPtr) cur.pointer()).getVar();

                // deal with each obj in the diff set
                for (Obj obj : diff) {
                    curObj = obj;

                    for (Stmt stmt: n.getStoreFields())
                        stmt.accept(stmtProcessor);

                    for (Stmt stmt: n.getLoadFields())
                        stmt.accept(stmtProcessor);

                    for (Stmt stmt: n.getStoreArrays())
                        stmt.accept(stmtProcessor);

                    for (Stmt stmt: n.getLoadArrays())
                        stmt.accept(stmtProcessor);

                    processCall(n, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me

        PointsToSet differencePTS = new PointsToSet();

        if (!pointsToSet.isEmpty()){
            for (Obj obj : pointsToSet.getObjects()){

                if (pointer.getPointsToSet().contains(obj)) continue;

                differencePTS.addObject(obj);
                pointer.getPointsToSet().addObject(obj);
                for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)){
                    workList.addEntry(succ, pointsToSet);
                }
            }
        }

        return differencePTS;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me

        // FIXME: use global vars to pass info to the corresponding visitor

        curObj = recv;
        curVar = var;

        // FIXME: var.getInvokes() is fully included by S?
        for (Stmt invoke : var.getInvokes()){
            invoke.accept(stmtProcessor);
        }

    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
