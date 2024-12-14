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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    private Context varContext = null;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */

    private void addReachable(CSMethod csMethod) {
        // TODO - finish me

        if (!callGraph.contains(csMethod)) {
            callGraph.addReachableMethod(csMethod);

            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);

            for (Stmt stmt : csMethod.getMethod().getIR().getStmts()){
                if (stmt instanceof New)
                    stmt.accept(stmtProcessor);

                else if (stmt instanceof Copy)
                    stmt.accept(stmtProcessor);

                    // static field store
                else if (stmt instanceof StoreField && ((StoreField) stmt).isStatic())
                    stmt.accept(stmtProcessor);

                    // static field load
                else if (stmt instanceof LoadField && ((LoadField) stmt).isStatic())
                    stmt.accept(stmtProcessor);

                    // static call
                else if (stmt instanceof Invoke && ((Invoke) stmt).isStatic())
                    stmt.accept(stmtProcessor);
                }
            }
        }


    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            if (!stmt.getDef().isPresent()) return null;

            CSObj csObj = csManager.getCSObj(
                    // e.g., [3]func1 -> [3]o1
                    contextSelector.selectHeapContext(csManager.getCSMethod(context, stmt.getContainer()), heapModel.getObj(stmt)),
                    heapModel.getObj(stmt));

            workList.addEntry(csManager.getCSVar(context, (Var) stmt.getDef().get()),
                    PointsToSetFactory.make(csObj));

            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            // x = y
            addPFGEdge(csManager.getCSVar(context, stmt.getRValue()), csManager.getCSVar(context, stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {

            if (stmt.isStatic()){
                // T.f = y
                addPFGEdge(csManager.getCSVar(context, stmt.getRValue()), csManager.getStaticField(stmt.getFieldAccess().getFieldRef().resolve()));
            }

            return null;
        }

        @Override
        public Void visit(LoadField stmt) {

            if (stmt.isStatic()){
                // y = T.f
                addPFGEdge(csManager.getStaticField(stmt.getFieldAccess().getFieldRef().resolve()), csManager.getCSVar(context, stmt.getLValue()));
            }

            return null;
        }


        @Override
        public Void visit(Invoke invoke) {
            JMethod m  = null;
            Context curContext = null;

            // static call
            m = resolveCallee(null, invoke);
            curContext = contextSelector.selectContext(csManager.getCSCallSite(context, invoke), m);

            // l -> G not available in CG
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke),
                    csManager.getCSCallSite(context, invoke),
                    csManager.getCSMethod(curContext, m)))){

                addReachable(csManager.getCSMethod(curContext, m));

                for (int idx = 0; idx < m.getIR().getParams().size(); idx++) {
                    addPFGEdge(csManager.getCSVar(context, invoke.getInvokeExp().getArgs().get(idx)),
                            csManager.getCSVar(curContext, m.getIR().getParams().get(idx)));
                }

                if (invoke.getDef().isPresent()) {
                    for (Var returnVar : m.getIR().getReturnVars()) {
                        addPFGEdge(csManager.getCSVar(curContext, returnVar),
                                csManager.getCSVar(context, invoke.getResult()));
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

            if (cur.pointer() instanceof CSVar) {
                Var n = ((CSVar) cur.pointer()).getVar();
                // since can't make a change in "context" of stmtProcessor, use a global variable to pass context of the current var
                varContext = ((CSVar) cur.pointer()).getContext();

                // deal with each obj in the diff set
                for (CSObj obj : diff) {
                    for (StoreField stmt: n.getStoreFields())
                        // x.f = y
                        addPFGEdge(csManager.getCSVar(varContext, stmt.getRValue()), csManager.getInstanceField(obj, stmt.getFieldRef().resolve()));

                    for (LoadField stmt: n.getLoadFields())
                        // y = x.f
                        addPFGEdge(csManager.getInstanceField(obj, stmt.getFieldRef().resolve()), csManager.getCSVar(varContext, stmt.getLValue()));

                    for (StoreArray stmt: n.getStoreArrays())
                        // x[i] = y
                        addPFGEdge(csManager.getCSVar(varContext, stmt.getRValue()), csManager.getArrayIndex(obj));

                    for (LoadArray stmt: n.getLoadArrays())
                        // y = x[i]
                        addPFGEdge(csManager.getArrayIndex(obj), csManager.getCSVar(varContext, stmt.getLValue()));

                    processCall((CSVar) cur.pointer(), obj);
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
        PointsToSet differencePTS = PointsToSetFactory.make();

        if (!pointsToSet.isEmpty()){
            for (CSObj obj : pointsToSet){

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
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me

        JMethod m = null;
        Context curContext = null;

        for (Invoke invoke : recv.getVar().getInvokes()){
            m = resolveCallee(recvObj, invoke);
            curContext = contextSelector.selectContext(csManager.getCSCallSite(recv.getContext(), invoke),
                    recvObj,
                    m);
            workList.addEntry(csManager.getCSVar(curContext, m.getIR().getThis()), PointsToSetFactory.make(recvObj));

            // l -> G not available in CG
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke),
                    csManager.getCSCallSite(recv.getContext(), invoke),
                    csManager.getCSMethod(curContext, m)))){

                addReachable(csManager.getCSMethod(curContext, m));

                for (int idx = 0; idx < m.getIR().getParams().size(); idx++) {
                    addPFGEdge(csManager.getCSVar(recv.getContext(), invoke.getInvokeExp().getArgs().get(idx)),
                            csManager.getCSVar(curContext, m.getIR().getParams().get(idx)));
                }

                if (invoke.getDef().isPresent()) {
                    for (Var returnVar : m.getIR().getReturnVars()) {
                        addPFGEdge(csManager.getCSVar(curContext, returnVar),
                                csManager.getCSVar(recv.getContext(), invoke.getResult()));
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
