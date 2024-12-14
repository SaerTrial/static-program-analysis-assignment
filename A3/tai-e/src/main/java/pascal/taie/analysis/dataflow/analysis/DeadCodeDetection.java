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

import org.checkerframework.checker.units.qual.C;
import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import soot.jimple.StmtSwitch;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }


    public ArrayList<Stmt> walkCFG(CFG<Stmt> cfg){

        ArrayList<Stmt> walkedStmt = new ArrayList<Stmt>();

        Stack<Stmt> workStack = new Stack<Stmt>();

        workStack.push(cfg.getEntry());

        while (!workStack.isEmpty()) {
            Stmt cur = workStack.pop();

            if (walkedStmt.contains(cur)) continue;

            if (cfg.getExit().equals(cur)) {
                walkedStmt.add(cur);
                continue;
            }

            for (Stmt succ : cfg.getSuccsOf(cur)) {
                workStack.push(succ);
            }

            walkedStmt.add(cur);
        }

        return walkedStmt;

    }

    // return
    Stmt analyzeIf(CFG<Stmt> cfg, If stmt_if, Set<Stmt>unreachable) {
        Stmt exit = null;
        Stack<Stmt> workStack = new Stack<Stmt>();

        unreachable.add(stmt_if);

        // TODO: add a goto edge in unreachable first, avoid failure of further checking
        for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt_if)) {
            if (!edge.getTarget().canFallThrough()) {
                unreachable.add(edge.getTarget());
                for (Edge<Stmt> gotoEdge : cfg.getOutEdgesOf(edge.getTarget())) {
                    workStack.push(gotoEdge.getTarget());
                }
            }
            else {
                workStack.push(edge.getTarget());
            }
        }

        while (!workStack.isEmpty()) {
            Stmt cur = workStack.pop();


            if (cur instanceof If)
                cur = analyzeIf(cfg, (If) cur, unreachable);

            // since we have already checked the goto at the edge of if stmt,
            // we just skip goto whenever come across them
            // note that we identify exit point if this goto does not jump backwards
            if (!cur.canFallThrough()) {
                unreachable.add(cur);

                // appliable for "for", "while" loop
                if(exit == null){
                    for (Edge<Stmt> jumpEdge : cfg.getOutEdgesOf(cur)) {
                        if(jumpEdge.getSource().getLineNumber() <= jumpEdge.getTarget().getLineNumber()){
                            exit = jumpEdge.getTarget();
                        }

                        if(jumpEdge.getSource().getLineNumber() == jumpEdge.getTarget().getLineNumber())
                            if (jumpEdge.getSource().getIndex() < jumpEdge.getTarget().getIndex()) {
                                exit = jumpEdge.getTarget();
                            }
                    }
                }

                continue;
            }


            if (cfg.getInEdgesOf(cur).size() == 2) {
                // if-else stmt uses a node with two in edges as an exit point
                // Hack: check if the node is a pred of while stmt
                boolean nextIf = false;
                unreachable.add(cur);
                for (Edge<Stmt> edge : cfg.getOutEdgesOf(cur)) {
                    if(edge.getTarget() instanceof If)
                        nextIf = true;
                    else
                        exit = edge.getTarget();
                }


                if (!nextIf) continue;
            }


            for (Stmt succ : cfg.getSuccsOf(cur)) {
                workStack.push(succ);
            }

            unreachable.add(cur);
        }

        return exit;
    }


    Stmt analyzeSwitch(CFG<Stmt> cfg, SwitchStmt sw, Set<Stmt> unreachable) {
        Stmt exit = null;

        for (Edge<Stmt> edge : cfg.getOutEdgesOf((Stmt) sw)) {
            Stack<Stmt> workStack = new Stack<Stmt>();
            workStack.push(edge.getTarget());

            while(!workStack.isEmpty()) {
                Stmt cur = workStack.pop();

                if (cur instanceof If) {
                    cur = analyzeIf(cfg, (If) cur, unreachable);
                    // Hack: a new node have to go through all checking again
                    workStack.push(cur);
                    continue;
                }

                if (cur instanceof SwitchStmt) {
                    cur = analyzeSwitch(cfg, (SwitchStmt) cur, unreachable);
                    workStack.push(cur);
                    continue;
                }

                if (!cur.canFallThrough()) {
                    boolean nonStop = false;

                    unreachable.add(cur);

                    for (Edge<Stmt> curEdge : cfg.getOutEdgesOf(cur)){
                        if (exit == null)
                            exit = curEdge.getTarget();

                        if (cfg.getInEdgesOf(curEdge.getTarget()).size() == 1) {
                            nonStop = true;
                            exit = null;
                        }
                    }

                    if(!nonStop) continue;
                }

                for (Stmt succ : cfg.getSuccsOf(cur)){
                    workStack.push(succ);
                }

                unreachable.add(cur);
            }

        }

        return exit;
    }



    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me

        // CFG iteration - unreachable nodes
        // Constprop - unreachable branch
        // Live var - dead assignment

        ArrayList<Stmt> walkedStmt = walkCFG(cfg);
        ArrayList<Stmt> workListWalkedStmt  = new ArrayList<>(walkedStmt);
        // deal with stmts unreachable in CFG
        Set<Stmt> unreachableCFGStmt = new HashSet<Stmt>();

        while(!workListWalkedStmt.isEmpty()){
        //for (Stmt stmt: walkedStmt){
            // dead assignment
            Stmt stmt = workListWalkedStmt.remove(0);

            // FIXME: is it doable if we skip a node already in unreachable stmt?
            if (unreachableCFGStmt.contains(stmt)) continue;

            if (stmt instanceof AssignStmt) {
                AssignStmt assignStmt = (AssignStmt) stmt;
                if (!hasNoSideEffect(assignStmt.getRValue())) continue;

                // checking left val
                if (!(assignStmt.getLValue() instanceof Var)) continue;

                if (liveVars.getOutFact(stmt).contains((Var) assignStmt.getLValue()))
                    continue;

                unreachableCFGStmt.add(stmt);
            }

            if (stmt instanceof If) {
                If stmt_if = (If) stmt;
                Value res = ConstantPropagation.evaluate(stmt_if.getCondition(), constants.getInFact(stmt));
                Edge<Stmt> deadEdge = null;

                if (res.isConstant()) {
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt_if)){
                        if (edge.getKind() == Edge.Kind.IF_FALSE && res.getConstant() == 1)
                            deadEdge = edge;

                        if (edge.getKind() == Edge.Kind.IF_TRUE && res.getConstant() == 0)
                            deadEdge = edge;
                    }

                    Stack<Stmt> workStack = new Stack<Stmt>();

                    // add first to avoid confusion of further checking
                    if (!deadEdge.getTarget().canFallThrough()){
                        unreachableCFGStmt.add(deadEdge.getTarget());
                        for (Edge<Stmt> gotoEdge : cfg.getOutEdgesOf(deadEdge.getTarget())){
                            workStack.push(gotoEdge.getTarget());
                        }
                    }
                    else {
                        workStack.push(deadEdge.getTarget());
                    }

                    while(!workStack.isEmpty()){
                        Stmt cur = workStack.pop();

                        if(cur instanceof If) {
                            cur = analyzeIf(cfg, (If) cur, unreachableCFGStmt);
                            workStack.push(cur);
                            continue;
                        }

                        if (cur instanceof SwitchStmt) {
                            cur = analyzeSwitch(cfg, (SwitchStmt) cur, unreachableCFGStmt);
                            workStack.push(cur);
                            continue;
                        }

                        // if stmt may have one branch pointing to a return (outside) or goto (while, for)
                        if (!cur.canFallThrough()) {
                            unreachableCFGStmt.add(cur);
                            continue;
                        }

                        // FIXME: this approach would miss a nop for if-else stmt sometimes
                        if (cfg.getInEdgesOf(cur).size() == 2) {
                            // Hack: check if the node is a pred of while stmt
                            boolean nextIf = false;

                            for (Edge<Stmt> edge : cfg.getOutEdgesOf(cur)) {
                                if(edge.getTarget() instanceof If)
                                    nextIf = true;
                            }

                            if (!nextIf) continue;
                        }


                        for (Stmt succ : cfg.getSuccsOf(cur)){
                            workStack.push(succ);
                        }

                        unreachableCFGStmt.add(cur);
                    }
                }
            }

            if (stmt instanceof SwitchStmt) {
                Set<Stmt> reachable = new HashSet<>();
                Set<Stmt> operatingSwitch = null;
                boolean notAllowed = false;

                if (!constants.getOutFact(stmt).get(((SwitchStmt) stmt).getVar()).isConstant()) continue;
                int switchConst = constants.getOutFact(stmt).get(((SwitchStmt) stmt).getVar()).getConstant();

                for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)){
                    operatingSwitch = unreachableCFGStmt;

                    if(edge.getKind() == Edge.Kind.SWITCH_CASE) {
                        if (edge.getCaseValue() == switchConst)
                            operatingSwitch = reachable;
                    }
                    else if (edge.getKind() == Edge.Kind.SWITCH_DEFAULT) {
                        if(!((SwitchStmt) stmt).getCaseValues().contains(switchConst))
                            operatingSwitch = reachable;
                    }

                    Stack<Stmt> workStack = new Stack<Stmt>();
                    workStack.push(edge.getTarget());

                    while(!workStack.isEmpty()){
                        Stmt cur = workStack.pop();
                        notAllowed = false;

                        if (cur instanceof If) {
                            cur = analyzeIf(cfg, (If) cur, operatingSwitch);
                            workStack.push(cur);
                            continue;
                        }

                        if (cur instanceof SwitchStmt) {
                            operatingSwitch.add(cur);
                            cur = analyzeSwitch(cfg, (SwitchStmt) cur, operatingSwitch);
                            operatingSwitch.add(cur);
                            workStack.push(cur);
                            continue;
                        }

                        if (cur instanceof Nop) {
                            if (operatingSwitch == unreachableCFGStmt)
                                if (cfg.getInEdgesOf(cur).size() > 1)
                                    notAllowed = true;
                        }

                        if (cur instanceof AssignStmt) {
                            AssignStmt assignStmt = (AssignStmt) cur;
                            if (!hasNoSideEffect(assignStmt.getRValue()) && operatingSwitch == reachable)
                                // with side effect
                                notAllowed = true;

                            // checking left val
                            if (operatingSwitch == reachable)
                                if (assignStmt.getLValue() instanceof Var)
                                    if (!liveVars.getOutFact(assignStmt).contains((Var) assignStmt.getLValue()))
                                        notAllowed = true;
                        }


                        if (!cur.canFallThrough()) {
                            // Return will introduce false positives, think about why?
                            // maybe return leads to side effect?


//                            if (cur instanceof Goto)  operatingSwitch.add(cur);
//                            continue;

                            boolean nonStop = false;

                            if (cur instanceof Goto)  {
                                operatingSwitch.add(cur);
                                for (Edge<Stmt> edgeStop : cfg.getOutEdgesOf(cur)) {
                                    if(cfg.getInEdgesOf(edgeStop.getTarget()).size() == 1)
                                        nonStop = true;
                                }
                            }

                            if (!nonStop) continue;
                        }

                        for (Stmt succ : cfg.getSuccsOf(cur)){
                            workStack.push(succ);
                        }

                        if(!notAllowed)
                            operatingSwitch.add(cur);
                    }
                }

                Set<Stmt> duplicates = new HashSet<>(reachable);
                duplicates.retainAll(unreachableCFGStmt);
                unreachableCFGStmt.removeAll(duplicates);

            }

        }

        Set<Stmt> tmp = new HashSet<>();
        tmp.addAll(cfg.getNodes());
        tmp.removeAll(walkedStmt);

        //        unreachableCFGStmt.addAll(cfg.getNodes());
//        unreachableCFGStmt.removeAll(walkedStmt);
        unreachableCFGStmt.addAll(tmp);

        deadCode.addAll(unreachableCFGStmt);
        unreachableCFGStmt.clear();

        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
