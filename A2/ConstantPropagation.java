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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        // if the current stmt (entry) is a function call
        // init its args as NAC, otherwise, transferNode will not work out

        CPFact fact = new CPFact();
        fact.clear();

        for(Var param: cfg.getMethod().getIR().getParams()){
            if (!canHoldInt(param)) continue;
            fact.update(param, Value.getNAC());
        }

        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        // as usual, create an empty dict
        // iterate the cfg except the entry node
        CPFact fact = new CPFact();
        fact.clear();
        return fact;
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me

        // we don't need to clear the set because this analysis is monotonic
        // a set always grows up than shrinks down

        // update its value in a key
        for (Var key : fact.keySet()){
            Value res = meetValue(fact.get(key), target.get(key));
            target.update(key, res);
        }
    }

    /**
     * Meets two Values.
     */
    /**
     * Meets two Values.
     */

    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        // intersection of two dict or set
        if (v1.isNAC() || v2.isNAC()) {
            // NAC ⊓ x = NAC
            return Value.getNAC();
        }

        if (v2.isUndef() && !v1.isNAC()) {
            // UNDEF ⊓ x = x
            return v1;
        }

        if (v1.isUndef() && !v2.isNAC()) {
            // UNDEF ⊓ x = x
            return v2;
        }

        if(v1.isConstant() && v2.isConstant()){
            if (v1.getConstant() == v2.getConstant()) {
                return v1;
            }
            else {
                return Value.getNAC();
            }
        }


        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me


        // no left value or left val is not a var
        if (!stmt.getDef().isPresent() || !(stmt.getDef().get() instanceof Var)) {
            if (in.equals(out))
                return false;

            out.clear();
            out.copyFrom(in);
            return true;
        }

        if(!canHoldInt((Var) stmt.getDef().get())) {
            if (in.equals(out))
                return false;

            out.clear();
            out.copyFrom(in);
            return true;
        }

        DefinitionStmt def = (DefinitionStmt) stmt;

        CPFact old_out = out.copy();
        out.copyFrom(in);

        out.update((Var) def.getLValue(), evaluate(def.getRValue(), in));

        if (old_out.equals(out)) return false;

        return true;

    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me

        if (exp instanceof Var){
            return in.get((Var) exp);
        }

        if (exp instanceof IntLiteral){
            return Value.makeConstant(((IntLiteral)exp).getValue());
        }

        if (exp instanceof ArithmeticExp){

            Value operand_1 = in.get(((ArithmeticExp) exp).getOperand1());
            Value operand_2 = in.get(((ArithmeticExp) exp).getOperand2());

            switch (((ArithmeticExp)exp).getOperator().toString()){
                case "+":

                    if (operand_1.isNAC() || operand_2.isNAC()) {
                        return Value.getNAC();
                    }

                    if (operand_1.isUndef() || operand_2.isUndef()) {
                        return Value.getUndef();
                    }

                    return Value.makeConstant(operand_1.getConstant() + operand_2.getConstant());
                case "-":

                    if (operand_1.isNAC() || operand_2.isNAC()) {
                        return Value.getNAC();
                    }

                    if (operand_1.isUndef() || operand_2.isUndef()) {
                        return Value.getUndef();
                    }

                    return Value.makeConstant(operand_1.getConstant() - operand_2.getConstant());

                case "*":

                    if (operand_1.isNAC() || operand_2.isNAC()) {
                        return Value.getNAC();
                    }

                    if (operand_1.isUndef() || operand_2.isUndef()) {
                        return Value.getUndef();
                    }

                    return Value.makeConstant(operand_1.getConstant() * operand_2.getConstant());

                case "/":

                    if (operand_1.isNAC() || operand_2.isNAC()) {
                        if (operand_2.isConstant())
                            if (operand_2.getConstant() == 0)
                                return  Value.getUndef();
                        return Value.getNAC();
                    }

                    if (operand_1.isUndef() || operand_2.isUndef()) {
                        return Value.getUndef();
                    }

                    if(operand_2.getConstant() == 0) return Value.getUndef();

                    return Value.makeConstant(operand_1.getConstant() / operand_2.getConstant());
                case "%":

                    if (operand_1.isNAC() || operand_2.isNAC()) {
                        if (operand_2.isConstant())
                            if (operand_2.getConstant() == 0)
                                return  Value.getUndef();
                        return Value.getNAC();
                    }

                    if (operand_1.isUndef() || operand_2.isUndef()) {
                        return Value.getUndef();
                    }

                    if(operand_2.getConstant() == 0) return Value.getUndef();

                    return Value.makeConstant(operand_1.getConstant() % operand_2.getConstant());
            }
        }

        if (exp instanceof BitwiseExp){

            Value operand_1 = in.get(((BitwiseExp) exp).getOperand1());
            Value operand_2 = in.get(((BitwiseExp) exp).getOperand2());

            if (operand_1.isNAC() || operand_2.isNAC()) {
                return Value.getNAC();
            }

            if (operand_1.isUndef() || operand_2.isUndef()) {
                return Value.getUndef();
            }

            switch (((BitwiseExp)exp).getOperator().toString()){
                case "|":
                    return Value.makeConstant(operand_1.getConstant() | operand_2.getConstant());
                case "^":
                    return Value.makeConstant(operand_1.getConstant() ^ operand_2.getConstant());
                case "&":
                    return Value.makeConstant(operand_1.getConstant() & operand_2.getConstant());
            }
        }

        if (exp instanceof ConditionExp){

            Value operand_1 = in.get(((ConditionExp) exp).getOperand1());
            Value operand_2 = in.get(((ConditionExp) exp).getOperand2());

            if (operand_1.isNAC() || operand_2.isNAC()) {
                return Value.getNAC();
            }

            if (operand_1.isUndef() || operand_2.isUndef()) {
                return Value.getUndef();
            }

            switch (((ConditionExp)exp).getOperator().toString()){
                case "==":
                    if (operand_1.getConstant() == operand_2.getConstant())
                        return Value.makeConstant(1);
                    return Value.makeConstant(0);
                case "!=":
                    if (operand_1.getConstant() != operand_2.getConstant())
                        return Value.makeConstant(1);
                    return Value.makeConstant(0);
                case "<":
                    if (operand_1.getConstant() < operand_2.getConstant())
                        return Value.makeConstant(1);
                    return Value.makeConstant(0);
                case ">":
                    if (operand_1.getConstant() > operand_2.getConstant())
                        return Value.makeConstant(1);
                    return Value.makeConstant(0);
                case "<=":
                    if (operand_1.getConstant() <= operand_2.getConstant())
                        return Value.makeConstant(1);
                    return Value.makeConstant(0);
                case ">=":
                    if (operand_1.getConstant() >= operand_2.getConstant())
                        return Value.makeConstant(1);
                    return Value.makeConstant(0);
            }
        }

        if (exp instanceof ShiftExp){

            Value operand_1 = in.get(((ShiftExp) exp).getOperand1());
            Value operand_2 = in.get(((ShiftExp) exp).getOperand2());

            if (operand_1.isNAC() || operand_2.isNAC()) {
                return Value.getNAC();
            }

            if (operand_1.isUndef() || operand_2.isUndef()) {
                return Value.getUndef();
            }

            switch (((ShiftExp)exp).getOperator().toString()){
                case "<<":
                    return Value.makeConstant(operand_1.getConstant() << operand_2.getConstant());
                case ">>":
                    return Value.makeConstant(operand_1.getConstant() >> operand_2.getConstant());
                case ">>>":
                    return Value.makeConstant(operand_1.getConstant() >>> operand_2.getConstant());
            }
        }

        return Value.getNAC();
    }
}
