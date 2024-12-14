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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;
import pascal.taie.language.type.Type;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me

        // init
        ArrayList<JMethod> workList = new ArrayList<>();
        workList.add(entry);

        while(!workList.isEmpty()) {
            JMethod currentMethod = workList.remove(0);
            if (!callGraph.contains(currentMethod)) {
                callGraph.addReachableMethod(currentMethod);
                for (Invoke cs: callGraph.callSitesIn(currentMethod).toList()){
                    for (JMethod targetMethod : resolve(cs)){
                        callGraph.addEdge(new Edge<Invoke, JMethod>(CallGraphs.getCallKind(cs), cs, targetMethod));
                        workList.add(targetMethod);
                    }
                }
            }
        }


        return callGraph;
    }

    private Set<JClass> allSubClasses(JClass top){
        Stack<JClass> workStack = new Stack<>();
        Set<JClass> subClasses = new HashSet<>();

        workStack.push(top);

        while(!workStack.isEmpty()){
            JClass current = workStack.pop();
            for (JClass sub : hierarchy.getDirectSubclassesOf(current)) {
                workStack.push(sub);
                subClasses.add(sub);
            }
        }

        return subClasses;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me

        Set<JMethod> T = new HashSet<>();

        if (callSite.isStatic()) {
            T.add(callSite.getMethodRef().getDeclaringClass().getDeclaredMethod(callSite.getMethodRef().getSubsignature()));
        }

        if (callSite.isSpecial()) {
            // TODO: consider other situations, e.g., private instance method, constructor, superclass instance method
            JMethod next = dispatch(callSite.getMethodRef().getDeclaringClass(), callSite.getMethodRef().getSubsignature());
            if (next != null) T.add(next);
        }

        if (callSite.isVirtual()) {
            // add itself
            JMethod next = dispatch(callSite.getMethodRef().getDeclaringClass(), callSite.getMethodRef().getSubsignature());
            if (next != null) T.add(next);

            // deal with its subclasses
            for (JClass child : allSubClasses(callSite.getMethodRef().getDeclaringClass())){
                next = dispatch(child, callSite.getMethodRef().getSubsignature());
                if (next != null) T.add(next);
            }
        }

        // TODO: invoke interface
        if (callSite.isInterface()) {
            ArrayList<JClass> workList = new ArrayList<>();
            Set<JClass> implementedClass = new HashSet<>();
            JMethod next;

            workList.add(callSite.getMethodRef().getDeclaringClass());

            while (!workList.isEmpty()) {
                JClass current = workList.remove(0);

                for (JClass sub : hierarchy.getDirectImplementorsOf(current)) {
                    implementedClass.add(sub);
                }

                // TODO: add its sub classes for each implemented? Since a class could extend another class and implement an interface.

                for (JClass sub : hierarchy.getDirectSubinterfacesOf(current)) {
                    workList.add(sub);
                }
            }


            for (JClass impl : implementedClass){
                next = dispatch(impl, callSite.getMethodRef().getSubsignature());
                if (next != null) T.add(next);

                for(JClass subcls : allSubClasses(impl)) {
                    next = dispatch(subcls, callSite.getMethodRef().getSubsignature());
                    if (next != null) T.add(next);
                }
            }
        }


        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me

        // interface class does not implement any declaring method
        // if (jclass.isInterface()) return null;

        // abstract class, interface, abstract method
        if (jclass.getDeclaredMethod(subsignature) == null){
            return dispatch(jclass.getSuperClass(), subsignature);
        }else {
            JMethod jMethod = jclass.getDeclaredMethod(subsignature);
            // if available but abstract, then returns null
            if (jMethod.isAbstract()) return null;

            // non-abstract
            return jMethod;
        }
    }
}
