package org.checkerframework.checker.guieffect;

import com.sun.source.tree.AssignmentTree;
import com.sun.source.tree.ClassTree;
import com.sun.source.tree.ExpressionTree;
import com.sun.source.tree.LambdaExpressionTree;
import com.sun.source.tree.MemberSelectTree;
import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.ReturnTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.VariableTree;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.Stack;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.TypeElement;
import javax.lang.model.element.VariableElement;
import org.checkerframework.checker.guieffect.qual.AlwaysSafe;
import org.checkerframework.checker.guieffect.qual.PolyUI;
import org.checkerframework.checker.guieffect.qual.PolyUIEffect;
import org.checkerframework.checker.guieffect.qual.SafeEffect;
import org.checkerframework.checker.guieffect.qual.UI;
import org.checkerframework.checker.guieffect.qual.UIEffect;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;
import org.checkerframework.framework.qual.PolyAll;
import org.checkerframework.framework.source.Result;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedExecutableType;
import org.checkerframework.framework.util.AnnotatedTypes;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.Pair;
import org.checkerframework.javacutil.TreeUtils;

/** Require that only UI code invokes code with the UI effect. */
public class GuiEffectVisitor extends BaseTypeVisitor<GuiEffectTypeFactory> {

    protected final boolean debugSpew;

    // effStack and currentMethods should always be the same size.
    protected final Stack<Effect> effStack;
    protected final Stack<MethodTree> currentMethods;

    public GuiEffectVisitor(BaseTypeChecker checker) {
        super(checker);
        debugSpew = checker.getLintOption("debugSpew", false);
        if (debugSpew) {
            System.err.println("Running GuiEffectVisitor");
        }
        effStack = new Stack<Effect>();
        currentMethods = new Stack<MethodTree>();
    }

    @Override
    protected GuiEffectTypeFactory createTypeFactory() {
        return new GuiEffectTypeFactory(checker, debugSpew);
    }

    // The issue is that the receiver implicitly receives an @AlwaysSafe anno, so calls on @UI
    // references fail because the framework doesn't implicitly upcast the receiver (which in
    // general wouldn't be sound).
    // TODO: Fix method receiver defaults: method-polymorphic for any polymorphic method, UI
    //       for any UI instantiations, safe otherwise
    @Override
    protected void checkMethodInvocability(
            AnnotatedExecutableType method, MethodInvocationTree node) {
        // The inherited version of this complains about invoking methods of @UI instantiations of
        // classes, which by default are annotated @AlwaysSafe, which for data type qualifiers is
        // reasonable, but it not what we want, since we want .
        // TODO: Undo this hack!
    }

    @Override
    protected boolean checkOverride(
            MethodTree overriderTree,
            AnnotatedTypeMirror.AnnotatedDeclaredType enclosingType,
            AnnotatedTypeMirror.AnnotatedExecutableType overridden,
            AnnotatedTypeMirror.AnnotatedDeclaredType overriddenType,
            Void p) {
        // Method override validity is checked manually by the type factory during visitation
        return true;
    }

    @Override
    protected Set<? extends AnnotationMirror> getExceptionParameterLowerBoundAnnotations() {
        return Collections.singleton(AnnotationUtils.fromClass(elements, AlwaysSafe.class));
    }

    @Override
    public boolean isValidUse(
            AnnotatedTypeMirror.AnnotatedDeclaredType declarationType,
            AnnotatedTypeMirror.AnnotatedDeclaredType useType,
            Tree tree) {
        boolean ret =
                useType.hasAnnotation(AlwaysSafe.class)
                        || useType.hasAnnotation(PolyAll.class)
                        || useType.hasAnnotation(PolyUI.class)
                        || atypeFactory.isPolymorphicType(
                                (TypeElement) declarationType.getUnderlyingType().asElement())
                        || (useType.hasAnnotation(UI.class)
                                && declarationType.hasAnnotation(UI.class));
        if (debugSpew && !ret) {
            System.err.println("use: " + useType);
            System.err.println("use safe: " + useType.hasAnnotation(AlwaysSafe.class));
            System.err.println("use poly: " + useType.hasAnnotation(PolyUI.class));
            System.err.println("use ui: " + useType.hasAnnotation(UI.class));
            System.err.println(
                    "declaration safe: " + declarationType.hasAnnotation(AlwaysSafe.class));
            System.err.println(
                    "declaration poly: "
                            + atypeFactory.isPolymorphicType(
                                    (TypeElement) declarationType.getUnderlyingType().asElement()));
            System.err.println("declaration ui: " + declarationType.hasAnnotation(UI.class));
            System.err.println("declaration: " + declarationType);
        }
        return ret;
    }

    // For assignments and local variable initialization:
    // Check for @UI annotations on the lhs, use them to infer @UI types on lambda expressions in the rhs
    private void inferLambdaTypeOnAssignment(Tree lhs, ExpressionTree rhs) {
        if (rhs.getKind() == Tree.Kind.LAMBDA_EXPRESSION) {
            LambdaExpressionTree lambdaTree = (LambdaExpressionTree) rhs;
            AnnotatedTypeMirror lhsType = atypeFactory.getAnnotatedType(lhs);
            if (lhsType.hasAnnotation(UI.class)) {
                ExecutableElement argFIMethodElt =
                        TreeUtils.getFunctionalInterfaceMethod(lambdaTree);
                Effect lambdaEffect = atypeFactory.getDeclaredEffect(argFIMethodElt);
                if (lambdaEffect.isPoly()) {
                    if (debugSpew) {
                        System.err.println(
                                "Lambda inferred to be @UIEffect: " + lambdaTree.getBody());
                    }
                    atypeFactory.constrainLambdaToUI(lambdaTree);
                }
            }
        }
    }

    @Override
    public Void visitVariable(VariableTree node, Void p) {
        Void result = super.visitVariable(node, p);
        if (node.getInitializer() != null && node.getInitializer().getKind() == Tree.Kind.LAMBDA_EXPRESSION) {
            // Re-do assignment check after lambda inference
            commonAssignmentCheck(
                    atypeFactory.getAnnotatedType(node),
                    node.getInitializer(),
                    "argument.type.incompatible");
        }
        return result;
    }

    @Override
    public Void visitAssignment(AssignmentTree node, Void p) {
        Void result = super.visitAssignment(node, p);
        if (node.getExpression().getKind() == Tree.Kind.LAMBDA_EXPRESSION) {
            // Re-do assignment check after lambda inference
            commonAssignmentCheck(
                    atypeFactory.getAnnotatedType(node.getVariable()),
                    node.getExpression(),
                    "argument.type.incompatible");
        }
        return result;
    }

    // Returning a lambda expression also triggers inference based on the method's return type.
    @Override
    public Void visitReturn(ReturnTree node, Void p) {
        if (node.getKind() == Tree.Kind.LAMBDA_EXPRESSION) {
            LambdaExpressionTree lambdaTree = (LambdaExpressionTree) node.getExpression();
            ExecutableElement retFIMethodElt = TreeUtils.getFunctionalInterfaceMethod(lambdaTree);
            Effect lambdaEffect = atypeFactory.getDeclaredEffect(retFIMethodElt);
            Tree callerTree = TreeUtils.enclosingMethodOrLambda(getCurrentPath());
            AnnotatedTypeMirror retType = null;
            if (callerTree.getKind() == Tree.Kind.METHOD) {
                retType = atypeFactory.getMethodReturnType((MethodTree) callerTree, node);
            } else if (callerTree.getKind() == Tree.Kind.LAMBDA_EXPRESSION) {
                // What to do about a lambda with @PolyUI return type returning another lambda? It is lambdas all the
                // way down.
                Pair<AnnotatedTypeMirror.AnnotatedDeclaredType, AnnotatedExecutableType> pair =
                        atypeFactory.getFnInterfaceFromTree((LambdaExpressionTree) callerTree);
                retType = pair.second.getReturnType();
            }
            assert retType != null;

            if (lambdaEffect.isPoly() && retType.hasAnnotation(UI.class)) {
                if (debugSpew) {
                    System.err.println("Lambda inferred to be @UIEffect: " + lambdaTree.getBody());
                }
                atypeFactory.constrainLambdaToUI(lambdaTree);
            }
        }
        return super.visitReturn(node, p);
    }

    // Check that the invoked effect is <= permitted effect (effStack.peek())
    @Override
    public Void visitMethodInvocation(MethodInvocationTree node, Void p) {
        if (debugSpew) {
            System.err.println("For invocation " + node + " in " + currentMethods.peek().getName());
        }

        // Target method annotations
        ExecutableElement methodElt = TreeUtils.elementFromUse(node);
        if (debugSpew) {
            System.err.println("methodElt found");
        }

        Tree callerTree = TreeUtils.enclosingMethodOrLambda(getCurrentPath());
        if (callerTree == null) {
            // Static initializer; let's assume this is safe to have the UI effect
            if (debugSpew) {
                System.err.println("No enclosing method: likely static initializer");
            }
            return super.visitMethodInvocation(node, p);
        }
        if (debugSpew) {
            System.err.println("callerTree found: " + callerTree.getKind());
        }

        Effect targetEffect =
                atypeFactory.getComputedEffectAtCallsite(
                        node, visitorState.getMethodReceiver(), methodElt);

        Effect callerEffect = null;
        if (callerTree.getKind() == Tree.Kind.METHOD) {
            ExecutableElement callerElt = TreeUtils.elementFromDeclaration((MethodTree) callerTree);
            if (debugSpew) {
                System.err.println("callerElt found");
            }

            callerEffect = atypeFactory.getDeclaredEffect(callerElt);
            // Field initializers inside anonymous inner classes show up with a null current-method ---
            // the traversal goes straight from the class to the initializer.
            assert (currentMethods.peek() == null || callerEffect.equals(effStack.peek()));
        } else if (callerTree.getKind() == Tree.Kind.LAMBDA_EXPRESSION) {
            callerEffect =
                    atypeFactory.getInferedEffectForLambdaExpression(
                            (LambdaExpressionTree) callerTree);
            System.err.println("lambda: " + callerTree + " with effect " + callerEffect);
            // Perform lambda polymorphic effect inference: @PolyUI lambda, calling @UIEffect => @UI lambda
            if (targetEffect.isUI() && callerEffect.isPoly()) {
                System.err.println(
                        "Poly lambda: "
                                + callerTree
                                + " calling @UIEffect method: "
                                + node
                                + " infer @UI.");
                atypeFactory.constrainLambdaToUI((LambdaExpressionTree) callerTree);
                callerEffect =
                        atypeFactory.getInferedEffectForLambdaExpression(
                                (LambdaExpressionTree) callerTree);
                //System.err.println("lambda is NOW: " + callerTree + " with effect " + callerEffect);
                assert callerEffect.isUI();
            }
        }
        assert callerEffect != null;

        if (!Effect.LE(targetEffect, callerEffect)) {
            checker.report(Result.failure("call.invalid.ui", targetEffect, callerEffect), node);
            if (debugSpew) {
                System.err.println("Issuing error for node: " + node);
            }
        }
        if (debugSpew) {
            System.err.println(
                    "Successfully finished main non-recursive checkinv of invocation " + node);
        }

        Void result = super.visitMethodInvocation(node, p);

        // Check arguments to this method invocation for UI-lambdas, this must be re-checked after visiting the lambda
        // body due to inference.
        List<? extends ExpressionTree> args = node.getArguments();
        Pair<AnnotatedExecutableType, List<AnnotatedTypeMirror>> mfuPair =
                atypeFactory.methodFromUse(node);
        AnnotatedExecutableType invokedMethod = mfuPair.first;
        List<? extends VariableElement> parameters = methodElt.getParameters();
        List<AnnotatedTypeMirror> typeargs =
                AnnotatedTypes.expandVarArgs(atypeFactory, invokedMethod, node.getArguments());
        for (int i = 0; i < args.size(); ++i) {
            if (args.get(i) instanceof LambdaExpressionTree) {
                /*LambdaExpressionTree lambdaTree = (LambdaExpressionTree) args.get(i);
                Effect lambdaEffect = atypeFactory.getInferedEffectForLambdaExpression(lambdaTree);
                AnnotatedTypeMirror lambdaType =
                        atypeFactory.getInferedTypeForLambdaExpression(lambdaTree);
                System.err.println(
                        "Call: "
                                + node
                                + " with lambda with effect "
                                + lambdaEffect
                                + " and arg: "
                                + typeargs.get(i).toString(true));*/
                commonAssignmentCheck(
                        typeargs.get(i), args.get(i), "argument.type.incompatible");
                /*if (lambdaType.hasAnnotation(UI.class)) {
                    AnnotatedTypeMirror argTypeFromArgElement =
                            atypeFactory.getAnnotatedType(parameters.get(i));
                    AnnotatedTypeMirror argTypeFromMFU = typeargs.get(i);
                    boolean argIsUI =
                            argTypeFromMFU.hasAnnotation(UI.class)
                                    || argTypeFromArgElement.hasAnnotation(UI.class);
                    boolean argIsPolyUI =
                            argTypeFromMFU.hasAnnotation(PolyUI.class)
                                    || argTypeFromArgElement.hasAnnotation(PolyUI.class);
                    if (argIsUI) {
                        continue;
                    } else if (argIsPolyUI) {
                        System.err.println("HERE: " + node);
                    }
                    // Check for @PolyUI methods instantiated @UI
                    String valueTypeString = valueTypeString = lambdaType.toString(true);
                    String varTypeString = typeargs.get(i).toString(true);
                    checker.report(
                            Result.failure(
                                    "argument.type.incompatible", valueTypeString, varTypeString),
                            node);
                }*/
            }
        }

        return result;
    }

    @Override
    public Void visitMethod(MethodTree node, Void p) {
        // TODO: If the type we're in is a polymorphic (over effect qualifiers) type, the receiver must be @PolyUI.
        //       Otherwise a "non-polymorphic" method of a polymorphic type could be called on a UI instance, which then
        //       gets a Safe reference to itself (unsound!) that it can then pass off elsewhere (dangerous!).  So all
        //       receivers in methods of a @PolyUIType must be @PolyUI.
        // TODO: What do we do then about classes that inherit from a concrete instantiation?  If it subclasses a Safe
        //       instantiation, all is well.  If it subclasses a UI instantiation, then the receivers should probably
        //       be @UI in both new and override methods, so calls to polymorphic methods of the parent class will work
        //       correctly.  In which case for proving anything, the qualifier on sublasses of UI instantiations would
        //       always have to be @UI... Need to write down |- t for this system!  And the judgments for method overrides
        //       and inheritance!  Those are actually the hardest part of the system.

        ExecutableElement methElt = TreeUtils.elementFromDeclaration(node);
        if (debugSpew) {
            System.err.println("\nVisiting method " + methElt);
        }

        // Check for conflicting (multiple) annotations
        assert (methElt != null);
        // TypeMirror scratch = methElt.getReturnType();
        AnnotationMirror targetUIP = atypeFactory.getDeclAnnotation(methElt, UIEffect.class);
        AnnotationMirror targetSafeP = atypeFactory.getDeclAnnotation(methElt, SafeEffect.class);
        AnnotationMirror targetPolyP = atypeFactory.getDeclAnnotation(methElt, PolyUIEffect.class);
        TypeElement targetClassElt = (TypeElement) methElt.getEnclosingElement();

        if ((targetUIP != null && (targetSafeP != null || targetPolyP != null))
                || (targetSafeP != null && targetPolyP != null)) {
            checker.report(Result.failure("annotations.conflicts"), node);
        }
        if (targetPolyP != null && !atypeFactory.isPolymorphicType(targetClassElt)) {
            checker.report(Result.failure("polymorphism.invalid"), node);
        }
        if (targetUIP != null && atypeFactory.isUIType(targetClassElt)) {
            checker.report(Result.warning("effects.redundant.uitype"), node);
        }

        // TODO: Report an error for polymorphic method bodies??? Until we fix the receiver defaults, it won't really be correct
        @SuppressWarnings("unused") // call has side-effects
        Effect.EffectRange range =
                atypeFactory.findInheritedEffectRange(
                        ((TypeElement) methElt.getEnclosingElement()), methElt, true, node);
        if (targetUIP == null && targetSafeP == null && targetPolyP == null) {
            // implicitly annotate this method with the LUB of the effects of the methods it overrides
            // atypeFactory.fromElement(methElt).addAnnotation(range != null ? range.min.getAnnot() : (isUIType(((TypeElement)methElt.getEnclosingElement())) ? UI.class : AlwaysSafe.class));
            // TODO: This line does nothing! AnnotatedTypeMirror.addAnnotation
            // silently ignores non-qualifier annotations!
            // System.err.println("ERROR: TREE ANNOTATOR SHOULD HAVE ADDED EXPLICIT ANNOTATION! ("+node.getName()+")");
            atypeFactory
                    .fromElement(methElt)
                    .addAnnotation(atypeFactory.getDeclaredEffect(methElt).getAnnot());
        }

        // We hang onto the current method here for ease.  We back up the old
        // current method because this code is reentrant when we traverse methods of an inner class
        currentMethods.push(node);
        // effStack.push(targetSafeP != null ? new Effect(AlwaysSafe.class) :
        //                (targetPolyP != null ? new Effect(PolyUI.class) :
        //                   (targetUIP != null ? new Effect(UI.class) :
        //                      (range != null ? range.min : (isUIType(((TypeElement)methElt.getEnclosingElement())) ? new Effect(UI.class) : new Effect(AlwaysSafe.class))))));
        effStack.push(atypeFactory.getDeclaredEffect(methElt));
        if (debugSpew) {
            System.err.println(
                    "Pushing " + effStack.peek() + " onto the stack when checking " + methElt);
        }

        Void ret = super.visitMethod(node, p);
        currentMethods.pop();
        effStack.pop();
        return ret;
    }

    @Override
    public Void visitMemberSelect(MemberSelectTree node, Void p) {
        //TODO: Same effect checks as for methods
        return super.visitMemberSelect(node, p);
    }

    @Override
    public void processClassTree(ClassTree node) {
        // TODO: Check constraints on this class decl vs. parent class decl., and interfaces
        // TODO: This has to wait for now: maybe this will be easier with the isValidUse on the TypeFactory
        // AnnotatedTypeMirror.AnnotatedDeclaredType atype = atypeFactory.fromClass(node);

        // Push a null method and UI effect onto the stack for static field initialization
        // TODO: Figure out if this is safe! For static data, almost certainly,
        // but for statically initialized instance fields, I'm assuming those
        // are implicitly moved into each constructor, which must then be @UI
        currentMethods.push(null);
        effStack.push(new Effect(UIEffect.class));
        super.processClassTree(node);
        currentMethods.pop();
        effStack.pop();
    }
}
