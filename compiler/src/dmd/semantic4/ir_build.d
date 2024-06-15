module dmd.semantic4.ir_build;
import dmd.semantic4.ir;
import dmd.semantic4.utils;
import dmd.arraytypes;
import dmd.root.region;
import dmd.visitor;
import dmd.astcodegen;
import dmd.dmodule;
import dmd.mtype;
import dmd.astenums;
import dmd.ast_node;
import dmd.identifier;
import dmd.dsymbol;
import dmd.tokens;
import dmd.expression;
import dmd.typesem;
import core.stdc.stdio : printf;

//version = DebugEndOfModuleSymbols;

extern (C++) final class FindAllFunctionsVisitor : SemanticTimeTransitiveVisitor
{
    alias visit = SemanticTimeTransitiveVisitor.visit;

    int depth;
    bool doTrace, debugIR;
    size_t maxNumberOfNamedVariables, maxNumberOfUnnamedVariables, maxNumberOfLabels;

    Module theModule;

    Verify4IRNode** pointerToNextSibling;
    Verify4IRVariable* lastVariableInExpressionLoadedInto;

    Verify4IRLabel* currentStatementLabel, currentDefaultLabel;

    extern (D) void trace(string func = __PRETTY_FUNCTION__)
    {
        if (!doTrace)
            return;

        version (all)
        {
            enum ToSlice = "extern (C++) void dmd.semantic4.ir_build.FindAllFunctionsVisitor.visit";

            printf("%*strace %s\n", this.depth * 2, "".ptr, func[ToSlice.length .. $].ptr);
        }
    }

    Verify4IRVariable* startExpression(ASTCodegen.Expression exp)
    {
        if (exp is null)
            return null;

        Verify4IRVariable* oldLastVariableInExpressionLoadedInto = this
            .lastVariableInExpressionLoadedInto;

        scope (exit)
        {
            this.lastVariableInExpressionLoadedInto = oldLastVariableInExpressionLoadedInto;
        }

        exp.accept(this);

        return this.lastVariableInExpressionLoadedInto;
    }

    Verify4IRScope* startScope(ref Verify4IRScope* previous,
            ASTCodegen.Expression e, ASTCodegen.Statement s, Verify4IRLabel* label = null)
    {
        if (e is null && s is null)
            return null;

        Verify4IRNode** oldPointerToNextSibling = pointerToNextSibling;
        Verify4IRVariable* oldLastVariableInExpressionLoadedInto = lastVariableInExpressionLoadedInto;

        scope (exit)
        {
            pointerToNextSibling = oldPointerToNextSibling;
            lastVariableInExpressionLoadedInto = oldLastVariableInExpressionLoadedInto;
        }

        Verify4IRScope* ret = threadState.allocateScope(previous);

        pointerToNextSibling = &ret.firstChild;
        lastVariableInExpressionLoadedInto = null;

        if (e !is null)
        {
            Verify4IRVariable* eVar = startExpression(e);
            if (eVar !is null)
                emitLoadReferenceVia(eVar, null, eVar.isTypeAPointer, eVar.willBeBorrowed);
        }

        if (s !is null)
        {
            if (label !is null)
            {
                if (auto scs = s.isScopeStatement())
                    threadState.mapToLabel(label, scs);
            }

            s.accept(this);
        }

        return ret;
    }

    Verify4IRScope* startScope(ref Verify4IRScope* previous, ASTCodegen.Expression e1, ASTCodegen.Expression e2,
            Verify4IRVariable* loadInto, out Verify4IRVariable* e1Var, out Verify4IRVariable* e2Var)
    {
        if (e1 is null && e2 is null)
            return null;

        Verify4IRNode** oldPointerToNextSibling = pointerToNextSibling;
        Verify4IRVariable* oldLastVariableInExpressionLoadedInto = lastVariableInExpressionLoadedInto;

        scope (exit)
        {
            pointerToNextSibling = oldPointerToNextSibling;
            lastVariableInExpressionLoadedInto = oldLastVariableInExpressionLoadedInto;
        }

        Verify4IRScope* ret = threadState.allocateScope(previous);

        pointerToNextSibling = &ret.firstChild;
        lastVariableInExpressionLoadedInto = null;

        if (e1 !is null)
        {
            e1Var = startExpression(e1);
            if (e1Var !is null)
                emitLoadReferenceVia(e1Var, null, e1Var.isTypeAPointer, e1Var.willBeBorrowed);
        }

        if (loadInto !is null)
        {
            e2Var = startExpression(e2);
            emitWrite(loadInto, e2Var);
        }
        else
        {
            e2Var = startExpression(e2);
            if (e2Var !is null)
                emitLoadReferenceVia(e2Var, null, e2Var.isTypeAPointer, e2Var.willBeBorrowed);
        }

        return ret;
    }

    Verify4IRVariable* allocateLiteral(bool isPointer)
    {
        Verify4IRVariable* variable = threadState.allocateVariable(isPointer, false, false);
        variable.isLiteral = true;

        this.lastVariableInExpressionLoadedInto = variable;
        return variable;
    }

    Verify4IRVariable* emitLoadReferenceVia(Verify4IRVariable* context,
            Verify4IRVariable* offset, bool isDestinationTypePointer, bool isDestinationBorrowed)
    {
        Verify4IRNode* loadReferenceVia = threadState.allocateNode(this.pointerToNextSibling,
                Verify4IRNode.Type.LoadReferenceVia);
        loadReferenceVia.loadViaReferenceContextVariable = context;
        loadReferenceVia.loadViaReferenceOffsetVariable = offset;

        Verify4IRVariable* destination = threadState.allocateVariable(
                isDestinationTypePointer, isDestinationBorrowed, false);
        loadReferenceVia.loadViaReferenceDestinationVariable = destination;

        this.lastVariableInExpressionLoadedInto = destination;
        return destination;
    }

    void emitWrite(Verify4IRVariable* destination, Verify4IRVariable* source)
    {
        Verify4IRNode* write = threadState.allocateNode(this.pointerToNextSibling,
                Verify4IRNode.Type.WriteByValue);
        write.writeSourceVariable = source;
        write.writeDestinationVariable = destination;
    }

    void emitReturn()
    {
        threadState.allocateNode(this.pointerToNextSibling, Verify4IRNode.Type.Return);
    }

    Verify4IRVariable* allocateReturnVariable(ASTCodegen.FuncDeclaration d)
    {
        if (d is null)
            return null;

        TypeFunction tf = d.type.isTypeFunction();
        assert(tf !is null);

        // if the return type is null then we are guaranteed to not have a return value
        if (tf.next is null || isTyWithoutValue(tf.next.ty))
            return null;
        else if (d.vresult is null)
        {
            // Allocate the variable as unnamed
            return threadState.allocateVariable(isTypePointer(tf.next), false, true);
        }
        else
        {
            return cast(Verify4IRVariable*) threadState.allocateNamedVariable(d.vresult,
                    Verify4IRNamedVariable.Type.Return);
        }
    }

public:

    VerificationDFAThreadState* threadState;
    int seenFunctions;

    void visitFunctionDeclaration(ASTCodegen.FuncDeclaration d)
    {
        trace();

        this.depth++;
        if (this.doTrace)
            printf("%*s[[%s]] %s\n", this.depth * 2, "".ptr, d.toChars, d.locToChars);

        scope (exit)
        {
            if (this.doTrace)
                printf("%*s{{%s}} %s\n", this.depth * 2, "".ptr, d.toChars, d.locToChars);
            this.depth--;
        }

        if (d.type is null)
            return;
        else if (d.semanticRun < PASS.semantic3done)
            return;
        else if (d.isCsymbol())
            return; // Obviously C cannot be memory verified, so don't try to.

        // if you never processed it, is it really seen?
        this.seenFunctions++;

        auto oldAllocatorState = threadState.allocator.savePos();
        auto oldPointerToNextSibling = this.pointerToNextSibling;

        Verify4IRFunction* currentFunction = threadState.allocateFunction(d);

        if (currentFunction !is threadState.irRoot.currentFunction)
        {
            // we've seen this function before???
            return;
        }

        assert(currentFunction is threadState.irRoot.currentFunction, d.toString());
        this.pointerToNextSibling = &currentFunction.topScope.firstChild;

        scope (exit)
        {
            if (this.debugIR && currentFunction.parent is null)
                threadState.irRoot.debugMe();

            threadState.irRoot.currentFunction = currentFunction.parent;
            this.pointerToNextSibling = oldPointerToNextSibling;

            if (threadState.irRoot.currentFunction is null)
            {
                // TODO: it's DFA time!

                threadState.irRoot = Verify4IRRoot.init;
                threadState.allocator.release(oldAllocatorState);

                version (all)
                {
                    if (this.maxNumberOfNamedVariables < threadState.numberOfNamedVariables)
                        this.maxNumberOfNamedVariables = threadState.numberOfNamedVariables;
                    if (this.maxNumberOfUnnamedVariables < threadState.numberOfUnnamedVariables)
                        this.maxNumberOfUnnamedVariables = threadState.numberOfUnnamedVariables;
                    if (this.maxNumberOfLabels < threadState.numberOfLabels)
                        this.maxNumberOfLabels = threadState.numberOfLabels;
                    threadState.numberOfNamedVariables = 0;
                    threadState.numberOfUnnamedVariables = 0;
                    threadState.numberOfLabels = 0;
                }
            }
        }

        TypeFunction tf = d.type.isTypeFunction();
        assert(tf !is null);

        if (d.vthis !is null)
        {
            assert(d.vthis.type !is null);
            const isPointer = isTypePointer(d.vthis.type);

            currentFunction.contextVariable = threadState.allocateNamedVariable(d.vthis, isPointer
                    ? Verify4IRNamedVariable.Type.ThisByPointer
                    : Verify4IRNamedVariable.Type.ThisByReference);
        }

        // Note we don't care about function parameters/return,
        //  DIP1000 escape analysis has already occured so guarantees
        //  wrt. scope and return have already been applied.

        if (d.parameters !is null)
        {
            foreach (param; *d.parameters)
            {
                threadState.allocateNamedVariable(param, Verify4IRNamedVariable.Type.Parameter);
            }
        }

        currentFunction.returnVariable = this.allocateReturnVariable(d);

        {
            this.visitFunctionType(tf, null);

            if (d.frequires)
            {
                foreach (frequire; *d.frequires)
                {
                    frequire.accept(this);
                }
            }

            if (d.fensures)
            {
                foreach (fensure; *d.fensures)
                {
                    fensure.ensure.accept(this);
                }
            }

            if (d.fbody)
            {
                d.fbody.accept(this);
            }
        }
    }

override:

    void visitFuncBody(ASTCodegen.FuncDeclaration d)
    {
        this.visit(d);
    }

    void visit(ASTCodegen.FuncDeclaration d)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if ((d.storage_class & STC.static_) != 0)
        {
            Verify4IRRoot oldIrRoot = threadState.irRoot;
            threadState.irRoot = Verify4IRRoot.init;

            scope (exit)
                threadState.irRoot = oldIrRoot;

            visitFunctionDeclaration(d);
        }
        else
            visitFunctionDeclaration(d);
    }

    override void visit(ASTCodegen.ClassDeclaration d)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (!d.isNested())
        {
            Verify4IRRoot oldIrRoot = threadState.irRoot;
            threadState.irRoot = Verify4IRRoot.init;

            scope (exit)
                threadState.irRoot = oldIrRoot;

            super.visit(d);
        }
        else
            super.visit(d);
    }

    // also covers unions
    override void visit(ASTCodegen.StructDeclaration d)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (!d.isNested())
        {
            Verify4IRRoot oldIrRoot = threadState.irRoot;
            threadState.irRoot = Verify4IRRoot.init;

            scope (exit)
                threadState.irRoot = oldIrRoot;

            super.visit(d);
        }
        else
            super.visit(d);
    }

    void visit(ASTCodegen.VarDeclaration d)
    {
        version (DebugEndOfModuleSymbols)
        {
        }
        else
        {
            if (threadState.irRoot.currentFunction is null)
                return;
        }

        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (threadState.irRoot.currentFunction is null)
            return;

        assert(d.ident !is null);

        Verify4IRNamedVariable* variable = threadState.allocateNamedVariable(d,
                Verify4IRNamedVariable.Type.Declared);

        if (d._init !is null)
        {
            if (auto expInitializer = d._init.isExpInitializer())
            {
                if (expInitializer.exp.op.isEXPLiteral)
                {
                    emitWrite(cast(Verify4IRVariable*) variable,
                            this.allocateLiteral(isTypePointer(expInitializer.exp.type)));
                }
                else if (expInitializer.exp.isConstructExp)
                {
                    expInitializer.exp.accept(this);
                }
                else if (auto commaExp = expInitializer.exp.isCommaExp)
                {
                    // we only care about commaExp.e2, commaExp.e1 was rewritten into the other
                    emitWrite(cast(Verify4IRVariable*) variable, startExpression(commaExp.e2));
                }
                else
                {
                    emitWrite(cast(Verify4IRVariable*) variable,
                            startExpression(expInitializer.exp));

                    version (none)
                    {
                        printf("%d %s at %s\n", expInitializer.exp.op,
                                expInitializer.exp.toChars, expInitializer.exp.loc.toChars);
                        assert(0, "Unknown initializer");
                    }
                }
            }
        }
    }

    override void visit(ASTCodegen.AssignExp e)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (threadState.irRoot.currentFunction is null)
            return;

        // This is identical to BinAssignExp for all intents and purposes

        // e.e1 is lhs
        // e.e2 is rhs

        assert(e.e1 !is null);
        assert(e.e2 !is null);

        Verify4IRVariable* destination, source;

        if (e.e2.op.isEXPLiteral)
        {
            // we don't have to load this
            source = this.allocateLiteral(isTypePointer(e.e2.type));
        }
        else
        {
            source = startExpression(e.e2);
        }

        destination = startExpression(e.e1);
        this.lastVariableInExpressionLoadedInto = destination;

        if (destination !is null && source !is null)
        {
            // convert a reference to variable into a pointer that we can then store
            if (destination.isTypeAPointer && !source.isTypeAPointer)
            {
                source = emitLoadReferenceVia(source, null, true, true);
            }

            emitWrite(destination, source);
        }
    }

    override void visit(ASTCodegen.BinAssignExp e)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (threadState.irRoot.currentFunction is null)
            return;

        // This is identical to AssignExp for all intents and purposes

        // e.e1 is lhs
        // e.e2 is rhs

        assert(e.e1 !is null);
        assert(e.e2 !is null);

        Verify4IRVariable* destination, source;

        if (e.e2.op.isEXPLiteral)
        {
            // we don't have to load this
            source = this.allocateLiteral(isTypePointer(e.e2.type));
        }
        else
        {
            source = startExpression(e.e2);
        }

        destination = startExpression(e.e1);
        this.lastVariableInExpressionLoadedInto = destination;

        if (destination !is null && source !is null)
        {
            // convert a reference to variable into a pointer that we can then store
            if (destination.isTypeAPointer && !source.isTypeAPointer)
            {
                source = emitLoadReferenceVia(source, null, true, true);
            }

            emitWrite(destination, source);
        }
    }

    override void visit(ASTCodegen.ReturnStatement e)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;
        if (threadState.irRoot.currentFunction is null)
            return;
        if (e.exp !is null)
        {
            assert(threadState.irRoot.currentFunction.returnVariable !is null);

            if (e.exp.op.isEXPLiteral)
                emitWrite(threadState.irRoot.currentFunction.returnVariable,
                        this.allocateLiteral(isTypePointer(e.exp.type)));
            else
                emitWrite(threadState.irRoot.currentFunction.returnVariable, startExpression(e.exp));
        }

        emitReturn;
    }

    override void visit(ASTCodegen.DotVarExp e)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (threadState.irRoot.currentFunction is null)
            return;

        // e.var is the field
        // e.e1 is the context variable

        assert(e.e1 !is null);
        assert(e.var !is null);

        if (ASTCodegen.VarDeclaration d = e.var.isVarDeclaration)
        {
            emitLoadReferenceVia(startExpression(e.e1),
                    cast(Verify4IRVariable*) threadState.allocateNamedVariable(d),
                    isTypePointer(d.type), false);
        }
        else if (ASTCodegen.FuncDeclaration d = e.var.isFuncDeclaration)
        {
            assert(0,
                    "Seen a function, shouldn't the only place for this to source from is CallExp???");
        }
        else
        {
            assert(0, "Unknown dot var declaration");
        }
    }

    override void visit(ASTCodegen.ThisExp e)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (threadState.irRoot.currentFunction is null)
            return;

        this.lastVariableInExpressionLoadedInto = cast(
                Verify4IRVariable*) threadState.allocateNamedVariable(e.var);
    }

    override void visit(ASTCodegen.SymbolExp e)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (threadState.irRoot.currentFunction is null)
            return;

        assert(e.var !is null);

        this.lastVariableInExpressionLoadedInto = cast(
                Verify4IRVariable*) threadState.allocateNamedVariable(e.var.isVarDeclaration);
    }

    override void visit(ASTCodegen.AddrExp e)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (threadState.irRoot.currentFunction is null)
            return;

        // This likely doesn't exist at this point in time

        emitLoadReferenceVia(startExpression(e.e1), null, true, true);
    }

    override void visit(ASTCodegen.CallExp e)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (threadState.irRoot.currentFunction is null)
            return;

        // e.e1 is context variable
        // e.f is function

        TypeFunction tf = calledFunctionType(e);
        if (tf is null || e.f is null)
            return; // WHAT??? I literally have no idea what to do now.

        Verify4IRArgument* callArguments;

        // If toCall is null, that means its not a nested function that we've already seen.
        // A nested function would have been seen by now thanks to sequential language rules.
        // Therefore if its null that it is a function we don't know about, and also don't care about.
        Verify4IRFunction* toCall = threadState.lookupFunction(e.f);

        Verify4IRVariable* returnVariable = allocateReturnVariable(e.f);
        const returnIsByReference = (e.f.storage_class & STC.ref_) != 0; // is this right?

        Verify4IRVariable* contextVariable;
        const contextContributesToOutput = tf.isreturn || tf.isreturninferred || tf.isreturnscope;
        const contextIsAnOutput = (e.f.storage_class & (STC.const_ | STC.immutable_)) == 0;
        const contextIsScope = (e.f.storage_class & STC.scope_) != 0;
        const contextIsByReference = true;

        if (auto dotVarExp = e.e1.isDotVarExp)
        {
            if (dotVarExp.var.isFuncDeclaration)
            {
                contextVariable = startExpression(dotVarExp.e1);
            }
        }

        {
            if (returnVariable !is null)
                threadState.allocateArgument(callArguments, returnVariable,
                        false, true, false, returnIsByReference);

            if (contextVariable !is null)
                threadState.allocateArgument(callArguments, contextVariable,
                        contextContributesToOutput, contextIsAnOutput,
                        contextIsScope, contextIsByReference);
        }

        scope (exit)
        {
            Verify4IRNode* node = threadState.allocateNode(this.pointerToNextSibling,
                    Verify4IRNode.Type.Call);
            node.callFunctionDeclaration = e.f;
            node.callFunction = toCall;
            node.callArguments = callArguments;

            this.lastVariableInExpressionLoadedInto = returnVariable;
        }

        if (e.arguments is null || e.arguments.length == 0)
            return;

        size_t parameterIndex, argumentIndex = tf.isDstyleVariadic();
        const numberOfParameters = tf.parameterList.length;

        Parameter parameter;
        StorageClass stc;
        bool isParameterScope, isParameterByReference;

        // non-variadics
        for (; argumentIndex < e.arguments.length; argumentIndex++, parameterIndex++)
        {
            if (parameterIndex >= numberOfParameters)
                continue; // we don't care about associating it???

            parameter = tf.parameterList[parameterIndex];

            stc = tf.parameterStorageClass(null, parameter);
            isParameterScope = (stc & STC.scope_) != 0;
            isParameterByReference = (stc & (STC.ref_ | STC.out_)) != 0;

            // if we reach a variadic parameter STOP
            if ((stc & STC.variadic) == STC.variadic)
                break;

            {
                // 1:1 argument to parameter

                Expression argument = (*e.arguments)[argumentIndex];
                Verify4IRVariable* argumentVariable = startExpression(argument);
                assert(argumentVariable !is null);

                const contributesToOutput = (stc & STC.return_) != 0;
                const isAnOutput = isParameterByReference
                    || isPointerMutable(stc, argument.type, parameter.type);

                threadState.allocateArgument(callArguments, argumentVariable,
                        contributesToOutput, isAnOutput, isParameterScope, isParameterByReference);
            }
        }

        // variadics
        // N:1 argument to parameter
        for (; argumentIndex < e.arguments.length; argumentIndex++)
        {
            Expression argument = (*e.arguments)[argumentIndex];
            Verify4IRVariable* argumentVariable = startExpression(argument);
            assert(argumentVariable !is null);

            const contributesToOutput = (stc & STC.return_) != 0;
            const isAnOutput = isParameterByReference || isPointerMutable(stc,
                    argument.type, parameter.type);

            threadState.allocateArgument(callArguments, argumentVariable,
                    contributesToOutput, isAnOutput, isParameterScope, isParameterByReference);
        }
    }

    override void visit(ASTCodegen.IndexExp e)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (threadState.irRoot.currentFunction is null)
            return;

        // e.e1 is context
        // e.e2 is index

        assert(e.e1 !is null);
        assert(e.e2 !is null);

        Verify4IRVariable* context, index;

        context = startExpression(e.e1);
        index = startExpression(e.e2);
        emitLoadReferenceVia(context, index, isTypePointer(e.type), false);
    }

    void visit(ASTCodegen.CondExp e)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (threadState.irRoot.currentFunction is null)
            return;

        // e.econd is condition
        // e.e1 is true block
        // e.e2 is false block

        assert(e.econd !is null);
        assert(e.e1 !is null);
        assert(e.e2 !is null);

        // See if condition visitor for information about handling or expressions,
        //  in case that it is needed in the future.

        Verify4IRScope* scopes;
        Verify4IRVariable* result = threadState.allocateVariable(isTypePointer(e.type),
                false, false);

        {
            Verify4IRVariable* e1Var, e2Var;
            startScope(scopes, null, e.e2, result, e1Var, e2Var);

            if (e2Var !is null)
                result.willBeBorrowed |= e2Var.willBeBorrowed;
        }

        {
            Verify4IRVariable* e1Var, e2Var;
            startScope(scopes, e.econd, e.e1, result, e1Var, e2Var);

            if (e2Var !is null)
                result.willBeBorrowed |= e2Var.willBeBorrowed;
        }

        if (scopes !is null)
        {
            Verify4IRNode* node = threadState.allocateNode(this.pointerToNextSibling,
                    Verify4IRNode.Type.Scopes);
            node.scopes = scopes;
        }

        this.lastVariableInExpressionLoadedInto = result;
    }

    void visit(FuncExp e)
    {
        version (DebugEndOfModuleSymbols)
        {
        }
        else
        {
            if (threadState.irRoot.currentFunction is null)
                return;
        }

        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        this.visit(cast(ASTCodegen.FuncDeclaration) e.fd);
        allocateLiteral(true);
    }

    override void visit(NullExp e)
    {
        version (DebugEndOfModuleSymbols)
        {
        }
        else
        {
            if (threadState.irRoot.currentFunction is null)
                return;
        }

        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        allocateLiteral(true);
    }

    override void visit(IntegerExp e)
    {
        version (DebugEndOfModuleSymbols)
        {
        }
        else
        {
            if (threadState.irRoot.currentFunction is null)
                return;
        }

        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        allocateLiteral(false);
    }

    override void visit(TupleExp e)
    {
        version (DebugEndOfModuleSymbols)
        {
        }
        else
        {
            if (threadState.irRoot.currentFunction is null)
                return;
        }

        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        allocateLiteral(false);
    }

    override void visit(RealExp e)
    {
        version (DebugEndOfModuleSymbols)
        {
        }
        else
        {
            if (threadState.irRoot.currentFunction is null)
                return;
        }

        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        allocateLiteral(false);
    }

    override void visit(StringExp e)
    {
        version (DebugEndOfModuleSymbols)
        {
        }
        else
        {
            if (threadState.irRoot.currentFunction is null)
                return;
        }

        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        allocateLiteral(true);
    }

    override void visit(ArrayLiteralExp e)
    {
        version (DebugEndOfModuleSymbols)
        {
        }
        else
        {
            if (threadState.irRoot.currentFunction is null)
                return;
        }

        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        allocateLiteral(true);
    }

    override void visit(AssocArrayLiteralExp e)
    {
        version (DebugEndOfModuleSymbols)
        {
        }
        else
        {
            if (threadState.irRoot.currentFunction is null)
                return;
        }

        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        allocateLiteral(true);
    }

    override void visit(ASTCodegen.TemplateInstance e)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (e !is e.inst && e.inst !is null && e.memberOf !is null && e.memberOf !is this.theModule)
            return; // Duplicate template instance that will be processed by another root module.

        if (e.members !is null)
        {
            foreach (member; (*e.members)[])
            {
                member.accept(this);
            }
        }
    }

    override void visit(ASTCodegen.IfStatement s)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (threadState.irRoot.currentFunction is null)
            return;
        else if (s.isIfCtfeBlock())
            return;

        Verify4IRScope* scopes;

        // Should we be splitting s.condition into lhs's and rhs's?
        // So that earlier checks apply even to the else body:

        // a.b !is null
        // becomes: ?nonnull a, ?nonnull .b

        startScope(scopes, null, s.elsebody);
        startScope(scopes, s.condition, s.ifbody);

        // While the above approach is "great" for owner escape analysis,
        //  it's going to run into some... hitches
        // With type state analysis it'll result in things being non-null that should be null.
        // The things the DFA things were checked, won't have been.
        // Which is a massive problem.

        // Instead we want to consider every possible permutation of the condition expressions or's.
        // Stuff like ``((a && b) || (c || d)) && e`` getting split into:
        // ``a && b && e``, ``c && e``, ``d && e``.
        // It could be implemented using a pushdown machine, with a list of IR nodes that _do not_ act as a scope.
        // After that create a scope, copy the push down machine permutation, create a scopes IR node using the true scope.

        if (scopes !is null)
        {
            Verify4IRNode* node = threadState.allocateNode(this.pointerToNextSibling,
                    Verify4IRNode.Type.Scopes);
            node.scopes = scopes;
        }
    }

    override void visit(ASTCodegen.ForStatement s)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (threadState.irRoot.currentFunction is null)
            return;

        // After semantic for statements look like:

        // initializers
        // for(; condition; increment) { loop_body }

        // Initializers have already been handled.
        // We do not deal with them here.

        version (none)
        {
            printf("for init %p condition %p increment %p body %p label %p\n",
                    s._init, s.condition, s.increment, s._body, s.relatedLabeled);
            if (s.relatedLabeled !is null)
                printf("%d\n", s.relatedLabeled.stmt);
        }

        Verify4IRLabel* label, oldLabel = this.currentStatementLabel;

        scope (exit)
            this.currentStatementLabel = oldLabel;

        if (s.relatedLabeled !is null)
        {
            if (auto scs = s.relatedLabeled.isScopeStatement())
            {
                label = threadState.labelForStatement(scs);
            }
            else if (auto la = s.relatedLabeled.isLabelStatement())
            {
                label = threadState.allocateLabel(la);
            }
            else
                assert(0, "ICE: Unknown for labeled statement");
        }

        bool needConvergeAfter;

        if (label is null)
        {
            label = threadState.allocateAnonymousLabel();
            needConvergeAfter = true;
        }
        else
            label.before.labelIsDisabled = true;

        this.currentStatementLabel = label;

        Verify4IRScope* scopes, scopesOnContinue;
        startScope(scopesOnContinue, s.increment, null);

        // See if statement overload of visit function,
        //  as to why this condition processing is not ideal and how to rectify it.
        startScope(scopes, s.condition, s._body);

        if (scopes !is null || scopesOnContinue !is null)
        {
            {
                Verify4IRNode* beforeConverge = threadState.allocateNode(this.pointerToNextSibling,
                        Verify4IRNode.Type.ConvergePoint);
                beforeConverge.label = label;
                beforeConverge.labelIsBeforeStatement = true;
                beforeConverge.labelIsDisabled = false;

                label.before = beforeConverge;
            }

            Verify4IRNode* node = threadState.allocateNode(this.pointerToNextSibling,
                    Verify4IRNode.Type.Scopes);
            node.scopesWillLoop = true;
            node.scopes = scopes;
            node.scopesOnContinue = scopesOnContinue;

            if (needConvergeAfter)
            {
                Verify4IRNode* afterConverge = threadState.allocateNode(this.pointerToNextSibling,
                        Verify4IRNode.Type.ConvergePoint);
                afterConverge.label = label;
                afterConverge.labelIsBeforeStatement = false;
                afterConverge.labelIsDisabled = false;

                label.after = afterConverge;
            }
        }
    }

    override void visit(ASTCodegen.SwitchStatement s)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (threadState.irRoot.currentFunction is null)
            return;
        else if (s.cases is null || (s.cases.length == 0 && s.sdefault is null))
            return;

        Verify4IRLabel* outerLabel = threadState.allocateAnonymousLabel(), defaultLabel;
        Verify4IRLabel* oldOuterLabel = this.currentStatementLabel,
            oldDefaultLabel = this.currentDefaultLabel;
        this.currentStatementLabel = outerLabel;

        scope (exit)
        {
            this.currentStatementLabel = oldOuterLabel;
            this.currentDefaultLabel = oldDefaultLabel;
        }

        Verify4IRScope* scopes;

        if (s.sdefault !is null)
        {
            defaultLabel = threadState.allocateAnonymousLabel();
            this.currentDefaultLabel = defaultLabel;

            startScope(scopes, null, s.sdefault);
        }

        // grab all goto's first
        foreach (caseStatement; (*s.cases))
        {
            if (caseStatement.hasCode)
            {
                Verify4IRLabel* label = threadState.allocateAnonymousLabel();
                threadState.mapToLabel(label, caseStatement);
            }
        }

        foreach (caseStatement; (*s.cases))
        {
            if (caseStatement.hasCode)
                startScope(scopes, null, caseStatement.statement);
        }

        if (scopes !is null)
        {
            // No convergence happens prior to a switch statement,
            //  nor can you goto it.

            {
                Verify4IRNode* node = threadState.allocateNode(this.pointerToNextSibling,
                        Verify4IRNode.Type.Scopes);
                node.scopes = scopes;
                node.scopesContextVariable = startExpression(s.condition);
            }

            {
                Verify4IRNode* afterConverge = threadState.allocateNode(this.pointerToNextSibling,
                        Verify4IRNode.Type.ConvergePoint);
                afterConverge.label = outerLabel;
                afterConverge.labelIsBeforeStatement = false;
                afterConverge.labelIsDisabled = false;

                outerLabel.after = afterConverge;
            }
        }
    }

    override void visit(ASTCodegen.LabelStatement s)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (threadState.irRoot.currentFunction is null)
            return;

        Verify4IRLabel* label = threadState.allocateLabel(s);

        Verify4IRNode* beforeConverge = threadState.allocateNode(this.pointerToNextSibling,
                Verify4IRNode.Type.ConvergePoint);
        beforeConverge.label = label;
        beforeConverge.labelIsBeforeStatement = true;
        beforeConverge.labelIsDisabled = false;

        label.before = beforeConverge;

        Verify4IRScope* scopes;
        startScope(scopes, null, s.statement, label);

        if (scopes !is null)
        {
            Verify4IRNode* node = threadState.allocateNode(this.pointerToNextSibling,
                    Verify4IRNode.Type.Scopes);
            node.scopes = scopes;

            // unnecessary memory allocation
            if (s.statement.isReturnStatement() is null)
            {
                Verify4IRNode* afterConverge = threadState.allocateNode(this.pointerToNextSibling,
                        Verify4IRNode.Type.ConvergePoint);
                afterConverge.label = label;
                afterConverge.labelIsBeforeStatement = false;
                afterConverge.labelIsDisabled = false;

                label.after = afterConverge;
            }
        }
    }

    override void visit(ASTCodegen.BreakStatement s)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (threadState.irRoot.currentFunction is null)
            return;

        Verify4IRLabel* label;

        if (s.ident is null)
            label = this.currentStatementLabel;
        else
            label = threadState.allocateLabel(s.ident.toChars);

        if (label is null)
            return;

        label.beforeGotoCount++;

        Verify4IRNode* node = threadState.allocateNode(this.pointerToNextSibling,
                Verify4IRNode.Type.Goto);
        node.gotoLabel = label;
        node.gotoAfter = true;
        node.gotoIsForwards = true;
    }

    override void visit(ASTCodegen.ContinueStatement s)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (threadState.irRoot.currentFunction is null)
            return;

        Verify4IRLabel* label;

        if (s.ident is null)
            label = this.currentStatementLabel;
        else
            label = threadState.allocateLabel(s.ident.toChars);

        if (label is null)
            return;

        label.afterGotoCount++;

        Verify4IRNode* node = threadState.allocateNode(this.pointerToNextSibling,
                Verify4IRNode.Type.Goto);
        node.gotoLabel = label;
        node.gotoAfter = false;
        node.gotoIsForwards = false;
    }

    override void visit(ASTCodegen.GotoStatement s)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (threadState.irRoot.currentFunction is null)
            return;

        Verify4IRLabel* label = threadState.allocateLabel(s.ident.toChars);

        Verify4IRNode* node = threadState.allocateNode(this.pointerToNextSibling,
                Verify4IRNode.Type.Goto);
        node.gotoLabel = label;
        node.gotoAfter = false;

        // The label is before us,
        //  so we'll need the label to synchronize all work below it (including us).
        if (label.before !is null)
        {
            label.beforeGotoCount++;
            node.gotoIsForwards = false;
        }
        else
        {
            label.forwardGotoCount++;
            node.gotoIsForwards = true;
        }
    }

    override void visit(ASTCodegen.GotoCaseStatement s)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (threadState.irRoot.currentFunction is null)
            return;

        Verify4IRLabel* label = threadState.labelForStatement(s.cs);
        assert(label !is null);

        Verify4IRNode* node = threadState.allocateNode(this.pointerToNextSibling,
                Verify4IRNode.Type.Goto);
        node.gotoLabel = label;
        node.gotoAfter = false;

        // We'll treat this type of goto as a forward.
        // Might result in somethings slip through but...
        //  otherwise we could end up in a cyclic situation.
        label.forwardGotoCount++;
        node.gotoIsForwards = true;
    }

    override void visit(ASTCodegen.GotoDefaultStatement s)
    {
        trace();
        this.depth++;
        scope (exit)
            this.depth--;

        if (threadState.irRoot.currentFunction is null)
            return;

        Verify4IRLabel* label = this.currentDefaultLabel;
        assert(label !is null);

        Verify4IRNode* node = threadState.allocateNode(this.pointerToNextSibling,
                Verify4IRNode.Type.Goto);
        node.gotoLabel = label;
        node.gotoAfter = false;

        // We'll treat this type of goto as a forward.
        // Might result in somethings slip through but...
        //  otherwise we could end up in a cyclic situation.
        label.forwardGotoCount++;
        node.gotoIsForwards = true;
    }
}
