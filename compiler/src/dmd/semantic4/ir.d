module dmd.semantic4.ir;
import dmd.semantic4.adt;
import dmd.semantic4.utils;
import dmd.arraytypes;
import dmd.root.region;
import dmd.ast_node;
import dmd.identifier;
import dmd.dsymbol;
import dmd.astenums;
import dmd.mtype;
import dmd.astcodegen;
import core.stdc.stdio : printf;

struct Verify4IRVariable
{
    private
    {
        bool isNamed_;
    }

    bool isTypeAPointer;
    bool isLiteral;
    bool willBeBorrowed;
    bool isGlobal;
    bool canBeWrittenToMoreThanOnce;

    Verify4IRNamedVariable* isNamed() return
    {
        if (isNamed_)
            return cast(Verify4IRNamedVariable*)&this;
        return null;
    }
}

struct Verify4IRNamedVariable
{
    Verify4IRVariable parent;
    alias parent this;

    private
    {
        Verify4IRNamedVariable* nextInBucket;
    }

    Type type;
    ASTCodegen.VarDeclaration declaration;

    enum Type
    {
        Unknown,
        Declared,
        Parameter,
        ThisByPointer, // could be null
        ThisByReference, // guaranteed to be non-null
        Return,
    }
}

struct Verify4IRLabel
{
    private
    {
        Verify4IRLabel* nextInBucket, nextInScopeBucket;
    }

    const(char)* name;
    ASTCodegen.LabelStatement declaration;
    ASTCodegen.ScopeStatement scopeStatement;
    ASTCodegen.CaseStatement caseStatement;

    Verify4IRNode* before;
    Verify4IRNode* after;
    // Note: do not count forward declaration gotos
    size_t beforeGotoCount;
    size_t forwardGotoCount;
    size_t afterGotoCount;
}

struct Verify4IRFunction
{
    private
    {
        Verify4IRFunction* nextInBucket;
        Verify4IRLabel*[16] bucketsOfLabels;
        Verify4IRLabel*[16] bucketsOfScopesToLabels;
        Verify4IRLabel*[16] bucketsOfCasesToLabels;
        Verify4IRLabel* anonymousLabels;
    }

    ASTCodegen.FuncDeclaration declaration;

    Verify4IRFunction* parent;
    Verify4IRFunction* nextSibling;
    Verify4IRFunction* firstChild;

    const(char)* functionName;
    TRUST safetyLevel;

    Verify4IRVariable* returnVariable;
    Verify4IRNamedVariable* contextVariable; // this pointer or __capture

    Verify4IRScope topScope;
}

struct Verify4IRArgument
{
    Verify4IRArgument* next;
    Verify4IRVariable* variable;
    bool contributesToOutput;
    bool isAnOutput;
    bool isParameterScope;
    bool isParameterByReference;
}

struct Verify4IRScope
{
    Verify4IRScope* nextSibling;
    Verify4IRNode* firstChild;
}

struct Verify4IRNode
{
    Type type;
    Verify4IRNode* nextSibling;

    union
    {
        // LoadReferenceVia
        struct
        {
            Verify4IRVariable* loadViaReferenceContextVariable;
            Verify4IRVariable* loadViaReferenceOffsetVariable;
            Verify4IRVariable* loadViaReferenceDestinationVariable;
        }

        // WriteByValue
        struct
        {
            Verify4IRVariable* writeSourceVariable;
            Verify4IRVariable* writeDestinationVariable;
        }

        // Scopes
        struct
        {
            Verify4IRVariable* scopesContextVariable;
            Verify4IRScope* scopes;
            Verify4IRScope* scopesOnContinue;
            bool scopesWillLoop;
        }

        // Sequence
        struct
        {
            Verify4IRNode* sequenceFirstChild;
        }

        // Call
        struct
        {
            ASTCodegen.FuncDeclaration callFunctionDeclaration;
            Verify4IRFunction* callFunction;
            Verify4IRArgument* callArguments;
        }

        // ConvergePoint
        struct
        {
            Verify4IRLabel* label;
            bool labelIsBeforeStatement;
            bool labelIsDisabled;
        }

        // Goto
        struct
        {
            Verify4IRLabel* gotoLabel;
            bool gotoAfter;
            bool gotoIsForwards;
        }
    }

    enum Type
    {
        LoadReferenceVia,
        WriteByValue,
        Scopes,
        Sequence,
        Return,
        Call,
        ConvergePoint,
        Goto,
    }
}

struct VerificationDFAThreadState
{
    Region allocator;
    Verify4IRRoot irRoot;
    size_t numberOfNamedVariables, numberOfUnnamedVariables;
    size_t numberOfLabels;

    package(dmd.semantic4)
    {
        SymbolLookupFreeLists symbolLookupFreeLists;
    }

    Verify4IRFunction* allocateFunction(ASTCodegen.FuncDeclaration d)
    {
        TypeFunction tf = d.type.isTypeFunction();
        assert(tf !is null);

        auto bucketId = (cast(size_t) cast(void*) d) % irRoot.bucketsOfFunctions.length;
        Verify4IRFunction** bucketOfFunction = &irRoot.bucketsOfFunctions[bucketId];

        while (*bucketOfFunction !is null)
        {
            if (cast(void*)(*bucketOfFunction).declaration > cast(void*) d)
                break;
            else if (cast(void*)(*bucketOfFunction).declaration is cast(void*) d)
                return *bucketOfFunction;

            bucketOfFunction = &((*bucketOfFunction).nextInBucket);
        }

        Verify4IRFunction* temp = cast(Verify4IRFunction*) allocator.malloc(
                Verify4IRFunction.sizeof);
        *temp = Verify4IRFunction(*bucketOfFunction, typeof(temp.bucketsOfLabels).init,
                typeof(temp.bucketsOfScopesToLabels).init, typeof(temp.bucketsOfCasesToLabels).init,
                null, d, irRoot.currentFunction, null, null, d.toChars(), tf.trust);

        if (irRoot.currentFunction !is null)
        {
            temp.nextSibling = irRoot.currentFunction.firstChild;
            irRoot.currentFunction.firstChild = temp;
        }

        irRoot.currentFunction = temp;
        *bucketOfFunction = temp;
        return temp;
    }

    Verify4IRFunction* lookupFunction(ASTCodegen.FuncDeclaration d)
    {
        if (d is null)
            return null;

        auto bucketId = (cast(size_t) cast(void*) d) % irRoot.bucketsOfFunctions.length;
        Verify4IRFunction** bucketOfFunction = &irRoot.bucketsOfFunctions[bucketId];

        while (*bucketOfFunction !is null)
        {
            if (cast(void*)(*bucketOfFunction).declaration > cast(void*) d)
                break;
            else if (cast(void*)(*bucketOfFunction).declaration is cast(void*) d)
                return *bucketOfFunction;

            bucketOfFunction = &((*bucketOfFunction).nextInBucket);
        }

        return null;
    }

    Verify4IRVariable* allocateVariable(bool isTypeAPointer, bool isBorrowed,
            bool canBeWrittenToMoreThanOnce)
    {
        Verify4IRVariable* temp = cast(Verify4IRVariable*) allocator.malloc(
                Verify4IRVariable.sizeof);
        assert(temp !is null);

        *temp = Verify4IRVariable(false, isTypeAPointer);
        temp.willBeBorrowed = isBorrowed;
        temp.canBeWrittenToMoreThanOnce = canBeWrittenToMoreThanOnce;

        numberOfUnnamedVariables++;
        return temp;
    }

    Verify4IRNamedVariable* allocateNamedVariable(ASTCodegen.VarDeclaration d,
            Verify4IRNamedVariable.Type type = Verify4IRNamedVariable.Type.Unknown)
    {
        if (d is null)
            return null;

        auto bucketId = (cast(size_t) cast(void*) d) % irRoot.bucketsOfVariables.length;
        Verify4IRNamedVariable** bucketOfVariable = &irRoot.bucketsOfVariables[bucketId];

        while (*bucketOfVariable !is null)
        {
            if (cast(void*)(*bucketOfVariable).declaration > cast(void*) d)
                break;
            else if (cast(void*)(*bucketOfVariable).declaration is cast(void*) d)
                return *bucketOfVariable;

            bucketOfVariable = &((*bucketOfVariable).nextInBucket);
        }

        assert(bucketOfVariable !is null);
        Verify4IRNamedVariable* temp = cast(Verify4IRNamedVariable*) allocator.malloc(
                Verify4IRNamedVariable.sizeof);
        assert(temp !is null);

        *temp = Verify4IRNamedVariable(Verify4IRVariable(true,
                isTypePointer(d.type)), *bucketOfVariable, type, d);
        temp.canBeWrittenToMoreThanOnce = true;

        // All variable declarations should have a parent, but...
        if (d.parent !is null)
            temp.parent.isGlobal = !d.needThis() && d.isDataseg();

        *bucketOfVariable = temp;
        numberOfNamedVariables++;
        return temp;
    }

    Verify4IRLabel* allocateLabel(ASTCodegen.LabelStatement d)
    {
        return this.allocateLabel(d.ident.toChars(), d);
    }

    Verify4IRLabel* allocateLabel(const(char)* id, ASTCodegen.LabelStatement d = null)
    {
        if (id is null)
            return null;

        auto bucketId = (cast(size_t) id) % irRoot.currentFunction.bucketsOfLabels.length;
        Verify4IRLabel** bucketOfLabel = &irRoot.currentFunction.bucketsOfLabels[bucketId];

        while (*bucketOfLabel !is null)
        {
            if (cast(void*)(*bucketOfLabel).name > id)
                break;
            else if (cast(void*)(*bucketOfLabel).name is id)
            {
                if (d !is null && (*bucketOfLabel).declaration is null)
                    (*bucketOfLabel).declaration = d;
                return *bucketOfLabel;
            }

            bucketOfLabel = &((*bucketOfLabel).nextInBucket);
        }

        assert(bucketOfLabel !is null);
        Verify4IRLabel* temp = cast(Verify4IRLabel*) allocator.malloc(Verify4IRLabel.sizeof);
        assert(temp !is null);

        *temp = Verify4IRLabel(*bucketOfLabel, null, id, d);

        if (d !is null)
        {
            if (auto scs = d.isScopeStatement)
                mapToLabel(temp, scs);
        }

        *bucketOfLabel = temp;
        numberOfLabels++;
        return temp;
    }

    Verify4IRLabel* allocateAnonymousLabel()
    {
        Verify4IRLabel* temp = cast(Verify4IRLabel*) allocator.malloc(Verify4IRLabel.sizeof);
        assert(temp !is null);

        *temp = Verify4IRLabel(irRoot.currentFunction.anonymousLabels);

        irRoot.currentFunction.anonymousLabels = temp;
        numberOfLabels++;
        return temp;
    }

    void mapToLabel(Verify4IRLabel* label, ASTCodegen.ScopeStatement s)
    {
        assert(label !is null);
        assert(s !is null);

        auto bucketId = (cast(size_t) cast(void*) s) % irRoot.currentFunction
            .bucketsOfScopesToLabels.length;
        Verify4IRLabel** bucketOfLabel = &irRoot.currentFunction.bucketsOfScopesToLabels[bucketId];

        while (*bucketOfLabel !is null)
        {
            if (cast(void*)(*bucketOfLabel).scopeStatement > cast(void*) s)
                break;
            else if (cast(void*)(*bucketOfLabel).scopeStatement is cast(void*) s)
                return;

            bucketOfLabel = &((*bucketOfLabel).nextInScopeBucket);
        }

        assert(bucketOfLabel !is null);

        label.nextInScopeBucket = *bucketOfLabel;
        label.scopeStatement = s;
        *bucketOfLabel = label;
    }

    void mapToLabel(Verify4IRLabel* label, ASTCodegen.CaseStatement s)
    {
        assert(label !is null);
        assert(s !is null);

        auto bucketId = (cast(size_t) cast(void*) s) % irRoot.currentFunction
            .bucketsOfCasesToLabels.length;
        Verify4IRLabel** bucketOfLabel = &irRoot.currentFunction.bucketsOfCasesToLabels[bucketId];

        while (*bucketOfLabel !is null)
        {
            if (cast(void*)(*bucketOfLabel).caseStatement > cast(void*) s)
                break;
            else if (cast(void*)(*bucketOfLabel).caseStatement is cast(void*) s)
                return;

            bucketOfLabel = &((*bucketOfLabel).nextInScopeBucket);
        }

        assert(bucketOfLabel !is null);

        label.nextInScopeBucket = *bucketOfLabel;
        label.caseStatement = s;
        *bucketOfLabel = label;
    }

    Verify4IRLabel* labelForStatement(ASTCodegen.ScopeStatement s)
    {
        auto bucketId = (cast(size_t) cast(void*) s) % irRoot.currentFunction
            .bucketsOfScopesToLabels.length;
        Verify4IRLabel** bucketOfLabel = &irRoot.currentFunction.bucketsOfScopesToLabels[bucketId];

        while (*bucketOfLabel !is null)
        {
            if (cast(void*)(*bucketOfLabel).scopeStatement > cast(void*) s)
                break;
            else if (cast(void*)(*bucketOfLabel).scopeStatement is cast(void*) s)
                return *bucketOfLabel;

            bucketOfLabel = &((*bucketOfLabel).nextInScopeBucket);
        }

        return null;
    }

    Verify4IRLabel* labelForStatement(ASTCodegen.CaseStatement s)
    {
        auto bucketId = (cast(size_t) cast(void*) s) % irRoot.currentFunction
            .bucketsOfCasesToLabels.length;
        Verify4IRLabel** bucketOfLabel = &irRoot.currentFunction.bucketsOfCasesToLabels[bucketId];

        while (*bucketOfLabel !is null)
        {
            if (cast(void*)(*bucketOfLabel).caseStatement > cast(void*) s)
                break;
            else if (cast(void*)(*bucketOfLabel).caseStatement is cast(void*) s)
                return *bucketOfLabel;

            bucketOfLabel = &((*bucketOfLabel).nextInScopeBucket);
        }

        return null;
    }

    Verify4IRNode* allocateNode(ref Verify4IRNode** pointerToSiblingNode, Verify4IRNode.Type type)
    {
        assert(pointerToSiblingNode !is null);

        Verify4IRNode* ret = cast(Verify4IRNode*) allocator.malloc(Verify4IRNode.sizeof);
        assert(ret !is null);
        *ret = Verify4IRNode(type);

        // null* => ret*
        // old* => ret*, ret.next = old.next, *old.next = ret

        if (*pointerToSiblingNode !is null)
        {
            ret.nextSibling = (*pointerToSiblingNode).nextSibling;
            (*pointerToSiblingNode).nextSibling = ret;
        }
        else
        {
            ret.nextSibling = null;
            *pointerToSiblingNode = ret;
        }

        pointerToSiblingNode = &ret.nextSibling;
        assert(pointerToSiblingNode !is null);
        return ret;
    }

    Verify4IRArgument* allocateArgument(ref Verify4IRArgument* previous, Verify4IRVariable* variable,
            bool contributesToOutput, bool isAnOutput, bool isParameterScope,
            bool isParameterByReference)
    {
        Verify4IRArgument* ret = cast(Verify4IRArgument*) allocator.malloc(
                Verify4IRArgument.sizeof);
        assert(ret !is null);
        *ret = Verify4IRArgument(previous, variable, contributesToOutput,
                isAnOutput, isParameterScope, isParameterByReference);

        previous = ret;
        return ret;
    }

    Verify4IRScope* allocateScope(ref Verify4IRScope* previous)
    {
        Verify4IRScope* ret = cast(Verify4IRScope*) allocator.malloc(Verify4IRScope.sizeof);
        assert(ret !is null);
        *ret = Verify4IRScope(previous);

        previous = ret;
        return ret;
    }
}

struct Verify4IRRoot
{
    package(dmd.semantic4)
    {
        // Verified, 16 buckets is enough for likely most tasks.
        // Anything above saw no improvements.
        Verify4IRNamedVariable*[16] bucketsOfVariables;
        Verify4IRFunction*[16] bucketsOfFunctions;
    }

    Verify4IRFunction* currentFunction;

    void debugMe()
    {
        if (this.currentFunction is null)
        {
            printf("No IR functions present\n");
            return;
        }

        int depth;

        {
            printf("%*sNamed Variables:\n", depth, "".ptr);

            foreach (var; this.bucketsOfVariables)
            {
                while (var !is null)
                {
                    printVariable("- ", cast(Verify4IRVariable*) var, depth, "\n");
                    var = var.nextInBucket;
                }
            }
        }

        Verify4IRFunction* mostParentFunction = this.currentFunction;

        while (mostParentFunction.parent !is null)
        {
            mostParentFunction = mostParentFunction.parent;
        }

        this.printIRFunction(mostParentFunction, depth);
    }

private:

    void printIRFunction(Verify4IRFunction* parent, int depth)
    {
        printf("%*s--- \\/ %s \\/ --- %s\n", depth, "".ptr,
                parent.functionName, parent.declaration.loc.toChars);
        depth += 5;

        {
            printf("%*sSafety level: %d\n", depth, "".ptr, parent.safetyLevel);
        }

        {
            printf("%*sNamed Labels:\n", depth, "".ptr);

            foreach (label; parent.bucketsOfLabels)
            {
                while (label !is null)
                {
                    printf("%*s- `%s`, forward: %zd, before: %zd, after: %zd\n", depth, "".ptr, label.name,
                            label.forwardGotoCount, label.beforeGotoCount, label.afterGotoCount);
                    label = label.nextInBucket;
                }
            }
        }

        {
            printf("%*sAnonymous Labels:\n", depth, "".ptr);
            Verify4IRLabel* label = parent.anonymousLabels;

            while (label !is null)
            {
                printf("%*s- %p, forward: %zd, before: %zd, after: %zd\n", depth, "".ptr, label,
                        label.forwardGotoCount, label.beforeGotoCount, label.afterGotoCount);
                label = label.nextInBucket;
            }
        }

        {
            printf("%*sScope %p, Nodes:\n", depth, "".ptr, &parent.topScope);
            printIRScope(&parent.topScope, depth);
        }

        {
            Verify4IRFunction* child = parent.firstChild;

            while (child !is null)
            {
                printIRFunction(child, depth);
                child = child.nextSibling;
            }
        }

        depth -= 5;
        printf("%*s=== /\\ %s /\\ === %s\n\n", depth, "".ptr,
                parent.functionName, parent.declaration.loc.toChars);
    }

    void printIRScope(Verify4IRScope* parent, int depth)
    {
        while (parent !is null)
        {
            printf("%*s- Scope:\n", depth, "".ptr);

            printIRNode(parent.firstChild, depth + 4);

            parent = parent.nextSibling;
        }
    }

    void printIRNode(Verify4IRNode* parent, int depth)
    {
        while (parent !is null)
        {
            assert(parent.type <= Verify4IRNode.Type.max);
            printf("%*s- %s\n", depth, "".ptr, [
                __traits(allMembers, Verify4IRNode.Type)
            ][parent.type].ptr);

            final switch (parent.type)
            {
            case Verify4IRNode.Type.LoadReferenceVia:
                printVariableReference("write into ",
                        parent.loadViaReferenceDestinationVariable, depth + 4, "");
                printVariableReference(", context ", parent.loadViaReferenceContextVariable, 0, "");
                printVariableReference(", offset ", parent.loadViaReferenceOffsetVariable, 0, "\n");

                if (parent.loadViaReferenceDestinationVariable !is null
                        && parent.loadViaReferenceDestinationVariable.isNamed is null)
                    printVariable("= ", parent.loadViaReferenceDestinationVariable, depth + 4, "\n");
                if (parent.loadViaReferenceContextVariable !is null
                        && parent.loadViaReferenceContextVariable.isNamed is null)
                    printVariable("= ", parent.loadViaReferenceContextVariable, depth + 4, "\n");
                if (parent.loadViaReferenceOffsetVariable !is null
                        && parent.loadViaReferenceOffsetVariable.isNamed is null)
                    printVariable("= ", parent.loadViaReferenceOffsetVariable, depth + 4, "\n");
                break;

            case Verify4IRNode.Type.WriteByValue:
                printVariableReference("write on ",
                        parent.writeDestinationVariable, depth + 4, "");
                printVariableReference(", from ", parent.writeSourceVariable, 0, "\n");

                if (parent.writeDestinationVariable !is null
                        && parent.writeDestinationVariable.isNamed is null)
                    printVariable("= ", parent.writeDestinationVariable, depth + 4, "\n");
                if (parent.writeSourceVariable !is null && parent.writeSourceVariable.isNamed is null)
                    printVariable("= ", parent.writeSourceVariable, depth + 4, "\n");
                break;

            case Verify4IRNode.Type.Scopes:
                if (parent.scopesContextVariable !is null)
                {
                    printVariable("Context variable ", parent.scopesContextVariable, depth + 4,
                            "\n");
                }

                if (parent.scopesOnContinue !is null)
                {
                    printf("%*son continue:\n", depth + 4, "".ptr);
                    printIRScope(parent.scopesOnContinue, depth + 4);
                }

                printf("%*swill loop %d\n", depth + 4, "".ptr, parent.scopesWillLoop);
                printIRScope(parent.scopes, depth + 4);
                break;

            case Verify4IRNode.Type.Sequence:
                printIRNode(parent.sequenceFirstChild, depth + 4);
                break;

            case Verify4IRNode.Type.Return:
                break;

            case Verify4IRNode.Type.Call:
                printf("%*s`%s` (reverse order):\n",
                        depth + 4, "".ptr, parent.callFunctionDeclaration.toChars);

                {
                    Verify4IRArgument* argument = parent.callArguments;

                    while (argument !is null)
                    {
                        printVariableReference("- ", argument.variable, depth + 4, ", ");
                        printf("contributes to output %d, is an output %d, is by reference %d\n",
                                argument.contributesToOutput,
                                argument.isAnOutput, argument.isParameterByReference);

                        argument = argument.next;
                    }
                }

                {
                    Verify4IRArgument* argument = parent.callArguments;

                    while (argument !is null)
                    {
                        if (argument.variable !is null && argument.variable.isNamed is null)
                            printVariable("= ", argument.variable, depth + 4, "\n");

                        argument = argument.next;
                    }
                }
                break;

            case Verify4IRNode.Type.ConvergePoint:
                printf("%*s", depth + 4, "".ptr);

                if (parent.label.name !is null)
                    printf("`%s`", parent.label.name);
                else
                    printf("%p", parent.label);

                if (parent.labelIsBeforeStatement)
                    printf(", before statement");
                else
                    printf(", after statement");

                if (parent.labelIsDisabled)
                    printf(", is disabled");

                if (parent.label.declaration !is null)
                    printf(", at %s\n", parent.label.declaration.loc.toChars);
                else
                    printf("\n");
                break;

            case Verify4IRNode.Type.Goto:
                printf("%*s", depth + 4, "".ptr);

                if (parent.gotoLabel.name !is null)
                    printf("`%s`", parent.gotoLabel.name);
                else
                    printf("%p", parent.gotoLabel);

                if (parent.gotoIsForwards)
                    printf(", is forwards");

                if (parent.gotoAfter)
                    printf(", after statement\n");
                else
                    printf(", for statement\n");
                break;
            }

            parent = parent.nextSibling;
        }
    }

    void printVariable(string prefix, Verify4IRVariable* variable, int depth, string suffix)
    {
        printf("%*s%s%p", depth, "".ptr, prefix.ptr, variable);
        scope (exit)
            printf("%s", suffix.ptr);

        if (variable is null)
            return;

        if (variable.isTypeAPointer)
            printf(", pointer");
        if (variable.isLiteral)
            printf(", literal");
        if (variable.isGlobal)
            printf(", global");
        if (variable.canBeWrittenToMoreThanOnce)
            printf(", multiple write");

        Verify4IRNamedVariable* named = variable.isNamed;

        if (named !is null && named.declaration !is null)
        {
            printf(", `%s`", named.declaration.ident.toChars);
            printf(" at %s", named.declaration.locToChars);
        }
    }

    void printVariableReference(string prefix, Verify4IRVariable* variable,
            int depth, string suffix)
    {
        printf("%*s%s%p%s", depth, "".ptr, prefix.ptr, variable, suffix.ptr);
    }
}
