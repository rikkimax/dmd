module dmd.semantic4.adt;
import dmd.semantic4.ir;

struct SymbolConvergeSetList
{
    private
    {
        VerificationDFAThreadState* threadState;
        SymbolLookupNode* firstNode;
    }

@safe nothrow @nogc:

    this(VerificationDFAThreadState* threadState)
    {
        assert(threadState !is null);
        this.threadState = threadState;
    }

    @disable this(this);

    ~this()
    {
        SymbolLookupNode* currentNode = this.firstNode;

        while (currentNode !is null)
        {
            SymbolLookupNode* nextNode = currentNode.next;

            currentNode.next = this.threadState.symbolLookupFreeLists.firstNode;
            this.threadState.symbolLookupFreeLists.firstNode = currentNode;

            currentNode = nextNode;
        }
    }

    int opApply(int delegate(SymbolLookupNode*) @safe nothrow @nogc del)
    {
        SymbolLookupNode* currentNode = this.firstNode;
        int ret;

        while (currentNode !is null && ret == 0)
        {
            ret = del(currentNode);
            currentNode = currentNode.next;
        }

        return ret;
    }
}

struct SymbolLookup
{
    private
    {
        VerificationDFAThreadState* threadState;
        SymbolLookupLayer* layers;
    }

@safe nothrow:

    this(VerificationDFAThreadState* threadState)
    {
        assert(threadState !is null);
        this.threadState = threadState;
    }

    @disable this(this);

    ~this() @nogc
    {
        SymbolLookupLayer* layer = this.layers;

        while (layer !is null)
        {
            SymbolLookupLayer* nextLayer = layer.next;

            while (layer !is null)
            {
                SymbolLookupLayer* nextSibling = layer.nextSibling;

                foreach (currentNode; layer.bucketsOfMultipleWritableNodes)
                {
                    while (currentNode !is null)
                    {
                        SymbolLookupNode* nextNode = currentNode.next;

                        currentNode.next = this.threadState.symbolLookupFreeLists.firstNode;
                        this.threadState.symbolLookupFreeLists.firstNode = currentNode;

                        currentNode = nextNode;
                    }
                }

                foreach (currentNode; layer.bucketsOfSingleWriteNodes)
                {
                    while (currentNode !is null)
                    {
                        SymbolLookupNode* nextNode = currentNode.next;

                        currentNode.next = this.threadState.symbolLookupFreeLists.firstNode;
                        this.threadState.symbolLookupFreeLists.firstNode = currentNode;

                        currentNode = nextNode;
                    }
                }

                layer.next = this.threadState.symbolLookupFreeLists.firstLayer;
                this.threadState.symbolLookupFreeLists.firstLayer = layer;

                layer = nextSibling;
            }

            layer = nextLayer;
        }
    }

    /// Creates a new layer
    void pushScopes()
    {
        SymbolLookupLayer* layer = this.allocateLayer();
        layer.next = this.layers;
        this.layers = layer;
    }

    /**
        Peek all convergable changes in scopes, use this before ``popScopes`` to have separate lists of
         convergable and non-convergable.

        Note: will clear all convergable changes from layer.

        Params:
            symbolConvergeSetList = The Converge set list.

        See_Also: popScopes
    */
    void peekScopesForConvergable(ref SymbolConvergeSetList symbolConvergeSetList) @nogc
    {
        if (this.layers is null)
            return;

        SymbolLookupLayer* layer = this.layers;

        while (layer !is null)
        {
            SymbolLookupLayer* nextLayer = layer.next;

            while (layer !is null)
            {
                SymbolLookupLayer* nextSibling = layer.nextSibling;

                layer.appendNodesToListAndClear(symbolConvergeSetList.firstNode, true);

                layer = nextSibling;
            }

            layer = nextLayer;
        }
    }

    /**
        This layer is done, pop all the changes over into a list to converge with.

        Params:
            symbolConvergeSetList = The Converge set list.
            convergableOnly       = Is the changes filtered by convergability?

        See_Also: peekScopesForConvergable
    */
    void popScopes(ref SymbolConvergeSetList symbolConvergeSetList, bool convergableOnly = true) @nogc
    {
        if (this.layers is null)
            return;

        SymbolLookupLayer* layer = this.layers;

        while (layer !is null)
        {
            SymbolLookupLayer* nextLayer = layer.next;

            while (layer !is null)
            {
                SymbolLookupLayer* nextSibling = layer.nextSibling;

                layer.appendNodesToListAndClear(symbolConvergeSetList.firstNode, convergableOnly);

                layer = nextSibling;
            }

            layer = nextLayer;
        }

        // pop!
        this.layers = this.layers.next;
    }

    /// Start a new set, per scope
    void startScope()
    {
        SymbolLookupLayer* layer = this.allocateLayer();
        layer.nextSibling = this.layers;

        if (this.layers !is null)
            layer.next = this.layers.next;

        this.layers = layer;
    }

    /// Find last state of a given variable, does not look in sibling scopes.
    const(SymbolLookupNode)* lookupLast(Verify4IRVariable* variable) @nogc
    {
        auto bucketId = (cast(size_t) variable) % 16;
        SymbolLookupLayer* layer = this.layers;

        while (layer !is null)
        {
            {
                SymbolLookupNode** bucketOfNode = &layer.bucketsOfMultipleWritableNodes[bucketId];

                while (*bucketOfNode !is null)
                {
                    if (cast(void*)(*bucketOfNode).key > variable)
                        break;
                    else if (cast(void*)(*bucketOfNode).key is variable)
                        return *bucketOfNode;

                    bucketOfNode = &((*bucketOfNode).next);
                }
            }

            {
                SymbolLookupNode** bucketOfNode = &layer.bucketsOfSingleWriteNodes[bucketId];

                while (*bucketOfNode !is null)
                {
                    if (cast(void*)(*bucketOfNode).key > variable)
                        break;
                    else if (cast(void*)(*bucketOfNode).key is variable)
                        return *bucketOfNode;

                    bucketOfNode = &((*bucketOfNode).next);
                }
            }

            layer = layer.next;
        }

        return null;
    }

    /**
        Find a variable in current scope or allocate it.

        Params:
            variable = The variable to find in curent scope.
            priorValue = The previous layour value if not in current scope.

        Returns:
            The variable value in current scope.
    */
    SymbolLookupNode* findOrAllocate(Verify4IRVariable* variable,
            out const(SymbolLookupNode)* priorValue) @trusted
    {
        auto bucketId = (cast(size_t) variable) % 16;
        SymbolLookupLayer* layer = this.layers;
        assert(layer !is null);

        SymbolLookupNode** bucketOfNode;

        void handle(ref SymbolLookupNode*[16] buckets) @trusted
        {
            bucketOfNode = &buckets[bucketId];

            while (*bucketOfNode !is null)
            {
                if (cast(void*)(*bucketOfNode).key > variable)
                    break;
                else if (cast(void*)(*bucketOfNode).key is variable)
                    return;

                bucketOfNode = &((*bucketOfNode).next);
            }

            *bucketOfNode = this.allocateNode(*bucketOfNode, variable);
            priorValue = this.lookupLast(variable);
        }

        if (variable.canBeWrittenToMoreThanOnce)
            handle(layer.bucketsOfMultipleWritableNodes);
        else
            handle(layer.bucketsOfSingleWriteNodes);

        return *bucketOfNode;
    }

private:

    SymbolLookupLayer* allocateLayer() @trusted
    {
        SymbolLookupLayer* ret = this.threadState.symbolLookupFreeLists.firstLayer;

        if (ret !is null)
        {
            this.threadState.symbolLookupFreeLists.firstLayer = ret.next;
        }
        else
        {
            ret = cast(SymbolLookupLayer*) this.threadState.allocator.malloc(
                    SymbolLookupLayer.sizeof);
        }

        *ret = SymbolLookupLayer.init;
        return ret;
    }

    SymbolLookupNode* allocateNode(SymbolLookupNode* next, Verify4IRVariable* variable) @trusted
    {
        SymbolLookupNode* ret = this.threadState.symbolLookupFreeLists.firstNode;

        if (ret !is null)
        {
            this.threadState.symbolLookupFreeLists.firstNode = ret.next;
        }
        else
        {
            ret = cast(SymbolLookupNode*) this.threadState.allocator.malloc(
                    SymbolLookupNode.sizeof);
        }

        *ret = SymbolLookupNode(next, variable);
        return ret;
    }
}

struct SymbolLookupLayer
{
    SymbolLookupLayer* next;
    SymbolLookupLayer* nextSibling;

    SymbolLookupNode*[16] bucketsOfMultipleWritableNodes;
    SymbolLookupNode*[16] bucketsOfSingleWriteNodes;

@safe nothrow @nogc:

    void appendNodesToListAndClear(ref SymbolLookupNode* onto, bool convergableOnly)
    {
        void handle(ref SymbolLookupNode*[16] buckets)
        {
            foreach (ref first; buckets)
            {
                if (first is null)
                    continue;

                SymbolLookupNode* last = first;

                while (last.next !is null)
                {
                    last = last.next;
                }

                last.next = onto;
                onto = first;

                first = null;
            }
        }

        handle(this.bucketsOfMultipleWritableNodes);

        if (!convergableOnly)
            handle(this.bucketsOfSingleWriteNodes);
    }
}

struct SymbolLookupNode
{
    SymbolLookupNode* next;

    Verify4IRVariable* key;
    // DFA state goes here
}

package(dmd.semantic4):

struct SymbolLookupFreeLists
{
    SymbolLookupNode* firstNode;
    SymbolLookupLayer* firstLayer;
}
