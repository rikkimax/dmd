module dmd.semantic4.entry;
import dmd.semantic4.ir;
import dmd.arraytypes;
import dmd.astenums;
import core.stdc.stdio : printf;

version = MeasureTime;
//version = DebugTrace;
//version = DebugMe;
//version = Parallelize;

void runSemantic4(ref Modules modules)
{
    import dmd.semantic4.ir_build;

    version (MeasureTime)
    {
        import std.datetime.stopwatch;

        StopWatch sw;
        sw.start;
    }

    int totalFunctions;
    size_t maxNumberOfNamedVariables, maxNumberOfUnnamedVariables, maxNumberOfLabels;

    version (Parallelize)
    {
        import std.range : iota;
        import std.parallelism : parallel;

        foreach (mi; iota(modules.length).parallel)
        {
            auto m = modules[mi];

            // Do not try to perform memory verification on non-D files.
            if (!(m.filetype == FileType.d || m.filetype == FileType.dhdr))
                continue;

            VerificationDFAThreadState threadState;

            {
                // reserve some memory
                auto pos = threadState.allocator.savePos();
                threadState.allocator.malloc(4096 * 1024);
                threadState.allocator.release(pos);
            }

            scope v = new FindAllFunctionsVisitor;
            v.threadState = &threadState;
            v.theModule = m;

            version (DebugTrace)
            {
                v.doTrace = true;
                v.debugIR = true;
            }
            else version (DebugMe)
            {
                v.debugIR = true;
            }

            v.threadState.irRoot = Verify4IRRoot();
            m.accept(v);

            version (MeasureTime)
            {
                totalFunctions += v.seenFunctions;
            }
        }
    }
    else
    {
        foreach (m; modules)
        {
            // Do not try to perform memory verification on non-D files.
            if (!(m.filetype == FileType.d || m.filetype == FileType.dhdr))
                continue;

            VerificationDFAThreadState threadState;

            {
                // reserve some memory
                auto pos = threadState.allocator.savePos();
                threadState.allocator.malloc(4096 * 1024);
                threadState.allocator.release(pos);
            }

            scope v = new FindAllFunctionsVisitor;
            v.threadState = &threadState;
            v.theModule = m;

            version (DebugTrace)
            {
                v.doTrace = true;
                v.debugIR = true;
            }
            else version (DebugMe)
            {
                v.debugIR = true;
            }

            v.threadState.irRoot = Verify4IRRoot();
            m.accept(v);

            version (MeasureTime)
            {
                totalFunctions += v.seenFunctions;

                if (maxNumberOfNamedVariables < v.maxNumberOfNamedVariables)
                    maxNumberOfNamedVariables = v.maxNumberOfNamedVariables;
                if (maxNumberOfUnnamedVariables < v.maxNumberOfUnnamedVariables)
                    maxNumberOfUnnamedVariables = v.maxNumberOfUnnamedVariables;
                if (maxNumberOfLabels < v.maxNumberOfLabels)
                    maxNumberOfLabels = v.maxNumberOfLabels;
            }
        }
    }

    version (MeasureTime)
    {
        printf("Semantic 4 ran in %lld ms with %d functions, named %zd variables, unnamed %zd variables, %zd labels\n",
                sw.peek.total!"msecs", totalFunctions,
                maxNumberOfNamedVariables, maxNumberOfUnnamedVariables, maxNumberOfLabels);
    }
}
