using Microsoft.Boogie;

namespace BoogieToStrata;

public static class BoogieToStrata {
    private const string Usage = "Usage: BoogieToStrata [--smack] <inputFile>";

    private static bool _smack;

    private static void PrintResolvedProgram(ExecutionEngineOptions options, ProcessedProgram prog) {
        var writer = new TokenTextWriter(Console.Out, options);
        StrataGenerator.EmitProgramAsStrata(options, prog.Program, writer, _smack);
    }

    /// <summary>
    /// Parse args into (smack, filename). Returns false on any malformed
    /// invocation (zero or two-plus positional args, unknown flags); the
    /// caller should print Usage and return exit code 1.
    /// </summary>
    private static bool TryParseArgs(string[] args, out bool smack, out string filename) {
        smack = false;
        filename = "";
        string? positional = null;
        foreach (var arg in args) {
            if (arg == "--smack") {
                smack = true;
            } else if (arg.StartsWith("--")) {
                return false; // unknown flag
            } else if (positional == null) {
                positional = arg;
            } else {
                return false; // two positional args
            }
        }
        if (positional == null) return false; // no positional arg
        filename = positional;
        return true;
    }

    public static int Main(string[] args) {
        if (!TryParseArgs(args, out var smack, out var filename)) {
            Console.Error.WriteLine(Usage);
            return 1;
        }
        _smack = smack;

        var options = new CommandLineOptions(Console.Out, new ConsolePrinter()) {
            Verify = false,
            TypeEncodingMethod = CoreOptions.TypeEncoding.Predicates,
            // Under --smack, SMACK-generated Boogie often omits explicit
            // `modifies` clauses on procedures that mutate globals.
            // InferModifies runs ModSetCollector.CollectModifies to populate
            // empty modifies clauses and suppresses modifies-clause
            // typechecking (via CheckModifies), so that ResolveAndTypecheck
            // does not reject SMACK programs missing modifies clauses.
            // For strict Boogie input (no --smack), this stays false and
            // missing modifies clauses are reported as typecheck errors.
            InferModifies = smack
        };

        var boogieEngine = ExecutionEngine.CreateWithoutSharedCache(options);
        var prog = boogieEngine.ParseBoogieProgram(new List<string> { filename }, false);
        if (prog == null) {
            Console.Error.WriteLine("Failed to parse Boogie program");
            return 1;
        }

        var tcResult = boogieEngine.ResolveAndTypecheck(prog, filename, out _);
        if (tcResult != PipelineOutcome.ResolvedAndTypeChecked) {
            Console.Error.WriteLine($"Failed to typecheck Boogie program (outcome = {tcResult})");
            return 1;
        }

        var stats = new PipelineStatistics();
        options.UseResolvedProgram.Add(PrintResolvedProgram);
        var task = boogieEngine.InferAndVerify(Console.Out, prog, stats);
        if (task.Result != PipelineOutcome.Done) {
            Console.Error.WriteLine($"Failed to process Boogie program (outcome = {task.Result}");
            return 1;
        }

        return 0;
    }
}
