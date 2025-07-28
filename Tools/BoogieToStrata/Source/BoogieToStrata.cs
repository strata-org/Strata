using Microsoft.Boogie;

namespace BoogieToStrata;

public static class BoogieToStrata {
    private static void PrintResolvedProgram(ExecutionEngineOptions options, ProcessedProgram prog) {
        var writer = new TokenTextWriter(Console.Out, options);
        StrataGenerator.EmitProgramAsStrata(options, prog.Program, writer);
    }

    public static int Main(string[] args) {
        if (args.Length != 1) {
            Console.Error.WriteLine("Usage: BoogieToStrata <inputFile>");
            return 1;
        }

        var filename = args[0];

        var options = new CommandLineOptions(Console.Out, new ConsolePrinter()) {
            Verify = false,
            TypeEncodingMethod = CoreOptions.TypeEncoding.Predicates
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