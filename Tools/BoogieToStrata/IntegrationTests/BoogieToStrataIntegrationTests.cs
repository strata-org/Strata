using System.Diagnostics;
using System.Reflection;
using Xunit;
using Xunit.Abstractions;

namespace BoogieToStrata.IntegrationTests;

public class BoogieToStrataIntegrationTests(ITestOutputHelper output) {
    private static readonly string TestsDirectory = Path.Combine(GetProjectDirectoryName(), "Tests");

    private static DirectoryInfo? GetProjectDirectory() {
        // Get the directory where the test assembly is located
        var assemblyLocation = Assembly.GetExecutingAssembly().Location;
        var directory = new DirectoryInfo(Path.GetDirectoryName(assemblyLocation)!);

        // Navigate up to find the project root (where the main .csproj file is located)
        while (directory != null && !directory.GetFiles("BoogieToStrata.sln").Any()) {
            directory = directory.Parent;
        }

        return directory;
    }

    private static string GetProjectDirectoryName() {
        var directory = GetProjectDirectory();
        return directory?.FullName ?? throw new DirectoryNotFoundException("Could not find project directory");
    }

    private static string GetVerifierPath() {
        var directory = GetProjectDirectory();
        if (directory == null) {
            throw new DirectoryNotFoundException("Could not find project directory");
        }

        directory = directory.Parent?.Parent;
        if (directory == null) {
            throw new DirectoryNotFoundException("Could not find project parent directory");
        }

        return Path.Combine(directory.FullName, ".lake", "build", "bin", "strata");
    }

    public static IEnumerable<object[]> GetBoogieTestFiles() {
        if (!Directory.Exists(TestsDirectory)) {
            yield break;
        }

        var bplFiles = Directory.GetFiles(TestsDirectory, "*.bpl", SearchOption.AllDirectories);
        foreach (var file in bplFiles.OrderBy(f => f)) {
            yield return new object[] { Path.GetFileName(file), file };
        }
    }

    /// <summary>
    /// Returns true if the first 5 lines of <paramref name="filePath"/> contain
    /// the literal token "{:smack}". Files carrying this marker opt into the
    /// --smack CLI flag, which gates the assert_.<type> synthetic-requires
    /// injection and InferModifies=true.
    /// </summary>
    private static bool HasSmackMarker(string filePath) {
        if (!File.Exists(filePath)) return false;
        using var reader = new StreamReader(filePath);
        for (var i = 0; i < 5; i++) {
            var line = reader.ReadLine();
            if (line == null) break;
            if (line.Contains("{:smack}", StringComparison.Ordinal)) return true;
        }
        return false;
    }

    private (int, string, string) RunTranslation(string filePath) {
        return RunTranslation(filePath, HasSmackMarker(filePath));
    }

    private (int, string, string) RunTranslation(string filePath, bool smack) {
        // Capture console output
        using var consoleOutput = new StringWriter();
        using var consoleError = new StringWriter();
        var originalOut = Console.Out;
        var originalError = Console.Error;
        var exitCode = 0;

        try {
            Console.SetOut(consoleOutput);
            Console.SetError(consoleError);
            var args = smack ? new[] { "--smack", filePath } : new[] { filePath };
            exitCode = BoogieToStrata.Main(args);
        } catch (Exception) {
            exitCode = 1;
        } finally {
            Console.SetOut(originalOut);
            Console.SetError(originalError);
        }

        return (exitCode, consoleOutput.ToString(), consoleError.ToString());
    }

    [Theory]
    [MemberData(nameof(GetBoogieTestFiles))]
    public void TranslateTestFileWithoutErrors(string fileName, string filePath) {
        // Arrange
        output.WriteLine($"Testing file: {fileName}");
        output.WriteLine($"Full path: {filePath}");

        Assert.True(File.Exists(filePath), $"Test file does not exist: {filePath}");

        var (exitCode, standardOutput, errorOutput) = RunTranslation(filePath);

        output.WriteLine($"Exit code: {exitCode}");
        output.WriteLine($"Console output length: {standardOutput.Length} characters");

        if (!string.IsNullOrEmpty(errorOutput)) {
            output.WriteLine($"Error output: {errorOutput}");
        }

        // The program should exit successfully (return code 0)
        Assert.Equal(0, exitCode);

        // There should be some output (the Strata representation)
        Assert.True(standardOutput.Length > 0, "Expected some output from BoogieToStrata");
    }

    [Theory]
    [MemberData(nameof(GetBoogieTestFiles))]
    public void VerifyTestFile(string fileName, string filePath) {
        output.WriteLine($"Testing file: {fileName}");
        output.WriteLine($"Full path: {filePath}");
        var currentDirectory = Directory.GetCurrentDirectory();
        var vcsDirectory = Path.Combine(currentDirectory, "vcs");
        Directory.CreateDirectory(vcsDirectory);

        Assert.True(File.Exists(filePath), $"Test file does not exist: {filePath}");

        var (exitCode, standardOutput, errorOutput) = RunTranslation(filePath);
        Assert.Equal(0, exitCode);
        Assert.True(standardOutput.Length > 0, "Expected some output from BoogieToStrata");
        Assert.True(errorOutput.Length == 0, "Expected no error output from BoogieToStrata");
        var strataFile = Path.ChangeExtension(filePath, "core.st");
        File.WriteAllText(strataFile, standardOutput);
        var expectFile = Path.ChangeExtension(filePath, "expect");
        string? expectString = null;
        if (File.Exists(expectFile)) {
            expectString = File.ReadAllText(expectFile);
        }

        var strataArgs = "";
        if (expectString is null || expectString.Contains("Skipping verification")) {
            strataArgs += " --check";
        }
        using var proc = new Process();
        proc.StartInfo.FileName = GetVerifierPath();
        proc.StartInfo.Arguments = $"verify {strataArgs} {strataFile}";
        proc.StartInfo.RedirectStandardOutput = true;
        proc.StartInfo.RedirectStandardError = true;
        proc.Start();
        proc.WaitForExit();
        File.Delete(strataFile);
        Directory.Delete(vcsDirectory, true);
        var stdout = proc.StandardOutput.ReadToEnd();
        var stderr = proc.StandardError.ReadToEnd();
        var expectedExitCode = 0;
        if (expectString is null) {
            Assert.Contains("Skipping verification", stdout);
        } else {
            Console.WriteLine("Checking expected output");
            Assert.Equal(expectString, stdout);
            if (expectString.Contains("failed")) {
                expectedExitCode = 2; // ExitCode.failuresFound (see StrataMain.lean)
            }
        }
        Assert.Equal(expectedExitCode, proc.ExitCode);
    }

    /// <summary>
    /// Regression test: assert_.<type> procedures must produce a single
    /// merged spec block, not duplicates, regardless of whether the input
    /// already has user-written specs. Two cases:
    ///   1. existing ensures only — synthetic requires merges in.
    ///   2. existing requires — synthetic requires is added alongside,
    ///      not silently dropped.
    /// </summary>
    [Fact]
    public void SmackAssertProducesSingleMergedSpecBlock() {
        var filePath = Path.Combine(TestsDirectory, "SmackAssertDuplicateSpec.bpl");
        Assert.True(File.Exists(filePath), $"Test file does not exist: {filePath}");

        var (exitCode, standardOutput, errorOutput) = RunTranslation(filePath);
        Assert.Equal(0, exitCode);

        // Three procedures (assert_.i32, assert_.i32_with_req, main); the two
        // assert_.<type> ones each produce one spec block; main has none.
        // Count occurrences of "spec {" in the output: must be exactly 2.
        var specCount = 0;
        var searchFrom = 0;
        while (true) {
            var idx = standardOutput.IndexOf("spec {", searchFrom, StringComparison.Ordinal);
            if (idx < 0) break;
            specCount++;
            searchFrom = idx + 1;
        }

        output.WriteLine($"Output:\n{standardOutput}");
        Assert.Equal(2, specCount);

        // Overall sanity: the output contains at least one of each clause kind.
        // (assert_.i32 has an `ensures`, both procedures have at least one
        // `requires`.)
        Assert.Contains("requires", standardOutput);
        Assert.Contains("ensures", standardOutput);

        // The critical regression check: BOTH clauses must appear in the
        // SECOND procedure's spec block (assert_.i32_with_req) — i.e., the
        // requires-already-present case must not silently drop the synthetic
        // clause. Procedures emit in source order, so the second `spec {` is
        // assert_.i32_with_req's.
        var firstSpec = standardOutput.IndexOf("spec {", StringComparison.Ordinal);
        Assert.True(firstSpec >= 0, "Expected at least one spec block");
        var secondSpecStart = standardOutput.IndexOf("spec {", firstSpec + 1, StringComparison.Ordinal);
        Assert.True(secondSpecStart >= 0, "Expected a second spec block for assert_.i32_with_req");
        var secondSpecEnd = standardOutput.IndexOf("}", secondSpecStart, StringComparison.Ordinal);
        Assert.True(secondSpecEnd > secondSpecStart, "Second spec block missing closing brace");
        var secondSpec = standardOutput.Substring(secondSpecStart, secondSpecEnd - secondSpecStart);

        // The user-written `requires (p.0 > -1)` (sanitized to `p_0 > -(1)`)
        // and the synthetic `requires (p.0 != 0)` (sanitized to `p_0 != 0`)
        // must both be present in this single spec block.
        Assert.Contains("p_0 > -(1)", secondSpec);
        Assert.Contains("p_0 != 0", secondSpec);
    }

    /// <summary>
    /// Regression test: old() expressions must use the renamed name when a
    /// variable has a name collision (e.g., global var `main` vs procedure `main`).
    /// Previously, IdentifierExpr with Decl != null used NameOf() correctly, but
    /// had a silent fallback to Name() when Decl was null — which would emit the
    /// unrenamed (wrong) name in the collision case. Post-resolution, Decl should
    /// always be non-null; the fallback masked potential bugs.
    /// </summary>
    [Fact]
    public void OldExprUsesRenamedNameOnCollision() {
        var filePath = Path.Combine(TestsDirectory, "OldExprRenameCollision.bpl");
        Assert.True(File.Exists(filePath), $"Test file does not exist: {filePath}");

        var (exitCode, standardOutput, errorOutput) = RunTranslation(filePath);

        output.WriteLine($"Output:\n{standardOutput}");
        if (!string.IsNullOrEmpty(errorOutput)) {
            output.WriteLine($"Error output: {errorOutput}");
        }

        Assert.Equal(0, exitCode);

        // The output should contain an `old` expression referencing the *renamed*
        // variable (e.g., __var_main), not the raw name `main` which is the procedure.
        // Look for the pattern "old __var_main" or similar renamed form.
        Assert.Contains("old __var_main", standardOutput);

        // Also ensure the output does NOT contain "old main" (unrenamed fallback).
        // This would indicate the fallback to Name() was used instead of NameOf().
        Assert.DoesNotContain("old main", standardOutput);
    }

    /// <summary>
    /// Regression test for InferModifies = true.
    ///
    /// SMACK-generated Boogie can omit explicit modifies clauses on procedures.
    /// With InferModifies = true, Boogie's ModSetCollector infers them so that
    /// the translator correctly emits globals as `inout` parameters (modified)
    /// rather than read-only parameters.
    ///
    /// This test uses a .bpl file where procedure p() assigns to global g but
    /// has no `modifies g;` clause.  If InferModifies is working, the output
    /// should contain `inout g` for procedure p.
    /// </summary>
    [Fact]
    public void InferModifiesEmitsInoutForMutatedGlobal() {
        var filePath = Path.Combine(TestsDirectory, "InferModifiesGlobal.bpl");
        Assert.True(File.Exists(filePath), $"Test file does not exist: {filePath}");

        var (exitCode, standardOutput, errorOutput) = RunTranslation(filePath);

        output.WriteLine($"Output:\n{standardOutput}");
        if (!string.IsNullOrEmpty(errorOutput)) {
            output.WriteLine($"Error output: {errorOutput}");
        }

        // Translation must succeed — if InferModifies is broken, Boogie would
        // reject the program because g is assigned without a modifies clause.
        Assert.Equal(0, exitCode);

        // The inferred modifies clause should cause the translator to emit
        // `inout g` on procedure p's parameter list.
        Assert.Contains("inout g", standardOutput);
    }

    /// <summary>
    /// Pin down the --smack gate: without the flag, the assert_.<type>
    /// pattern is treated as an opaque procedure (no synthetic requires
    /// injected). Translation succeeds; the output does not contain a
    /// requires clause for the assert_ procedure.
    /// </summary>
    [Fact]
    public void SmackAssertWithoutFlagDoesNotInjectRequires() {
        var filePath = Path.Combine(TestsDirectory, "SmackAssert.bpl");
        Assert.True(File.Exists(filePath), $"Test file does not exist: {filePath}");

        var (exitCode, standardOutput, errorOutput) = RunTranslation(filePath, smack: false);

        output.WriteLine($"Output:\n{standardOutput}");
        if (!string.IsNullOrEmpty(errorOutput)) {
            output.WriteLine($"Error output: {errorOutput}");
        }

        Assert.Equal(0, exitCode);

        // Without --smack, no synthetic requires is added, so no `requires`
        // clause should appear anywhere in the translation of this file
        // (the .bpl has no user-written requires either).
        Assert.DoesNotContain("requires", standardOutput);
    }

    /// <summary>
    /// Pin down the --smack gate: without the flag, InferModifies is off.
    /// A program that omits an explicit `modifies` clause on a procedure
    /// that mutates a global is rejected at typecheck.
    /// </summary>
    [Fact]
    public void InferModifiesOffWithoutSmackFlag() {
        var filePath = Path.Combine(TestsDirectory, "InferModifiesGlobal.bpl");
        Assert.True(File.Exists(filePath), $"Test file does not exist: {filePath}");

        var (exitCode, standardOutput, errorOutput) = RunTranslation(filePath, smack: false);

        output.WriteLine($"Exit code: {exitCode}");
        output.WriteLine($"Output:\n{standardOutput}");
        if (!string.IsNullOrEmpty(errorOutput)) {
            output.WriteLine($"Error output: {errorOutput}");
        }

        // Without --smack, ResolveAndTypecheck rejects the program because
        // procedure p mutates global g without an explicit `modifies g;`
        // clause. BoogieToStrata.Main writes a "Failed to typecheck" line
        // to stderr and returns exit code 1. Pin both signals so a future
        // regression that fails for an unrelated reason (parse error,
        // arg-handling change) doesn't silently pass this test.
        Assert.Equal(1, exitCode);
        Assert.Contains("Failed to typecheck", errorOutput);
    }

    [Fact]
    public void ErrorCodeWithNoArguments() {
        var result = BoogieToStrata.Main(Array.Empty<string>());
        Assert.Equal(1, result);
    }

    [Fact]
    public void ErrorCodeOnNonexistentFile() {
        var nonExistentFile = "non_existent_file.bpl";
        var result = BoogieToStrata.Main([nonExistentFile]);
        Assert.Equal(1, result);
    }

    [Fact]
    public void TestsDirectoryContainsBoogieFiles() {
        var bplFiles = Directory.GetFiles(TestsDirectory, "*.bpl", SearchOption.AllDirectories);

        Assert.True(bplFiles.Length > 0, $"No .bpl files found in {TestsDirectory}");

        output.WriteLine($"Found {bplFiles.Length} .bpl test files:");
        foreach (var file in bplFiles.OrderBy(f => f)) {
            output.WriteLine($"  - {Path.GetFileName(file)}");
        }
    }
}
