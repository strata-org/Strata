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

        return Path.Combine(directory.FullName, ".lake", "build", "bin", "StrataVerify");
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

    private (int, string, string) RunTranslation(string filePath) {
        // Capture console output
        using var consoleOutput = new StringWriter();
        using var consoleError = new StringWriter();
        var originalOut = Console.Out;
        var originalError = Console.Error;
        var exitCode = 0;

        try {
            Console.SetOut(consoleOutput);
            Console.SetError(consoleError);
            exitCode = BoogieToStrata.Main([filePath]);
        }
        finally {
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

        // Act
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

        // Act
        var (exitCode, standardOutput, errorOutput) = RunTranslation(filePath);
        Assert.Equal(0, exitCode);
        Assert.True(standardOutput.Length > 0, "Expected some output from BoogieToStrata");
        Assert.True(errorOutput.Length == 0, "Expected no error output from BoogieToStrata");
        var tempFile = Path.GetTempFileName();
        File.WriteAllText(tempFile, standardOutput);
        using var myProcess = new Process();
        myProcess.StartInfo.FileName = GetVerifierPath();
        myProcess.StartInfo.Arguments = tempFile;
        myProcess.StartInfo.RedirectStandardOutput = true;
        myProcess.StartInfo.RedirectStandardError = true;
        myProcess.Start();
        myProcess.WaitForExit();
        File.Delete(tempFile);
        Directory.Delete(vcsDirectory, true);
        // TODO: actually check output
        //output.WriteLine(myProcess.StandardOutput.ReadToEnd());
        //output.WriteLine(myProcess.StandardError.ReadToEnd());
        //Assert.Equal(0, myProcess.ExitCode);
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
        // Arrange & Act
        var bplFiles = Directory.GetFiles(TestsDirectory, "*.bpl", SearchOption.AllDirectories);

        // Assert
        Assert.True(bplFiles.Length > 0, $"No .bpl files found in {TestsDirectory}");

        output.WriteLine($"Found {bplFiles.Length} .bpl test files:");
        foreach (var file in bplFiles.OrderBy(f => f)) {
            output.WriteLine($"  - {Path.GetFileName(file)}");
        }
    }
}
