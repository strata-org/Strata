import static com.strata.simple.Simple.*;
import com.strata.simple.*;
import com.amazon.ion.*;
import com.amazon.ion.system.*;
import java.io.*;
import java.util.*;

/** Generates comprehensive.ion covering all DDM types. */
public class GenerateTestData {
    public static void main(String[] args) throws Exception {
        var ion = IonSystemBuilder.standard().build();
        var serializer = new IonSerializer(ion);
        generateSingleProgram(ion, serializer, args[0]);

        if (args.length > 1) {
            generateMultipleFiles(ion, serializer, args[1]);
        }
    }

    private static void generateSingleProgram(IonSystem ion, IonSerializer serializer, String outPath) throws Exception {
        
        // AST covering: Num, Str, Ident, Bool, Decimal, ByteArray, Option, Seq, nesting
        Node ast = block(List.of(
            assign("x", add(num(1), neg(num(2)))),
            print("hello"),
            ifStmt(true, data(new byte[]{0x01, (byte)0xFF}), Optional.of(decimal(3.14))),
            ifStmt(false, block(List.of()), Optional.empty())));
        
        IonList program = ion.newEmptyList();
        IonSexp header = ion.newEmptySexp();
        header.add(ion.newSymbol("program"));
        header.add(ion.newString("Simple"));
        program.add(header);
        program.add(serializer.serializeCommand(ast));
        
        try (var out = new FileOutputStream(outPath)) {
            var writer = IonBinaryWriterBuilder.standard().build(out);
            program.writeTo(writer);
            writer.close();
        }
        System.out.println("Generated: " + outPath);
    }

    private static void generateMultipleFiles(IonSystem ion, IonSerializer serializer, String outPath) throws Exception {
        Node ast1 = block(List.of(
            assign("x", num(42)),
            print("first file")));

        IonList program1 = ion.newEmptyList();
        IonSexp header1 = ion.newEmptySexp();
        header1.add(ion.newSymbol("program"));
        header1.add(ion.newString("Simple"));
        program1.add(header1);
        program1.add(serializer.serializeCommand(ast1));

        Node ast2 = block(List.of(
            assign("y", add(num(1), num(2))),
            print("second file"),
            ifStmt(true, block(List.of()), Optional.empty())));

        IonList program2 = ion.newEmptyList();
        IonSexp header2 = ion.newEmptySexp();
        header2.add(ion.newSymbol("program"));
        header2.add(ion.newString("Simple"));
        program2.add(header2);
        program2.add(serializer.serializeCommand(ast2));

        IonList files = ion.newEmptyList();

        IonStruct file1 = ion.newEmptyStruct();
        file1.put("filePath", ion.newString("file1.st"));
        file1.put("program", program1);
        files.add(file1);

        IonStruct file2 = ion.newEmptyStruct();
        file2.put("filePath", ion.newString("file2.st"));
        file2.put("program", program2);
        files.add(file2);

        try (var out = new FileOutputStream(outPath)) {
            var writer = IonBinaryWriterBuilder.standard().build(out);
            files.writeTo(writer);
            writer.close();
        }
        System.out.println("Generated: " + outPath);
    }
}
