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
        
        try (var out = new FileOutputStream(args[0])) {
            var writer = IonBinaryWriterBuilder.standard().build(out);
            program.writeTo(writer);
            writer.close();
        }
        System.out.println("Generated: " + args[0]);
    }
}
