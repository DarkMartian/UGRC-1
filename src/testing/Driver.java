package testing;

import java.util.Arrays;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.stream.Collectors;
import soot.G;
import soot.PackManager;
import soot.options.Options;
import soot.Transform;
import java.io.FileOutputStream;
import java.io.PrintStream;

public class Driver {

    // Each entry: { classPath, mainClass, reflLog, label }
    static final String[][] BENCHMARKS = {
            {
                "out",                           // [0] classPath = TamiFlex-dumped dir
                "Harness",                       // [1] mainClass = always "Harness" for DaCapo
                "tests/reflogs/avrora.log",      // [2] reflection log
                "avrora"                         // [3] label for output files
            },
    };

    public static void main(String[] args) throws Exception {
    	long start = System.nanoTime();
        for (String[] bench : BENCHMARKS) {
            String classPath = bench[0];
            String mainClass = bench[1];
            String reflLog   = bench[2];
            String label     = bench[3];

            String outFile = "tests/results/" + label + "_result.txt";
            new java.io.File("tests/results").mkdirs();
            PrintStream out = new PrintStream(new FileOutputStream(outFile));
            System.setOut(out);
            System.setErr(out);

            System.out.println("=== Benchmark: " + label + " ===");

            G.reset();

            Options.v().set_no_bodies_for_excluded(true);
            Options.v().set_allow_phantom_refs(true);
            Options.v().set_whole_program(true);

            Options.v().set_include(Arrays.asList(
                "org.apache.",
                "org.w3c"
            ));
            Options.v().set_exclude(Arrays.asList(
                "java.", "javax.", "sun.", "com.sun."
            ));

            String jreLib = System.getProperty("java.home") + "/lib";
            String[] sootArgs = {
                "-cp", classPath
                      + ";" + jreLib + "/rt.jar"
                      + ";" + jreLib + "/jce.jar"
                      + ";" + jreLib + "/jsse.jar"
                      + ";dacapo-9.12-MR1-bach.jar",
                "-pp",
                "-w", "-app",
                "-src-prec", "class",
                "-f", "class",
                "-d", "tests/checking1/" + label,
                "-p", "cg.spark", "enabled:true",
                "-p", "cg", "reflection-log:" + reflLog,  
                mainClass
            };

            callGraphAnalysis analysis = new callGraphAnalysis();
            PackManager.v().getPack("wjtp")
                           .add(new Transform("wjtp.mhpA", analysis));

            try {
                soot.Main.main(sootArgs);
                System.out.println("=== DONE: " + label + " ===");
            } catch (Exception e) {
                System.out.println("=== FAILED: " + label + " ===");
                e.printStackTrace();
            }

            out.flush();
            out.close();
        }
        long end = System.nanoTime();
        System.setOut(new PrintStream(new FileOutputStream(java.io.FileDescriptor.out)));
        System.out.println("All benchmarks complete. Results in tests/results/");
        System.out.println("Time taken (ms): " + ((end - start) / 1_000_000));
    }
}
