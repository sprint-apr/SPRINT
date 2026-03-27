package sprint.tracer.data;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.invoke.MethodHandles;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import sprint.tracer.Config;
import sprint.tracer.key.Context;

public class SwitchValue {
    public static int probe = 0;
    public static HashMap<String, Set<Integer>> map = new HashMap<>();

    public static void record(String key) {
        String contextKey = String.format("%s/%s", Context.get(), key);
        map.compute(contextKey, (k, v) -> {
            Set<Integer> s = v == null ? new HashSet<Integer>() : v;
            s.add(probe);
            return s;
        });
    }

    public static void print(File resultsDir) {
        File outFile = new File(resultsDir, MethodHandles.lookup().lookupClass().getSimpleName() + ".csv");
        try {
            BufferedWriter writer = new BufferedWriter(new FileWriter(outFile));
            for (Entry<String, Set<Integer>> entry : map.entrySet()) {
                String row = String.format("%s/%s", entry.getKey(),
                        entry.getValue().stream().map(String::valueOf).collect(Collectors.joining(",")));
                writer.write(row + "\n");
            }
            writer.close();
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(Config.CANNOT_OPEN_FILE);
        }
    }

}
