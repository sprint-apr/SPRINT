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

import sprint.tracer.Config;
import sprint.tracer.key.Context;

public class InvokedMethodSet {
  public static HashMap<String, Set<String>> map = new HashMap<>();

  public static void record(String invokedMethodName) {
    map.compute(invokedMethodName, (k, v) -> {
      Set<String> _v = v == null ? new HashSet<String>() : v;
      _v.add(Context.get());
      return _v;
    });
  }

  public static void print(File resultsDir) {
    File outFile = new File(resultsDir, MethodHandles.lookup().lookupClass().getSimpleName() + ".csv");
    try {
      BufferedWriter writer = new BufferedWriter(new FileWriter(outFile));
      for (Entry<String, Set<String>> entry : map.entrySet()) {
        String row = String.format("%s/%s", entry.getKey(), String.join("@", entry.getValue()));
        writer.write(row + "\n");
      }
      writer.close();
    } catch (IOException e) {
      e.printStackTrace();
      System.exit(Config.CANNOT_OPEN_FILE);
    }
  }

}
