package sprint.tracer.data;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.invoke.MethodHandles;
import java.util.HashMap;
import java.util.Map.Entry;

import sprint.tracer.Config;
import sprint.tracer.key.Context;

public class Catched {
  public static HashMap<String, Boolean> map = new HashMap<>();

  public static void record(String key) {
    map.put(Context.get() + "/" + key, true);
  }

  public static void print(File resultsDir) {
    File outFile = new File(resultsDir, MethodHandles.lookup().lookupClass().getSimpleName() + ".csv");
    try {
      BufferedWriter writer = new BufferedWriter(new FileWriter(outFile));
      for (Entry<String, Boolean> entry : map.entrySet()) {
        String row = String.format("%s/%b", entry.getKey(), entry.getValue());
        writer.write(row + "\n");
      }
      writer.close();
    } catch (IOException e) {
      e.printStackTrace();
      System.exit(Config.CANNOT_OPEN_FILE);
    }
  }
}
