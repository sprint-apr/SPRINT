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

public class InvokedWell {
  private static class Pair {
    public int cnt = 0;
    public boolean completed = false;
    public boolean isBaseNullable = false;
  }

  public static HashMap<String, Pair> map = new HashMap<>();

  private static String computeKey(String key) {
    return Context.get() + "/" + key;
  }

  public static boolean isNullable(Object o) {
    return o == null;
  }

  public static void init(String key, boolean isBaseNullable) {
    String contextKey = computeKey(key);
    Pair pair = map.get(contextKey);
    if (pair == null) {
      pair = new Pair();
      map.put(contextKey, pair);
      pair.isBaseNullable = isBaseNullable;
    }
    pair.cnt++;
    pair.isBaseNullable = isBaseNullable ? isBaseNullable : pair.isBaseNullable;
  }

  public static void completed(String key) {
    Pair pair = map.get(computeKey(key));
    pair.cnt--;
    pair.completed = true;
  }

  public static void print(File resultsDir) {
    File outFile = new File(resultsDir, MethodHandles.lookup().lookupClass().getSimpleName() + ".csv");

    try {
      BufferedWriter writer = new BufferedWriter(new FileWriter(outFile));
      for (Entry<String, Pair> entry : map.entrySet()) {
        Pair value = entry.getValue();
        String row = String.format("%s/%d,%b,%b", entry.getKey(), value.cnt, value.completed, value.isBaseNullable);
        writer.write(row + "\n");
      }
      writer.close();
    } catch (IOException e) {
      e.printStackTrace();
      System.exit(Config.CANNOT_OPEN_FILE);
    }
  }
}
