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

public class CastedWell {
  private static class Pair {
    public int cnt = 0;
    public boolean completed = false;
  }

  public static HashMap<String, Pair> map = new HashMap<>();

  private static String computeKey(String key) {
    return Context.get() + "/" + key;
  }

  public static void init(String key) {
    String contextKey = computeKey(key);
    Pair pair = map.get(contextKey);
    if (pair == null) {
      pair = new Pair();
      map.put(contextKey, pair);
    }
    pair.cnt++;
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
        String row = String.format("%s/%d,%b", entry.getKey(), value.cnt, value.completed);
        writer.write(row + "\n");
      }
      writer.close();
    } catch (IOException e) {
      e.printStackTrace();
      System.exit(Config.CANNOT_OPEN_FILE);
    }
  }
}
