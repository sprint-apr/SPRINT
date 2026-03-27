package sprint.tracer.key;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import javassist.CtBehavior;
import javassist.expr.MethodCall;

public abstract class KeyGenerator<Element> {
  protected final CtBehavior method;
  protected final String sourceFileName;

  protected final HashMap<Element, String> bindings = new HashMap<>();
  protected final Set<String> keys = new HashSet<>();
  protected final SortedMap<Integer, Integer> sameLineCounter = new TreeMap<>();

  protected int lastByteIndex = -1;

  public KeyGenerator(CtBehavior method) {
    this.method = method;
    this.sourceFileName = method.getDeclaringClass().getName();
  }

  /* compute must be invoked in the bytecode order */
  public String compute(Element e) {
    if (bindings.containsKey(e)) {
      return bindings.get(e);
    }

    if (e instanceof MethodCall) {
      MethodCall mc = (MethodCall) e;
      if (mc.getClassName().startsWith("sprint")) {
        return null;
      }
    }

    int byteIndex = getByteIndex(e);
    assert (byteIndex > lastByteIndex);

    int line = getLine(e);
    int count = sameLineCounter.compute(line, (l, cnt) -> cnt == null ? 0 : ++cnt);
    String key = String.format("%s,%d,%d", method.getDeclaringClass().getName(), line, count);

    bindings.put(e, key);

    assert (!keys.contains(key));

    return key;
  }

  abstract protected Iterable<Element> getOrderedElementIterator();

  abstract protected int getLine(Element e);

  abstract protected int getByteIndex(Element e);
}
