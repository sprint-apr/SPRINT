package sprint.verifier.junit;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.junit.runner.Request;
import org.junit.runner.Result;
import org.junit.runner.notification.Failure;
import org.junit.runner.notification.StoppedByUserException;

public class JUnitRunner {

  public static void main(String[] args) {
    boolean testFailureFound = false;
    List<Request> requests = args[0].contains("#") ? createRequest(args)
        : Collections.singletonList((createRequestWithClasses(args)));

    if (requests == null) {
      System.err.println("Failed to create request");
      System.exit(1);
    }

    /* Executing failing tests */
    if (args[0].contains("#")) {
      org.junit.runner.JUnitCore core = new org.junit.runner.JUnitCore();
      List<Failure> failures = new ArrayList<>();
      for (Request rq : requests) {
        Result result = core.run(rq);
        failures.addAll(result.getFailures());
      }
      System.out.println(String.format("# Runned tests until failure: -1"));
      if (failures.isEmpty()) {
        System.exit(0);
      } else {
        for (Failure failure : failures) {
          System.out.println(failure.getTestHeader());
        }
        System.exit(1);
      }
    } 
  
    /* Executing regression test-suite, we stopped tests if one of failures found */
    JUnitCore core = new JUnitCore();
    try {
      requests.forEach(rq -> core.run(rq));
    } catch (StoppedByUserException e) {
      testFailureFound = true;
    }
    if (testFailureFound || core.lastFailure != null) {
      System.out.println(String.format("# Runned tests until failure: %d", core.runCount));
      System.out.println(core.lastFailure.getTestHeader());
      System.exit(1);
    } else {
      System.out.println("All Tests Passed!");
      System.exit(0);

    }
  }

  public static List<Request> createRequest(String[] args) {
    List<Request> requests = new ArrayList<>();
    for (String testInfo : args[0].split(",")) {
      try {
        if (testInfo.contains("#")) {
          String[] arr = testInfo.split("#");
          Class<?> testClass = Class.forName(arr[0]);
          String methodName = arr[1];
          requests.add(Request.method(testClass, methodName));
        }
      } catch (Exception e) {
        return null;
      }
    }
    return requests;
  }

  public static Request createRequestWithClasses(String[] args) {
    List<Class<?>> testClasses = new ArrayList<>();
    try {
      for (String testInfo : args[0].split(",")) {
        testClasses.add(Class.forName(testInfo));
      }
    } catch (Exception e) {
      return null;
    }

    return Request.classes(testClasses.toArray(new Class<?>[0]));
  }

}
