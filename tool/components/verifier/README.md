# Custom JUnit for Running Single TestMethod


## Prerequisites
- JDK 1.8+
- Maven 

## Usage
### Build
```bash
mvn package
```
### Command
```bash
java -classpath "<target_classes_classpath>:<dependent_classes_classpath>:<test_classes_classpath>:./target/junit-prl-1.0.0.jar" \
  kr.ac.korea.prl.SingleMethodJUnitRunner \
  "fully.qualified.TestClassName#testMethodName"
```
