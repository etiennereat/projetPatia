# satplanner
=======
SATPlanner based on PDDL4J and SAT4J.

Compile with:

javac -d classes -cp classes:lib/pddl4j-3.8.3.jar:lib/sat4j-sat.jar src/fr/uga/pddl4j/tutorial/*/*.java -Xlint:unchecked \
or \
bash compilation.sh

Test with:

java -cp classes:lib/pddl4j-3.8.3.jar:lib/sat4j-sat.jar fr.uga.pddl4j.tutorial.satplanner.SATPlanner -o pddl/test/logistics.pddl -f pddl/test/problem.pddl -n 20 -t 300

Script with:

bash script_exec.sh