bash compilation.sh

benchmark="pddl/logistics" 
echo "SAT solveur"
for problem in $benchmark/p*.pddl; do
    filename=`basename $problem`
    echo "Test for $filename :"
    java -cp classes:lib/pddl4j-3.8.3.jar:lib/sat4j-sat.jar fr.uga.pddl4j.tutorial.satplanner.SATPlanner -o $benchmark/domain.pddl -f $problem -t 300 -q -s stat.csv 
    echo "done"
done

