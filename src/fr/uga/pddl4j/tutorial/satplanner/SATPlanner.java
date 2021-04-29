package fr.uga.pddl4j.tutorial.satplanner;


import fr.uga.pddl4j.encoding.CodedProblem;
import fr.uga.pddl4j.parser.ErrorManager;
import fr.uga.pddl4j.planners.Planner;
import fr.uga.pddl4j.planners.ProblemFactory;
import fr.uga.pddl4j.planners.statespace.AbstractStateSpacePlanner;
import fr.uga.pddl4j.planners.statespace.StateSpacePlanner;
import fr.uga.pddl4j.util.*;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Arrays;
import java.util.Properties;
import java.util.List;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.ModelIterator;

import static fr.uga.pddl4j.tutorial.satplanner.SATEncoding.unpair;
import static java.lang.System.currentTimeMillis;

/**
 * This class implements a simple SAT planner based on SAT4J.
 *
 * @author H. Fiorino
 * @version 1.0 - 29.03.2021
 */
public final class SATPlanner extends AbstractStateSpacePlanner {

    /*
     * The arguments of the planner.
     */
    private Properties arguments;

    /**
     * Creates a new SAT planner with the default parameters.
     *
     * @param arguments the arguments of the planner.
     */
    public SATPlanner(final Properties arguments) {
        super();
        this.arguments = arguments;
    }

    /**
     * Solves the planning problem and returns the first solution found.
     *
     * @param problem the problem to be solved.
     * @return a solution search or null if it does not exist.
     */
    @Override
    public Plan search(final CodedProblem problem) {
        // The solution plan is sequential
        final Plan plan = new SequentialPlan();
        // We get the initial state from the planning problem
        final BitState init = new BitState(problem.getInit());
        // We get the goal from the planning problem
        final BitState goal = new BitState(problem.getGoal());
        // Nothing to do, goal is already satisfied by the initial state
        if (init.satisfy(problem.getGoal())) {
            return plan;
        }
        // Otherwise, we start the search
        else {

            List<int[]> clauses = null;
            // SAT solver timeout
            final int timeout = ((int) this.arguments.get(Planner.TIMEOUT));
            // SAT solver max number of var
            int MAXVAR = 50000;
            // SAT solver max number of clauses
            int NBCLAUSES = 100000;

            ISolver solver = SolverFactory.newDefault();
            solver.setTimeout(timeout);
            ModelIterator mi = new ModelIterator(solver);
            IProblem ip = null;

            int max_step = (Integer) this.arguments.get("steps");
            //On a pas eu le temps d optimiser pour avoir une étape initial cohérente avec le probleme donc on commence a 1
            int current_step = 1;
            SATEncoding encoder = new SATEncoding(problem, current_step);


            solver.newVar(MAXVAR);
            solver.setExpectedNumberOfClauses(NBCLAUSES);

            //boucle tant que le sat solver ne trouve pas de solution ou que l'on atteint pas une limite (nb clauses ou temps)
            try {
                do {
                    try {
                        //reinitialise le solver
                        solver.reset();
                        if ((int) arguments.get("quiet") == 0)
                            System.out.println("On esssaie de resoudre a l'etape " + current_step);
                        //on genere les clauses a l'etape +1
                        clauses = encoder.next();
                        //ajout des clauses au solver
                        for (int[] clause : clauses) {
                            solver.addClause(new VecInt(clause));
                        }
                        ip = solver;
                        current_step++;
                        //si c'est solvable on s'arrete
                        if (ip.isSatisfiable()) {
                            break;
                        }
                        //si ce n'est pas solvable a l'etape n on boucle pour tester a n+1
                    } catch (ContradictionException e) {
                        if ((int) arguments.get("quiet") == 0)
                            System.out.println("SAT encoding failure!");
                        current_step++;
                    }
                } while ((current_step < max_step));
                //si on atteint la borne temporelle on s'arrete
            } catch (TimeoutException e) {
                System.out.println("Timeout! No solution found!");
                return null;
            }

            if(current_step == max_step){
                return null;
            }

            int factSize = problem.getRelevantFacts().size();
            BitOp[] sortingActions = new BitOp[current_step];
            //réalisation du plan a partir de la solution rendu par le SAT solver
            for (int variable : ip.model()) {
                //traduction la variable pour obtenir le bitnum et l'etape
                int[] coupleSolution = unpair(variable);
                int bitnum = coupleSolution[0];
                int step = coupleSolution[1];
                // si le bitnum est plus grand que le nombre de fait alors c'est une action
                if (bitnum > factSize) {
                    //on récupere l'encodage de l'action
                    BitOp action = problem.getOperators().get(bitnum - (factSize));
                    //on la sauvegarde dans l'ordre grace a son étape
                    sortingActions[step] = action;
                }
            }
            //on sauvegarde les actions dans le plan
            for (int i = 0; i < current_step - 1; i++) {
                plan.add(0, sortingActions[i + 1]);
            }

            //si on n'a pas enlevé l'affichage on le réalise :
            if ((int) arguments.get("quiet") == 0) {
                if (clauses != null)
                    System.out.println("\nnb clauses : " + clauses.size());
                System.out.println("Une des solutions :");
                for (int variable : ip.model()) {
                    int[] tmp = unpair(variable);
                    System.out.println("[ " + tmp[0] + " " + tmp[1] + " ] ");
                }
                System.out.println(problem.toString(plan));
            }
            return plan;
        }
    }

    /**
     * Print the usage of the SAT planner.
     */
    private static void printUsage() {
        final StringBuilder strb = new StringBuilder();
        strb.append("\nusage of PDDL4J:\n")
                .append("OPTIONS   DESCRIPTIONS\n")
                .append("-o <str>    operator file name\n")
                .append("-f <str>    fact file name\n")
                .append("-t <num>    SAT solver timeout in seconds\n")
                .append("-n <num>    Max number of steps\n")
                .append("-q          quiet console output\n")
                .append("-s <str>   specifies save file name\n")
                .append("-h          print this message\n\n");
        Planner.getLogger().trace(strb.toString());
    }

    /**
     * Parse the command line and return the planner's arguments.
     *
     * @param args the command line.
     * @return the planner arguments or null if an invalid argument is encountered.
     */
    private static Properties parseCommandLine(String[] args) {

        // Get the default arguments from the super class
        final Properties arguments = StateSpacePlanner.getDefaultArguments();
        arguments.put("quiet", 0);
        arguments.put("steps", 200000);
        arguments.put(Planner.TIMEOUT, 300);
        // Parse the command line and update the default argument value
        for (int i = 0; i < args.length; i += 2) {
            if ("-o".equalsIgnoreCase(args[i]) && ((i + 1) < args.length)) {
                if (!new File(args[i + 1]).exists()) return null;
                arguments.put(Planner.DOMAIN, new File(args[i + 1]));
            } else if ("-f".equalsIgnoreCase(args[i]) && ((i + 1) < args.length)) {
                if (!new File(args[i + 1]).exists()) return null;
                arguments.put(Planner.PROBLEM, new File(args[i + 1]));
            } else if ("-t".equalsIgnoreCase(args[i]) && ((i + 1) < args.length)) {
                final int timeout = Integer.parseInt(args[i + 1]);
                if (timeout < 0) return null;
                arguments.put(Planner.TIMEOUT, timeout);
            } else if ("-s".equalsIgnoreCase(args[i]) && ((i + 1) < args.length)) {
                try {
                    arguments.put("csvFile", new FileWriter(args[i + 1], true));
                } catch (IOException e) {
                    e.printStackTrace();
                }
            } else if ("-q".equalsIgnoreCase(args[i])) {
                arguments.put("quiet", 1);
                i--;
            } else if ("-n".equalsIgnoreCase(args[i]) && ((i + 1) < args.length)) {
                final int steps = Integer.parseInt(args[i + 1]);
                if (steps > 0)
                    arguments.put("steps", steps);
                else
                    return null;
            } else {
                return null;
            }
        }
        // Return null if the domain or the problem was not specified
        return (arguments.get(Planner.DOMAIN) == null
                || arguments.get(Planner.PROBLEM) == null) ? null : arguments;
    }

    /**
     * The main method of the <code>SATPlanner</code> example. The command line syntax is as
     * follow:
     * usage of SATPlanner:
     * <p>
     * OPTIONS   DESCRIPTIONS
     * <p>
     * -o <i>str</i>   operator file name
     * -f <i>str</i>   fact file name
     * -t <i>num</i>   specifies the maximum CPU-time in seconds
     * -n <i>num</i>   specifies the maximum number of steps
     * -q              quiet console output
     * -s <i>str</i>   specifies save file name
     * -h              print this message
     *
     * @param args the arguments of the command line.
     */
    public static void main(String[] args) {
        final Properties arguments = SATPlanner.parseCommandLine(args);
        if (arguments == null) {
            SATPlanner.printUsage();
            System.exit(0);
        }

        final SATPlanner planner = new SATPlanner(arguments);
        final ProblemFactory factory = ProblemFactory.getInstance();

        File domain = (File) arguments.get(Planner.DOMAIN);
        File problem = (File) arguments.get(Planner.PROBLEM);
        ErrorManager errorManager = null;
        try {
            errorManager = factory.parse(domain, problem);
        } catch (IOException e) {
            Planner.getLogger().trace("\nUnexpected error when parsing the PDDL files.");
            System.exit(0);
        }

        if (!errorManager.isEmpty()) {
            errorManager.printAll();
            System.exit(0);
        } else {
            if ((int) arguments.get("quiet") == 0) {
                Planner.getLogger().trace("\nParsing domain file: successfully done");
                Planner.getLogger().trace("\nParsing problem file: successfully done\n");
            }
        }
        final CodedProblem pb = factory.encode();
        if ((int) arguments.get("quiet") == 0) {
            Planner.getLogger().trace("\nGrounding: successfully done ("
                    + pb.getOperators().size() + " ops, "
                    + pb.getRelevantFacts().size() + " facts)\n");

            if (!pb.isSolvable()) {
                Planner.getLogger().trace(String.format("Goal can be simplified to FALSE."
                        + "No search will solve it%n%n"));
                System.exit(0);
            }
        }
        long startTime = currentTimeMillis();
        final Plan plan = planner.search(pb);
        long endTime = currentTimeMillis();

        long execTime = endTime - startTime;

        FileWriter csvWriter = (FileWriter) arguments.get("csvFile");
        if(csvWriter != null) {

            int makespan = -1;
            if(plan != null){
                makespan = plan.size();
            }
            List<String> rowData = Arrays.asList("SatSolver",domain.getName(), problem.getName(), Integer.toString(makespan),Long.toString(execTime));
            try {
                csvWriter.append(String.join(",", rowData));
                csvWriter.append("\n");
                csvWriter.flush();
                csvWriter.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }
}