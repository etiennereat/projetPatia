package fr.uga.pddl4j.tutorial.satplanner;

import fr.uga.pddl4j.encoding.CodedProblem;
import fr.uga.pddl4j.util.*;

import java.util.*;


/**
 * This class implements a simple SAT planner based on SAT4J.
 *
 * @author H. Fiorino and complete by C. Him, D. Lepas, T. Perin E. Reat.
 * @version 1.0 - 18.04.2021
 */
public final class SATEncoding {

    /*
     * A SAT problem in dimacs format is a list of int list a.k.a clauses
     */
    private final List<int[]> dimacs;

    //map pour sauvegarder les transitions des actions entre 2 étapes
    private HashMap<Integer, ArrayList<Integer>> transitions;

    //sauvegarde des faits a l'initialisation du problem
    private final BitState init;
    //sauvegarde des faits au but voulu du problem
    private final BitState goal;
    //l'ensemble des fait "interessants" dans le problem
    private final List<IntExp> relevantfact;
    //le problem
    private final CodedProblem problem;

    /*
     * Current number of steps of the SAT encoding
     */
    private int steps;

    /**
     * Creates a new Sat Encodeur pour la generation des clauses
     *
     * @param problem le problem à encoder
     * @param steps   l'étape initial où l'on va commencer les encodages
     */
    public SATEncoding(final CodedProblem problem, final int steps) {
        dimacs = new ArrayList<>();
        this.steps = steps;
        this.problem = problem;
        // We get the initial state from the planning problem
        init = new BitState(problem.getInit());
        goal = new BitState(problem.getGoal());
        relevantfact = problem.getRelevantFacts();
        //generation des clauses de l'initialisation
        buildInit();

        //generation des clauses pour les étapes qu'on veut "sauter" au debut
        for (int i = 1; i < steps; i++) {
            next();
        }
    }

    /**
     * Ajoute a Dimac les clauses qui encodent l'etat initial du problem
     */
    private void buildInit() {
        for (int i = 0; i < relevantfact.size(); i++) {
            if (init.get(i)) {
                addClause(pair(i, steps));
            } else {
                addClause(-pair(i, steps));
            }
        }
    }

    /**
     * genere les clauses qui encodent l'etat final du problem
     *
     * @return une liste contenant les clause de Dimac et celle de l'etat final du problem
     */
    private List<int[]> buildGoal() {
        List<int[]> list = new ArrayList<>(dimacs);
        for (int i = 0; i < relevantfact.size(); i++) {
            int[] clause = new int[1];
            if (goal.get(i)) {
                clause[0] = pair(i, steps + 1);
                list.add(clause);
            }
        }
        return list;
    }

    /**
     * affiche les clauses de la liste
     *
     * @param clauses la liste a afficher
     */
    public void showClause(List<int[]> clauses) {
        for (int[] clause : clauses) {
            System.out.print("( ");
            for (int variable : clause) {
                System.out.print(variable + " ");
            }
            System.out.println(" ) ^");
        }
    }

    /**
     * affiche les clauses de la liste en decodant leurs couplages
     *
     * @param clauses la liste à afficher
     */
    public void showUnpairing(List<int[]> clauses) {
        for (int[] clause : clauses) {
            for (int variable : clause) {
                int[] tmp = unpair(variable);
                System.out.print("[ " + tmp[0] + " " + tmp[1] + " ] ");
            }
            System.out.println(" ^");
        }
    }

    /**
     * ajoute une clause unitaire a Dimac
     *
     * @param clause la clause unitaire à ajouter
     */
    private void addClause(int clause) {
        int[] clauseTab = new int[1];
        clauseTab[0] = clause;
        addClause(clauseTab);
    }

    /**
     * ajoute une clause a Dimac
     *
     * @param clauseTab la clause à ajouter
     */
    private void addClause(int[] clauseTab) {
        dimacs.add(clauseTab);
    }

    /**
     * ajoute une clause a Dimac
     *
     * @param clause la clause unitaire à ajouter
     */
    private void addClause(ArrayList<Integer> clause) {
        int[] clauseTab = new int[clause.size()];
        int i = 0;

        for (Integer variable : clause) {
            clauseTab[i] = variable;
            i++;
        }
        addClause(clauseTab);
    }


    /**
     * Réalise l'encodage à l'etape +1 du problem
     *
     * @return une liste contenant les clauses qui encode le probleme en x etape
     */
    public List<int[]> next() {
        transitions = new HashMap<>();
        for (int i = 0; i < problem.getOperators().size(); i++) {
            addAction(i);
        }

        buildtransition();
        List<int[]> res = buildGoal();
        steps++;
        return res;
    }


    // action => precondition1 ^ ..... preconditionN ^ positifefect1 ^ ... positifefectN ^ - negatifeffect1 ^ ... - negatifeffectN
    // A => B  equivalent a  -A v B
    // -code_op v ( pre1 ^ pre2 ^ pre3 ^ positifefect1 ^ positifeffect2 ^ - negatifeffect1 )
    // (-code_op v pre1) ^ (-code_op  v pre2) ...

    /**
     * ajoute les clause en lien avec l'action a Dimac
     *
     * @param bitnum le bit qui encode l'action
     */
    private void addAction(int bitnum) {
        final BitOp action = problem.getOperators().get(bitnum);
        final BitVector precond = action.getPreconditions().getPositive();
        final BitVector positive = action.getUnconditionalEffects().getPositive();
        final BitVector negative = action.getUnconditionalEffects().getNegative();

        int code_op = pair(bitnum + relevantfact.size(), steps);

        //genere les clauses de disjonction (pour eviter de faire 2 actions pour une étape)
        for (int i = bitnum + 1; i < problem.getOperators().size(); i++) {
            int code_other_op = pair(i + relevantfact.size(), steps);
            int[] clause = new int[2];
            clause[0] = -code_op;
            clause[1] = -code_other_op;
            addClause(clause);
        }

        //genere les clause qui encode l'action
        for (int i = 0; i < relevantfact.size(); i++) {

            //genere les clauses pour les préconditions de l'action à l'etape courante
            if (precond.get(i)) {
                int[] clause = new int[2];
                clause[0] = -code_op;
                clause[1] = pair(i, steps);
                addClause(clause);
            }

            //genere les clause pour les effets positifs qu'elle entraine à l'etape +1
            if (positive.get(i)) {
                int[] clause = new int[2];
                clause[0] = -code_op;
                clause[1] = pair(i, steps + 1);
                addClause(clause);
                addtransition(i, code_op);
            }
            //genere les clause pour les effets négatif qu'elle entraine à l'etape +1
            if (negative.get(i)) {
                int[] clause = new int[2];
                clause[0] = -code_op;
                clause[1] = -pair(i, steps + 1);
                addClause(clause);
                addtransition(-i, code_op);
            }
        }
    }

    /**
     * ajoute a la map de transition une action qui a fait un effet
     *
     * @param fi l'effet (positif ou négatif)
     * @param ai l'action encodée à une etape donnée
     */
    private void addtransition(int fi, int ai) {
        transitions.putIfAbsent(fi, new ArrayList<>());
        transitions.get(fi).add(ai);
    }

    // fi ^ - fi+1 => a v a4 v ... ai
    // -fi v fi+1 v a v a4 v ... ai

    /**
     * genere et ajoute à dimac les clauses de transition à partir de la map de transition
     */
    private void buildtransition() {
        for (Map.Entry<Integer, ArrayList<Integer>> operations_fi : transitions.entrySet()) {
            ArrayList<Integer> clause = operations_fi.getValue();
            if (operations_fi.getKey() > 0) {
                clause.add(pair(operations_fi.getKey(), steps));
                clause.add(-pair(operations_fi.getKey(), steps + 1));

            } else {
                clause.add(-pair(-operations_fi.getKey(), steps));
                clause.add(pair(-operations_fi.getKey(), steps + 1));
            }
            addClause(clause);
        }

    }

    /**
     * réalise un couplage entre un bitnum et son étape
     *
     * @param bitnum le numéro a encodé
     * @param step   l'étape à laquelle il doit etre encodé
     * @return le couplage des deux nombres
     */
    private static int pair(int bitnum, int step) {
        //Using Cantor paring function to generate unique number
        return (int) (0.5 * (bitnum + step) * (bitnum + step + 1) + step) + 1;
    }

    /**
     * réalise un découplage pour récuperer le bitnum et son étape
     *
     * @param z le numéro découplé
     * @return un tableau contenant bitnum et son étape
     */
    public static int[] unpair(long z) {
        if (z >= 0) {
            return unPairPositive(z);
        } else {
            return unPairNegative(z);
        }
    }


    /**
     * réalise un découplage pour récuperer le bitnum et son étape quand z est postif
     *
     * @param z le numéro découplé
     * @return un tableau contenant bitnum et son étape
     */
    private static int[] unPairPositive(long z) {
        z--;
        //Cantors depairing function:
        long t = (int) (Math.floor((Math.sqrt(8 * z + 1) - 1) / 2));
        long x = t * (t + 3) / 2 - z;
        long y = z - t * (t + 1) / 2;
        x++;
        y++;
        return new int[]{(int) x, (int) y}; //Returning an array containing the two numbers

    }

    /**
     * réalise un découplage pour récuperer le bitnum et son étape quand z est négatif
     *
     * @param z le numéro découplé
     * @return un tableau contenant bitnum et son étape
     */
    private static int[] unPairNegative(long z) {
        int[] tmp = unPairPositive(-z);

        return new int[]{-tmp[0], tmp[1]}; //Returning an array containing the two numbers
    }

}