package fr.uga.pddl4j.tutorial.satplanner;

import fr.uga.pddl4j.encoding.CodedProblem;
import fr.uga.pddl4j.util.*;

import java.util.*;

import static java.lang.Math.max;

/**
 * This class implements a planning problem/domain encoding into DIMACS
 *
 * @author H. Fiorino
 * @version 1.0 - 30.03.2021
 */
public final class SATEncoding {

    /*
     * A SAT problem in dimacs format is a list of int list a.k.a clauses
     */
    private final List<int[]> dimacs;
    private HashMap<Integer, ArrayList> transitions;

    private final BitState init;
    private final BitState goal;
    private final List<IntExp> relevantfact;
    private final CodedProblem problem;
    /*
     * Current number of steps of the SAT encoding
     */
    private int steps;

    public SATEncoding(final CodedProblem problem, final int steps) {
        super();
        dimacs = new ArrayList<int[]>();

        this.steps = steps;
        this.problem = problem;
        // We get the initial state from the planning problem
       init = new BitState(problem.getInit());
       goal = new BitState(problem.getGoal());
       relevantfact = problem.getRelevantFacts();

       buildInit();
    }

    private void buildInit(){
        for(int i=0;i < relevantfact.size();i++ ){
            if(init.get(i)) {
                addClause(pair(i,steps));
            }
            else {
                addClause(-pair(i,steps));
            }
        }
    }

    private List<int[]> buildGoal(){
        List<int[]> list = new ArrayList<int[]>(dimacs);
        for(int i=0;i < relevantfact.size();i++ ){
            int[] clause = new int[1];
            if(goal.get(i)) {
                clause[0]= pair(i,steps +1);
            }
            else {
                clause[0]= - pair(i,steps +1);
            }
            list.add(clause);

        }
        return list;
    }

    public void showClause(List<int[]> clauses){
        for(int[] clause : clauses){
            System.out.print("( ");
            for(int variable : clause){
                System.out.print(variable+" ");
            }
            System.out.println(" ) ^");
        }
    }

    private void addClause(int clause) {
        int[] clauseTab = new int[1];
        clauseTab[0] = clause;
        addClause(clauseTab);
    }

    private void addClause(int[] clauseTab) {
        dimacs.add(clauseTab);
    }

    private void addClause(ArrayList<Integer> clause){
        int[] clauseTab = new int[clause.size()];
        int i=0;
        System.out.print("Je construis cette transition : ");

        for(Integer variable : clause){
            clauseTab[i]=variable;
            System.out.print(clauseTab[i]+" ");
            i++;
        }
        System.out.println("");
        addClause(clauseTab);
    }


    /*
     * SAT encoding for next step
     */
    public List<int[]> next() {
        transitions = new HashMap<Integer, ArrayList>();
        for (int i = 0; i < problem.getOperators().size(); i++) {
            addAction(i);
        }

        buildtransition();
        List<int[]> res =buildGoal();
        showClause(res);
        steps++;
        return res;
    }
    // action => precondition1 ^ ..... preconditionN ^ positifefect1 ^ ... positifefectN ^ - negatifeffect1 ^ ... - negatifeffectN
    // A => B  equivalent a  -A v B
    // -code_op v ( pre1 ^ pre2 ^ pre3 ^ positifefect1 ^ positifeffect2 ^ - negatifeffect1 )
    // (-code_op v pre1) ^ (-code_op  v pre2) ...
    private void addAction(int indice) {

        final BitOp action = problem.getOperators().get(indice);
        final BitVector precond = action.getPreconditions().getPositive();
        final BitVector positive = action.getUnconditionalEffects().getPositive();
        final BitVector negative = action.getUnconditionalEffects().getNegative();

        int code_op = pair(indice+ relevantfact.size(),steps);
        for(int i=indice+1;i< problem.getOperators().size();i++){
            int code_other_op = pair(i+ relevantfact.size(),steps);
            int[] clause = new int[2];
            clause[0] =  - code_op;
            clause[1] =  - code_other_op;
            addClause(clause);
        }
        for(int i=0;i < relevantfact.size();i++ ){
            if(precond.get(i)){
                int[] clause = new int[2];
                clause[0] = -code_op;
                clause[1] = pair(i,steps);
                addClause(clause);
            }
            if(positive.get(i)){
                int[] clause = new int[2];
                clause[0] = -code_op;
                clause[1] = pair(i,steps);
                addClause(clause);
                addtransition(i,code_op);
            }
            if(negative.get(i)){
                int[] clause = new int[2];
                clause[0] = -code_op;
                clause[1] = - pair(i,steps);
                addClause(clause);
                addtransition(-i,code_op);
            }
        }
    }


    private void addtransition(int fi,int ai){
        transitions.putIfAbsent(fi,new ArrayList<Integer>());
        transitions.get(fi).add(ai);
    }

    // fi ^ - fi+1 => a v a4 v ... ai
    // -fi v fi+1 v a v a4 v ... ai
    private void buildtransition(){
        for(Map.Entry<Integer, ArrayList> operations_fi : transitions.entrySet()){
            ArrayList clause = operations_fi.getValue();
            if(operations_fi.getKey() > 0){
                clause.add(- pair(operations_fi.getKey(),steps));
                clause.add(pair(operations_fi.getKey(),steps + 1));
            }
            else{
                clause.add( pair(- operations_fi.getKey(),steps));
                clause.add(- pair(- operations_fi.getKey(),steps + 1));
            }
            addClause(clause);
        }

    }
    private static int pair(int bitnum, int step) {
        //Using Cantor paring function to generate unique number
        return (int) (0.5 * (bitnum + step) * (bitnum + step + 1) + step) + 1;
    }


    private static int[] unpair(int z) {
        /*
        Cantor unpair function is the reverse of the pairing function. It takes a single input
        and returns the two corespoding values.
        */
        z--;
        int t = (int) (Math.floor((Math.sqrt(8 * z + 1) - 1) / 2));
        int bitnum = t * (t + 3) / 2 - z;
        int step = z - t * (t + 1) / 2;
        return new int[]{bitnum, step}; //Returning an array containing the two numbers
    }
}