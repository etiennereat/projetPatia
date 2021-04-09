package fr.uga.pddl4j.tutorial.satplanner;

import fr.uga.pddl4j.encoding.CodedProblem;
import fr.uga.pddl4j.util.*;

import java.util.ArrayList;
import java.util.List;

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
        // Encoding of init
        // Each fact is a unit clause

        // We get the goal from the planning problem

        //Bitvector = 0001001 => les modifications
        //BitState  = 0101010 => etat des variable a ce moment
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
                clause[0]= pair(i,steps+1);
            }
            else {
                clause[0]= - pair(i,steps+1);
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
        dimacs.add(clauseTab);
    }

    private void addClause(int[] clause) {
        dimacs.add(clause);
    }


    /*
     * SAT encoding for next step
     */
    public List<int[]> next() {
        for (int i = 0; i < problem.getOperators().size(); i++) {
            addAction(i);
        }
        List<int[]> res =buildGoal();
        steps++;
        showClause(res);
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
            }
            if(negative.get(i)){
                int[] clause = new int[2];
                clause[0] = -code_op;
                clause[1] = - pair(i,steps);
                addClause(clause);
            }
        }
    }

    private static int pair(int a, int b) {
        return (int) ( ( (float)1.0/(float)2.0 )  * ( (float) ( (a+b) * (a+b+1) +b ) ) )  + 1;
    }

    public static int[] unpair(int z) {
        z--;
        long t = (int) (Math.floor((Math.sqrt(8 * z + 1) - 1) / 2));
        int x = (int) (t * (t + 3) / 2 - z);
        int y = (int) (z - t * (t + 1) / 2);
        return new int[]{x, y}; //Returning an array containing the two numbers
    }
}