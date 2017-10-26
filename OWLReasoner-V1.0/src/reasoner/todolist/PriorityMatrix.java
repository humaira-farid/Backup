package reasoner.todolist;


import org.semanticweb.owlapi.reasoner.ReasonerInternalException;

import reasoner.graph.NodeTag;


public class PriorityMatrix {

	/** number of regular options (o- and NN-rules are not included) */
	public static final int NREGULAROPTIONS = 5;
    /**
     * priority index for o- operations (note that these ops have the
     * highest priority)
     */
    protected static final int PRIORITYINDEXID = NREGULAROPTIONS + 1;
    /** priority index for lesser than or equal operation in nominal node */
    protected static final int PRIORITYINDEXNOMINALNODE = NREGULAROPTIONS + 2;
    // regular operation indexes
    private int indexAnd;
    private int indexOr;
    private int indexExists;
    private int indexForall;
   // private int indexLE;
   // private int indexGE;

    public void initPriorities(String options) {
        // check for correctness
        if (options.length() < 5) {
            throw new ReasonerInternalException("ToDo List option string should have length 7");
        }
        // init values by symbols loaded
        indexAnd = 1; // options.charAt(1) - '0';
        indexOr = 2; //options.charAt(2) - '0';
        indexExists = 3; //options.charAt(3) - '0';
        indexForall = 4; //options.charAt(4) - '0';
      //  indexLE = options.charAt(5) - '0';
       // indexGE = options.charAt(6) - '0';
        
    }
    public int getIndex(NodeTag op) {
        switch (op) {
            case AND:
                return indexAnd;
            case FORALL:
            		return indexForall;
            case TOP: // no need to process these ops
                return NREGULAROPTIONS;
            case OR:
            		return indexOr;
            case EXISTS:
        			return indexExists;
            default: // safety check
                return -1;
        }
    }
    
}
