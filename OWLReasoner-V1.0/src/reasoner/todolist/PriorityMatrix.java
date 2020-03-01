package reasoner.todolist;


import org.semanticweb.owlapi.reasoner.ReasonerInternalException;

import reasoner.graph.NodeTag;


public class PriorityMatrix {

	/** number of regular options (o- and NN-rules are not included) */
	public static final int NREGULAROPTIONS = 2;
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
    private int indexAll;

    public void initPriorities(String options) {
        // check for correctness
        if (options.length() < 2) {
            throw new ReasonerInternalException("ToDo List option string should have length 2");
        }
        // init values by symbols loaded
        indexAll =  options.charAt(1) - '0';
     //   indexOr = options.charAt(2) - '0';
       // indexAll = options.charAt(3) - '0';
        
        
    }
    public int getIndex(NodeTag op) {
        switch (op) {
            case AND:
                return indexAll;
            case FORALL:
            		return indexAll;
            case TOP: // no need to process these ops
                return NREGULAROPTIONS;
            case OR:
            		return indexAll;
            case EXISTS:
        			return indexAll;
            case LE:
    				return indexAll;
            case GE:
    				return indexAll;
            default: // safety check
                return -1;
        }
    }
    
}
