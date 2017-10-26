package reasoner.todolist;

import static reasoner.todolist.PriorityMatrix.NREGULAROPTIONS;

import java.util.ArrayList;
import java.util.List;

import org.semanticweb.owlapi.model.OWLClassExpression;

import reasoner.Dependencies.DependencySet;
import reasoner.graph.*;
import reasoner.state.SaveStack;


public class ToDoList {
	private final List<RegQueue> waitQueue = new ArrayList<>(NREGULAROPTIONS);
	private final PriorityMatrix matrix = new PriorityMatrix();
	private final SaveStack<TDLSaveState> saveStack = new SaveStack<>();
	/** number of un-processed entries */
    private int noe;
	public ToDoList() {
		noe = 0;
		for (int i = 0; i < NREGULAROPTIONS; i++) {
            waitQueue.add(new RegQueue());
        }
	}
	
	public void addEntry(Node node, NodeTag type, ConceptNDepSet cnds) {
        int index = matrix.getIndex(type);
        waitQueue.get(index).add(node, cnds, type);
        /*switch (index) {
            case NREGULAROPTIONS: // unused entry
                return;
            case PRIORITYINDEXID: // ID
                queueID.add(node, c);
                break;
            case PRIORITYINDEXNOMINALNODE: // NN
                queueNN.add(node, c);
                break;
            default: // regular queue
                waitQueue.get(index).add(node, c);
                break;
        }*/
        ++noe; 
    }
	
	public ToDoEntry getNextEntry() {
        if(isEmpty())
        		return null;
        // decrease amount of elements-to-process
       
        // check ID queue
     /*   if (!queueID.isEmpty()) {
            return queueID.get();
        }
        // check NN queue
        if (!queueNN.isEmpty()) {
            return queueNN.get();
        }*/
        // check regular queues
        else {
        	 --noe;
        for (int i = 0; i < NREGULAROPTIONS; ++i) {
            RegQueue arrayQueue = waitQueue.get(i);
            if (!arrayQueue.isEmpty()) {
                return arrayQueue.get();
            }
        }
        // that's impossible, but still...
        return null;
        }
    }
	/** @return check if Todo table is empty */
    public boolean isEmpty() {
        return noe == 0;
    }
    public int entries() {
    		return noe;
    }
    
    public void saveState(TDLSaveState tss) {
      //  tss.backupIDsp = queueID.getsPointer();
       // tss.backupIDep = queueID.getWaitSize();
     //   queueNN.save(tss);
     //   tss.backup6key = waitQueue.get(6).getsPointer();
      //  tss.backup6value = waitQueue.get(6).getWaitSize();
      //  tss.backup5key = waitQueue.get(5).getsPointer();
      //  tss.backup5value = waitQueue.get(5).getWaitSize();
        tss.backup4key = waitQueue.get(4).getsPointer();
        tss.backup4value = waitQueue.get(4).getWaitSize();
        tss.backup3key = waitQueue.get(3).getsPointer();
        tss.backup3value = waitQueue.get(3).getWaitSize();
        tss.backup2key = waitQueue.get(2).getsPointer();
        tss.backup2value = waitQueue.get(2).getWaitSize();
        tss.backup1key = waitQueue.get(1).getsPointer();
        tss.backup1value = waitQueue.get(1).getWaitSize();
        tss.backup0key = waitQueue.get(0).getsPointer();
        tss.backup0value = waitQueue.get(0).getWaitSize();
        tss.noe = noe;
    }
    
    public void restoreState(TDLSaveState tss) {
       // queueID.restore(tss.backupIDsp, tss.backupIDep);
       // queueNN.restore(tss);
        waitQueue.get(0).restore(tss.backup0key, tss.backup0value);
        waitQueue.get(1).restore(tss.backup1key, tss.backup1value);
        waitQueue.get(2).restore(tss.backup2key, tss.backup2value);
        waitQueue.get(3).restore(tss.backup3key, tss.backup3value);
        waitQueue.get(4).restore(tss.backup4key, tss.backup4value);
      //  waitQueue.get(5).restore(tss.backup5key, tss.backup5value);
     //   waitQueue.get(6).restore(tss.backup6key, tss.backup6value);
        noe = tss.noe;
    }
    /** save current state using internal stack */
    public void save() {
    	TDLSaveState state = new TDLSaveState();
        saveState(state);
        saveStack.push(state);
       
       // saveStack.push(state, level);
    }
    
    /**
     * restore state to the given level using internal stack
     */
    public void restore(int level) {
    		restoreState(saveStack.pop(level));
    		//restoreState(saveStack.pop1(level));
    }

	public void updateToDoEntry(Node n, NodeTag type, OWLClassExpression c, DependencySet ds) {
		int index = matrix.getIndex(type);
        waitQueue.get(index).wait.stream().
        		filter(entry -> entry.getNode().equals(n) && entry.getClassExpression().equals(c)).
        			forEach(entry -> entry.setDs(DependencySet.plus(entry.getDs(), ds)));
		
	}

}
