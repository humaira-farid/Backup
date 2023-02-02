package reasoner.todolist;

import static reasoner.todolist.PriorityMatrix.NREGULAROPTIONS;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLClassExpression;

import reasoner.Dependencies.DependencySet;
import reasoner.graph.*;
import reasoner.state.SaveStack;


public class ToDoList {
	private final List<RegQueue> waitQueue = new ArrayList<>(NREGULAROPTIONS);
	private final PriorityMatrix matrix = new PriorityMatrix();
	private Map<Node, Integer> nodeEntries = new HashMap<>();
	/** number of un-processed entries */
    private int noe;
    private Map<Integer, TDLSaveState> saveMap = new HashMap<>();
	
    public ToDoList() {
		noe = 0;
		for (int i = 0; i < NREGULAROPTIONS; i++) {
            waitQueue.add(new RegQueue());
        }
	}
    
	public void initPriorities(String options) {
	        matrix.initPriorities(options);
	 }
	public void addEntry(Node node, NodeTag type, ConceptNDepSet cnds) {
        int index = matrix.getIndex(type);
     //   System.err.println(cnds.getDs().getMax()  +" node: "+ node.getId() + " addEntry  "+ cnds.getCe());
        waitQueue.get(index).add(node, cnds, type);
        int nodeEntry = 1;
        if(this.nodeEntries.get(node) != null) {
        	nodeEntry = this.nodeEntries.get(node) + 1;
        	this.nodeEntries.put(node, nodeEntry);
        }
        else
        	this.nodeEntries.put(node, nodeEntry);
       // System.err.println("adding nodeEntries "+ node.getId() +" : "+this.nodeEntries.get(node)) ;
        ++noe; 
    }
	public ToDoEntry getNextEntry() {
        if(isEmpty())
        		return null;
        else {
	        	--noe;
	        	
	        	// System.out.println("entry remaining : "+noe);
	    for (int i = 0; i < NREGULAROPTIONS; ++i) {
	    	RegQueue arrayQueue = waitQueue.get(i);
	        if (!arrayQueue.isEmpty()) {
	        	ToDoEntry entry = arrayQueue.get();
		        Node node = entry.getNode();
	            int nodeEntry =  this.nodeEntries.get(node) - 1;
	            this.nodeEntries.put(node, nodeEntry);

	            //    System.err.println("getting entry "+ node.getId() +" : "+entry.getClassExpression()) ;
		        return entry;
	         }
	    }
	        // that's impossible, but still...
	        return null;
        }
    }
	/*public Set<ToDoEntry> getAllToDoEntry(Node n, NodeTag type) {
		if(isEmpty())
    			return new HashSet<>();
		else {
       	 	--noe;
			Set<ToDoEntry> entries = new HashSet<>();
			int index = matrix.getIndex(type);
			RegQueue arrayQueue = waitQueue.get(index);
			if (!arrayQueue.isEmpty()) {
				entries.addAll(arrayQueue.getNodeEntry(n));
			}
			noe = noe - entries.size();
			//System.out.println("entries size : "+entries.size());
			//System.out.println("entries remaining : "+noe);
	        return entries;
		}
	}*/
	/** @return check if Todo table is empty */
    public boolean isEmpty() {
        return noe == 0;
    }
    public int entries() {
    		return noe;
    }
    
    public void saveState(TDLSaveState tss) {
     
        tss.backup1key = waitQueue.get(1).getsPointer();
        tss.backup1value = waitQueue.get(1).getWaitSize();
        tss.backup0key = waitQueue.get(0).getsPointer();
        tss.backup0value = waitQueue.get(0).getWaitSize();
        tss.waitingQueue = new ArrayList<>(waitQueue.get(1).wait);
        tss.noe = noe;
    }
    
    public void restoreState(TDLSaveState tss) {
    //	System.err.println("before noe "+ noe);
        waitQueue.get(0).restore(tss.backup0key, tss.backup0value);
    //    waitQueue.get(1).restore(tss.backup1key, tss.backup1value);
        waitQueue.get(1).restoreWait(tss.backup1key, tss.waitingQueue);
        noe = tss.noe;
        
     //  System.err.println("after noe "+ noe);
    }
    /** save current state 
     * @param level */
    public void save(int level) {
    	TDLSaveState state = new TDLSaveState();
        saveState(state);
       saveMap.put(level, state);
    }
    
    
    public void restore(int level) {
   // 	System.out.println("todo restore level "+level);
    //	restoreState(saveMap.get(level));
    	restoreState(saveMap.get(level), level);
    }
    private void restoreState(TDLSaveState tss, int level) {
    	waitQueue.get(0).restore(tss.backup0key, tss.backup0value);
        //    waitQueue.get(1).restore(tss.backup1key, tss.backup1value);
            waitQueue.get(1).restoreWait(tss.backup1key, level);
            noe = waitQueue.get(1).getNOE();
		
	}

	public void updateToDoEntry(Node n, NodeTag type, OWLClassExpression c, DependencySet ds) {
		int index = matrix.getIndex(type);
      //  waitQueue.get(index).wait.stream().
        //		filter(entry -> entry.getNode().equals(n) && entry.getClassExpression().equals(c)).
        	//		forEach(entry -> entry.setDs(DependencySet.update(DependencySet.create(entry.getDs()), DependencySet.create(ds))));
		
		
		List<ToDoEntry> entries = waitQueue.get(index).wait;
		for(ToDoEntry entry : entries) {
			if( entry != null) {
			if(entry.getNode() != null && entry.getClassExpression() != null) {
				if(entry.getNode().equals(n) && entry.getClassExpression().equals(c)) {
					entry.setDs(DependencySet.update(DependencySet.create(entry.getDs()), DependencySet.create(ds)));
				}
			}
		}
		}
	}
	public void updateToDoEntry(Node n, NodeTag type, OWLClassExpression c) {
		int index = matrix.getIndex(type);
      //  waitQueue.get(index).wait.stream().
        //		filter(entry -> entry.getNode().equals(n) && entry.getClassExpression().equals(c)).
        	//		forEach(entry -> entry.setDs(DependencySet.update(DependencySet.create(entry.getDs()), DependencySet.create(ds))));
		
		
		List<ToDoEntry> entries = waitQueue.get(index).wait;
		for(ToDoEntry entry : entries) {
			if( entry != null) {
			if(entry.getNode() != null && entry.getClassExpression() != null) {
				if(entry.getNode().equals(n) && entry.getClassExpression().equals(c)) {
					entry.setDs(DependencySet.create());
					//entry.setDs(DependencySet.update(DependencySet.create(entry.getDs()), DependencySet.create(ds)));
				}
			}
		}
		}
	}
	public void plusToDoEntry(Node n, NodeTag type, OWLClassExpression c, DependencySet ds) {
		int index = matrix.getIndex(type);
     //   waitQueue.get(index).wait.stream().
       // 		filter(entry -> entry.getNode().equals(n) && entry.getClassExpression().equals(c)).
        	//		forEach(entry -> entry.setDs(DependencySet.plus(DependencySet.create(entry.getDs()), DependencySet.create(ds))));
        List<ToDoEntry> entries = waitQueue.get(index).wait;
		for(ToDoEntry entry : entries) {
			if( entry != null) {
			if(entry.getNode() != null && entry.getClassExpression() != null) {
				if(entry.getNode().equals(n) && entry.getClassExpression().equals(c)) {
					entry.setDs(DependencySet.plus(DependencySet.create(entry.getDs()), DependencySet.create(ds)));
				}
			}
		}
		}
	}
	public boolean isToDoEntry1(Node n, NodeTag type, OWLClassExpression c, DependencySet ds) {
		int index = matrix.getIndex(type);
		return waitQueue.get(index).hasEntry(n, c);
        /*return waitQueue.get(index).wait.stream().
        		filter(entry -> entry.getNode().equals(n) && entry.getClassExpression().equals(c)).findAny().isPresent();*/
        		
		
	}
	public boolean hasToDoEntry(Node n, NodeTag type, OWLClassExpression c) {
		int index = matrix.getIndex(type);
		return waitQueue.get(index).hasEntry(n, c);
        /*return waitQueue.get(index).wait.stream().
        		filter(entry -> entry.getNode().equals(n) && entry.getClassExpression().equals(c)).findAny().isPresent();*/
        		
		
	}
	public boolean hasToDoEntry(Node n, OWLClassExpression c) {
		return waitQueue.get(1).hasEntry(n, c);
        /*return waitQueue.get(index).wait.stream().
        		filter(entry -> entry.getNode().equals(n) && entry.getClassExpression().equals(c)).findAny().isPresent();*/
        		
		
	}
	public ToDoEntry getEntry(Node n, OWLClassExpression c) {
		return waitQueue.get(1).getEntry(n, c);
        /*return waitQueue.get(index).wait.stream().
        		filter(entry -> entry.getNode().equals(n) && entry.getClassExpression().equals(c)).findAny().isPresent();*/
        		
		
	}
	public boolean hasToDoEntry(Node n, NodeTag type, OWLClassExpression c, DependencySet ds) {
		int index = matrix.getIndex(type);
		ToDoEntry en = waitQueue.get(index).hasEntry2(n, c);
		
		if(en != null) {
			removeEntry(index, en);
			return true;
		}
		else 
			return false;
        /*return waitQueue.get(index).wait.stream().
        		filter(entry -> entry.getNode().equals(n) && entry.getClassExpression().equals(c)).findAny().isPresent();*/
        		
		
	}
	/*public void updateToDoEntry(Node n, Node to, NodeTag type, OWLClassExpression c, DependencySet ds) {
		int index = matrix.getIndex(type);
        waitQueue.get(index).wait.stream().
        		filter(entry -> entry.getNode().equals(n) && entry.getClassExpression().equals(c)).
        			forEach(entry -> {
        				entry.setDs(DependencySet.update(entry.getDs(), ds));
        				entry.setNode(to);
        			});
		
	}*/

	public void removeEntry(int index, ToDoEntry entry) {
		
		waitQueue.get(index).remove(entry);
	}
	public boolean hasUnprocessedEntries(Node p) {
		//System.err.println( this.nodeEntries.get(p)) ;
		return (this.nodeEntries.get(p)!=null && this.nodeEntries.get(p) > 0);
	}
	
}
