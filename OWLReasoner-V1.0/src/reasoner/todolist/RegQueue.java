package reasoner.todolist;

import java.util.*;

import org.semanticweb.owlapi.model.*;

import reasoner.Helper;
import reasoner.graph.*;

public class RegQueue {
	 /** waiting ops queue */
    protected List<ToDoEntry> wait = new ArrayList<>();
    /** start pointer; points to the 1st element in the queue */
    protected int sPointer = 0;

	
	public void add(Node node, ConceptNDepSet cnds, NodeTag type) {
		wait.add(new ToDoEntry(node, cnds, type));

	}
	
	 public boolean isEmpty() {
	        return sPointer == wait.size();
	    }

	 public ToDoEntry get() {
	        return wait.get(sPointer++);
	    }
	 
	 public void setsPointer(int sPointer) {
	        this.sPointer = sPointer;
	    }

	    /** @return wait size */
	    public int getWaitSize() {
	        return wait.size();
	    }
	    
	    public int getsPointer() {
	        return sPointer;
	    }
	    
	    public void restore(int sp, int ep) {
	        setsPointer(sp);
	       Helper.resize(wait, ep, null);
	    }
}
