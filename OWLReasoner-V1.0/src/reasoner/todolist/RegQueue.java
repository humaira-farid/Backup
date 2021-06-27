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
		 int sp = this.getsPointer();
		 int size = this.getWaitSize();
	//	 System.out.println("sp " + sp +" size "+ size);
		//	wait.stream().forEach( c -> System.out.println("before sort "+ c.getNode().getId()+ " type "+c.getType()));
		 if(sp < size) {
			// Collections.sort(wait.subList(sp, size), new ToDoEntryIDComparator()
			//		 .thenComparing(new ToDoEntryTypeComparator()));
			 Collections.sort(wait.subList(sp, size));
				/*
				  Collections.sort(wait.subList(sp, size), new ToDoEntryComparator(
						new ToDoEntryIDComparator(),
						new ToDoEntryTypeComparator()));
				  */
			}
	//	 wait.stream().forEach( c -> System.err.println("after sort "+ c.getNode().getId() + " type "+c.getType()));
		 return wait.get(sPointer++);
	   }
	 
	 public  Set<ToDoEntry> getNodeEntry(Node n) {
		/* Set<ToDoEntry> entries = new HashSet<>();
		 for(ToDoEntry en : wait) {
			 if(en.getNode().equals(n)) {
				 entries.add(en);
				 sPointer++;
			 }
		 }
		 return entries;*/
		
		 
		 Set<ToDoEntry> entries = new HashSet<>();
		 
		 for(int i = sPointer; i<wait.size(); i++) {
			 if(wait.get(sPointer).getNode().equals(n)) {
				 entries.add(wait.get(sPointer));
			 }
		 }
		 return entries;
	    }
	public void remove(ToDoEntry entry) {
		wait.remove(entry);
		//sPointer++;
	}
	public boolean hasEntry(Node n, OWLClassExpression c) {
		for(int i = sPointer; i< wait.size(); i++) {
			ToDoEntry en = wait.get(i);
			if(en.getNode().equals(n) && en.getClassExpression().equals(c))
				return true;
		}
		return false;
	}
	public ToDoEntry hasEntry2(Node n, OWLClassExpression c) {
		for(int i = sPointer; i< wait.size(); i++) {
			ToDoEntry en = wait.get(i);
			if(en != null)
				if(en.getNode().equals(n) && en.getClassExpression().equals(c))
					return en;
		}
		return null;
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
	    public void restoreWait(int sp, List<ToDoEntry> wait) {
	        setsPointer(sp);
	        this.wait = new ArrayList<>(wait);
	      // Helper.resize(wait, ep, null);
	    }
}
