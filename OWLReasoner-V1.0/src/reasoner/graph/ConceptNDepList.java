package reasoner.graph;

import java.util.*;

import org.semanticweb.owlapi.model.OWLClassExpression;

import reasoner.Helper;

import static reasoner.Helper.*;

public class ConceptNDepList {
	/** List of concepts along with dependency sets */
	private final List<ConceptNDepSet> cdSet;
	private int size = 0;
	Map<OWLClassExpression, Integer> concepts = new HashMap<>();
	public ConceptNDepList() {
		cdSet = new ArrayList<>();
	}

	public List<ConceptNDepSet> getCdSet() {
		return cdSet;
	}
	
	protected void add(ConceptNDepSet cnd) {
		cdSet.add(cnd);
		size++;
		concepts.put(cnd.getCe(), size-1);
	}
	protected Set<OWLClassExpression> getConcepts(){
		return concepts.keySet();
	}
	public int save() {
        return size;
    }
	 public void removeLabel() {
		 cdSet.clear();
		 size = 0;
	 }
	 public void restore(int ss, int level) {
	        // count the number of entries /not/ deleted
	        int count = 0;
	     //   List<ConceptNDepSet> remove = new ArrayList<ConceptNDepSet>();
	        System.out.println("restore label level "+ level + "ss "+ss+" size: "+ size);
	        for (int i = ss; i < size; i++) {
	            // if backjumping is enabled, an entity is deleted only if the
	            // depset level is the same or above level, otherwise the entry is
	            // kept
	     //   	System.out.println("level "+ level +" bp "+ cdSet.get(i).getDs().getMax());
	        	if (cdSet.get(i) != null) {
	        		if (cdSet.get(i).getDs().getMax() >= level) {
	        			OWLClassExpression concept = cdSet.get(i).getCe();
	      //  	remove.add(cdSet.get(i));
	        			System.out.println("remove concept "+ concept);
	                concepts.remove(concept);
	          //      cache.remove(asPositive(concept));
	            } else {
	                count++;
	            }
	        	}
	        }
	      //  System.out.println("size before "+cdSet.size());
	       // cdSet.removeAll(remove);
	      //  System.out.println("size after "+cdSet.size());
	        Helper.resize(cdSet, ss + count, null);
	      //  System.out.println("size after "+cdSet.size());
	        size = ss + count;
	        
	    }

	public void init() {
		size = 0;
		concepts.clear();
		cdSet.clear();
	}
	
}
