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
		cdSet = new ArrayList();
	}

	public List<ConceptNDepSet> getCdSet() {
		return cdSet;
	}
	
	protected void add(ConceptNDepSet cnd) {
		cdSet.add(cnd);
		size++;
		concepts.put(cnd.getCe(), size-1);
	}
	
	public int save() {
        return size;
    }
	 public void restore(int ss, int level) {
	        // count the number of entries /not/ deleted
	        int count = 0;
	        for (int i = ss; i < size; i++) {
	            // if backjumping is enabled, an entity is deleted only if the
	            // depset level is the same or above level, otherwise the entry is
	            // kept
	         //   if (!options.isUseDynamicBackjumping() || base.get(i).getDep().level() >= level) {
	        	OWLClassExpression concept = cdSet.get(i).getCe();
	                concepts.remove(concept);
	          //      cache.remove(asPositive(concept));
	          //  } else {
	          //      count++;
	          //  }
	        }
	        Helper.resize(cdSet, ss + count, null);
	        size = ss + count;
	    }
	
}
