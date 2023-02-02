package reasoner.graph;

import java.util.*;

import org.semanticweb.owlapi.model.OWLClassExpression;

import reasoner.Helper;

import static reasoner.Helper.*;

public class ConceptNDepList {
	/** List of concepts along with dependency sets */
	private List<ConceptNDepSet> cdSet;
	private int size = 0;
	Map<OWLClassExpression, Integer> concepts = new HashMap<>();

	public int getSize() {
		return size;
	}
	public void setSize(int size) {
		this.size = size;
	}
	public void setCdSet(List<ConceptNDepSet> cdSet) {
		this.cdSet = cdSet;
	}
	public void setConcepts(Map<OWLClassExpression, Integer> concepts) {
		this.concepts = concepts;
	}
	public ConceptNDepList() {
		cdSet = new ArrayList<>();
	}
	public ConceptNDepList(ConceptNDepList cndList) {
		this.setConcepts(cndList.concepts);
		this.setSize(cndList.getSize());
		this.setCdSet(cndList.getCdSetCopy());
	}
	public void init() {
		size = 0;
		concepts.clear();
		cdSet.clear();
	}

	public List<ConceptNDepSet> getCdSet() {
		return cdSet;
	}
	public List<ConceptNDepSet> getCdSetCopy() {
		 List<ConceptNDepSet> copyList = new ArrayList<>();
		 for(ConceptNDepSet cds : this.getCdSet()) {
			 copyList.add(new ConceptNDepSet(cds.getCe(), cds.getDs()));
		 }
		 return copyList;
	}

	protected void add(ConceptNDepSet cnd) {

	//	System.err.println(" size"+ size);
		cdSet.add(cnd);
		size++;
		concepts.put(cnd.getCe(), size - 1);
	//	System.err.println(" size after"+ size);
		
	}

	protected Set<OWLClassExpression> getConcepts() {
		return concepts.keySet();
	}

	public int save() {
		return size;
	}
	
	public void restore(int ss, int level, boolean ilp, boolean merge, boolean disjunction) {
	//	System.out.println("ss "+ss+" size " + size);
		for (int i = size - 1; i >= ss && i >= 0; i--) {
			assert cdSet.get(i) != null;
		//	System.out.println("restore level "+level+" concept " + cdSet.get(i).getCe() +" ds "+cdSet.get(i).getDs().getbpList());
			if(merge) {
				if (cdSet.get(i).getDs().getMax() >= level) {
					OWLClassExpression concept = cdSet.get(i).getCe();
				//	System.out.println("remove concept " + concept);
					concepts.remove(concept);
					cdSet.remove(i);
					size--;
				}
			}
			else {
				if (cdSet.get(i).getDs().getMax() >= level) {
					OWLClassExpression concept = cdSet.get(i).getCe();
					//System.out.println("remove concept " + concept);
					concepts.remove(concept);
					cdSet.remove(i);
					size--;
				}
			}
		}
	}
	/*public void restore(int ss, int level, boolean ilp, boolean merge, boolean disjunction) {
		System.out.println("ss "+ss+" size " + size);
		for (int i = size - 1; i >= ss && i >= 0; i--) {
			assert cdSet.get(i) != null;
			System.out.println("restore level "+level+" concept " + cdSet.get(i).getCe() +" ds "+cdSet.get(i).getDs().getbpList());
			if (cdSet.get(i).getDs().getMax() >= level) {
				OWLClassExpression concept = cdSet.get(i).getCe();
				System.out.println("remove concept " + concept);
				concepts.remove(concept);
				cdSet.remove(i);
				size--;
			}
		}
	}*/
	

	public void removeLabel() {
		cdSet.clear();
		size = 0;
		concepts.clear();
	}
	/*
	public void restore(int ss, int level) {
		// count the number of entries /not/ deleted
		int count = 0;
		for (int i = ss; i < size; i++) {
			System.out.println("level " + level + " bp " + cdSet.get(i).getDs().getMax());
			if (cdSet.get(i) != null) {
				if (cdSet.get(i).getDs().getMax() >= level) {
					OWLClassExpression concept = cdSet.get(i).getCe();
					// remove.add(cdSet.get(i));
					System.out.println("remove concept " + concept);
					concepts.remove(concept);
					// cache.remove(asPositive(concept));
				} else {
					count++;
				}
			}

		}
		Helper.resize(cdSet, ss + count, null);
		size = ss + count;
	}
	
	public void restore(int ss, int level) {
		// count the number of entries /not/ deleted
		int count = 0;
		// List<ConceptNDepSet> remove = new ArrayList<ConceptNDepSet>();
		// System.out.println("restore label level "+ level + "ss "+ss+" size: "+ size);
		for (int i = ss; i < size; i++) {
			// if backjumping is enabled, an entity is deleted only if the
			// depset level is the same or above level, otherwise the entry is
			// kept
			// System.out.println("level "+ level +" bp "+ cdSet.get(i).getDs().getMax());
			if (cdSet.get(i) != null) {
				if (cdSet.get(i).getDs().getMax() >= level) {
					OWLClassExpression concept = cdSet.get(i).getCe();
					// remove.add(cdSet.get(i));
					System.out.println("remove concept " + concept);
					concepts.remove(concept);
					// cache.remove(asPositive(concept));
				} else {
					count++;
				}
			}
		}
		// System.out.println("size before "+cdSet.size());
		// cdSet.removeAll(remove);
		// System.out.println("size after "+cdSet.size());
		Helper.resize(cdSet, ss + count, null);
		// System.out.println("size after "+cdSet.size());
		size = ss + count;
	}
    */
}	

