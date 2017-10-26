package reasoner.graph;

import org.semanticweb.owlapi.model.OWLClassExpression;

import reasoner.Dependencies.DependencySet;

public class ConceptNDepSet {

	private OWLClassExpression ce;
	private DependencySet ds;
	
	public ConceptNDepSet(OWLClassExpression ce, DependencySet ds) {
		this.setCe(ce);
		this.setDs(ds);
	}

	public OWLClassExpression getCe() {
		return ce;
	}

	public void setCe(OWLClassExpression ce) {
		this.ce = ce;
	}

	public DependencySet getDs() {
		return ds;
	}

	public void setDs(DependencySet ds) {
		this.ds = ds;
	}
	
}
