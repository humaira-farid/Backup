package reasoner;

import org.semanticweb.owlapi.model.OWLClassExpression;

public class Disjunct {
	private OWLClassExpression lhs;
	private OWLClassExpression rhs;
	
	public Disjunct(OWLClassExpression l, OWLClassExpression r) {
		this.lhs = l;
		this.rhs = r;
	}
	public OWLClassExpression getLHS() {
		return this.lhs;
	}
	public OWLClassExpression getRHS() {
		return this.rhs;
	}
}
