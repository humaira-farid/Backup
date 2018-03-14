package reasoner.ilp;

import org.semanticweb.owlapi.model.OWLClassExpression;

public class Nominal {
	int cardinality;
	OWLClassExpression qualifier;
	
	public Nominal(OWLClassExpression n) {
		this.cardinality = 1;
		this.qualifier = n;
	}
}
