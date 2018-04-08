package reasoner.ilp;

import org.semanticweb.owlapi.model.*;

import reasoner.Dependencies.DependencySet;

public class QCR {
	int cardinality;
	OWLClassExpression qualifier;
	String type;
	OWLObjectPropertyExpression role;
	DependencySet ds;
	
	QCR(OWLObjectCardinalityRestriction qcr, DependencySet ds){
		this.role = qcr.getProperty();
		this.cardinality = qcr.getCardinality();
		this.qualifier = qcr.getFiller();
		this.ds = ds;
		if (qcr instanceof OWLObjectMinCardinality){
			this.type = "MIN";
		} else if(qcr instanceof OWLObjectMaxCardinality){
			this.type = "MAX";
		} else 
			this.type = "EXACT";
	}
	QCR(OWLObjectOneOf o, DependencySet ds){
		this.role = null;
		this.cardinality = 1;
		this.qualifier = o;
		this.type = "EXACT";
		this.ds = ds;
	}
	
}
