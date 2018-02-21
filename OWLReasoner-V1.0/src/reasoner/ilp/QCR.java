package reasoner.ilp;

import org.semanticweb.owlapi.model.*;

public class QCR {
	int cardinality;
	OWLClassExpression qualifier;
	String type;
	OWLObjectPropertyExpression role;
	
	QCR(OWLObjectCardinalityRestriction qcr){
		this.role = qcr.getProperty();
		this.cardinality = qcr.getCardinality();
		this.qualifier = qcr.getFiller();
		if (qcr instanceof OWLObjectMinCardinality){
			this.type = "MIN";
		} else if(qcr instanceof OWLObjectMaxCardinality){
			this.type = "MAX";
		} else 
			this.type = "EXACT";
	}
	
}
