package reasoner;

import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.reasoner.ConsoleProgressMonitor;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerConfiguration;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;
import org.semanticweb.owlapi.reasoner.structural.StructuralReasonerFactory;

public class ReasonerFactory implements OWLReasonerFactory{
	
	public ReasonerFactory() {
		new StructuralReasonerFactory();
	}

	@Override
	public OWLReasoner createNonBufferingReasoner(OWLOntology arg0) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public OWLReasoner createNonBufferingReasoner(OWLOntology arg0, OWLReasonerConfiguration arg1) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Reasoner createReasoner(OWLOntology ont) {
		try {
			ConsoleProgressMonitor progressMonitor = new ConsoleProgressMonitor();
		    Configuration config = new Configuration(progressMonitor);
		    Reasoner reasoner = new Reasoner( ont, config );
			
			return reasoner;
		} catch( Exception e ) {
			throw new RuntimeException( e );
		}  
	}

	@Override
	public OWLReasoner createReasoner(OWLOntology ont, OWLReasonerConfiguration config) {
		return null;
	}

	@Override
	public String getReasonerName() {
		// TODO Auto-generated method stub
		return null;
	}

}
