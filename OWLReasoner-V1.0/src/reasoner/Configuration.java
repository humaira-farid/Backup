package reasoner;

import org.semanticweb.owlapi.reasoner.ConsoleProgressMonitor;
import org.semanticweb.owlapi.reasoner.FreshEntityPolicy;
import org.semanticweb.owlapi.reasoner.IndividualNodeSetPolicy;
import org.semanticweb.owlapi.reasoner.OWLReasonerConfiguration;
import org.semanticweb.owlapi.reasoner.ReasonerProgressMonitor;
import org.semanticweb.owlapi.reasoner.SimpleConfiguration;

public class Configuration implements OWLReasonerConfiguration{
	
	 public PrepareReasonerInferences prepareReasonerInferences;
	 
	 private boolean useAnywhereBlocking = true;
	 private boolean useEqualityBlocking = false;
	 private boolean usePairwiseBlocking = false;
	 private boolean useSubsetBlocking = false;
	 
	public Configuration(ConsoleProgressMonitor progressMonitor) {
		new SimpleConfiguration(progressMonitor);
	}

	@Override
	public FreshEntityPolicy getFreshEntityPolicy() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IndividualNodeSetPolicy getIndividualNodeSetPolicy() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ReasonerProgressMonitor getProgressMonitor() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public long getTimeOut() {
		// TODO Auto-generated method stub
		return 0;
	}
	public static class PrepareReasonerInferences {
	    public boolean classClassificationRequired=true;
	    public boolean objectPropertyClassificationRequired=true;
	    public boolean dataPropertyClassificationRequired=true;
	    public boolean objectPropertyDomainsRequired=true;
	    public boolean objectPropertyRangesRequired=true;
	    public boolean realisationRequired=true;
	    public boolean objectPropertyRealisationRequired=true;
	    public boolean dataPropertyRealisationRequired=true;
	    public boolean sameAs=true;
	}

}
