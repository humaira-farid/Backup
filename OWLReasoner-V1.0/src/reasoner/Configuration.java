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
	 private boolean isALC = false;
	 private boolean isSHO = false;
	 private boolean isSHI = false;
	 private boolean isSHQ = false;
	 private boolean isSHOI = false;
	 private boolean isSHOQ = false;
	 private boolean isSHIQ = false;
	 private boolean isSHOIQ = false;
	 private boolean hasRoleHierarchy = false;
	 
	public Configuration(ConsoleProgressMonitor progressMonitor) {
		new SimpleConfiguration(progressMonitor);
	}
	 
	 
	 public boolean hasRoleHierarchy() {
		return hasRoleHierarchy;
	}


	public void setHasRoleHierarchy(boolean hasRoleHierarchy) {
		this.hasRoleHierarchy = hasRoleHierarchy;
	}


	public boolean isALC() {
		return isALC;
	}


	public void setALC(boolean isALC) {
		this.isALC = isALC;
	}


	public boolean isSHO() {
		return isSHO;
	}


	public void setSHO(boolean isSHO) {
		this.isSHO = isSHO;
	}


	public boolean isSHI() {
		return isSHI;
	}


	public void setSHI(boolean isSHI) {
		this.isSHI = isSHI;
	}
	public boolean isSHQ() {
		return isSHQ;
	}


	public void setSHQ(boolean isSHQ) {
		this.isSHQ = isSHQ;
	}

	public boolean isSHOI() {
		return isSHOI;
	}


	public void setSHOI(boolean isSHOI) {
		this.isSHOI = isSHOI;
	}


	public boolean isSHOQ() {
		return isSHOQ;
	}


	public void setSHOQ(boolean isSHOQ) {
		this.isSHOQ = isSHOQ;
	}


	public boolean isSHIQ() {
		return isSHIQ;
	}


	public void setSHIQ(boolean isSHIQ) {
		this.isSHIQ = isSHIQ;
	}


	public boolean isSHOIQ() {
		return isSHOIQ;
	}


	public void setSHOIQ(boolean isSHOIQ) {
		this.isSHOIQ = isSHOIQ;
	}
	
	

	public boolean isUseAnywhereBlocking() {
		return useAnywhereBlocking;
	}

	public void setUseAnywhereBlocking(boolean useAnywhereBlocking) {
		this.useAnywhereBlocking = useAnywhereBlocking;
	}

	public boolean isUseEqualityBlocking() {
		return useEqualityBlocking;
	}

	public void setUseEqualityBlocking(boolean useEqualityBlocking) {
		this.useEqualityBlocking = useEqualityBlocking;
	}

	public boolean isUsePairwiseBlocking() {
		return usePairwiseBlocking;
	}

	public void setUsePairwiseBlocking(boolean usePairwiseBlocking) {
		this.usePairwiseBlocking = usePairwiseBlocking;
	}

	public boolean isUseSubsetBlocking() {
		return useSubsetBlocking;
	}

	public void setUseSubsetBlocking(boolean useSubsetBlocking) {
		this.useSubsetBlocking = useSubsetBlocking;
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
