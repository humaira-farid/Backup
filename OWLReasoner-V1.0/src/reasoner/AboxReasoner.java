package reasoner;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;

public class AboxReasoner {

	Set<OWLSubClassOfAxiom> aboxClassAss;
	Map<Integer, Set<OWLSubClassOfAxiom>> bpNAboxAss = new HashMap<>();
	Set<OWLSubClassOfAxiom> processedAboxAss;
	
	public AboxReasoner(Set<OWLSubClassOfAxiom> aboxClassAss){
		this.processedAboxAss = new HashSet<>();
		this.aboxClassAss = aboxClassAss;
	}
	public void addProcessed(OWLSubClassOfAxiom abAx) {
		this.processedAboxAss.add(abAx);
	}
	public void removeProcessed(Set<OWLSubClassOfAxiom> abAx) {
		this.processedAboxAss.removeAll(abAx);
	}
	public void save(int level) {
		bpNAboxAss.put(level,  new HashSet<>(this.processedAboxAss));
	}
	public boolean needRestore(int level) {
		if(level==0)
			return false;
		return bpNAboxAss.get(level).size() < aboxClassAss.size();
	}
	public Set<OWLSubClassOfAxiom> restore(int level) {
		Set<OWLSubClassOfAxiom> returnSet = new HashSet<>(aboxClassAss);
		returnSet.removeAll(bpNAboxAss.get(level));
		return returnSet;
	}
}
