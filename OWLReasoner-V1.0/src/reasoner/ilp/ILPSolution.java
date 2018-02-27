package reasoner.ilp;

import java.util.HashSet;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLObjectCardinalityRestriction;

public class ILPSolution {
	boolean solved = false;
	Set<EdgeInformation> edgeInformation = null;
	Set<OWLObjectCardinalityRestriction> infeasible_set = null;
	boolean isUnique =true;
	
	public ILPSolution(){
		this.edgeInformation = new HashSet<EdgeInformation>();
		this.infeasible_set = new HashSet<>();
	}
	
	public ILPSolution(boolean solved , Set<EdgeInformation> edgeInformation, 
					Set<OWLObjectCardinalityRestriction> infeasible_set){
		this.solved = solved;
		this.edgeInformation = edgeInformation;
		this.infeasible_set = infeasible_set;
	}
	
	public boolean isSolved() {
		return solved;
	}
	
	public void setSolved(boolean solved) {
		this.solved = solved;
	}
	
	public Set<EdgeInformation> getEdgeInformation() {
		return edgeInformation;
	}
	
	public void setEdgeInformation(Set<EdgeInformation> edgeInformation) {
		this.edgeInformation = edgeInformation;
	}

	public Set<OWLObjectCardinalityRestriction> getInfeasible_set() {
		return infeasible_set;
	}

	public void setInfeasible_set(
			Set<OWLObjectCardinalityRestriction> infeasible_set) {
		this.infeasible_set = infeasible_set;
	}

	public boolean isUnique() {
		return isUnique;
	}

	public void setUnique(boolean isUnique) {
		this.isUnique = isUnique;
	}

	
}

