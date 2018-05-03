package reasoner.graph;

import java.util.*;

import org.semanticweb.owlapi.model.*;

import reasoner.Dependencies.DependencySet;

public class Edge {
	
	 private Node node1;

	    private Node node2;
	    private DependencySet depSet;
	    /** true if the edge going from a predecessor to a successor */
	    private boolean succEdge = true;
	    private Set<OWLObjectPropertyExpression> edgeLabel = new HashSet<OWLObjectPropertyExpression>();;

	    public Edge(Node node1, Node node2, OWLObjectPropertyExpression edgeLabel, DependencySet ds) {
	        this.node1 = node1;
	        this.node2 = node2;
	        this.edgeLabel.add(edgeLabel);
	        this.depSet = ds;
	    }

	    public Edge(Node from, Node to, Set<OWLObjectPropertyExpression> edgeLabel2, DependencySet ds) {
	    		this.node1 = from;
	        this.node2 = to;
	        this.edgeLabel.addAll(edgeLabel2);
	        this.depSet = ds;
		}

		public void addLabel(OWLObjectPropertyExpression edgeLabel) {
	    		this.edgeLabel.add(edgeLabel);
	    }
	    public Node getFromNode() {
	        return node1;
	    }

	    public Node getToNode() {
	        return node2;
	    }
 
	    public boolean isBetween(Node node1, Node node2) {
	        return (this.node1 == node1 && this.node2 == node2);
	    }
	    
	    public Set<OWLObjectPropertyExpression> getLabel() {
	    	return this.edgeLabel;
	    }

		public DependencySet getDepSet() {
			return depSet;
		}

		public void setDepSet(DependencySet depSet) {
			this.depSet = depSet;
		}
		public void updateDepSet(DependencySet depSet) {
			this.depSet.add(depSet);
		}
		public boolean isIBlocked() {
			if(this.edgeLabel.isEmpty())
				return true;
			return false;
		}
		
		
	    public void setSuccEdge(boolean val) {
	        succEdge = val;
	    }

	    /** @return true if the edge is the successor one */
	    public boolean isSuccEdge() {
	        return succEdge;
	    }
	    /** @return true if the edge is the predecessor one */
	    public boolean isPredEdge() {
	        return !succEdge;
	    }

		public void addLabel(Set<OWLObjectPropertyExpression> label) {
			this.edgeLabel.addAll(label);
			
		}
}
