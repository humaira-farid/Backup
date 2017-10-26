package reasoner.todolist;

import org.semanticweb.owlapi.model.*;

import reasoner.graph.*;
import reasoner.Dependencies.DependencySet;
import reasoner.graph.Node;

public class ToDoEntry {
	
	private final Node node;
	private final OWLClassExpression ce;
	private final NodeTag type;
	private DependencySet ds;
	
	public ToDoEntry(Node node, ConceptNDepSet cnds, NodeTag type) {
		this.node = node;
		this.ce = cnds.getCe();
		this.type = type;
		this.setDs(cnds.getDs());
		
	}

	public Node getNode() {
		return node;
	}

	public OWLClassExpression getClassExpression() {
		return ce;
	}

	public NodeTag getType() {
		return type;
	}

	public DependencySet getDs() {
		return ds;
	}

	public void setDs(DependencySet ds) {
		this.ds = ds;
	}
}
