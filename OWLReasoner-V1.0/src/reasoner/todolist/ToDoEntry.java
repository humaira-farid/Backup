package reasoner.todolist;

import org.semanticweb.owlapi.model.*;

import reasoner.graph.*;
import reasoner.Dependencies.DependencySet;
import reasoner.graph.Node;

public class ToDoEntry implements Comparable<ToDoEntry>{
	
	private Node node;
	private final OWLClassExpression ce;
	private final NodeTag type;
	private DependencySet ds;
	ConceptNDepSet cnds;
	
	public ToDoEntry(Node node, ConceptNDepSet cnds, NodeTag type) {
		this.node = node;
		this.ce = cnds.getCe();
		this.type = type;
		this.setDs(cnds.getDs());
		this.cnds = cnds;
	}

	public Node getNode() {
		return node;
	}

	public ConceptNDepSet getCnds() {
		return cnds;
	}

	public void setCnds(ConceptNDepSet cnds) {
		this.cnds = cnds;
	}

	public OWLClassExpression getClassExpression() {
		return ce;
	}

	public NodeTag getType() {
		return type;
	}
	public String getTypeValue() {
		if(this.getType().equals(NodeTag.AND))
			return "Aab";
		else if(this.getType().equals(NodeTag.OR))
			return "Bbc";
		else
			return "Ccd";
	}
	public DependencySet getDs() {
		return ds;
	}

	public void setDs(DependencySet ds) {
		this.ds = ds;
	}

	public void setNode(Node to) {
		this.node = to;
		
	}

///*
	@Override
	public int compareTo(ToDoEntry e1) {
		int value1 = this.node.getId()-e1.getNode().getId();
		if(value1 == 0) {
			int value2 = this.getTypeValue().compareTo(e1.getTypeValue());
			if(value2 == 0) {
				return value1;
			}
			else 
				return value2;
		}
		return value1;
		//return this.node.getId()-e1.getNode().getId();
	}
	//*/
}
