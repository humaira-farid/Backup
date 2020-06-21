package reasoner; 

import static reasoner.Helper.INITBRANCHINGLEVELVALUE;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectCardinalityRestriction;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectHasValue;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectOneOf;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.util.DefaultPrefixManager;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import com.google.common.collect.SetMultimap;

import ilog.concert.IloException;
import reasoner.Dependencies.DependencySet;
import reasoner.graph.CompletionGraph;
import reasoner.graph.ConceptNDepSet;
import reasoner.graph.Edge;
import reasoner.graph.Node;
import reasoner.graph.Node.NodeType;
import reasoner.graph.NodeTag;
import reasoner.ilp.EdgeInformation;
import reasoner.ilp.ILPPreprocessor;
import reasoner.ilp.ILPSolution;
import reasoner.preprocessing.Internalization;
import reasoner.todolist.ToDoEntry;
import reasoner.todolist.ToDoList;

public class RuleEngine3 {
	Internalization intl;
	Ontology ontology;
	CompletionGraph cg;
	ToDoList todo;
	private int currentBranchingPoint;
	OWLDataFactory df;
	boolean forAllCheck = false;
	boolean isExistential = false;
	boolean aboxReasoning = false;
	Map<Integer, BranchHandler> branches = new HashMap<Integer, BranchHandler>();
	Map<Integer, CompletionGraph> copies = new HashMap<Integer, CompletionGraph>();
	Map<Integer, Multimap<Integer,OWLClassExpression>> branches2 = new HashMap<Integer, Multimap<Integer,OWLClassExpression>>();
	SetMultimap<Node, ToDoEntry> nodeEntries = HashMultimap.create();
	List<ToDoEntry> entries = new ArrayList<>();
	SetMultimap<Node, ToDoEntry> nodeExistEntries = HashMultimap.create(); 
	SetMultimap<Node, ToDoEntry> nodeMinEntries = HashMultimap.create(); 
	SetMultimap<Node, ToDoEntry> nodeMaxEntries = HashMultimap.create(); 
	SetMultimap<Node, OWLObjectPropertyExpression> axiomRoles = HashMultimap.create();
	SetMultimap<Node, ToDoEntry> nodeForAllEntries = HashMultimap.create();
	SetMultimap<Node, ToDoEntry> relatedForAllEntries = HashMultimap.create();
	SetMultimap<Node, ToDoEntry> relatedMaxEntries = HashMultimap.create();
	SetMultimap<Node, ToDoEntry> unrelatedMaxEntries = HashMultimap.create();
	Set<Edge> outgoingEdges = new HashSet<>();
	Node currNode = null;
	AboxReasoner ar;
	Configuration config;
	OWLClassExpression tgAxiom;
	int currRestore = 0;
	Set<OWLObjectPropertyExpression> transitiveRoles = new HashSet<>();
	Set<OWLSubClassOfAxiom> niSubAx = new HashSet<>();
	DefaultPrefixManager prefixManager;
	String base = null;
	int counter = 0;
	int niCounter = 1;
	public RuleEngine3(Internalization i, ToDoList todo, OWLDataFactory df, Configuration config) {
		this.intl= i;
		this.todo = todo;
		this.df = df;
		this.cg = null;//new CompletionGraph(this, config, df);
		this.config = config;
		currentBranchingPoint = INITBRANCHINGLEVELVALUE;
		this.ontology = this.intl.getOntology();
		this.prefixManager = intl.getPrefixManager();
		this.base = this.prefixManager.getDefaultPrefix();
		 todo.initPriorities("0123333");
	}
	public void setTransitiveRoles(Set<OWLObjectPropertyExpression> trans) {
		this.transitiveRoles = trans;
		
	}
	/**
	 * checking ontology consistency
	 * @param tgAxiom 
	 */
	public void checkConsistency(OWLClassExpression tgAxiom) {
		this.tgAxiom = tgAxiom;
		createFirstNode(tgAxiom);
		if(config.isALC() || config.isSHI()) {
			while(!todo.isEmpty()) {
				
			 	ToDoEntry entry = todo.getNextEntry();
			 	//System.out.println("node id "+ entry.getNode().getId());
				
			 	//System.out.println("while loop "+ entry.getClassExpression());
				if(entry!=null && !entry.getNode().isReset()) {
		 			this.applyRules(entry);
				}
			}
		}
		else {
			processToDoList();
		}
			
	/*	while(!todo.isEmpty()) {
			
		 	ToDoEntry entry = todo.getNextEntry();
		 	System.out.println("node id "+ entry.getNode().getId());
			
		 	System.out.println("while loop "+ entry.getClassExpression());
			if(entry!=null) {
	 			this.applyRules(entry);
			}
		}*/

		
		
		
		//System.out.println("No. of nodes : "+ cg.getTotalNodes());
	}
	public void createFirstNode(OWLClassExpression tgAxiom) {
		
		Node from = cg.addNode(NodeType.NOMINAL, tgAxiom, DependencySet.create());
		this.absorbRule1(df.getOWLThing(), from, DependencySet.create());
		ConceptNDepSet cnds = new ConceptNDepSet(tgAxiom, DependencySet.create());
		cg.addConceptToNode(from, cnds);
		addToDoEntry(from, tgAxiom, cnds);
		//todo.addEntry(from, NodeTag.AND, cnds);
	}
	private void processToDoList() {
		while(!todo.isEmpty()) {
		 	//System.out.println("while loop "+ todo.entries());
		 	ToDoEntry entry = todo.getNextEntry();
		 //	System.out.println("processToDoList ");
		 	if(entry!=null && !entry.getNode().isReset()) {
		 		Node n = entry.getNode();
		 		if(currNode!=null)
		 		System.out.println("n "+ n.getId() +" entry "+ entry.getClassExpression() +" curr node "+ currNode.getId());
		 		
		 		//if(currNode!=null)
		 		if(currNode!=null && currNode.equals(n)) {
		 			processEntry(entry);
		 		}
		 		else {
		 			if(!nodeExistEntries.get(currNode).isEmpty() || !nodeMinEntries.get(currNode).isEmpty()) {
		 				if(isNIRuleApplicable(currNode)) {
		 					System.err.println("ni applicable 1");
	 						addExistentialRestrictions(currNode);
	 					} 
		 				addRangeRestrictions(this.axiomRoles.get(currNode));
		 				checkRelatedForAll(currNode, nodeForAllEntries.get(currNode), this.axiomRoles.get(currNode));
		 				///
		 				checkRelatedMax(currNode, nodeMaxEntries.get(currNode), this.axiomRoles.get(currNode));
		 				//
		 				/*if(!nodeMaxEntries.get(currNode).isEmpty()) {	
		 					checkOutgoingEdges(currNode, nodeMaxEntries.get(currNode));
		 				}*/
		 				if(!relatedMaxEntries.get(currNode).isEmpty()) {	
		 					checkOutgoingEdges(currNode, relatedMaxEntries.get(currNode));
		 				}
		 				if(needILPModule(currNode)) {
		 					
		 						//List<ToDoEntry> entries = new ArrayList<>();
		 						Set<ToDoEntry> entries = new HashSet<>();
		 						if(!nodeExistEntries.get(currNode).isEmpty())
		 							entries.addAll(nodeExistEntries.get(currNode));
		 						if(!nodeMinEntries.get(currNode).isEmpty())
		 							entries.addAll(nodeMinEntries.get(currNode));
		 						/*if(!nodeMaxEntries.get(currNode).isEmpty())
		 							entries.addAll(nodeMaxEntries.get(currNode));*/
		 						if(!relatedMaxEntries.get(currNode).isEmpty())
		 							entries.addAll(relatedMaxEntries.get(currNode));
		 						if(!relatedForAllEntries.get(currNode).isEmpty())
		 							entries.addAll(relatedForAllEntries.get(currNode));
		 						nodeExistEntries.get(currNode).clear();
		 						nodeMinEntries.get(currNode).clear();
		 						nodeMaxEntries.get(currNode).clear();
		 						nodeForAllEntries.get(currNode).clear();
		 						relatedForAllEntries.get(currNode).clear();
		 						relatedMaxEntries.get(currNode).clear();
		 						callILP(currNode, entries, new HashSet<OWLSubClassOfAxiom>(this.niSubAx), outgoingEdges);
		 						for(ToDoEntry en : unrelatedMaxEntries.get(currNode))
									applyRules(en);
		 						unrelatedMaxEntries.get(currNode).clear();
		 						axiomRoles.get(currNode).clear();
		 						this.niSubAx.clear();
		 				}
		 				else {
		 						if(!nodeExistEntries.get(currNode).isEmpty()) {
			 						for(ToDoEntry en : nodeExistEntries.get(currNode))
			 							applyRules(en);
		 						}
		 						if(!nodeForAllEntries.get(currNode).isEmpty()) {
			 						for(ToDoEntry en : nodeForAllEntries.get(currNode))
			 							applyRules(en);
		 						}
		 						nodeExistEntries.get(currNode).clear();
		 						nodeForAllEntries.get(currNode).clear();
		 						axiomRoles.get(currNode).clear();
		 				}
		 				
		 			}
		 			else if(!nodeMaxEntries.get(currNode).isEmpty() || !nodeForAllEntries.get(currNode).isEmpty()) {
		 				if(isNIRuleApplicable(currNode)) {
		 					System.err.println("ni applicable 2");
	 						addExistentialRestrictions(currNode);
	 						addRangeRestrictions(this.axiomRoles.get(currNode));
	 						checkRelatedForAll(currNode, nodeForAllEntries.get(currNode), this.axiomRoles.get(currNode));
	 						checkRelatedMax(currNode, nodeMaxEntries.get(currNode), this.axiomRoles.get(currNode));
		 				
			 				if(!relatedMaxEntries.get(currNode).isEmpty()) {	
			 					checkOutgoingEdges(currNode, relatedMaxEntries.get(currNode));
			 				}
			 				Set<ToDoEntry> entries = new HashSet<>();
	 						if(!nodeExistEntries.get(currNode).isEmpty())
	 							entries.addAll(nodeExistEntries.get(currNode));
	 						if(!relatedMaxEntries.get(currNode).isEmpty())
	 							entries.addAll(relatedMaxEntries.get(currNode));
	 						if(!relatedForAllEntries.get(currNode).isEmpty())
	 							entries.addAll(relatedForAllEntries.get(currNode));
	 						nodeExistEntries.get(currNode).clear();
	 						nodeMaxEntries.get(currNode).clear();
	 						nodeForAllEntries.get(currNode).clear();
	 						relatedForAllEntries.get(currNode).clear();
	 						relatedMaxEntries.get(currNode).clear();
	 						callILP(currNode, entries, new HashSet<OWLSubClassOfAxiom>(this.niSubAx), outgoingEdges);
	 						for(ToDoEntry en : unrelatedMaxEntries.get(currNode))
								applyRules(en);
	 						unrelatedMaxEntries.get(currNode).clear();
	 						axiomRoles.get(currNode).clear();
	 						this.niSubAx.clear();
		 				}
		 				else {
		 					checkRelatedForAll(currNode, nodeForAllEntries.get(currNode), this.axiomRoles.get(currNode));
	 						checkRelatedMax(currNode, nodeMaxEntries.get(currNode), this.axiomRoles.get(currNode));
		 				
			 				if(!relatedMaxEntries.get(currNode).isEmpty()) {	
			 					checkOutgoingEdges(currNode, relatedMaxEntries.get(currNode));
			 				}
			 				if(!nodeExistEntries.get(currNode).isEmpty() || !this.outgoingEdges.isEmpty()) {
				 				Set<ToDoEntry> entries = new HashSet<>();
		 						if(!nodeExistEntries.get(currNode).isEmpty())
		 							entries.addAll(nodeExistEntries.get(currNode));
		 						if(!relatedMaxEntries.get(currNode).isEmpty())
		 							entries.addAll(relatedMaxEntries.get(currNode));
		 						if(!relatedForAllEntries.get(currNode).isEmpty())
		 							entries.addAll(relatedForAllEntries.get(currNode));
		 						nodeExistEntries.get(currNode).clear();
		 						nodeMaxEntries.get(currNode).clear();
		 						nodeForAllEntries.get(currNode).clear();
		 						relatedForAllEntries.get(currNode).clear();
		 						relatedMaxEntries.get(currNode).clear();
		 						callILP(currNode, entries, new HashSet<OWLSubClassOfAxiom>(this.niSubAx), outgoingEdges);
		 						for(ToDoEntry en : unrelatedMaxEntries.get(currNode))
									applyRules(en);
		 						unrelatedMaxEntries.get(currNode).clear();
		 						axiomRoles.get(currNode).clear();
		 						this.niSubAx.clear();
			 				}
			 				else {
			 					if(!nodeForAllEntries.get(currNode).isEmpty()) {
					 				for(ToDoEntry en : nodeForAllEntries.get(currNode))
					 					applyRules(en);
				 				}
				 				if(!nodeMaxEntries.get(currNode).isEmpty()) {
					 				for(ToDoEntry en : nodeMaxEntries.get(currNode))
					 					applyRules(en);
				 				}
				 				nodeForAllEntries.get(currNode).clear();
				 				nodeMaxEntries.get(currNode).clear();
			 				}
		 				}
		 				
		 			}
		 			currNode = entry.getNode();
		 			processEntry(entry);
		 			
		 		}
		 		
		 	}
		 	/*	if(entry!=null) {
		 		currNode = entry.getNode();
		 		entries.add(entry);
	    	 	entries.addAll(todo.getAllToDoEntry(currNode, NodeTag.AND));
	    	 	entries.addAll(todo.getAllToDoEntry(currNode, NodeTag.OR));
	    	 	entries.addAll(todo.getAllToDoEntry(currNode, NodeTag.FORALL));
	    	 	entries.addAll(todo.getAllToDoEntry(currNode, NodeTag.EXISTS));
	    	 	for(ToDoEntry en : entries) {
	    	 		processEntry(en);
	    	 	}
	    	 	if(!nodeExistEntries.get(currNode).isEmpty()) {
		 			if(needILPModule(currNode)) {
		 				List<ToDoEntry> ILPEntries = new ArrayList<>();
		 				ILPEntries.addAll(nodeExistEntries.get(currNode));
		 				ILPEntries.addAll(nodeForAllEntries.get(currNode));
		    	 			callILP(currNode, ILPEntries);
		 			}
		 			else {
		 				for(ToDoEntry en : nodeExistEntries.get(currNode))
		 					applyRules(en);
		 				for(ToDoEntry en : nodeForAllEntries.get(currNode))
		 					applyRules(en);
		 				}
		    	 	}
		 	}
		 	
		 	
		 /*	if(entry!=null) {
		 		if(entry.getType().equals(NodeTag.OR)) {
		 			System.out.println("expression with OR"+ entry.getClassExpression());
		 			applyOrRule(entry.getNode(), (OWLObjectUnionOf)entry.getClassExpression(), entry.getDs());
		 			//this.applyRules(entry);
		 		}
		 		else {
	    	 		//check if we need ILP
	    	 		if(needILPModule(entry))
	    	 			callILP(entry);
	    	 		else
	    	 			this.applyRules(entry);
		 		}
		 	}*/
		}
		if(!nodeExistEntries.get(currNode).isEmpty() || !nodeMinEntries.get(currNode).isEmpty()) {
//			System.err.println(isNIRuleApplicable(currNode));
			if(isNIRuleApplicable(currNode)) {
				System.err.println("ni applicable 3");
				addExistentialRestrictions(currNode);
			} 
			addRangeRestrictions(this.axiomRoles.get(currNode));
			checkRelatedForAll(currNode, nodeForAllEntries.get(currNode), this.axiomRoles.get(currNode));
			checkRelatedMax(currNode, nodeMaxEntries.get(currNode), this.axiomRoles.get(currNode));
			/*if(!nodeMaxEntries.get(currNode).isEmpty()) {	
				checkOutgoingEdges(currNode, nodeMaxEntries.get(currNode));
			}*/
			if(!relatedMaxEntries.get(currNode).isEmpty()) {	
				checkOutgoingEdges(currNode, relatedMaxEntries.get(currNode));
			}
			if(needILPModule(currNode)) {
			
			//	System.err.println("exist entries : "+nodeExistEntries.size());
					//List<ToDoEntry> entries = new ArrayList<>();
				Set<ToDoEntry> entries = new HashSet<>();
					if(!nodeExistEntries.get(currNode).isEmpty())
						entries.addAll(nodeExistEntries.get(currNode));
					if(!nodeMinEntries.get(currNode).isEmpty())
						entries.addAll(nodeMinEntries.get(currNode));
					/*if(!nodeMaxEntries.get(currNode).isEmpty())
						entries.addAll(nodeMaxEntries.get(currNode));*/
					if(!relatedMaxEntries.get(currNode).isEmpty())
						entries.addAll(relatedMaxEntries.get(currNode));
				//	System.err.println("max "+nodeMaxEntries.get(currNode).isEmpty());
					if(!relatedForAllEntries.get(currNode).isEmpty())
						entries.addAll(relatedForAllEntries.get(currNode));
					nodeExistEntries.get(currNode).clear();
					nodeMinEntries.get(currNode).clear();
					nodeMaxEntries.get(currNode).clear();
					nodeForAllEntries.get(currNode).clear();
					relatedForAllEntries.get(currNode).clear();
					relatedMaxEntries.get(currNode).clear();
					callILP(currNode, entries, new HashSet<OWLSubClassOfAxiom>(this.niSubAx), outgoingEdges);
					for(ToDoEntry en : unrelatedMaxEntries.get(currNode))
						applyRules(en);
					unrelatedMaxEntries.get(currNode).clear();
					axiomRoles.get(currNode).clear();
					this.niSubAx.clear();
			}
			else {
					
					if(!nodeExistEntries.get(currNode).isEmpty()) {
 						for(ToDoEntry en : nodeExistEntries.get(currNode))
 							applyRules(en);
						}
					if(!nodeForAllEntries.get(currNode).isEmpty()) {
 						for(ToDoEntry en : nodeForAllEntries.get(currNode))
 							applyRules(en);
						}
					
					nodeExistEntries.get(currNode).clear();
					nodeForAllEntries.get(currNode).clear();
					axiomRoles.get(currNode).clear();
			}
				if(!todo.isEmpty())
					processToDoList();
		}
		else if(!nodeForAllEntries.get(currNode).isEmpty()|| !nodeMaxEntries.get(currNode).isEmpty()) {
			if(isNIRuleApplicable(currNode)) {
					System.err.println("ni applicable 4");
					addExistentialRestrictions(currNode);
					addRangeRestrictions(this.axiomRoles.get(currNode));
					checkRelatedForAll(currNode, nodeForAllEntries.get(currNode), this.axiomRoles.get(currNode));
					checkRelatedMax(currNode, nodeMaxEntries.get(currNode), this.axiomRoles.get(currNode));
				
 				if(!relatedMaxEntries.get(currNode).isEmpty()) {	
 					checkOutgoingEdges(currNode, relatedMaxEntries.get(currNode));
 				}
 				Set<ToDoEntry> entries = new HashSet<>();
					if(!nodeExistEntries.get(currNode).isEmpty())
						entries.addAll(nodeExistEntries.get(currNode));
					if(!relatedMaxEntries.get(currNode).isEmpty())
						entries.addAll(relatedMaxEntries.get(currNode));
					if(!relatedForAllEntries.get(currNode).isEmpty())
						entries.addAll(relatedForAllEntries.get(currNode));
					nodeExistEntries.get(currNode).clear();
					nodeMaxEntries.get(currNode).clear();
					nodeForAllEntries.get(currNode).clear();
					relatedForAllEntries.get(currNode).clear();
					relatedMaxEntries.get(currNode).clear();
					callILP(currNode, entries, new HashSet<OWLSubClassOfAxiom>(this.niSubAx), outgoingEdges);
					for(ToDoEntry en : unrelatedMaxEntries.get(currNode))
						applyRules(en);
					unrelatedMaxEntries.get(currNode).clear();
					axiomRoles.get(currNode).clear();
					this.niSubAx.clear();
				}
				else {
					checkRelatedForAll(currNode, nodeForAllEntries.get(currNode), this.axiomRoles.get(currNode));
					checkRelatedMax(currNode, nodeMaxEntries.get(currNode), this.axiomRoles.get(currNode));
				
	 				if(!relatedMaxEntries.get(currNode).isEmpty()) {	
	 					checkOutgoingEdges(currNode, relatedMaxEntries.get(currNode));
	 				}
	 				if(!nodeExistEntries.get(currNode).isEmpty() || !this.outgoingEdges.isEmpty()) {
		 				Set<ToDoEntry> entries = new HashSet<>();
							if(!nodeExistEntries.get(currNode).isEmpty())
								entries.addAll(nodeExistEntries.get(currNode));
							if(!relatedMaxEntries.get(currNode).isEmpty())
								entries.addAll(relatedMaxEntries.get(currNode));
							if(!relatedForAllEntries.get(currNode).isEmpty())
								entries.addAll(relatedForAllEntries.get(currNode));
							nodeExistEntries.get(currNode).clear();
							nodeMaxEntries.get(currNode).clear();
							nodeForAllEntries.get(currNode).clear();
							relatedForAllEntries.get(currNode).clear();
							relatedMaxEntries.get(currNode).clear();
							callILP(currNode, entries, new HashSet<OWLSubClassOfAxiom>(this.niSubAx), outgoingEdges);
							for(ToDoEntry en : unrelatedMaxEntries.get(currNode))
								applyRules(en);
							unrelatedMaxEntries.get(currNode).clear();
							axiomRoles.get(currNode).clear();
	 						this.niSubAx.clear();
	 				}
	 				else {
	 					if(!nodeForAllEntries.get(currNode).isEmpty()) {
			 				for(ToDoEntry en : nodeForAllEntries.get(currNode))
			 					applyRules(en);
		 				}
		 				if(!nodeMaxEntries.get(currNode).isEmpty()) {
			 				for(ToDoEntry en : nodeMaxEntries.get(currNode))
			 					applyRules(en);
		 				}
		 				nodeForAllEntries.get(currNode).clear();
		 				nodeMaxEntries.get(currNode).clear();
	 				}
				}
			
			if(!todo.isEmpty())
				processToDoList();
		}
	}

	private void addExistentialRestrictions(Node node) {
		DependencySet newDS = DependencySet.create();
		Set<DependencySet> nomDS = new HashSet<>();
		Set<DependencySet> conDS = new HashSet<>();
		for(OWLObjectOneOf nominal : node.getLabel().stream().filter(ce -> ce instanceof OWLObjectOneOf).map(ce -> (OWLObjectOneOf)ce).collect(Collectors.toSet())) {
			ConceptNDepSet cnd = node.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(nominal)).iterator().next();
			nomDS.add(cnd.getDs());
		}
		if(!nomDS.stream().anyMatch(ds -> ds.isEmpty())) {
			//FIXME check if it is changing the original ds?? it should not change original ds
			nomDS.stream().forEach(ds -> newDS.add(DependencySet.create(ds)));
		}
		for(OWLObjectMaxCardinality mxCard : node.getLabel().stream().filter(ce -> ce instanceof OWLObjectMaxCardinality).map(ce -> (OWLObjectMaxCardinality)ce).collect(Collectors.toSet())) {
			OWLObjectPropertyExpression role = mxCard.getProperty();
			OWLClassExpression filler = mxCard.getFiller();
			//System.err.println(filler);
			if(node.getOutgoingEdges().stream().anyMatch(e -> e.isPredEdge() && !e.isReset() && e.getLabel().contains(role) 
					&& e.getToNode().getLabel().contains(filler) && e.getToNode().isBlockableNode() && !e.getToNode().isReset())) {
			
			int cardinality = mxCard.getCardinality();
			ConceptNDepSet cnd = node.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(mxCard)).iterator().next();
			//FIXME check if it is changing the original ds?? it should not change original ds
			newDS.add(DependencySet.create(cnd.getDs()));
			
			List<Edge> outgoingEdges = node.getOutgoingEdges().stream().filter(e -> !e.isReset() && e.getLabel().contains(role) /*&& e.isSuccEdge()*/ 
												&& e.getToNode().getLabel().contains(filler) && e.getToNode().isNINode()).collect(Collectors.toList());

			if(outgoingEdges.size() != 0 && outgoingEdges.size() < cardinality) {
				int diff = cardinality - outgoingEdges.size();
				System.err.println("diff "+diff);
				List<Edge> predEdges = node.getOutgoingEdges().stream().filter(e -> !e.isReset() && e.getLabel().contains(role) 
						&& e.isPredEdge() && e.getToNode().getLabel().contains(filler) && e.getToNode().isBlockableNode() 
						&& !e.getToNode().isReset()).collect(Collectors.toList());
				for(Edge edge : predEdges) {
					Node to = edge.getToNode();
					ConceptNDepSet cnd2 = to.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).iterator().next();
					conDS.add(cnd2.getDs());
					if(to.getCardinality() > 1) {
						this.splitNode2(to);
					}
				}
				if(!conDS.stream().anyMatch(ds -> ds.isEmpty())) {
					//FIXME check if it is changing the original ds?? it should not change original ds
					conDS.stream().forEach(ds -> newDS.add(DependencySet.create(ds)));
				}
				Set<OWLClassExpression> niNominals = new HashSet<>(); 
				for(int i = 0; i < diff; i++) {
					OWLNamedIndividual namedInd = df.getOWLNamedIndividual(IRI.create(base+"#ni_"+niCounter+"_node_"+node.getId()));
					OWLClassExpression ni = df.getOWLObjectOneOf(namedInd);
					niNominals.add(ni);
					ConceptNDepSet cnds = new ConceptNDepSet(df.getOWLObjectSomeValuesFrom(role, df.getOWLObjectIntersectionOf(ni,filler)), newDS);
					ToDoEntry entry = new ToDoEntry(node, cnds, NodeTag.EXISTS);
					nodeExistEntries.put(node, entry);
					niCounter++;
				}
				niSubAx.add(df.getOWLSubClassOfAxiom(filler, df.getOWLObjectUnionOf(niNominals)));
				this.axiomRoles.put(node, role);
			}
			else if(outgoingEdges.size() == 0) {
				List<Edge> predEdges = node.getOutgoingEdges().stream().filter(e -> !e.isReset() && e.getLabel().contains(role) 
						&& e.isPredEdge() && e.getToNode().getLabel().contains(filler) && e.getToNode().isBlockableNode() 
						&& !e.getToNode().isReset()).collect(Collectors.toList());
				for(Edge edge : predEdges) {
					Node to = edge.getToNode();
					ConceptNDepSet cnd2 = to.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).iterator().next();
					conDS.add(cnd2.getDs());
					if(to.getCardinality() > 1) {
						this.splitNode2(to);
					}
				}
				if(!conDS.stream().anyMatch(ds -> ds.isEmpty())) {
					//FIXME check if it is changing the original ds?? it should not change original ds
					conDS.stream().forEach(ds -> newDS.add(DependencySet.create(ds)));
				}
				Set<OWLClassExpression> niNominals = new HashSet<>(); 
				for(int i = 0; i < cardinality; i++) {
					OWLNamedIndividual namedInd = df.getOWLNamedIndividual(IRI.create(base+"#ni_"+niCounter+"_node_"+node.getId()));
					OWLClassExpression ni = df.getOWLObjectOneOf(namedInd);
					niNominals.add(ni);
					ConceptNDepSet cnds = new ConceptNDepSet(df.getOWLObjectSomeValuesFrom(role, df.getOWLObjectIntersectionOf(ni,filler)), newDS);
					ToDoEntry entry = new ToDoEntry(node, cnds, NodeTag.EXISTS);
					nodeExistEntries.put(node, entry);
					niCounter++;
				}
				niSubAx.add(df.getOWLSubClassOfAxiom(filler, df.getOWLObjectUnionOf(niNominals)));
				this.axiomRoles.put(node, role);
			}
			}
			// no need to make them disjoint
			/*for(int i = 0; i < ni.size(); i++) {
				for(int j = 0; j < ni.size(); j++) {
					if(!ni.get(i).equals(ni.get(j))) {
						ontology.addDiffIndividuals(ni.get(i), ni.get(j));
					}
				}
			}
			this.intl.addDiffInd(df.getOWLDifferentIndividualsAxiom(namedInds));*/
		}
	}
	private boolean isNIRuleApplicable(Node n) {
		if(n.isNominalNode()) {
			DependencySet newDS = DependencySet.create();
			Set<DependencySet> nomDS = new HashSet<>();
			for(OWLObjectOneOf nominal : n.getLabel().stream().filter(ce -> ce instanceof OWLObjectOneOf).map(ce -> (OWLObjectOneOf)ce).collect(Collectors.toSet())) {
				ConceptNDepSet cnd = n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(nominal)).iterator().next();
				nomDS.add(cnd.getDs());
			}
			if(!nomDS.stream().anyMatch(ds -> ds.isEmpty())) {
				//FIXME check if it is changing the original ds?? it should not change original ds
				nomDS.stream().forEach(ds -> newDS.add(DependencySet.create(ds)));
			}
			Set<OWLObjectMaxCardinality> mxCards = n.getLabel().stream().filter(ce -> ce instanceof OWLObjectMaxCardinality).map(ce -> (OWLObjectMaxCardinality)ce).collect(Collectors.toSet());
		    for(OWLObjectMaxCardinality mx : mxCards){
		    		OWLObjectPropertyExpression role = mx.getProperty();
		    		OWLClassExpression filler = mx.getFiller();
		    		////
		    		DependencySet ds = n.getnLabel().getCndList().getCdSet().stream().filter(ce -> ce.getCe().equals(mx)).iterator().next().getDs();
		    		newDS.add(DependencySet.create(ds));
		    		int cardinality = mx.getCardinality();
				int maxCard = 0;
				DependencySet maxDs = DependencySet.create();
				for(Edge e : n.getOutgoingEdges()) {
					if(!e.isReset() && e.getLabel().contains(role) && e.getToNode().getLabel().contains(filler)) {
						Node to = e.getToNode();
							System.err.println("to "+ to.getId());
						int card = to.getCardinality();
						if(maxCard < card) {
							maxCard = card;
							maxDs = to.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(filler)).iterator().next().getDs();
								
							}
						}
					}

					if(maxCard > cardinality) {
						//FIXME: check dependency set 
						if(!newDS.isEmpty() || !maxDs.isEmpty()) {
						//	System.err.println("mxds "+ maxDs.getMax() +" "+filler);
							if(!clashHandler(DependencySet.plus(DependencySet.create(newDS), DependencySet.create(maxDs)), n))
								isInconsistent(n);
						}
						else
							isInconsistent(n);
						return false;
						
					}
		    		
		    		/////
		    		if(n.getOutgoingEdges().stream().anyMatch(e -> e.isPredEdge() && !e.isReset() && e.getLabel().contains(role) 
		    											&& e.getToNode().getLabel().contains(filler) && e.getToNode().isBlockableNode() && !e.getToNode().isReset())) {
		    			List<Edge> outgoingEdges = n.getOutgoingEdges().stream().filter(e -> !e.isReset() && e.getLabel().contains(role) && e.isSuccEdge() 
		    																		&& e.getToNode().getLabel().contains(filler) && e.getToNode().isNINode()).collect(Collectors.toList());
		    			/*Set<Node> existingNINodes = new HashSet<>();
		    			for(Edge e :outgoingEdges) {
		    				Node to = e.getToNode();
		    				if(to.isNINode()) {
		    					existingNINodes.add(to);
		    				}
		    			}*/
		    			if(outgoingEdges.size() == mx.getCardinality()) {
		    				return false;
		    			}
		    			else
		    			 return true;
		    		}
		    }
		}
		/*if(n.isNominalNode() && 
			n.getLabel().stream().anyMatch(ce -> ce instanceof OWLObjectMaxCardinality) && 
				n.getOutgoingEdges().stream().anyMatch(e -> e.isPredEdge())) {
			return true;
		}*/
		return false;
	}
	private void checkOutgoingEdges(Node n, Set<ToDoEntry> maxCardEntries) {
		for(ToDoEntry en : maxCardEntries) {
			//System.out.println("entry for all "+en);
			OWLObjectMaxCardinality av = (OWLObjectMaxCardinality)en.getClassExpression();
			OWLObjectPropertyExpression role = av.getProperty();
			OWLClassExpression ce = av.getFiller();
			for(Edge e : n.getOutgoingEdges()) {
					//System.err.println("e  "+ e.getLabel() +" label "+e.getToNode().getLabel());
					
					//if(e.getLabel().contains(role) && e.getToNode().getLabel().contains(ce) && !e.isReset() && !e.getToNode().isReset())
					if(e.getLabel().contains(role) && !e.isReset() && !e.getToNode().isReset())
								outgoingEdges.add(e);
			}
				//return true;
		}
	}
	private void checkOutgoingEdges2(Node n, Set<OWLObjectMaxCardinality> maxCardEntries) {
		outgoingEdges.clear();
		for(OWLObjectMaxCardinality av : maxCardEntries) {
			OWLObjectPropertyExpression role = av.getProperty();
			OWLClassExpression ce = av.getFiller();
			for(Edge e : n.getOutgoingEdges()) {
					//System.err.println("e  "+ e.getLabel() +" label "+e.getToNode().getLabel());
					
					//if(e.getLabel().contains(role) && e.getToNode().getLabel().contains(ce) && !e.isReset() && !e.getToNode().isReset())
					if(e.getLabel().contains(role) && !e.isReset() && !e.getToNode().isReset())
								outgoingEdges.add(e);
			}
				//return true;
		}
	}
	private void processEntry(ToDoEntry entry) {
		//System.out.println("entry "+ entry.getType());
		if(entry.getType().equals(NodeTag.OR) || entry.getType().equals(NodeTag.AND)) {
 			this.applyRules(entry);
 		}
		else if(entry.getType().equals(NodeTag.EXISTS)) {
			nodeExistEntries.put(currNode, entry);
			if(entry.getClassExpression() instanceof OWLObjectSomeValuesFrom) {
				OWLObjectPropertyExpression obj = ((OWLObjectSomeValuesFrom)entry.getClassExpression()).getProperty(); 
				//System.out.println("obj pro "+ obj);
				this.axiomRoles.put(currNode, obj);
				this.axiomRoles.get(currNode).addAll(this.getAllSuperRoles(obj));
			}
			else if (entry.getClassExpression() instanceof OWLObjectHasValue){
				OWLObjectPropertyExpression obj = ((OWLObjectHasValue)entry.getClassExpression()).getProperty(); 
				//System.out.println("obj pro "+ obj);
				this.axiomRoles.put(currNode, obj);
				this.axiomRoles.get(currNode).addAll(this.getAllSuperRoles(obj));
			}	
			
		}
		else if(entry.getType().equals(NodeTag.LE)) {
			nodeMinEntries.put(currNode, entry);
			OWLObjectPropertyExpression obj = ((OWLObjectMinCardinality)entry.getClassExpression()).getProperty(); 
			//System.out.println("obj pro "+ obj);
			this.axiomRoles.put(currNode, obj);
			this.axiomRoles.get(currNode).addAll(this.getAllSuperRoles(obj));
		}
		else if(entry.getType().equals(NodeTag.GE)) {
			nodeMaxEntries.put(currNode, entry);
			OWLObjectPropertyExpression obj = ((OWLObjectMaxCardinality)entry.getClassExpression()).getProperty(); 
		//	System.out.println("obj pro "+ obj);
		//	this.axiomRoles.put(currNode, obj);
		}
		else if(entry.getType().equals(NodeTag.FORALL)) {
			nodeForAllEntries.put(currNode, entry);
		}
	}
	public void addRangeRestrictions(Set<OWLObjectPropertyExpression> roles) {
		//System.out.println("forall: "+ nodeForAllEntries.get(currNode).size());
		for(OWLObjectPropertyExpression obj : roles) {
			if(!(intl.getOntology().getRoleRange(obj).isEmpty())) {
				for(OWLObjectAllValuesFrom rr : intl.getOntology().getRoleRange(obj)) {
					//System.out.println("obj pro range "+ rr);
					ConceptNDepSet cnds = new ConceptNDepSet(rr, DependencySet.create());
					nodeForAllEntries.put(currNode, new ToDoEntry(currNode, cnds, NodeTag.FORALL));
				}
			}
			if(intl.getOntology().getSuperRolesMap().containsKey(obj)) { 
				for(OWLObjectPropertyExpression r : intl.getOntology().getSuperRolesMap().get(obj)) {
					if(!(intl.getOntology().getRoleRange(r).isEmpty())) {
						for(OWLObjectAllValuesFrom rr : intl.getOntology().getRoleRange(r)) {
							ConceptNDepSet cnds = new ConceptNDepSet(rr, DependencySet.create());
							nodeForAllEntries.put(currNode, new ToDoEntry(currNode, cnds, NodeTag.FORALL));
						}
					}
				}
			}
		}
	//	System.out.println("after forall: "+ nodeForAllEntries.get(currNode).size());
		
	}
	public boolean needILPModule(Node n) {
	//	forAllCheck = false;
	//	isExistential = false;
	//	if(!nodeMinEntries.get(n).isEmpty() || !nodeMaxEntries.get(n).isEmpty()) {
		if(!nodeMinEntries.get(n).isEmpty() || !relatedMaxEntries.get(n).isEmpty()) {
			if(!n.isBlocked()) 
				return true;
		}
			
		else if(!n.isBlocked()) {
			for(ToDoEntry entry : nodeExistEntries.get(n)) {
				OWLClassExpression ce = entry.getClassExpression();
				
				if(ce instanceof OWLObjectSomeValuesFrom) {
					
				//	isExistential = true;
					if(hasNominal((OWLObjectSomeValuesFrom) ce)) 
						return true;
				}
				else if(ce instanceof OWLObjectHasValue) {
					
					return true;
				}
			}
			
			if(!relatedForAllEntries.get(n).isEmpty()) {
			
				for(ToDoEntry entry : relatedForAllEntries.get(n)) {
					
					OWLClassExpression ce = entry.getClassExpression();
					if(ce instanceof OWLObjectAllValuesFrom) {
						if(hasNominal((OWLObjectAllValuesFrom) ce)) {
							//forAllCheck = true;
							return true;
						}
					}
				}
			}
			/*if(forAllCheck && isExistential)
				return true;*/
		}
		return false;
	}
	private void checkRelatedForAll(Node n, Set<ToDoEntry> forAllEntries, Set<OWLObjectPropertyExpression> roles) {
		//Set<OWLObjectAllValuesFrom> forAll = new HashSet<>();
		outgoingEdges.clear();
		System.out.println("related forall: "+ forAllEntries.size());
		System.out.println("roles  "+ roles);
		//forAllEntries.stream().forEach(en -> forAll.add((OWLObjectAllValuesFrom)en.getClassExpression()));
		for(ToDoEntry en : forAllEntries) {
			//System.out.println("entry for all "+en);
			OWLObjectAllValuesFrom av = (OWLObjectAllValuesFrom)en.getClassExpression();
			OWLObjectPropertyExpression role = av.getProperty();
			System.out.println("role  "+ role);
			if(roles.contains(role)){
				System.out.println("role  "+ role);
				relatedForAllEntries.put(n, en);
				for(Edge e : n.getOutgoingEdges()) {
					//System.out.println("e  "+ e.getLabel());
					if(e.getLabel().contains(role) && !e.isReset() && !e.getToNode().isReset())
						outgoingEdges.add(e);
				}
				//return true;
			}
			else{
				for(OWLObjectPropertyExpression r : intl.getOntology().getSuperRolesMap().keySet()) {
					if(roles.contains(r)) {
						System.out.println("role  "+ role);
						if(intl.getOntology().getSuperRolesMap().get(r).contains(role)) {
							relatedForAllEntries.put(n, en);
							for(Edge e : n.getOutgoingEdges()) {
								if(e.getLabel().contains(role) && !e.isReset() && !e.getToNode().isReset())
									outgoingEdges.add(e);
							}
							//return true;
						}
					}
				}
			}
		}
	//	System.out.println("after related forall: "+ relatedForAllEntries.get(currNode).size());
		
		//System.out.println("outgoingEdges "+ outgoingEdges.size());
		//return false;
	}
	private void checkRelatedMax(Node n, Set<ToDoEntry> maxEntries, Set<OWLObjectPropertyExpression> roles) {
	//	outgoingEdges.clear();
		//System.out.println("related max: "+ relatedMaxEntries.get(currNode).size());
		//System.out.println("roles  "+ roles);
		
		for(ToDoEntry en : maxEntries) {
			boolean flag = false;
			//System.out.println("entry for all "+en);
			OWLObjectMaxCardinality mx = (OWLObjectMaxCardinality)en.getClassExpression();
			OWLObjectPropertyExpression role = mx.getProperty();
		//	System.out.println("role  "+ role);
			if(roles.contains(role)){
		//		System.out.println("role  "+ role);
				relatedMaxEntries.put(n, en);
				flag = true;
				//return true;
			}
			else{
				for(OWLObjectPropertyExpression r : intl.getOntology().getSuperRolesMap().keySet()) {
					if(roles.contains(r)) {
						if(intl.getOntology().getSuperRolesMap().get(r).contains(role)) {
							relatedMaxEntries.put(n, en);
							flag = true;
							//return true;
						}
					}
				}
			}
			if(!flag) {
				unrelatedMaxEntries.put(n, en);
			}
		}
	//	System.out.println("after related max: "+ relatedMaxEntries.get(currNode).size());
		
		//System.out.println("outgoingEdges "+ outgoingEdges.size());
		//return false;
	}

	public void blockNode(Node n, Node blocker){
		cg.setNodeBlocked(n, blocker);
	}
	public boolean needILPModule(ToDoEntry entry) {
		forAllCheck = false;
		isExistential = false;
		Node n = entry.getNode();
		if(!n.isBlocked()) {
			
			if(entry.getType().equals(NodeTag.AND)) {
				for(OWLClassExpression ce : entry.getClassExpression().asConjunctSet()) {
					if(ce instanceof OWLObjectHasValue)
						return true;
					else if (ce instanceof OWLObjectIntersectionOf) {
						if(hasNominal((OWLObjectIntersectionOf)ce)) {
							return true;
						}
					}
					else if (ce instanceof OWLObjectUnionOf) {
						if(hasNominal((OWLObjectUnionOf)ce)) {
							return true;
						}
					}
						
					else if(ce instanceof OWLObjectSomeValuesFrom) {
						isExistential = true;
						if(hasNominal((OWLObjectSomeValuesFrom) ce)) 
							return true;
					}
					else if(ce instanceof OWLObjectAllValuesFrom) {
						if(hasNominal((OWLObjectAllValuesFrom) ce)) {
							forAllCheck = true;
						}
					}
				}
			}
			else if(entry.getType().equals(NodeTag.EXISTS)) {
				OWLClassExpression ce = entry.getClassExpression();
				if(ce instanceof OWLObjectHasValue)
					return true;
				else if(hasNominal((OWLObjectSomeValuesFrom) ce)) 
					return true;
			}
		}
		if(forAllCheck && isExistential)
			return true;
		return false;
	}
	private boolean hasNominal(OWLObjectAllValuesFrom ce) {
		OWLClassExpression filler = ce.getFiller();
		if(filler instanceof OWLObjectOneOf)
			return true;
		else if(filler instanceof OWLClass) {
			if(hasNominal(filler)) {
				return true;
			}
		}
		else if(filler instanceof OWLObjectIntersectionOf) {
			for(OWLClassExpression c : filler.asConjunctSet()) {
				if(c instanceof OWLClass) {
					if(hasNominal(c)) {
						return true;
					}
				}
				else if(c instanceof OWLObjectOneOf)
					return true;
			}
		}
		else if(filler instanceof OWLObjectUnionOf) {
			for(OWLClassExpression c : filler.asDisjunctSet()) {
				if(c instanceof OWLClass) {
					if(hasNominal(c)) {
						return true;
					}
				}
				else if(c instanceof OWLObjectOneOf)
					return true;
			}
		} 
		return false;
	}
	private boolean hasNominal(OWLObjectSomeValuesFrom ce) {
		OWLClassExpression filler = ce.getFiller();
		
		if(filler instanceof OWLObjectOneOf)
			return true;
		else if(filler instanceof OWLClass) {
			if(hasNominal(filler)) 
				return true;
		}
		else if(filler instanceof OWLObjectIntersectionOf) {
			for(OWLClassExpression c : filler.asConjunctSet()) {
				if(c instanceof OWLClass) {
					if(hasNominal(c)) {
						return true;
					}
				}
				else if(c instanceof OWLObjectOneOf)
					return true;
			}
		}
		else if(filler instanceof OWLObjectUnionOf) {
			for(OWLClassExpression c : filler.asDisjunctSet()) {
				if(c instanceof OWLClass) {
					if(hasNominal(c)) {
						return true;
					}
				}
				else if(c instanceof OWLObjectOneOf)
					return true;
			}
		}
		for(OWLObjectAllValuesFrom forAll : this.intl.getRoleRange(ce.getProperty())) {
			if(forAll.getFiller() instanceof OWLObjectOneOf)
				return true;
			else if(forAll.getFiller() instanceof OWLObjectIntersectionOf) {
				if(forAll.getFiller().asConjunctSet().stream().anyMatch(cj -> (cj instanceof OWLObjectOneOf)))
					return true;
			}
			else if(forAll.getFiller() instanceof OWLObjectUnionOf) {
				if(forAll.getFiller().asDisjunctSet().stream().anyMatch(dj -> (dj instanceof OWLObjectOneOf)))
					return true;
			}
		}
		return false;
	}
	private boolean hasNominal(OWLObjectIntersectionOf ce) {
		for(OWLClassExpression c : ce.asConjunctSet()) {
			if(c instanceof OWLObjectHasValue)
				return true;
			else if (c instanceof OWLObjectIntersectionOf) {
				if(hasNominal((OWLObjectIntersectionOf)c)) {
					return true;
				}
			}
			else if (c instanceof OWLObjectSomeValuesFrom) {
				isExistential = true;
				if(hasNominal((OWLObjectSomeValuesFrom)c)) {
					return true;
				}
				
			}
			else if (c instanceof OWLObjectAllValuesFrom) {
				if(hasNominal((OWLObjectAllValuesFrom)c)) {
					forAllCheck = true;
					return true;
				}
			}
			else if (c instanceof OWLObjectUnionOf) {
				if(hasNominal((OWLObjectUnionOf)c)) {
					return true;
				}
			}
		}
		return false;
	}
	

	private boolean hasNominal(OWLObjectUnionOf ce) {
		for(OWLClassExpression c : ce.asDisjunctSet()) {
			if (c instanceof OWLObjectIntersectionOf) {
				if(hasNominal((OWLObjectIntersectionOf)c)) {
					return true;
				}
			}
			else if(c instanceof OWLObjectHasValue)
				return true;
			else if (c instanceof OWLObjectSomeValuesFrom) {
				isExistential = true;
				if(hasNominal((OWLObjectSomeValuesFrom)c)) {
					return true;
				}
				
			}
			else if (c instanceof OWLObjectAllValuesFrom) {
				if(hasNominal((OWLObjectAllValuesFrom)c)) {
					forAllCheck = true;
					return true;
				}
			}
			else if (c instanceof OWLObjectUnionOf) {
				if(hasNominal((OWLObjectUnionOf)c)) {
					return true;
				}
			}
		}
		return false;
	}

	private boolean hasNominal(OWLClassExpression filler) {
		if(filler instanceof OWLObjectOneOf) {
			return true;
		}
		else if(filler instanceof OWLClass) {
			//System.out.println("class expression "+filler);
			if(intl.getOntology().hasNominal(filler))
				return true;
		}
		else if(filler instanceof OWLObjectIntersectionOf) {
			for(OWLClassExpression objIn : filler.asConjunctSet()) {
				if(objIn instanceof OWLObjectOneOf) {
					return true;
				}
				else
					return hasNominal(objIn);
			}
		}
		else if(filler instanceof OWLObjectUnionOf) {
			for(OWLClassExpression objUn : filler.asDisjunctSet()) {
				if(objUn instanceof OWLObjectOneOf) {
					return true;
				}
				else if(objUn instanceof OWLClass) {
					if(hasNominal(objUn))
						return true;
				}
				else
					return hasNominal(objUn);
			}
		}
		
		return false;
	}
	
	public void callILP(Node n, Set<ToDoEntry> entries, Set<OWLSubClassOfAxiom> subsumption, Set<Edge> outgoingEdges) {
		System.out.println("Calling ILP module..."+ entries.size() +" node id: "+n.getId());
	//	n.getLabel().stream().forEach(e -> System.out.println(e));
		entries.stream().forEach(e -> System.err.println(e.getClassExpression()));
		Node blocker =  findBlocker(n);
		if(blocker != null) {
			blockNode(n, blocker);
			//cg.setNodeBlocked(n, blocker);
			return;
		}
		if(outgoingEdges == null) {
			outgoingEdges = checkOutGoingEdges(n, entries);
		}
		
		///// added 24-oct-2019
		DependencySet newDs = DependencySet.create(getCurLevel());
		for(ToDoEntry entry : entries) {
			entry.setDs(DependencySet.plus(DependencySet.create(newDs),DependencySet.create(entry.getDs())));
		}
		BranchHandler bh = new BranchHandler(entries, newDs, n, outgoingEdges, subsumption);
		this.branches.put(getCurLevel(), bh);
		save(n);
		incCurLevel();
		
		/////
		Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> superRolesMap = new HashMap<>();
		for(OWLObjectPropertyExpression r : this.axiomRoles.get(currNode)) {
			if(!getAllSuperRoles(r).isEmpty())
				superRolesMap.put(r, this.getAllSuperRoles(r));
		}
		System.err.println(""+superRolesMap);
		if(outgoingEdges.size() > 0)
			outgoingEdges.stream().forEach(e -> System.err.println(e.getLabel()));
		
			//System.err.println("inverse edges : "+outgoingEdges.size() +"  : "+outgoingEdges.stream().filter(predicate) +outgoingEdges.iterator().next().getLabel());
		
		ILPPreprocessor ilpPro = new ILPPreprocessor(cg, entries, this.intl, this.df, n, outgoingEdges, subsumption, superRolesMap);
		ILPSolution sol = null;
		try {
			sol = ilpPro.callILP();
		} catch (IloException e) {
			e.printStackTrace();
		}
		
		if(sol.isSolved()) {
			for(EdgeInformation ei : sol.getEdgeInformation()) {
			//	DependencySet ds = ei.getDs();
				DependencySet ds = DependencySet.plus(ei.getDs(), newDs);
				Set<OWLObjectPropertyExpression> roles = ei.getEdges();
				Set<Integer> nodeIds = ei.getNodeSet();
				System.out.println("nodeIds.isEmpty() "+ nodeIds.isEmpty());
				Node to = null;
				Node node = null;
				Edge e = null;
				boolean niCheck = false;
				boolean newNode = false;
				if(nodeIds.isEmpty()) {
					/*Node blocker =  findBlocker(n);
					if(blocker != null) {
						cg.setNodeBlocked(n, blocker);
						return;
					}*/
					if(ei.getFillers().stream().anyMatch(ce -> ce instanceof OWLObjectOneOf)) {
						boolean niNode = false;
						Set<Node> nomNodes = new HashSet<>();
						SetMultimap<OWLClassExpression, Node> nomNodesMap = HashMultimap.create();
						for(OWLClassExpression filler : ei.getFillers().stream().filter(ce -> ce instanceof OWLObjectOneOf).map(ce -> (OWLClassExpression)ce).collect(Collectors.toSet())) {
							//OWLClassExpression ci = df.getOWLObjectOneOf(filler.individuals().iterator().next());
							//System.out.println("nominal "+ filler);
							if(filler.toString().contains("#ni_")) {
								niNode = true;
							}
							Node nom = findNominalNode(filler);
							if(nom != null) {
								nomNodes.add(nom);
								nomNodesMap.put(filler, nom);
							}
							//System.out.println("nom "+ nomNodes.size());
						}
						if(!nomNodes.isEmpty()) {
							if(nomNodes.size()==1) {
								to = nomNodes.iterator().next();
								e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
								niCheck = true;
							//	e = this.cg.addEdge(n, to, roles, ds);
							}
							else {
								
								System.out.println("Needs Merging!");
								List<Node> nomNodesL = new ArrayList<>(nomNodes);
								for(int i = 0; i < nomNodesL.size()-1; i++) {
									if(nomNodesL.get(i).equals(n)) {
										to = mergeNodes(nomNodesL.get(i), nomNodesL.get(i+1), ds);
									}
									else if(nomNodesL.get(i).getLabel().size() < nomNodesL.get(i+1).getLabel().size())
										to = mergeNodes(nomNodesL.get(i), nomNodesL.get(i+1), ds);
									else
										to = mergeNodes(nomNodesL.get(i+1), nomNodesL.get(i), ds);
								}
								if(to==null) 
									return;
								e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
								////  new code 27-oct-2019
								reset(to);
								this.addToDoEntries(to);
								////
								/*System.err.println("Sorry! it needs Merging!");
								Main.getExecutionTime();
								System.exit(0);*/
							}
							
						}
						else {
							newNode = true;
							to =this.cg.addNode(NodeType.NOMINAL, ds);
							//this.absorbRule1(df.getOWLThing(), to, ds);
							to.setCardinality(ei.getCardinality());
							addTGAxiom(to, ds);
							e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
							//e = this.cg.addEdge(n, to, roles, ds);
						}
						if(niNode) {
							to.makeNINode();
						}
					}
					else {
						newNode = true;
						to =this.cg.addNode(NodeType.BLOCKABLE, ds);
						//this.absorbRule1(df.getOWLThing(), to, ds);
						to.setCardinality(ei.getCardinality());
						addTGAxiom(to, ds);
						e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
						//e = this.cg.addEdge(n, to, roles, ds);
					}
				//	if(!checkAtLeastRestrictions(n))
				//		return;
					addLabel(n, to, ei.getFillers(), ds, newNode, entries);
				}
				else if(nodeIds.size()==1) {
					//System.err.println("node exists");
					node  = cg.getNode(nodeIds.iterator().next());
					if(ei.getFillers().stream().anyMatch(ce -> ce instanceof OWLObjectOneOf)) {
						Set<Node> nomNodes = new HashSet<>();
						boolean niNode = false;
						SetMultimap<OWLClassExpression, Node> nomNodesMap = HashMultimap.create();
						for(OWLClassExpression filler : ei.getFillers().stream().filter(ce -> ce instanceof OWLObjectOneOf).map(ce -> (OWLClassExpression)ce).collect(Collectors.toSet())) {
							//OWLClassExpression ci = df.getOWLObjectOneOf(filler.individuals().iterator().next());
							System.out.println("nominal "+ filler);
							if(filler.toString().contains("#ni_")) {
								niNode = true;
							}
							Node nom = findNominalNode(filler);
							//System.out.println("nominal node"+ nom);
							if(nom != null) {
								nomNodes.add(nom);
								nomNodesMap.put(filler, nom);
							}
						}
						if(!nomNodes.isEmpty()) {
							if(nomNodes.size()==1) {
								//System.err.println("nominAl node exists");
								to = nomNodes.iterator().next();
								if(node.getCardinality() > 1) {
									reset(node);
									this.splitNode(node);
									return;
								}
								if(node != null) {
									if(to.getId() != node.getId()) {
										//System.out.println("Needs Merging!");
										to = mergeNodes(node, to, ds);
									////  new code 27-oct-2019
										if(to==null) 
											return;
										reset(to);
										this.addToDoEntries(to);
										////
									}
									else
										niCheck = true;
								}
								//System.err.println("node label" + to.getLabel());
								e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
							
							//	e = this.cg.addEdge(n, to, roles, ds);
							}
							else {
								if(node.getCardinality() > 1) {
									reset(node);
									this.splitNode(node);
									return;
								}
								System.out.println("Needs Merging! nomNodes size" + nomNodes.size());
								List<Node> nomNodesL = new ArrayList<>(nomNodes);
								for(int i = 0; i < nomNodesL.size()-1; i++) {
									if(nomNodesL.get(i).equals(n)) {
										to = mergeNodes(nomNodesL.get(i), nomNodesL.get(i+1), ds);
									}
									else if(nomNodesL.get(i).getLabel().size() < nomNodesL.get(i+1).getLabel().size())
										to = mergeNodes(nomNodesL.get(i), nomNodesL.get(i+1), ds);
									else
										to = mergeNodes(nomNodesL.get(i+1), nomNodesL.get(i), ds);
								}
								if(node != null) {
									if(to.getId() != node.getId() && !nomNodesL.contains(node)) {
										//System.out.println("Needs Merging! again");
										to = mergeNodes(node, to, ds);
									}
								}
								if(to==null) 
									return;
								e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
							////  new code 27-oct-2019
								reset(to);
								this.addToDoEntries(to);
								////
							}
							if(niNode) {
								to.makeNINode();
							}
						}
						else {
							if(node.getCardinality() > 1) {
								reset(node);
								this.splitNode(node);
								return;
							}
							if(niNode) {
								node.makeNINode();
							}
							node.makeNominalNode();
							to = node;
							niCheck = true;
							e = cg.findEdge(n, to.getId());
							updateEdgeDepSet(ds, e);
							//node.setCardinality(ei.getCardinality());
						}
					}
					else {
						node.setCardinality(ei.getCardinality());
						to = node;
						e = cg.findEdge(n, to.getId());
						updateEdgeDepSet(ds, e);
					}
					//addLabel(n, to, ei.getFillers(), ds);
					
					//System.out.println("edge "+ e);
				//	updateEdgeDepSet(ds, e);
				//	if(!checkAtLeastRestrictions(n))
				//		return;
					Set<OWLClassExpression> newCE = new HashSet<>();
					for(OWLClassExpression c : ei.getFillers()) {
						if(!to.getLabel().contains(c))
							newCE.add(c);
					}
					if(!newCE.isEmpty()) {
						/*///new code start
						boolean resetRequired = newCE.stream().anyMatch(ce -> ce instanceof OWLObjectMinCardinality || ce instanceof OWLObjectMaxCardinality);
						if(!resetRequired) {
							for(OWLClassExpression ce : newCE) {
								resetRequired = ontology.getAllSubsumers(ce).stream().anyMatch(sub -> sub instanceof OWLObjectMinCardinality || sub instanceof OWLObjectMaxCardinality);
								
								if(resetRequired)
									break;
							}
						}
						
						if(resetRequired) {
							reset(to);
							addToDoEntries(to);
						}
						/// new code end 
*/						addLabel(n, to, newCE, ds, newNode, entries);
						
					}
					
				}
				else if(nodeIds.size()>1) {
					//FIXME: merge nodes
					List<Node> nodes = new ArrayList<>();
					for(Edge edge : cg.findEdges(n, nodeIds)) {
						nodes.add(edge.getToNode());
					}
					
					System.out.println("Needs Merging! ");
					for(int i = 0; i < nodes.size()-1; i++) {
						if((nodes.get(i+1).isNominalNode() || nodes.get(i+1).isNINode()) && (!nodes.get(i).isNominalNode() || !nodes.get(i).isNINode()))
							node = mergeNodes(nodes.get(i), nodes.get(i+1), ds);
						else if((!nodes.get(i+1).isNominalNode() || !nodes.get(i+1).isNINode()) && (nodes.get(i).isNominalNode() || nodes.get(i).isNINode()))
							node = mergeNodes(nodes.get(i+1), nodes.get(i), ds);
						else if(nodes.get(i).getLabel().size() < nodes.get(i+1).getLabel().size())
							node = mergeNodes(nodes.get(i), nodes.get(i+1), ds);
						else
							node = mergeNodes(nodes.get(i+1), nodes.get(i), ds);
					}
					if(node==null)
						return;
					////
					if(ei.getFillers().stream().anyMatch(ce -> ce instanceof OWLObjectOneOf)) {
						Set<Node> nomNodes = new HashSet<>();
						int nominals = 0;
						boolean niNode = false;
						SetMultimap<OWLClassExpression, Node> nomNodesMap = HashMultimap.create();
						for(OWLClassExpression filler : ei.getFillers().stream().filter(ce -> ce instanceof OWLObjectOneOf).map(ce -> (OWLClassExpression)ce).collect(Collectors.toSet())) {
							//OWLClassExpression ci = df.getOWLObjectOneOf(filler.individuals().iterator().next());
							//System.out.println("nominal "+ filler);
							if(filler.toString().contains("#ni_")) {
								niNode = true;
							}
							nominals++;
							Node nom = findNominalNode(filler);
							if(nom != null) {
								nomNodes.add(nom);
								nomNodesMap.put(filler, nom);
							}
						}
						if(!nomNodes.isEmpty()) {
							if(nomNodes.size()==1) {

								//System.err.println("node exists");
								to = nomNodes.iterator().next();
								if(node.getCardinality() > 1) {
									reset(node);
									this.splitNode(node);
									return;
								}
								if(node != null) {
									if(to.getId() != node.getId()) {
										System.out.println("Needs Merging!");
										to = mergeNodes(node, to, ds);
									}
								}
								if(to==null) 
									return;
								//System.err.println("node label" + to.getLabel());
								e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
							////  new code 27-oct-2019
								reset(to);
								this.addToDoEntries(to);
								////
							//	e = this.cg.addEdge(n, to, roles, ds);
							}
							else {
								if(node.getCardinality() > 1) {
									reset(node);
									this.splitNode(node);
									return;
								}
								System.out.println("Needs Merging!");
								List<Node> nomNodesL = new ArrayList<>(nomNodes);
								for(int i = 0; i < nomNodesL.size()-1; i++) {
									if(nomNodesL.get(i).equals(n)) {
										to = mergeNodes(nomNodesL.get(i), nomNodesL.get(i+1), ds);
									}
									else if(nomNodesL.get(i).getLabel().size() < nomNodesL.get(i+1).getLabel().size())
										to = mergeNodes(nomNodesL.get(i), nomNodesL.get(i+1), ds);
									else
										to = mergeNodes(nomNodesL.get(i+1), nomNodesL.get(i), ds);
								}
								if(node != null) {
									if(to.getId() != node.getId() && !nomNodesL.contains(node)) {
										//System.out.println("Needs Merging!");
										to = mergeNodes(node, to, ds);
									}
								}
								if(to==null) 
									return;
								e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
							////  new code 27-oct-2019
								reset(to);
								this.addToDoEntries(to);
								////
							}
							
						}
						else {
							if(node.getCardinality() > 1) {
								reset(node);
								this.splitNode(node);
								return;
							}
							node.makeNominalNode();
							to = node;
							e = cg.findEdge(n, to.getId());
							//System.err.println("edge "+e);
							updateEdgeDepSet(ds, e);
							//node.setCardinality(ei.getCardinality());
						}
						if(niNode) {
							to.makeNINode();
						}
					}
					else {
						node.setCardinality(ei.getCardinality());
						to = node;
						e = cg.findEdge(n, to.getId());
						updateEdgeDepSet(ds, e);
					}
					//addLabel(n, to, ei.getFillers(), ds);
					
					

					Set<OWLClassExpression> newCE = new HashSet<>();
					for(OWLClassExpression c : ei.getFillers()) {
						if(!to.getLabel().contains(c))
							newCE.add(c);
					}
					
					if(!newCE.isEmpty()) {
						///new code start
						boolean resetRequired = newCE.stream().anyMatch(ce -> ce instanceof OWLObjectMinCardinality || ce instanceof OWLObjectMaxCardinality);
						if(!resetRequired) {
							for(OWLClassExpression ce : newCE) {
								resetRequired = ontology.getAllSubsumers(ce).stream().anyMatch(sub -> sub instanceof OWLObjectMinCardinality || sub instanceof OWLObjectMaxCardinality);
								
								if(resetRequired)
									break;
							}
						}
						
						if(resetRequired) {
							reset(to);
							addToDoEntries(to);
							return;
						}
						/// new code end 
						addLabel(n, to, newCE, ds, newNode, entries);
						
					}
					
				}
				/*// if to is nominal node and has atmost restriction then apply NI rule
				if(to.isNominalNode() && to.getLabel().stream().anyMatch(lb -> lb instanceof OWLObjectMaxCardinality)) {
					applyNIRule(to);
				}*/
			}
		//	if(!checkAtLeastRestrictions(n))
		//		return;
			
		}
		else {
			System.out.println(sol.getInfeasible_set());
			boolean handleClash = false;
			DependencySet clashSet = DependencySet.create();
			//System.out.println("size "+entries.size());
			for(ToDoEntry entry: entries) {
				if(!entry.getDs().isEmpty()) {
					handleClash = true;
					//System.out.println("max "+entry.getDs().getMax()+" "+ entry.getClassExpression());
					clashSet.add(entry.getDs());
				}
			}
			if(handleClash) {
				if(!clashHandler(clashSet, n))
					isInconsistent(n);
			}
			else
				isInconsistent(n);
		}
		
	}
	
	private Set<Edge> checkOutGoingEdges(Node n, Set<ToDoEntry> entries2) {
		Set<Edge> outEdges = new HashSet<>();
		for(ToDoEntry en : entries2) {
			if(en.getType().equals(NodeTag.GE)) {
			//System.out.println("entry for all "+en);
				OWLObjectMaxCardinality av = (OWLObjectMaxCardinality)en.getClassExpression();
				OWLObjectPropertyExpression role = av.getProperty();
				for(Edge e : n.getOutgoingEdges()) {
					if(e.getLabel().contains(role) && !e.isReset() && !e.getToNode().isReset())
						outEdges.add(e);
				}
			}
			else if(en.getType().equals(NodeTag.FORALL)) {
				//System.out.println("entry for all "+en);
				OWLObjectAllValuesFrom av = (OWLObjectAllValuesFrom)en.getClassExpression();
				OWLObjectPropertyExpression role = av.getProperty();
				for(Edge e : n.getOutgoingEdges()) {
					if(e.getLabel().contains(role) && !e.isReset() && !e.getToNode().isReset())
							outEdges.add(e);
				}
			}
		}
		return outEdges;
	}
	private boolean checkAtLeastRestrictions(Node n) {
		//System.err.println("here");
		if(n.getLabel().stream().anyMatch(ce -> ce instanceof OWLObjectMinCardinality)) {
			for(OWLObjectMinCardinality minCard : n.getLabel().stream().filter(ce -> ce instanceof OWLObjectMinCardinality).map(ce -> (OWLObjectMinCardinality)ce).collect(Collectors.toSet())) {
				int card = minCard.getCardinality();
				int totalNodes = 0;
				OWLObjectPropertyExpression role = minCard.getProperty();
				OWLClassExpression filler = minCard.getFiller();
				for(Edge edge : n.getOutgoingEdges().stream().filter(e -> !e.isReset() && e.getLabel().contains(role)).map(e -> (Edge)e).collect(Collectors.toSet())) {
					Node to = edge.getToNode();
					if((to.getLabel().contains(filler) || 
								(filler instanceof OWLObjectIntersectionOf && to.getLabel().containsAll(filler.asConjunctSet())) || 
								(filler instanceof OWLObjectUnionOf && to.getLabel().stream().anyMatch(filler.asDisjunctSet()::contains))) 
							&& !to.isReset()) {
						if(edge.isPredEdge() && !edge.getToNode().isNominalNode()) {
							totalNodes++;
						}
						else {
							totalNodes += edge.getToNode().getCardinality();
						}
					}
					
				}
				System.err.println(""+ totalNodes);
				if(totalNodes < card) {
					DependencySet ds = DependencySet.create(n.getnLabel().getCndList().getCdSet().stream().filter(ce -> ce.getCe().equals(minCard)).iterator().next().getDs());
					if(!ds.isEmpty()) {
						ds.setCe(minCard);
						if(!clashHandler(ds, n))
							isInconsistent(n);
					}
					else
						isInconsistent(n);
					return false;
				}
			}
		}
		return true;
	}
	private void splitNode2(Node x) {
		//System.err.println("split Node");
		List<Node> newNodes = new ArrayList<>();
		List<OWLClassExpression> classExp = new ArrayList<>();
		for(int i = 0; i < x.getCardinality(); i++) {
			classExp.add(df.getOWLClass("#re_aux_" + ++counter, prefixManager));
		}
		for(int i = 0; i < x.getCardinality()-1; i++) {
			//FIXME: check dependency set
			Node newNode = cg.addNode(NodeType.BLOCKABLE, DependencySet.create());
			//this.absorbRule1(df.getOWLThing(), newNode, DependencySet.create());
			newNodes.add(newNode);
			newNode.addDisjointNode(x);
			x.addDisjointNode(newNode);
			//System.err.println("concept added "+ classExp.get(i));
			cg.addConceptToNode(newNode, new ConceptNDepSet(classExp.get(i), DependencySet.create()));
			for(ConceptNDepSet cnds : x.getnLabel().getCndList().getCdSet()) {
				cg.addConceptToNode(newNode, cnds);
			}
			//newEdges.add(cg.addEdge(from, newNode, e.getLabel(), e.getDepSet(), e.isSuccEdge()));
			for(Edge outE : x.getOutgoingEdges()) {
				if(!outE.isReset())
					cg.addEdge(newNode, outE.getToNode(), outE.getLabel(), outE.getDepSet(), outE.isSuccEdge());
			}
			for(int k = 0; k < i; k++) {
				cg.addConceptToNode(newNode, new ConceptNDepSet(classExp.get(k).getComplementNNF(), DependencySet.create()));
			}
			for(int k = i+1; k < x.getCardinality(); k++) {
				cg.addConceptToNode(newNode, new ConceptNDepSet(classExp.get(k).getComplementNNF(), DependencySet.create()));
			}
		}
		
		for(int i = 0; i < newNodes.size(); i++) {
			Node nn = newNodes.get(i);
			//addToDoEntries(nn);
			for(int k = 0; k < i; k++) {
				nn.addDisjointNode(newNodes.get(k));
			}
			for(int k = i+1; k < newNodes.size(); k++) {
				nn.addDisjointNode(newNodes.get(k));
			}
		}
		
		
		//System.err.println("concept added "+ classExp.get(x.getCardinality()-1));
		cg.addConceptToNode(x, new ConceptNDepSet(classExp.get(x.getCardinality()-1), DependencySet.create()));
		for(int k = 0; k < x.getCardinality()-1; k++) {
			cg.addConceptToNode(x, new ConceptNDepSet(classExp.get(k).getComplementNNF(), DependencySet.create()));
		}
		cg.updateNodeCardinality(x, 1);
		newNodes.add(x);
		addToDoEntries(x);
		for(int i = 0; i < classExp.size(); i++) {
			for(int j = 0; j < classExp.size(); j++) {
				if(!classExp.get(i).equals(classExp.get(j))) {
					ontology.addDiffIndividuals(classExp.get(i), classExp.get(j));
				}
			}
		}
		
	}
	private void splitNode(Node x) {
		System.err.println("split Node "+x.getId());
		List<Node> newNodes = new ArrayList<>();
		List<OWLClassExpression> classExp = new ArrayList<>();
		for(int i = 0; i < x.getCardinality(); i++) {
			classExp.add(df.getOWLClass("#re_aux_" + ++counter, prefixManager));
		}
		for(int i = 0; i < x.getCardinality()-1; i++) {
			//FIXME: check dependency set
			Node newNode = cg.addNode(NodeType.BLOCKABLE, DependencySet.create(x.getDs()));
			//this.absorbRule1(df.getOWLThing(), newNode, DependencySet.create());
			newNodes.add(newNode);
			newNode.addDisjointNode(x);
			x.addDisjointNode(newNode);
			//System.err.println("concept added "+ classExp.get(i));
			cg.addConceptToNode(newNode, new ConceptNDepSet(classExp.get(i), DependencySet.create(x.getDs())));
			for(ConceptNDepSet cnds : x.getnLabel().getCndList().getCdSet()) {
				cg.addConceptToNode(newNode, cnds);
			}
			//newEdges.add(cg.addEdge(from, newNode, e.getLabel(), e.getDepSet(), e.isSuccEdge()));
			for(Edge outE : x.getOutgoingEdges()) {
				if(!outE.isReset())
					cg.addEdge(newNode, outE.getToNode(), outE.getLabel(), outE.getDepSet(), outE.isSuccEdge());
			}
			for(int k = 0; k < i; k++) {
				cg.addConceptToNode(newNode, new ConceptNDepSet(classExp.get(k).getComplementNNF(), DependencySet.create(x.getDs())));
			}
			for(int k = i+1; k < x.getCardinality(); k++) {
				cg.addConceptToNode(newNode, new ConceptNDepSet(classExp.get(k).getComplementNNF(), DependencySet.create(x.getDs())));
			}
		}
		
		for(int i = 0; i < newNodes.size(); i++) {
			Node nn = newNodes.get(i);
			addToDoEntries(nn);
			for(int k = 0; k < i; k++) {
				nn.addDisjointNode(newNodes.get(k));
			}
			for(int k = i+1; k < newNodes.size(); k++) {
				nn.addDisjointNode(newNodes.get(k));
			}
		}
		
		
		//System.err.println("concept added "+ classExp.get(x.getCardinality()-1));
		cg.addConceptToNode(x, new ConceptNDepSet(classExp.get(x.getCardinality()-1), DependencySet.create(x.getDs())));
		for(int k = 0; k < x.getCardinality()-1; k++) {
			cg.addConceptToNode(x, new ConceptNDepSet(classExp.get(k).getComplementNNF(), DependencySet.create(x.getDs())));
		}
		cg.updateNodeCardinality(x, 1);
		newNodes.add(x);
		addToDoEntries(x);
		for(int i = 0; i < classExp.size(); i++) {
			for(int j = 0; j < classExp.size(); j++) {
				if(!classExp.get(i).equals(classExp.get(j))) {
					ontology.addDiffIndividuals(classExp.get(i), classExp.get(j));
				}
			}
		}
		
	}
	private boolean needReset(ILPSolution sol) {
		for(EdgeInformation ei : sol.getEdgeInformation()) {
			if(ei.getFillers().stream().anyMatch(ce -> ce instanceof OWLObjectOneOf)) {
				return true;
			}
		}
		return false;
	}
		// Aug 27, 2019
	/*public void callILP(Node n, Set<ToDoEntry> entries) {
		System.out.println("Calling ILP module...");//+ entries.size() +" node id: "+n.getId());
		//n.getLabel().stream().forEach(e -> System.out.println(e));
		//entries.stream().forEach(e -> System.out.println(e.getClassExpression()));
		Node blocker =  findBlocker(n);
		if(blocker != null) {
			blockNode(n, blocker);
			//cg.setNodeBlocked(n, blocker);
			return;
		}
		//System.err.println("inverse edges : "+outgoingEdges.size());
		ILPPreprocessor ilpPro = new ILPPreprocessor(entries, this.intl, this.df, n, outgoingEdges);
		ILPSolution sol = null;
		try {
			sol = ilpPro.callILP();
		} catch (IloException e) {
			e.printStackTrace();
		}
		//System.out.print("hi there");
		if(sol.isSolved()) {
				
			for(EdgeInformation ei : sol.getEdgeInformation()) {
				DependencySet ds = ei.getDs();
				Set<OWLObjectPropertyExpression> roles = ei.getEdges();
				Set<Integer> nodeIds = ei.getNodeSet();
				
				Node to = null;
				Node node = null;
				if(nodeIds.isEmpty()) {
					Node blocker =  findBlocker(n);
					if(blocker != null) {
						cg.setNodeBlocked(n, blocker);
						return;
					}
					if(ei.getFillers().stream().anyMatch(ce -> ce instanceof OWLObjectOneOf)) {
						Set<Node> nomNodes = new HashSet<>();
						SetMultimap<OWLClassExpression, Node> nomNodesMap = HashMultimap.create();
						for(OWLClassExpression filler : ei.getFillers().stream().filter(ce -> ce instanceof OWLObjectOneOf).map(ce -> (OWLClassExpression)ce).collect(Collectors.toSet())) {
							//OWLClassExpression ci = df.getOWLObjectOneOf(filler.individuals().iterator().next());
							//System.out.println("nominal "+ filler);
							
							Node nom = findNominalNode(filler);
							if(nom != null) {
								nomNodes.add(nom);
								nomNodesMap.put(filler, nom);
							}
						}
						if(!nomNodes.isEmpty()) {
							if(nomNodes.size()==1) {
								//System.err.println("node exists");
								to = nomNodes.iterator().next();
								Edge e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
							//	e = this.cg.addEdge(n, to, roles, ds);
							}
							else {
								
								System.out.println("Needs Merging!");
								List<Node> nomNodesL = new ArrayList<>(nomNodes);
								for(int i = 0; i < nomNodesL.size()-1; i++) {
									if(nomNodesL.get(i).equals(n)) {
										to = mergeNodes(nomNodesL.get(i), nomNodesL.get(i+1), ds);
									}
									else if(nomNodesL.get(i).getLabel().size() < nomNodesL.get(i+1).getLabel().size())
										to = mergeNodes(nomNodesL.get(i), nomNodesL.get(i+1), ds);
									else
										to = mergeNodes(nomNodesL.get(i+1), nomNodesL.get(i), ds);
								}
								Edge e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
								System.err.println("Sorry! it needs Merging!");
								Main.getExecutionTime();
								System.exit(0);
							}
							
						}
						else {
							to =this.cg.addNode(NodeType.NOMINAL, ds);
							
							to.setCardinality(ei.getCardinality());
							addTGAxiom(to, ds);
							Edge e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
							//e = this.cg.addEdge(n, to, roles, ds);
						}
					}
					else {
						to =this.cg.addNode(NodeType.BLOCKABLE, ds);
						to.setCardinality(ei.getCardinality());
						addTGAxiom(to, ds);
						Edge e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
						//e = this.cg.addEdge(n, to, roles, ds);
					}
					addLabel(n, to, ei.getFillers(), ds);
				}
				else if(nodeIds.size()==1) {
					//System.err.println("node exists");
					node  = cg.getNode(nodeIds.iterator().next());
					if(ei.getFillers().stream().anyMatch(ce -> ce instanceof OWLObjectOneOf)) {
						Set<Node> nomNodes = new HashSet<>();
						int nominals = 0;
						SetMultimap<OWLClassExpression, Node> nomNodesMap = HashMultimap.create();
						for(OWLClassExpression filler : ei.getFillers().stream().filter(ce -> ce instanceof OWLObjectOneOf).map(ce -> (OWLClassExpression)ce).collect(Collectors.toSet())) {
							//OWLClassExpression ci = df.getOWLObjectOneOf(filler.individuals().iterator().next());
							//System.out.println("nominal "+ filler);
							nominals++;
							Node nom = findNominalNode(filler);
							//System.out.println("nominal node"+ nom);
							if(nom != null) {
								nomNodes.add(nom);
								nomNodesMap.put(filler, nom);
							}
						}
						if(!nomNodes.isEmpty()) {
							if(nomNodes.size()==1) {

								//System.err.println("nominAl node exists");
								to = nomNodes.iterator().next();
								if(node.getCardinality() > nominals) {
									System.err.println("Cannot make it a nominal node");
								}
								if(node != null) {
									if(to.getId() != node.getId()) {
										//System.out.println("Needs Merging!");
										to = mergeNodes(node, to, ds);
									}
								}
								//System.err.println("node label" + to.getLabel());
								Edge e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
							//	e = this.cg.addEdge(n, to, roles, ds);
							}
							else {
								System.out.println("Needs Merging!" + nomNodes.size());
								List<Node> nomNodesL = new ArrayList<>(nomNodes);
								for(int i = 0; i < nomNodesL.size()-1; i++) {
									if(nomNodesL.get(i).equals(n)) {
										to = mergeNodes(nomNodesL.get(i), nomNodesL.get(i+1), ds);
									}
									else if(nomNodesL.get(i).getLabel().size() < nomNodesL.get(i+1).getLabel().size())
										to = mergeNodes(nomNodesL.get(i), nomNodesL.get(i+1), ds);
									else
										to = mergeNodes(nomNodesL.get(i+1), nomNodesL.get(i), ds);
								}
								if(node != null) {
									if(to.getId() != node.getId() && !nomNodesL.contains(node)) {
										//System.out.println("Needs Merging! again");
										to = mergeNodes(node, to, ds);
									}
								}
								Edge e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
							}
							
						}
						else {
							if(node.getCardinality() > 1) {
								System.err.println("Cannot make it a nominal node");
							}
							node.makeNominalNode();
							to = node;
							//node.setCardinality(ei.getCardinality());
						}
					}
					else {
						node.setCardinality(ei.getCardinality());
						to = node;
					}
					//addLabel(n, to, ei.getFillers(), ds);
					Edge e = cg.findEdge(n, to.getId());
					//System.out.println("edge "+ e);
					updateEdgeDepSet(ds, e);

					Set<OWLClassExpression> newCE = new HashSet<>();
					for(OWLClassExpression c : ei.getFillers()) {
						if(!to.getLabel().contains(c))
							newCE.add(c);
					}
					if(!newCE.isEmpty()) {
						///new code start
						boolean resetRequired = newCE.stream().anyMatch(ce -> ce instanceof OWLObjectMinCardinality || ce instanceof OWLObjectMaxCardinality);
						if(!resetRequired) {
							for(OWLClassExpression ce : newCE) {
								resetRequired = ontology.getAllSubsumers(ce).stream().anyMatch(sub -> sub instanceof OWLObjectMinCardinality || sub instanceof OWLObjectMaxCardinality);
								
								if(resetRequired)
									break;
							}
						}
						
						if(resetRequired) {
							reset(to);
							addToDoEntries(to);
						}
						/// new code end 
						addLabel(n, to, newCE, ds);
						
					}
					
				}
				else if(nodeIds.size()>1) {
					//FIXME: merge nodes
					List<Node> nodes = new ArrayList<>();
					for(Edge e : cg.findEdges(n, nodeIds)) {
						nodes.add(e.getToNode());
					}
					
					System.out.println("Needs Merging! ");
					for(int i = 0; i < nodes.size()-1; i++) {
						if(nodes.get(i).getLabel().size() < nodes.get(i+1).getLabel().size())
							node = mergeNodes(nodes.get(i), nodes.get(i+1), ds);
						else
							node = mergeNodes(nodes.get(i+1), nodes.get(i), ds);
					}
					////
					if(ei.getFillers().stream().anyMatch(ce -> ce instanceof OWLObjectOneOf)) {
						Set<Node> nomNodes = new HashSet<>();
						int nominals = 0;
						SetMultimap<OWLClassExpression, Node> nomNodesMap = HashMultimap.create();
						for(OWLClassExpression filler : ei.getFillers().stream().filter(ce -> ce instanceof OWLObjectOneOf).map(ce -> (OWLClassExpression)ce).collect(Collectors.toSet())) {
							//OWLClassExpression ci = df.getOWLObjectOneOf(filler.individuals().iterator().next());
							//System.out.println("nominal "+ filler);
							nominals++;
							Node nom = findNominalNode(filler);
							if(nom != null) {
								nomNodes.add(nom);
								nomNodesMap.put(filler, nom);
							}
						}
						if(!nomNodes.isEmpty()) {
							if(nomNodes.size()==1) {

								//System.err.println("node exists");
								to = nomNodes.iterator().next();
								if(node.getCardinality() > nominals) {
									System.err.println("Cannot make it a nominal node");
								}
								if(node != null) {
									if(to.getId() != node.getId()) {
										System.out.println("Needs Merging!");
										to = mergeNodes(node, to, ds);
									}
								}
								//System.err.println("node label" + to.getLabel());
								Edge e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
							//	e = this.cg.addEdge(n, to, roles, ds);
							}
							else {
								if(node.getCardinality() > nominals) {
									System.err.println("Cannot make it a nominal node!");
								}
								System.out.println("Needs Merging!");
								List<Node> nomNodesL = new ArrayList<>(nomNodes);
								for(int i = 0; i < nomNodesL.size()-1; i++) {
									if(nomNodesL.get(i).equals(n)) {
										to = mergeNodes(nomNodesL.get(i), nomNodesL.get(i+1), ds);
									}
									else if(nomNodesL.get(i).getLabel().size() < nomNodesL.get(i+1).getLabel().size())
										to = mergeNodes(nomNodesL.get(i), nomNodesL.get(i+1), ds);
									else
										to = mergeNodes(nomNodesL.get(i+1), nomNodesL.get(i), ds);
								}
								if(node != null) {
									if(to.getId() != node.getId() && !nomNodesL.contains(node)) {
										//System.out.println("Needs Merging!");
										to = mergeNodes(node, to, ds);
									}
								}
								Edge e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
							}
							
						}
						else {
							if(node.getCardinality() > nominals) {
								System.err.println("Cannot make it a nominal node");
							}
							node.makeNominalNode();
							to = node;
							//node.setCardinality(ei.getCardinality());
						}
					}
					else {
						node.setCardinality(ei.getCardinality());
						to = node;
					}
					//addLabel(n, to, ei.getFillers(), ds);
					Edge e = cg.findEdge(n, to.getId());
					updateEdgeDepSet(ds, e);

					Set<OWLClassExpression> newCE = new HashSet<>();
					for(OWLClassExpression c : ei.getFillers()) {
						if(!to.getLabel().contains(c))
							newCE.add(c);
					}
					
					if(!newCE.isEmpty()) {
						///new code start
						boolean resetRequired = newCE.stream().anyMatch(ce -> ce instanceof OWLObjectMinCardinality || ce instanceof OWLObjectMaxCardinality);
						if(!resetRequired) {
							for(OWLClassExpression ce : newCE) {
								resetRequired = ontology.getAllSubsumers(ce).stream().anyMatch(sub -> sub instanceof OWLObjectMinCardinality || sub instanceof OWLObjectMaxCardinality);
								
								if(resetRequired)
									break;
							}
						}
						
						if(resetRequired) {
							reset(to);
							addToDoEntries(to);
						}
						/// new code end 
						addLabel(n, to, newCE, ds);
						
					}
					
				}
				// if to is nominal node and has atmost restriction then apply NI rule
				if(to.isNominalNode() && to.getLabel().stream().anyMatch(lb -> lb instanceof OWLObjectMaxCardinality)) {
					applyNIRule(to);
				}
			}
		}
		else {
			boolean handleClash = false;
			DependencySet clashSet = DependencySet.create();
			System.out.println("size "+entries.size());
			for(ToDoEntry entry: entries) {
				if(!entry.getDs().isEmpty()) {
					handleClash = true;
					System.out.println("max "+entry.getDs().getMax()+" "+ entry.getClassExpression());
					clashSet.add(entry.getDs());
				}
			}
			if(handleClash) {
				if(!clashHandler(clashSet))
					isInconsistent(n);
			}
			else
				isInconsistent(n);
		}
	}*/
	public void callILPOld(Node n, Set<ToDoEntry> entries) {
		System.out.println("Calling ILP module...");//+ entries.size() +" node id: "+n.getId());
		//n.getLabel().stream().forEach(e -> System.out.println(e));
		//entries.stream().forEach(e -> System.out.println(e.getClassExpression()));
		Node blocker =  findBlocker(n);
		if(blocker != null) {
			blockNode(n, blocker);
			//cg.setNodeBlocked(n, blocker);
			return;
		}
		ILPPreprocessor ilpPro = new ILPPreprocessor(cg, entries, this.intl, this.df, n, outgoingEdges);
		ILPSolution sol = null;
		try {
			sol = ilpPro.callILP();
		} catch (IloException e) {
			e.printStackTrace();
		}
		//System.out.print("hi there");
		if(sol.isSolved()) {
				
			for(EdgeInformation ei : sol.getEdgeInformation()) {
				DependencySet ds = ei.getDs();
				Set<OWLObjectPropertyExpression> roles = ei.getEdges();
				Set<Integer> nodeIds = ei.getNodeSet();
				//FIXME: findEdge can return more than one edges, so might need to merge these nodes
				if(nodeIds.isEmpty()) {
					
				}
				else if(nodeIds.size()==1) {
					
				}
				else if(nodeIds.size()>1) {
					
				}
				Edge e = this.cg.findEdge(n, ei.getFillers(), roles);
				Node to = null;
				if(e == null) {
					/*Node blocker =  findBlocker(n);
					if(blocker != null) {
						cg.setNodeBlocked(n, blocker);
						return;
					}*/
					if(ei.getFillers().stream().anyMatch(ce -> ce instanceof OWLObjectOneOf)) {
						Set<Node> nomNodes = new HashSet<>();
						SetMultimap<OWLClassExpression, Node> nomNodesMap = HashMultimap.create();
						for(OWLClassExpression filler : ei.getFillers().stream().filter(ce -> ce instanceof OWLObjectOneOf).map(ce -> (OWLClassExpression)ce).collect(Collectors.toSet())) {
							//OWLClassExpression ci = df.getOWLObjectOneOf(filler.individuals().iterator().next());
							Node nom = findNominalNode(filler);
							if(nom != null) {
								nomNodes.add(nom);
								nomNodesMap.put(filler, nom);
							}
						}
						if(!nomNodes.isEmpty()) {
							if(nomNodes.size()==1) {
								//System.err.println("node exists");
								to = nomNodes.iterator().next();
								//System.err.println("node label" + to.getLabel());
								e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
							//	e = this.cg.addEdge(n, to, roles, ds);
							}
							else {
								System.out.println("Needs Merging!");
								List<Node> nomNodesL = new ArrayList<>(nomNodes);
								for(int i = 0; i < nomNodesL.size()-1; i++) {
									if(nomNodesL.get(i).getLabel().size() < nomNodesL.get(i+1).getLabel().size())
										to = mergeNodes(nomNodesL.get(i), nomNodesL.get(i+1), ds);
									else
										to = mergeNodes(nomNodesL.get(i+1), nomNodesL.get(i), ds);
								}
								e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
							////  new code 27-oct-2019
								reset(to);
								this.addToDoEntries(to);
								////
								/*System.err.println("Sorry! it needs Merging!");
								Main.getExecutionTime();
								System.exit(0);*/
							}
						}
						else {
							to =this.cg.addNode(NodeType.NOMINAL, ds);
							this.absorbRule1(df.getOWLThing(), to, ds);
							to.setCardinality(ei.getCardinality());
							addTGAxiom(to, ds);
							e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
							//e = this.cg.addEdge(n, to, roles, ds);
						}
					}
					else {
						to =this.cg.addNode(NodeType.BLOCKABLE, ds);
						this.absorbRule1(df.getOWLThing(), to, ds);
						to.setCardinality(ei.getCardinality());
						addTGAxiom(to, ds);
						e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
						//e = this.cg.addEdge(n, to, roles, ds);
					}
					addLabel(n, to, ei.getFillers(), ds, false, entries);
				}
				else {
					to = e.getToNode();
					// FIXME: new line added for updating cardinality, might be need to check if any at-most restriction is violated 
					to.setCardinality(ei.getCardinality());
					updateEdgeDepSet(ds, e);

					Set<OWLClassExpression> newCE = new HashSet<>();
					for(OWLClassExpression c : ei.getFillers()) {
						if(!to.getLabel().contains(c))
							newCE.add(c);
					}
					
					if(!newCE.isEmpty()) {
						///new code start
						boolean resetRequired = newCE.stream().anyMatch(ce -> ce instanceof OWLObjectMinCardinality || ce instanceof OWLObjectMaxCardinality);
						if(!resetRequired) {
							for(OWLClassExpression ce : newCE) {
								resetRequired = ontology.getAllSubsumers(ce).stream().anyMatch(sub -> sub instanceof OWLObjectMinCardinality || sub instanceof OWLObjectMaxCardinality);
								
								if(resetRequired)
									break;
							}
						}
						
						if(resetRequired) {
							reset(to);
							addToDoEntries(to);
						}
						/// new code end 
						addLabel(n, to, newCE, ds, false, entries);
						
					}
				}
				/*// if to is nominal node and has atmost restriction then apply NI rule
				if(to.isNominalNode() && to.getLabel().stream().anyMatch(lb -> lb instanceof OWLObjectMaxCardinality)) {
					applyNIRule(to);
				}*/
			}
		}
		else {
			boolean handleClash = false;
			DependencySet clashSet = DependencySet.create();
			System.out.println("size "+entries.size());
			for(ToDoEntry entry: entries) {
				if(!entry.getDs().isEmpty()) {
					handleClash = true;
					System.out.println("max "+entry.getDs().getMax()+" "+ entry.getClassExpression());
					clashSet.add(DependencySet.create(entry.getDs()));
				}
			}
			if(handleClash) {
				if(!clashHandler(clashSet, n))
					isInconsistent(n);
			}
			else
				isInconsistent(n);
		}
	}
	/*private boolean needReset(OWLClassExpression ce, Node n) {
		
		if(ce instanceof OWLObjectMinCardinality || ce instanceof OWLObjectMaxCardinality) {
			OWLObjectPropertyExpression role = ((OWLObjectCardinalityRestriction)ce).getProperty();
			//OWLClassExpression c = ((OWLObjectCardinalityRestriction)ce).getFiller();
			//System.out.println("size"+ n.getSuccEdges().size());
			if(!n.getSuccEdges().isEmpty()) {
				for(Edge e: n.getSuccEdges()) {
					if(e.getLabel().contains(role)) {
						return true;
					}
				}
			}
		}
		return false;
	}*/
	private boolean needReset(OWLClassExpression ce, Node n) {
		if(ce instanceof OWLObjectMinCardinality || ce instanceof OWLObjectMaxCardinality) {
			OWLObjectPropertyExpression role = ((OWLObjectCardinalityRestriction)ce).getProperty();
			OWLClassExpression c = ((OWLObjectCardinalityRestriction)ce).getFiller();
			//System.out.println("size"+ n.getSuccEdges().size());
			
			for(Edge e: n.getOutgoingEdges()) {
				if(e.isSuccEdge() && !e.isReset() && e.getLabel().contains(role) && e.getToNode().getLabel().contains(c)) {
					if(!e.getToNode().isNominalNode() && !e.getToNode().isReset()) {
						return true;
					}
				}
			}
		}
		return false;
	}
	private void addToDoEntries(Node to) {
		List<ConceptNDepSet> cndList = to.getnLabel().getCndList().getCdSet();
		for(ConceptNDepSet cnds : cndList) {
			//System.err.println("add to do entry  " +cnds.getCe());
			
			if(!(cnds.getCe() instanceof OWLObjectIntersectionOf) || !(cnds.getCe() instanceof OWLObjectUnionOf))
				this.addToDoEntry(to, cnds.getCe(), cnds);
		}
		
	}
	private void reset(Node n) {
		System.err.println("reset " + n.getId() +" out edges"+n.getOutgoingEdges().stream().filter(e -> e.isSuccEdge()).count());
		for(Edge e : n.getOutgoingEdges()) {
			System.err.println("n id "+n.getId() +" "+e.isSuccEdge() +" id "+ e.getToNode().getId());
			
			if(e.isSuccEdge() && !e.isReset()) {
				e.setReset(true);
				Node to = e.getToNode();
				//if(!to.isNominalNode()){
					System.err.println("reset to node " + to.getId());
					to.setReset(true);
					if(cg.getEdge(to, n)!=null)
						cg.getEdge(to, n).setReset(true);
					reset(to);
			//	}
			//	if(cg.getEdge(to, n)!=null)
			//		cg.getEdge(to, n).setReset(true);
			}
		}
		/*for(Edge e : n.getOutgoingEdges()) {
			if(e.isPredEdge()) {
			e.setReset(true);
			Node from = e.getFromNode();
			if(!from.isNominalNode()){
				from.setReset(true);
				reset(from);
			}
			}
		}*/
	}
	private Set<OWLObjectPropertyExpression> getAllRoles(Set<OWLObjectPropertyExpression> roles) {
		Set<OWLObjectPropertyExpression> allRoles = new HashSet<>(roles);
		roles.stream().forEach(r -> allRoles.addAll(intl.getOntology().getSuperRoles(r)));
		roles.stream().forEach(r -> allRoles.addAll(intl.getOntology().getInvOfInvSuperRoles(r)));
		
		roles.stream().forEach(r -> allRoles.addAll(intl.getOntology().getInverseOfInverseProperty(r)));
		return allRoles;
	}
	private Set<OWLObjectPropertyExpression> getAllRoles(OWLObjectPropertyExpression role) {
		Set<OWLObjectPropertyExpression> allRoles = new HashSet<>();
		allRoles.add(role);
		allRoles.addAll(intl.getOntology().getSuperRoles(role));
		allRoles.addAll(intl.getOntology().getInvOfInvSuperRoles(role));
		allRoles.addAll(intl.getOntology().getInverseOfInverseProperty(role));
		return allRoles;
	}
	private Set<OWLObjectPropertyExpression> getAllSuperRoles(OWLObjectPropertyExpression role) {
		Set<OWLObjectPropertyExpression> allRoles = new HashSet<>();
		allRoles.addAll(intl.getOntology().getSuperRoles(role));
		allRoles.addAll(intl.getOntology().getInvOfInvSuperRoles(role));
		allRoles.addAll(intl.getOntology().getInverseOfInverseProperty(role));
		return allRoles;
	}
	/*public void callILP(ToDoEntry entry) {
		System.out.println("Calling ILP module...");
		Node n = entry.getNode();
		DependencySet ds = entry.getDs();
		ILPPreprocessor ilpPro = new ILPPreprocessor(entry, this.intl, this.df, n);
		ILPSolution sol = null;
		try {
			sol = ilpPro.callILP();
		} catch (IloException e) {
			e.printStackTrace();
		}
		if(sol.isSolved()) {
			for(EdgeInformation ei : sol.getEdgeInformation()) {
				Set<OWLObjectPropertyExpression> roles = ei.getEdges();
				Edge e = this.cg.findEdge(n, ei.getFillers(), roles);
				Node to = null;
				if(e == null) {
					Node blocker =  findBlocker(n);
					if(blocker != null) {
						cg.setNodeBlocked(n, blocker);
						return;
					}
					if(ei.getFillers().stream().anyMatch(ce -> ce instanceof OWLObjectOneOf)) {
						Set<Node> nomNodes = new HashSet<>();
						for(OWLObjectOneOf filler : ei.getFillers().stream().filter(ce -> ce instanceof OWLObjectOneOf).map(ax -> (OWLObjectOneOf)ax).collect(Collectors.toSet())) {
							OWLClassExpression ci = df.getOWLObjectOneOf(filler.individuals().iterator().next());
							Node nom = findNominalNode(ci);
							if(nom != null) {
								nomNodes.add(nom);
							}
						}
						if(!nomNodes.isEmpty()) {
							if(nomNodes.size()==1) {
								to = nomNodes.iterator().next();
								e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
								//e = this.cg.addEdge(n, to, roles, ds);
							}
							else {
								System.err.println("Sorry! it needs Merging!");
								TestReasoner.getExecutionTime();
								System.exit(0);
							}
						}
						else {
							to =this.cg.addNode(NodeType.NOMINAL);
							addTGAxiom(to, ds);
							e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
							//e = this.cg.addEdge(n, to, roles, ds);
						}
					}
					else {
						to =this.cg.addNode(NodeType.BLOCKABLE);
						addTGAxiom(to, ds);
						e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
						//e = this.cg.addEdge(n, to, roles, ds);
					}
					addLabel(n, to, ei.getFillers(), ds);
				}
				else {
					to = e.getToNode();
					updateEdgeDepSet(ds, e);
					Set<OWLClassExpression> newCE = new HashSet<>();
					for(OWLClassExpression c : ei.getFillers()) {
						if(!to.getLabel().contains(c))
							newCE.add(c);
					}
					if(!newCE.isEmpty())
						addLabel(n, to, newCE, ds);
				}
				
			}
		}
		else {
			isInconsistent(n);
		}
	}*/
	
	private void addLabel(Node from, Node to, Set<OWLClassExpression> fillers, DependencySet ds, boolean newNode, Set<ToDoEntry> entries) {
		if(!newNode) {
			addBackPropagatedConcepts(to, entries, fillers);
		}
		System.out.println("add label : "+to.getId());
		for(OWLClassExpression ce : fillers) {
			System.out.println("add label : "+to.getId() +" "+ ce);
			
			if(isConceptExist(to, ce)) {
				updateConceptDepSet(to, ds, ce);
				if(!((ce instanceof OWLClass) || (ce instanceof OWLObjectOneOf) || (ce instanceof OWLObjectComplementOf)))
					updateToDoEntryDepSet(to, ce, ds);
				else
					to.addSimpleILPLabel(ce);
					//updateToDoEntryDepSet(to, ce, to.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(ce)).iterator().next().getDs());
			}
			else {
				ConceptNDepSet cnds = new ConceptNDepSet(ce,ds);
				System.out.println(ce +" ds "+ ds.getbpList());
				if(ce instanceof OWLObjectOneOf) {
					to.addSimpleILPLabel(ce);
					this.cg.addConceptToNode(to, cnds);
					if(ce.toString().contains("#ni_")) {
						to.makeNINode();
					}
					if(checkClash(to, ce)) {
						DependencySet clashSet = getClashSet(to, ce, ce.getComplementNNF());
						if(!clashSet.isEmpty()) {
							clashSet.setCe(ce);
							clashSet.setCeNNF(ce.getComplementNNF());
							if(!clashHandler(clashSet, to))
								isInconsistent(to);
						}
						else
							isInconsistent(to);
						return;
					}
					/*Set<Set<OWLClassExpression>> djGrp = checkDisjointGroups(to);
					if(!djGrp.isEmpty()) {
						DependencySet clashSet = getClashSet(to, djGrp);
						if(!clashSet.isEmpty()) {
							if(!clashHandler(clashSet))
								isInconsistent(to);
						}
						else
							isInconsistent(to);
						return;
					}*/
				}
				else if(ce instanceof OWLObjectCardinalityRestriction) {
					if(needToAdd((OWLObjectCardinalityRestriction)ce, to)) {
						this.cg.addConceptToNode(to, cnds);
						if(!checkClash(to, ce)) {
							if(needReset(ce,to)) {
								reset(to);
								addToDoEntries(to);
							}
							else
								addToDoEntry(to, ce, cnds);
						}
						else {
							DependencySet clashSet = getClashSet(to, ce, ce.getComplementNNF());
							if(!clashSet.isEmpty()) {
								clashSet.setCe(ce);
								clashSet.setCeNNF(ce.getComplementNNF());
								if(!clashHandler(clashSet, to))
									isInconsistent(to);
							}
							else
								isInconsistent(to);
							return;
						}
					}
				}
				else {
					this.cg.addConceptToNode(to, cnds);
					if(!checkClash(to, ce)) {
					//////	
						if(ce instanceof OWLClass) {
							to.addSimpleLabel(ce);
							to.addSimpleILPLabel(ce);
						}
						else if(ce instanceof OWLObjectComplementOf) {
							to.addSimpleILPLabel(ce);
						}
						else {
							addToDoEntry(to, ce, cnds);
						}
					}
					else {
						DependencySet clashSet = getClashSet(to, ce, ce.getComplementNNF());
						if(!clashSet.isEmpty()) {
							clashSet.setCe(ce);
							clashSet.setCeNNF(ce.getComplementNNF());
							if(!clashHandler(clashSet, to))
								isInconsistent(to);
						}
						else
							isInconsistent(to);
						return;
					}
				}
			}
		}
		applyAbsorption(to, fillers, ds);
		checkAtMost(to);
	//	processAtMost(to);
		if(!newNode)
			processForAll(to);
		//System.out.println("to label "+ to .getLabel());
		
		Edge e = cg.getEdge(from, to);
		if(e != null)
			applyTransitiveRule(from, to, e.getLabel(), ds);
		//processForAll(from);
		
	}
	private void addBackPropagatedConcepts(Node to, Set<ToDoEntry> entries2, Set<OWLClassExpression> fillers) {

		for(ToDoEntry entry : entries2) {
			if(entry.getType().equals(NodeTag.EXISTS)) {
				OWLObjectSomeValuesFrom exist = (OWLObjectSomeValuesFrom) entry.getClassExpression();
				OWLClassExpression fil = exist.getFiller();
				if(fil instanceof OWLClass || fil instanceof OWLObjectOneOf || fil instanceof OWLObjectComplementOf) {
					if(fillers.contains(fil) && !isConceptExist(to, fil)) {
						to.addBackPropagatedLabel(fil);
					}
				}
				else if(fil instanceof OWLObjectIntersectionOf) {
					if(fillers.containsAll(fil.asConjunctSet()) /*&& fil.asConjunctSet().stream().allMatch(cj -> !isConceptExist(to, cj))*/) {
						to.addBackPropagatedLabel(fil);
					}
				}
				else if(fil instanceof OWLObjectUnionOf) {
					if(fil.asDisjunctSet().stream().anyMatch(dj -> fillers.contains(dj))) {
						to.addBackPropagatedLabel(fil);
					}
				}
			}
			else if(entry.getType().equals(NodeTag.LE)) {
				OWLObjectMinCardinality minCard = (OWLObjectMinCardinality) entry.getClassExpression();
				OWLClassExpression fil = minCard.getFiller();
				if(fil instanceof OWLClass || fil instanceof OWLObjectOneOf || fil instanceof OWLObjectComplementOf) {
					if(fillers.contains(fil) && !isConceptExist(to, fil)) {
						to.addBackPropagatedLabel(fil);
					}
				}
				else if(fil instanceof OWLObjectIntersectionOf) {
					if(fillers.containsAll(fil.asConjunctSet()) /*&& fil.asConjunctSet().stream().allMatch(cj -> !isConceptExist(to, cj))*/) {
						to.addBackPropagatedLabel(fil);
					}
				}
				else if(fil instanceof OWLObjectUnionOf) {
					if(fil.asDisjunctSet().stream().anyMatch(dj -> fillers.contains(dj))) {
						to.addBackPropagatedLabel(fil);
					}
				}
			}
			else if(entry.getType().equals(NodeTag.FORALL)) {
				OWLObjectAllValuesFrom forAll = (OWLObjectAllValuesFrom) entry.getClassExpression();
				OWLClassExpression fil = forAll.getFiller();
				if(fil instanceof OWLClass || fil instanceof OWLObjectOneOf || fil instanceof OWLObjectComplementOf) {
					if(fillers.contains(fil) && !isConceptExist(to, fil)) {
						to.addBackPropagatedLabel(fil);
					}
				}
				else if(fil instanceof OWLObjectIntersectionOf) {
					if(fillers.containsAll(fil.asConjunctSet()) /*&& fil.asConjunctSet().stream().allMatch(cj -> !isConceptExist(to, cj))*/) {
						to.addBackPropagatedLabel(fil);
					}
				}
				else if(fil instanceof OWLObjectUnionOf) {
					if(fil.asDisjunctSet().stream().anyMatch(dj -> fillers.contains(dj))) {
						to.addBackPropagatedLabel(fil);
					}
				}
			}
				
		}
		
	}
	private void checkAtMost(Node to) {
		if(to.isNominalNode()){
			Set<ToDoEntry> relatedMaxCardEntries = new HashSet<>();
			Set<ToDoEntry> relatedForAllEntries = new HashSet<>();
			Set<OWLObjectMaxCardinality> mxCards = to.getLabel().stream().filter(ce -> ce instanceof OWLObjectMaxCardinality).map(ce -> (OWLObjectMaxCardinality)ce).collect(Collectors.toSet());
		    for(OWLObjectMaxCardinality mx : mxCards){
		    		ConceptNDepSet cnd = to.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(mx)).iterator().next();
				OWLObjectPropertyExpression role = mx.getProperty();
		    		OWLClassExpression filler = mx.getFiller();
		    		if(to.getOutgoingEdges().stream().anyMatch(e -> e.isPredEdge() && !e.isReset() && e.getLabel().contains(role) 
		    											&& e.getToNode().getLabel().contains(filler) && e.getToNode().isBlockableNode() && !e.getToNode().isReset())) {
		    			List<Edge> outgoingEdges = to.getOutgoingEdges().stream().filter(e -> e.getLabel().contains(role) && e.isSuccEdge() 
		    																		&& e.getToNode().getLabel().contains(filler) && e.getToNode().isNINode()).collect(Collectors.toList());
		    			
		    			if((outgoingEdges.size() == mx.getCardinality()) && this.needToApplyAtMost(to, mx, cnd.getDs())) {
		    				this.atMostNomRule(to, mx);
		    			}
		    			else if(outgoingEdges.size() != mx.getCardinality()){
		    				ToDoEntry mxEntry = new ToDoEntry(to, cnd, NodeTag.GE);
		    				relatedMaxCardEntries.add(mxEntry);
		    				Set<OWLObjectAllValuesFrom> forAll = to.getLabel().stream().filter(ce -> ce instanceof OWLObjectAllValuesFrom).map(ce -> (OWLObjectAllValuesFrom)ce).collect(Collectors.toSet());
		    				for(OWLObjectAllValuesFrom fa : forAll) {
		    					ConceptNDepSet facnd = to.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(fa)).iterator().next();
		    					if(fa.getProperty().equals(role)) {
		    						ToDoEntry faEntry = new ToDoEntry(to, facnd, NodeTag.FORALL);
		    						relatedForAllEntries.add(faEntry);
		    					}
		    				}
		    			    
		    			}
		    		}
		    		else if(to.getOutgoingEdges().stream().anyMatch(e -> e.isPredEdge() && !e.isReset() && e.getLabel().contains(role))) {
		    			ToDoEntry mxEntry = new ToDoEntry(to, cnd, NodeTag.GE);
	    				relatedMaxCardEntries.add(mxEntry);
	    				Set<OWLObjectAllValuesFrom> forAll = to.getLabel().stream().filter(ce -> ce instanceof OWLObjectAllValuesFrom).map(ce -> (OWLObjectAllValuesFrom)ce).collect(Collectors.toSet());
	    				for(OWLObjectAllValuesFrom fa : forAll) {
	    					ConceptNDepSet facnd = to.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(fa)).iterator().next();
	    					if(fa.getProperty().equals(role)){
	    						ToDoEntry faEntry = new ToDoEntry(to, facnd, NodeTag.FORALL);
	    						relatedForAllEntries.add(faEntry);
	    					}
	    				}
		    		}
		    }
		    if(!relatedMaxCardEntries.isEmpty()) {
		    		applyNIRule(to, relatedMaxCardEntries, relatedForAllEntries);
		    }
		}
	}
	private void applyNIRule(Node to, Set<ToDoEntry> relatedMaxCardEntries, Set<ToDoEntry> relatedForAllEntries2) {
		if(isNIRuleApplicable(to)) {
				System.err.println("ni applicable 5");
				addExistentialRestrictions(to);
				addRangeRestrictions(this.axiomRoles.get(to));
				//checkRelatedForAll(to, nodeForAllEntries.get(currNode), this.axiomRoles.get(currNode));
				//checkRelatedMax(currNode, nodeMaxEntries.get(currNode), this.axiomRoles.get(currNode));
				outgoingEdges.clear();
				if(!relatedMaxCardEntries.isEmpty()) {	
					checkOutgoingEdges(to, relatedMaxCardEntries);
				}
				Set<ToDoEntry> entries = new HashSet<>();
				if(!nodeExistEntries.get(to).isEmpty())
					entries.addAll(nodeExistEntries.get(to));
				if(!relatedMaxCardEntries.isEmpty())
					entries.addAll(relatedMaxCardEntries);
				if(!relatedForAllEntries2.isEmpty())
					entries.addAll(relatedForAllEntries2);
				nodeExistEntries.get(to).clear();
				callILP(to, entries, new HashSet<OWLSubClassOfAxiom>(this.niSubAx), outgoingEdges);
				
				axiomRoles.get(to).clear();
				this.niSubAx.clear();
			}
		
	}
	private void checkAtMostOLD(Node to) {
		if(to.isNominalNode()){
			Set<OWLObjectMaxCardinality> mxCards = to.getLabel().stream().filter(ce -> ce instanceof OWLObjectMaxCardinality).map(ce -> (OWLObjectMaxCardinality)ce).collect(Collectors.toSet());
		    for(OWLObjectMaxCardinality mx : mxCards){
		    		ConceptNDepSet cnd = to.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(mx)).iterator().next();
				OWLObjectPropertyExpression role = mx.getProperty();
		    		OWLClassExpression filler = mx.getFiller();
		    		if(to.getOutgoingEdges().stream().anyMatch(e -> e.isPredEdge() && !e.isReset() && e.getLabel().contains(role) 
		    											&& e.getToNode().getLabel().contains(filler) && e.getToNode().isBlockableNode() && !e.getToNode().isReset())) {
		    			List<Edge> outgoingEdges = to.getOutgoingEdges().stream().filter(e -> e.getLabel().contains(role) && e.isSuccEdge() 
		    																		&& e.getToNode().getLabel().contains(filler) && e.getToNode().isNINode()).collect(Collectors.toList());
		    			
		    			if((outgoingEdges.size() == mx.getCardinality()) && this.needToApplyAtMost(to, mx, cnd.getDs())) {
		    				this.atMostNomRule(to, mx);
		    			}
		    			else if(outgoingEdges.size() != mx.getCardinality()){
		    				this.addToDoEntry(to, mx, cnd);
		    				Set<OWLObjectAllValuesFrom> forAll = to.getLabel().stream().filter(ce -> ce instanceof OWLObjectAllValuesFrom).map(ce -> (OWLObjectAllValuesFrom)ce).collect(Collectors.toSet());
		    				for(OWLObjectAllValuesFrom fa : forAll) {
		    					ConceptNDepSet facnd = to.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(fa)).iterator().next();
		    					if(fa.getProperty().equals(role))
		    						this.addToDoEntry(to, fa, facnd);
		    				}
		    			    
		    			}
		    		}
		    		else if(to.getOutgoingEdges().stream().anyMatch(e -> e.isPredEdge() && !e.isReset() && e.getLabel().contains(role))) {
		    			this.addToDoEntry(to, mx, cnd);
	    				Set<OWLObjectAllValuesFrom> forAll = to.getLabel().stream().filter(ce -> ce instanceof OWLObjectAllValuesFrom).map(ce -> (OWLObjectAllValuesFrom)ce).collect(Collectors.toSet());
	    				for(OWLObjectAllValuesFrom fa : forAll) {
	    					ConceptNDepSet facnd = to.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(fa)).iterator().next();
	    					if(fa.getProperty().equals(role))
	    						this.addToDoEntry(to, fa, facnd);
	    				}
		    		}
		    }
		}
	}
	private boolean needToAdd(OWLObjectCardinalityRestriction c, Node to) {
		for(OWLObjectCardinalityRestriction cr : to.getLabel().stream().filter(ce -> ce instanceof OWLObjectCardinalityRestriction).map(ce -> (OWLObjectCardinalityRestriction)ce).collect(Collectors.toSet())) {
			if(cr.equals(c)) {
				return false;
			}
			else if(cr instanceof OWLObjectMinCardinality && c instanceof OWLObjectMinCardinality) {
				if(cr.getProperty().equals(c.getProperty()) && cr.getFiller().equals(c.getFiller())) {
					if(cr.getCardinality() >= c.getCardinality())
						return false;
				}
			}
			else if(cr instanceof OWLObjectMaxCardinality && c instanceof OWLObjectMaxCardinality) {
				if(cr.getProperty().equals(c.getProperty()) && cr.getFiller().equals(c.getFiller())) {
					if(cr.getCardinality() <= c.getCardinality())
						return false;
				}
			}
		}
		return true;
	}
	private void applyAbsorption(Node to, Set<OWLClassExpression> fillers, DependencySet ds) {
		for(OWLClassExpression ce : fillers) {
			if(ce instanceof OWLObjectOneOf) {
				absorbNominal(ce, to, ds);
			}
			else if(ce instanceof OWLClass) {
				absorbRule1(ce, to, ds);
				absorbRule2(to);
			}
			
		}
	}
	/*private void addLabel2(Node from, Node to, Set<OWLClassExpression> fillers, DependencySet ds) {
		for(OWLClassExpression ce : fillers) {
			if(isConceptExist(to, ce)) {
				updateConceptDepSet(to, ds, ce);
				if(!((ce instanceof OWLClass) || (ce instanceof OWLObjectOneOf) || (ce instanceof OWLObjectComplementOf)))
					updateToDoEntryDepSet(to, ce, ds);
					//updateToDoEntryDepSet(to, ce, to.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(ce)).iterator().next().getDs());
			}
			else {
				ConceptNDepSet cnds = new ConceptNDepSet(ce,ds);
				if(ce instanceof OWLObjectOneOf) {
					this.cg.addConceptToNode(to, cnds);
					if(!checkClash(to, ce)) {
						absorbNominal(ce, to, ds);
					}
					else {
						DependencySet clashSet = getClashSet(to, ce, ce.getComplementNNF());
						if(!clashSet.isEmpty()) {
							if(!clashHandler(clashSet))
								isInconsistent(to);
						}
						else
							isInconsistent(to);
						return;
					}
				}
				else {
					this.cg.addConceptToNode(to, cnds);
					if(!checkClash(to, ce)) {
						if(ce instanceof OWLClass) {
							to.addSimpleLabel(ce);
							absorbRule1(ce, to, ds);
							absorbRule2(to);
						}
						else 
							addToDoEntry(to, ce, cnds);
						}
					else {
						DependencySet clashSet = getClashSet(to, ce, ce.getComplementNNF());
						if(!clashSet.isEmpty()) {
							if(!clashHandler(clashSet))
								isInconsistent(to);
						}
						else
							isInconsistent(to);
						return;
					}
				}
			}
		}
		processForAll(to);
		//processForAll(from);
	}*/

	private void addTGAxiom(Node n, DependencySet ds) {
		if(this.tgAxiom != null) {
			ConceptNDepSet cnds = new ConceptNDepSet(tgAxiom, ds);
			cg.addConceptToNode(n, cnds);
			addToDoEntry(n, tgAxiom, cnds);
			//todo.addEntry(n, NodeTag.AND, cnds);
		}
	}
// --- Rule Application ---//	
	public void applyRules(ToDoEntry entry) {
		
		Node n = entry.getNode();
		NodeTag nt = entry.getType();
		switch(nt) {
		case AND:
			System.out.println("Applying 'AND' expansion Rule...");
			applyAndRule(n, (OWLObjectIntersectionOf)entry.getClassExpression(), entry.getDs());
			break;
		case OR:
			System.out.println("Applying 'OR' expansion Rule...");
			applyOrRule(n, (OWLObjectUnionOf)entry.getClassExpression(), entry.getCnds());
			break;
		case EXISTS:
			System.out.println("Applying 'EXISTS' expansion Rule...");
			if(entry.getClassExpression() instanceof OWLObjectSomeValuesFrom)
				applyExistentialRule(n, (OWLObjectSomeValuesFrom)entry.getClassExpression(), entry.getDs());
			else 
				applyExistentialRule(n, (OWLObjectHasValue)entry.getClassExpression(), entry.getDs());
			break;
		case FORALL:
			System.out.println("Applying 'FORALL' expansion Rule...");
			applyForAllRule(n, (OWLObjectAllValuesFrom)entry.getClassExpression(), entry.getDs());
			break;
		case GE:
			System.out.println("Applying 'GE' expansion Rule...");
			applyGERule(n, (OWLObjectMaxCardinality)entry.getClassExpression(), entry.getDs());
			break;
		default:
			break;
		}
		
	}
	
	
	private void applyGERule(Node n, OWLObjectMaxCardinality mc, DependencySet ds) {
		if(n.isNominalNode() && this.needToApplyAtMost(n, mc, ds) && needAtMostNomRule(n, mc)) {
			this.atMostNomRule(n, mc);
			return;
		}
		if(!n.isBlocked() && this.needToApplyAtMost(n, mc, ds)){
		OWLObjectPropertyExpression role = mc.getProperty();
		OWLClassExpression filler = mc.getFiller();
		int cardinality = mc.getCardinality();
		List<Node> otherNodes = new ArrayList<>();
		Map<Node, DependencySet> dsMap = new HashMap<>();
		List<List<Node>> splitNodes = new ArrayList<>();
		List<Node> allNodes = new ArrayList<>();
		int nodesCard = 0;
		int maxCard = 0;
		DependencySet maxDs = DependencySet.create();
		int predEdges = 0;
		
		List<Edge> outgoingEdges =  n.getOutgoingEdges();
		
		/*if(n.isNominalNode()) {
			for(Edge e : outgoingEdges) {
				if(e.isPredEdge() && e.getLabel().contains(role)) {
					Node to = e.getToNode();
					if((to.getLabel().contains(filler) || 
								(filler instanceof OWLObjectIntersectionOf && to.getLabel().containsAll(filler.asConjunctSet())) || 
								(filler instanceof OWLObjectUnionOf && to.getLabel().stream().anyMatch(filler.asDisjunctSet()::contains))) 
							&& !to.isReset()) {
						this.applyNIRule(n, mc, ds);
						this.atMostNomRule(n, mc);
					}
				}
			}
		}
		else if(n.isBlockableNode() ) {*/
			for(Edge e : outgoingEdges) {
				if(e.getLabel().contains(role)) {
					Node to = e.getToNode();
					if((to.getLabel().contains(filler) || 
								(filler instanceof OWLObjectIntersectionOf && to.getLabel().containsAll(filler.asConjunctSet())) || 
								(filler instanceof OWLObjectUnionOf && to.getLabel().stream().anyMatch(filler.asDisjunctSet()::contains))) 
							&& !to.isReset()) {
						if(e.isPredEdge() ) {
							predEdges++;
							otherNodes.add(to);
						}
						else if(e.isSuccEdge()) {
							int card = to.getCardinality();
							nodesCard += card;
							if(maxCard < card) {
								maxCard = card;
								if(filler instanceof OWLObjectIntersectionOf) {
									for(OWLClassExpression cj : filler.asConjunctSet()) {
										maxDs.add(to.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(cj)).iterator().next().getDs());
									}
								}
								else if(filler instanceof OWLObjectUnionOf) {
									for(OWLClassExpression dj : filler.asDisjunctSet()) {
										maxDs.add(to.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(dj)).iterator().next().getDs());
									}
								}
								else {
									maxDs = to.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(filler)).iterator().next().getDs();
									
								}
							}
							otherNodes.add(to);
						}
					}
				}
			}
	//	}
		if(maxCard > cardinality) {
			//FIXME: check dependency set 
			if(!ds.isEmpty() || !maxDs.isEmpty()) {
				System.err.println("mxds "+ maxDs.getMax());
				if(!clashHandler(DependencySet.plus(DependencySet.create(ds), DependencySet.create(maxDs)), n))
					isInconsistent(n);
			}
			else
				isInconsistent(n);
			return;
			
		}
		System.err.println("otherNodes "+ otherNodes.size());
		if(cardinality < (nodesCard + predEdges)) {
				for(Node x : otherNodes) {
					if(x.getCardinality() > 1) {
						List<Node> newNodes = new ArrayList<>();
						for(int i = 0; i < x.getCardinality()-1; i++) {
							//FIXME: check dependency set --- checked 14 sep 2019
							Node newNode = cg.addNode(NodeType.BLOCKABLE, x.getDs());
							newNodes.add(newNode);
							newNode.addDisjointNode(x);
							x.addDisjointNode(newNode);
							
							for(ConceptNDepSet cnds : x.getnLabel().getCndList().getCdSet()) {
								if(cnds != null)
									cg.addConceptToNode(newNode, cnds);
							}
							//newEdges.add(cg.addEdge(from, newNode, e.getLabel(), e.getDepSet(), e.isSuccEdge()));
							for(Edge outE : x.getOutgoingEdges()) {
								cg.addEdge(newNode, outE.getToNode(), outE.getLabel(), outE.getDepSet(), outE.isSuccEdge());
							}
						}
						for(int i = 0; i < newNodes.size(); i++) {
							Node nn = newNodes.get(i);
							for(int k = 0; k < i; k++) {
								nn.addDisjointNode(newNodes.get(k));
							}
							for(int k = i+1; k < newNodes.size(); k++) {
								nn.addDisjointNode(newNodes.get(k));
							}
						}
						
						cg.updateNodeCardinality(x, 1);
						newNodes.add(x);
						splitNodes.add(newNodes);
						allNodes.addAll(newNodes);
					}
					else
						allNodes.add(x);
				}
				
			//needs merging
				System.err.println("splitNodes "+ splitNodes.size() + "cardinality "+ cardinality);
				
			
			while(allNodes.size() > cardinality) {
				for(int i = 0; i < allNodes.size()-1; i++) {
					for(int j = i+1; j < allNodes.size(); j++) {
						if(canMerge(allNodes.get(j), allNodes.get(i))) {
							mergeNodes(allNodes.get(j), allNodes.get(i), ds);
							allNodes.remove(allNodes.get(j));
							if(allNodes.size() <= cardinality)
								break;
						}
					}
					if(allNodes.size() <= cardinality)
						break;
				}
			}
			
			if(allNodes.size() > cardinality) {
				// not able to satisfy at-most restriction
				//FIXME: Check dependencySet ds
				if(!ds.isEmpty()) {
					if(!clashHandler(ds, n))
						isInconsistent(n);
				}
				else
					isInconsistent(n);
				return;
			}
			
		}
		}
	}

	private boolean needAtMostNomRule(Node n, OWLObjectMaxCardinality mx) {
		OWLObjectPropertyExpression role = mx.getProperty();
		OWLClassExpression filler = mx.getFiller();
		List<Edge> outgoingEdges = n.getOutgoingEdges().stream().filter(e -> e.getLabel().contains(role) && e.isSuccEdge() 
																		&& e.getToNode().getLabel().contains(filler) && e.getToNode().isNINode()).collect(Collectors.toList());
			
			if(outgoingEdges.size() == mx.getCardinality()) 
				return true;
			else
			 return false;
	}
	private void applyGERule1(Node n, OWLObjectMaxCardinality mc, DependencySet ds) {
		if(!n.isBlocked() && this.needToApplyAtMost(n, mc, ds)){
		OWLObjectPropertyExpression role = mc.getProperty();
		OWLClassExpression filler = mc.getFiller();
		int cardinality = mc.getCardinality();
		List<Node> otherNodes = new ArrayList<>();
		Map<Node, DependencySet> dsMap = new HashMap<>();
		List<List<Node>> allNodes = new ArrayList<>();
		int nodesCard = 0;
		int maxCard = 0;
		DependencySet maxDs = DependencySet.create();
		int predEdges = 0;
		
		List<Edge> outgoingEdges =  n.getOutgoingEdges();
		
		/*if(n.isNominalNode()) {
			for(Edge e : outgoingEdges) {
				if(e.isPredEdge() && e.getLabel().contains(role)) {
					Node to = e.getToNode();
					if((to.getLabel().contains(filler) || 
								(filler instanceof OWLObjectIntersectionOf && to.getLabel().containsAll(filler.asConjunctSet())) || 
								(filler instanceof OWLObjectUnionOf && to.getLabel().stream().anyMatch(filler.asDisjunctSet()::contains))) 
							&& !to.isReset()) {
						this.applyNIRule(n, mc, ds);
						this.atMostNomRule(n, mc);
					}
				}
			}
		}
		else if(n.isBlockableNode() ) {*/
			for(Edge e : outgoingEdges) {
				if(e.getLabel().contains(role)) {
					Node to = e.getToNode();
					if((to.getLabel().contains(filler) || 
								(filler instanceof OWLObjectIntersectionOf && to.getLabel().containsAll(filler.asConjunctSet())) || 
								(filler instanceof OWLObjectUnionOf && to.getLabel().stream().anyMatch(filler.asDisjunctSet()::contains))) 
							&& !to.isReset()) {
						if(e.isPredEdge() ) {
							predEdges++;
							otherNodes.add(to);
						}
						else if(e.isSuccEdge()) {
							int card = to.getCardinality();
							nodesCard += card;
							if(maxCard < card) {
								maxCard = card;
								if(filler instanceof OWLObjectIntersectionOf) {
									for(OWLClassExpression cj : filler.asConjunctSet()) {
										maxDs.add(to.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(cj)).iterator().next().getDs());
									}
								}
								else if(filler instanceof OWLObjectUnionOf) {
									for(OWLClassExpression dj : filler.asDisjunctSet()) {
										maxDs.add(to.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(dj)).iterator().next().getDs());
									}
								}
								else {
									maxDs = to.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(filler)).iterator().next().getDs();
									
								}
							}
							otherNodes.add(to);
						}
					}
				}
			}
	//	}
		if(maxCard > cardinality) {
			//FIXME: check dependency set 
			if(!ds.isEmpty() || !maxDs.isEmpty()) {
				System.err.println("mxds "+ maxDs.getMax());
				if(!clashHandler(DependencySet.plus(DependencySet.create(ds), DependencySet.create(maxDs)), n))
					isInconsistent(n);
			}
			else
				isInconsistent(n);
			return;
			
		}
		System.err.println("otherNodes "+ otherNodes.size());
		if(cardinality < (nodesCard + predEdges)) {
				for(Node x : otherNodes) {
					if(x.getCardinality() > 1) {
						List<Node> newNodes = new ArrayList<>();
						for(int i = 0; i < x.getCardinality()-1; i++) {
							//FIXME: check dependency set --- checked 14 sep 2019
							Node newNode = cg.addNode(NodeType.BLOCKABLE, x.getDs());
							newNodes.add(newNode);
							newNode.addDisjointNode(x);
							x.addDisjointNode(newNode);
							
							for(ConceptNDepSet cnds : x.getnLabel().getCndList().getCdSet()) {
								cg.addConceptToNode(newNode, cnds);
							}
							//newEdges.add(cg.addEdge(from, newNode, e.getLabel(), e.getDepSet(), e.isSuccEdge()));
							for(Edge outE : x.getOutgoingEdges()) {
								cg.addEdge(newNode, outE.getToNode(), outE.getLabel(), outE.getDepSet(), outE.isSuccEdge());
							}
						}
						for(int i = 0; i < newNodes.size(); i++) {
							Node nn = newNodes.get(i);
							for(int k = 0; k < i; k++) {
								nn.addDisjointNode(newNodes.get(k));
							}
							for(int k = i+1; k < newNodes.size(); k++) {
								nn.addDisjointNode(newNodes.get(k));
							}
						}
						
						cg.updateNodeCardinality(x, 1);
						newNodes.add(x);
						allNodes.add(newNodes);
					}
				}
				
			//needs merging
			int i = 0;
			while(otherNodes.size() > cardinality && i < allNodes.size()) {
				for(int j = 0; j < allNodes.size(); j++) {
					if(i != j) {
						List<Node> node1 = allNodes.get(i);
						List<Node> node2 = allNodes.get(j);
						for(int k = 0; k < node1.size(); k++) {
							for(int l = 0; l < node2.size(); l++) {
								if(canMerge(node1.get(k), node2.get(l))) {
									mergeNodes(node1.get(k), node2.get(l), ds);
									otherNodes.remove(node1.get(k));
									if(otherNodes.size() <= cardinality)
										break;
								}
							}
							if(otherNodes.size() <= cardinality)
								break;
						}
						for(int l = 0; l < node2.size(); l++) {
							processForAll(node2.get(l));
						//	processAtMost(node2.get(l));
						}
					}
					if(otherNodes.size() <= cardinality)
						break;
				}
				i++;
			}
			if(otherNodes.size() > cardinality) {
				// not able to satisfy at-most restriction
				//FIXME: Check dependencySet ds
				if(!ds.isEmpty()) {
					if(!clashHandler(ds, n))
						isInconsistent(n);
				}
				else
					isInconsistent(n);
				return;
			}
			
		}
		/*if(maxCard > cardinality) {
			//FIXME: check dependency set
			if(!ds.isEmpty()) {
				if(!clashHandler(ds))
					isInconsistent(n);
			}
			else
				isInconsistent(n);
			return;
		}
		else {
			for(Edge e : n.getOutgoingEdges()) {
				if(e.getLabel().contains(role) && e.getToNode().getLabel().contains(filler)) {
					Node to = e.getToNode();
					int card = to.getCardinality();
					nodesCard += card;
					if(maxCard < card) {
						maxCard = card;
					}
					otherNodes.add(to);
				}
			}
			if(maxCard > cardinality) {
				//FIXME: check dependency set 
				if(!ds.isEmpty()) {
					if(!clashHandler(ds))
						isInconsistent(n);
				}
				else
					isInconsistent(n);
				return;
				
			}
			if(cardinality < nodesCard) {
				if(maxCard > 1) {
					for(Node x : otherNodes) {
						if(x.getCardinality() > 1) {
							List<Node> newNodes = new ArrayList<>();
							for(int i = 0; i < x.getCardinality()-1; i++) {
								//FIXME: check dependency set
								Node newNode = cg.addNode(NodeType.BLOCKABLE, DependencySet.create());
								newNodes.add(newNode);
								newNode.addDisjointNode(x);
								x.addDisjointNode(newNode);
								
								for(ConceptNDepSet cnds : x.getnLabel().getCndList().getCdSet()) {
									cg.addConceptToNode(newNode, cnds);
								}
								//newEdges.add(cg.addEdge(from, newNode, e.getLabel(), e.getDepSet(), e.isSuccEdge()));
								for(Edge outE : x.getOutgoingEdges()) {
									cg.addEdge(newNode, outE.getToNode(), outE.getLabel(), outE.getDepSet(), outE.isSuccEdge());
								}
							}
							for(int i = 0; i < newNodes.size(); i++) {
								Node nn = newNodes.get(i);
								for(int k = 0; k < i; k++) {
									nn.addDisjointNode(newNodes.get(k));
								}
								for(int k = i+1; k < newNodes.size(); k++) {
									nn.addDisjointNode(newNodes.get(k));
								}
							}
							
							cg.updateNodeCardinality(x, 1);
							newNodes.add(x);
							allNodes.add(newNodes);
							otherNodes.addAll(newNodes);
						}
						
					}
				}
				
				//needs merging
				int i = 0;
				while(otherNodes.size() > cardinality && i < allNodes.size()) {
					for(int j = 0; j < allNodes.size(); j++) {
						if(i != j) {
							List<Node> node1 = allNodes.get(i);
							List<Node> node2 = allNodes.get(j);
							for(int k = 0; k < node1.size(); k++) {
								for(int l = 0; l < node2.size(); l++) {
									if(canMerge(node1.get(k), node2.get(l))) {
										mergeNodes(node1.get(k), node2.get(l), ds);
										otherNodes.remove(node1.get(k));
										if(otherNodes.size() <= cardinality)
											break;
									}
								}
								if(otherNodes.size() <= cardinality)
									break;
							}
							for(int l = 0; l < node2.size(); l++) {
								processForAll(node2.get(l));
								processAtMost(node2.get(l));
							}
						}
						if(otherNodes.size() <= cardinality)
							break;
					}
					i++;
				}
				if(otherNodes.size() > cardinality) {
					// not able to satisfy at-most restriction
					//FIXME: Check dependencySet ds
					if(!ds.isEmpty()) {
						if(!clashHandler(ds))
							isInconsistent(n);
					}
					else
						isInconsistent(n);
					return;
				}
				
			}
		}*/
		}
	}
	private boolean canMerge(Node node, Node node2) {
		if(node.getDisjointNodes().contains(node2)) {
			return false;
		}
		for(OWLClassExpression c :node.getLabel()){
			if(node2.getLabel().contains(c.getComplementNNF())) {
				ConceptNDepSet cnds = node.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(c)).iterator().next();
				ConceptNDepSet cnds2 = node2.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(c.getComplementNNF())).iterator().next();
				if(cnds.getDs().isEmpty() && cnds2.getDs().isEmpty()) {
					return false;
				}
			}
		}
		return true;
	}
	private void applyNIRule(Node to, OWLObjectMaxCardinality mxCard, DependencySet ds1) {
		DependencySet ds = DependencySet.create();
		ds.add(DependencySet.create(ds1));
		OWLObjectPropertyExpression role = mxCard.getProperty();
		OWLClassExpression filler = mxCard.getFiller();
		int cardinality = mxCard.getCardinality();
		for(OWLClassExpression nominal : to.getLabel().stream().filter(ce -> ce instanceof OWLObjectOneOf).map(ce -> (OWLClassExpression)ce).collect(Collectors.toSet())) {
			ds.add(DependencySet.create(to.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(nominal)).iterator().next().getDs()));
		}
			ConceptNDepSet cnd = to.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(mxCard)).iterator().next();
			List<OWLClassExpression> ni = new ArrayList<>();
			for(int i = 0; i < cardinality; i++) {
				ni.add(df.getOWLObjectOneOf(df.getOWLNamedIndividual(IRI.create(base+"#ni_"+niCounter+"_node_"+to.getId()))));
				niCounter++;
			}
			for(int i = 0; i < cardinality; i++) {
				Node n = cg.addNode(NodeType.NOMINAL, DependencySet.plus(DependencySet.create(ds), DependencySet.create(cnd.getDs())));
				this.absorbRule1(df.getOWLThing(), n, DependencySet.plus(DependencySet.create(ds), DependencySet.create(cnd.getDs())));
				addTGAxiom(n, DependencySet.plus(DependencySet.create(ds), DependencySet.create(cnd.getDs())));
				cg.addConceptToNode(n, new ConceptNDepSet(ni.get(i), DependencySet.plus(DependencySet.create(ds), DependencySet.create(cnd.getDs()))));
				cg.addConceptToNode(n, new ConceptNDepSet(filler, DependencySet.plus(DependencySet.create(ds), DependencySet.create(cnd.getDs()))));
				this.addToDoEntry(n, filler, new ConceptNDepSet(filler, DependencySet.plus(DependencySet.create(ds), DependencySet.create(cnd.getDs()))));
				cg.addEdge(to, n, getAllRoles(role), DependencySet.plus(DependencySet.create(ds), DependencySet.create(cnd.getDs()))); 
				for(int k = 0; k < i; k++) {
					cg.addConceptToNode(n, new ConceptNDepSet(ni.get(k).getComplementNNF(), DependencySet.plus(DependencySet.create(ds), DependencySet.create(cnd.getDs()))));
				}
				for(int k = i+1; k < cardinality; k++) {
					cg.addConceptToNode(n, new ConceptNDepSet(ni.get(k).getComplementNNF(), DependencySet.plus(DependencySet.create(ds), DependencySet.create(cnd.getDs()))));
				}
			}
		
	}
	public void applyExistentialRule(Node from, OWLObjectSomeValuesFrom objSV, DependencySet ds) {
		System.out.println("Applying exist Rule...");
		System.out.println("nid: "+from.getId()+" blocked "+ from.isBlocked());
	/*	for(OWLClassExpression oc : from.getLabel()) {
			System.out.println("exist before "+ oc + " ds "+ from.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(oc)).iterator().next().getDs().getbpList());
		}*/
		if(!from.isBlocked()) {
			OWLObjectPropertyExpression role = objSV.getProperty();
			OWLClassExpression filler = objSV.getFiller();
			Edge e = this.cg.getEdge(from, filler, role);
			if(e == null) {
				//System.out.println("nid: "+from.getId()+" role " + role);
				Node blocker =  findBlocker(from);
				if(blocker != null) {
					blockNode(from, blocker);
					//cg.setNodeBlocked(from, blocker);
					return;
				}
				if(filler instanceof OWLObjectOneOf) {
					OWLClassExpression ci = df.getOWLObjectOneOf(((OWLObjectOneOf)filler).individuals().iterator().next());
					Node nom = findNominalNode(ci);
					if(nom != null) {
						e = this.cg.addEdge(from, nom, getAllRoles(role), ds);
						//e = this.cg.addEdge(from, nom, role, ds);
						updateConceptDepSet(nom, ds, ci);
						processForAll(from);
						processForAll(nom);
					//	processAtMost(from);
						processAtMost(nom);
						applyTransitiveRule(from, nom, e.getLabel(), ds);
						
					}
					else {
						Node to =this.cg.addNode(NodeType.NOMINAL, ci, ds);
						this.absorbRule1(df.getOWLThing(), to, ds);
						addTGAxiom(to, ds);
						to.setConceptsDependencies(ci, ds);
						ConceptNDepSet cnds = new ConceptNDepSet(ci, ds);
						e = this.cg.addEdge(from, to, getAllRoles(role), ds);
						//e = this.cg.addEdge(from, to, role, ds);
						this.cg.addConceptToNode(to, cnds);
						processForAll(from);
					//	processAtMost(from);
						absorbNominal(ci, to, ds);
						applyTransitiveRule(from, to, e.getLabel(), ds);
						
					}
				}
				
				else {
					Node to =this.cg.addNode(NodeType.BLOCKABLE, filler, ds);
					this.absorbRule1(df.getOWLThing(), to, ds);
					addTGAxiom(to, ds);
					to.setConceptsDependencies(filler, ds);
					ConceptNDepSet cnds = new ConceptNDepSet(filler, ds);
					e = this.cg.addEdge(from, to, getAllRoles(role), ds);
					//e = this.cg.addEdge(from, to, role, ds);
					this.cg.addConceptToNode(to, cnds);
					processForAll(from);
					//processAtMost(from);
					if(filler instanceof OWLClass ) { 
						to.addSimpleLabel(filler);
						absorbRule1(filler, to, ds);
						absorbRule2(to);
					}
					else 
						addToDoEntry(to, filler, cnds);
					applyTransitiveRule(from, to, e.getLabel(), ds);
				}
			}
			else {
				
				Node to = e.getToNode();
				//System.out.println("nid: "+from.getId()+" nid exists "+to.getId()+" node label " + from.getLabel());
				updateConceptDepSet(to, ds, filler);
				updateEdgeDepSet(ds, e);
				if(!((filler instanceof OWLClass) || (filler instanceof OWLObjectOneOf) || (filler instanceof OWLObjectComplementOf)))
					updateToDoEntryDepSet(to, filler, ds);
					//updateToDoEntryDepSet(to, filler, to.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).iterator().next().getDs());
				
			}
		}
	}
	

	public void applyExistentialRule(Node from, OWLObjectHasValue objSV, DependencySet ds) {
	//	System.out.println("Applying has value Rule...");
		if(!from.isBlocked()) {
		OWLObjectPropertyExpression role = objSV.getProperty();
		OWLClassExpression filler = df.getOWLObjectOneOf(objSV.getFiller());
		Edge e = this.cg.getEdge(from, filler, role);
		
		if(e == null) {
			Node blocker = findBlocker(from);
			if(blocker != null) {
				blockNode(from, blocker);
				//cg.setNodeBlocked(from, blocker);
				return;
			}
			OWLClassExpression ci = df.getOWLObjectOneOf(((OWLObjectOneOf)filler).individuals().iterator().next());
			Node nom = findNominalNode(ci);
			if(nom != null) {
				e = this.cg.addEdge(from, nom, getAllRoles(role), ds);
				//e = this.cg.addEdge(from, nom, role, ds);
				
				updateConceptDepSet(nom, ds, ci);
				processForAll(from);
				processForAll(nom);
				//processAtMost(from);
				processAtMost(nom);
				applyTransitiveRule(from, nom, e.getLabel(), ds);
			}
			else {
				Node to =this.cg.addNode(NodeType.NOMINAL, ci, ds);
				this.absorbRule1(df.getOWLThing(), to, ds);
				addTGAxiom(to, ds);
				to.setConceptsDependencies(ci, ds);
				ConceptNDepSet cnds = new ConceptNDepSet(ci, ds);
				e = this.cg.addEdge(from, to, getAllRoles(role), ds);
				//e = this.cg.addEdge(from, to, role, ds);
				this.cg.addConceptToNode(to, cnds);
				
				processForAll(from);
			//	processAtMost(from);
				absorbNominal(ci, to, ds);
				applyTransitiveRule(from, to, e.getLabel(), ds);
			}
		}
		else {
			Node to = e.getToNode();
			updateConceptDepSet(to, ds, filler);
			updateEdgeDepSet(ds, e);
		}
		}
	}
	private void applyTransitiveRule(Node from, Node to, Set<OWLObjectPropertyExpression> edgeLabel, DependencySet ds) {
		//System.out.println("transitive roles");
		if(!this.transitiveRoles.isEmpty()) {
			for(OWLObjectPropertyExpression role : edgeLabel) {
				//System.out.println("role "+role+" inverse "+ role.getInverseProperty());
				if(this.transitiveRoles.contains(role) || this.transitiveRoles.contains(role.getInverseProperty())) {
					Set<OWLObjectPropertyExpression> supRoles = this.getAllRoles(role);
					for(OWLObjectAllValuesFrom forAll : from.getLabel().stream().filter(l -> l instanceof OWLObjectAllValuesFrom).map(l -> (OWLObjectAllValuesFrom)l).collect(Collectors.toSet())) {
						if(supRoles.contains(forAll.getProperty())) {
							OWLObjectAllValuesFrom fa = df.getOWLObjectAllValuesFrom(role, forAll.getFiller());
							ConceptNDepSet cnds = new ConceptNDepSet(fa, ds);
							this.cg.addConceptToNode(to, cnds);
							if(!checkClash(to, fa)) {
								addToDoEntry(to, fa, cnds);
							}
							else {
								DependencySet clashSet = getClashSet(to, fa, fa.getComplementNNF());
								if(!clashSet.isEmpty()) {
									clashSet.setCe(fa);
									clashSet.setCeNNF(fa.getComplementNNF());
									if(!clashHandler(clashSet, to))
										isInconsistent(to);
								}
								else
									isInconsistent(to);
								return;
							}
						}
					}
				}
			}
		}
	} 
	public void applyResetRule() {
		
	}

	public void applyNIRule(Node to) {
		DependencySet ds = DependencySet.create();
		for(OWLClassExpression nominal : to.getLabel().stream().filter(ce -> ce instanceof OWLObjectOneOf).map(ce -> (OWLClassExpression)ce).collect(Collectors.toSet())) {
			ds.add(DependencySet.create(to.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(nominal)).iterator().next().getDs()));
		}
		
		for(OWLObjectMaxCardinality mxCard : to.getLabel().stream().filter(ce -> ce instanceof OWLObjectMaxCardinality).map(ce -> (OWLObjectMaxCardinality)ce).collect(Collectors.toSet())) {
			OWLObjectPropertyExpression role = mxCard.getProperty();
			OWLClassExpression filler = mxCard.getFiller();
			int cardinality = mxCard.getCardinality();
			ConceptNDepSet cnd = to.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(mxCard)).iterator().next();
			List<OWLClassExpression> ni = new ArrayList<>();
			for(int i = 0; i < cardinality; i++) {
				ni.add(df.getOWLObjectOneOf(df.getOWLNamedIndividual(IRI.create(base+"#ni_"+niCounter+"_node_"+to.getId()))));
				niCounter++;
			}
			for(int i = 0; i < cardinality; i++) {
				Node n = cg.addNode(NodeType.NOMINAL, DependencySet.plus(DependencySet.create(ds), DependencySet.create(cnd.getDs())));
				this.absorbRule1(df.getOWLThing(), n, DependencySet.plus(DependencySet.create(ds), DependencySet.create(cnd.getDs())));
				addTGAxiom(n, DependencySet.plus(DependencySet.create(ds), DependencySet.create(cnd.getDs())));
				cg.addConceptToNode(n, new ConceptNDepSet(ni.get(i), DependencySet.plus(DependencySet.create(ds), DependencySet.create(cnd.getDs()))));
				cg.addConceptToNode(n, new ConceptNDepSet(filler, DependencySet.plus(DependencySet.create(ds), DependencySet.create(cnd.getDs()))));
				this.addToDoEntry(n, filler, new ConceptNDepSet(filler, DependencySet.plus(DependencySet.create(ds), DependencySet.create(cnd.getDs()))));
				cg.addEdge(to, n, getAllRoles(role), DependencySet.plus(DependencySet.create(ds), DependencySet.create(cnd.getDs()))); 
				for(int k = 0; k < i; k++) {
					cg.addConceptToNode(n, new ConceptNDepSet(ni.get(k).getComplementNNF(), DependencySet.plus(DependencySet.create(ds), DependencySet.create(cnd.getDs()))));
				}
				for(int k = i+1; k < cardinality; k++) {
					cg.addConceptToNode(n, new ConceptNDepSet(ni.get(k).getComplementNNF(), DependencySet.plus(DependencySet.create(ds), DependencySet.create(cnd.getDs()))));
				}
			}
		}
		
	}
	public void applyAtMostNomRule(Node n) {
		Set<OWLObjectMaxCardinality> maxCards = n.getLabel().stream().filter(ce -> ce instanceof OWLObjectMaxCardinality).map(ce -> (OWLObjectMaxCardinality)ce).collect(Collectors.toSet());
		for(OWLObjectMaxCardinality mc : maxCards) {
			atMostNomRule(n, mc);
		}
	}
	public void atMostNomRule(Node n, OWLObjectMaxCardinality mc) {
		DependencySet ds = n.getnLabel().getCndList().getCdSet().stream().filter(ce -> ce.getCe().equals(mc)).iterator().next().getDs();
		OWLObjectPropertyExpression role = mc.getProperty();
		OWLClassExpression filler = mc.getFiller();
		int cardinality = mc.getCardinality();
		List<Node> niNodes = new ArrayList<>();
		List<Node> otherNodes = new ArrayList<>();
		int nodesCard = 0;
		int maxCard = 0;
		DependencySet maxDs = DependencySet.create();
		
		for(Edge e : n.getOutgoingEdges()) {
			if(e.getLabel().contains(role) && !e.isReset()) {
				Node to = e.getToNode();
				if((to.getLabel().contains(filler) || 
						(filler instanceof OWLObjectIntersectionOf && to.getLabel().containsAll(filler.asConjunctSet())) || 
						(filler instanceof OWLObjectUnionOf && to.getLabel().stream().anyMatch(filler.asDisjunctSet()::contains))) 
						&& !to.isReset()) {
					int card = to.getCardinality();
					nodesCard += card;
					if(maxCard < card) {
						maxCard = card;
						if(filler instanceof OWLObjectIntersectionOf) {
							for(OWLClassExpression cj : filler.asConjunctSet()) {
								maxDs.add(to.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(cj)).iterator().next().getDs());
							}
						}
						else if(filler instanceof OWLObjectUnionOf) {
							for(OWLClassExpression dj : filler.asDisjunctSet()) {
								maxDs.add(to.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(dj)).iterator().next().getDs());
							}
						}
						else {
							maxDs = to.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(filler)).iterator().next().getDs();
							
						}
					}
					if(to.isNINode()) {
						niNodes.add(to);
					}
					else {
						otherNodes.add(to);
					}
				}/*
				if(to.getLabel().contains(filler) && !to.isReset()) {
					int card = to.getCardinality();
					nodesCard += card;
					if(maxCard < card) {
						maxCard = card;
						maxDs = DependencySet.create(to.getnLabel().getCndList().getCdSet().stream().filter(ce -> ce.getCe().equals(filler)).iterator().next().getDs());
					}
					if(to.isNINode()) {
						niNodes.add(to);
					}
					else {
						otherNodes.add(to);
					}
				}*/
			}
		}
		if(maxCard > cardinality) {
			//FIXME: check dependency set 
			DependencySet clashSet = DependencySet.plus(DependencySet.create(ds), maxDs);
			if(!clashSet.isEmpty()) {
				if(!clashHandler(clashSet, n))
					isInconsistent(n);
			}
			else
				isInconsistent(n);
			return;
			
		}
		if(cardinality < nodesCard) {
			if(maxCard > 1) {
				List<Node> allNewNodes = new ArrayList<>();
				for(Node x : otherNodes) {
					if(x.getCardinality() > 1) {
						List<Node> newNodes = new ArrayList<>();
						for(int i = 0; i < x.getCardinality()-1; i++) {
							Node newNode = cg.addNode(NodeType.BLOCKABLE, ds);
							//this.absorbRule1(df.getOWLThing(), newNode, ds);
							newNodes.add(newNode);
							newNode.addDisjointNode(x);
							x.addDisjointNode(newNode);
							
							for(ConceptNDepSet cnds : x.getnLabel().getCndList().getCdSet()) {
								cg.addConceptToNode(newNode, cnds);
							}
							//newEdges.add(cg.addEdge(from, newNode, e.getLabel(), e.getDepSet(), e.isSuccEdge()));
							for(Edge outE : x.getOutgoingEdges()) {
								cg.addEdge(newNode, outE.getToNode(), outE.getLabel(), outE.getDepSet(), outE.isSuccEdge());
							}
						}
						for(int i = 0; i < newNodes.size(); i++) {
							Node nn = newNodes.get(i);
							for(int k = 0; k < i; k++) {
								nn.addDisjointNode(newNodes.get(k));
							}
							for(int k = i+1; k < newNodes.size(); k++) {
								nn.addDisjointNode(newNodes.get(k));
							}
						}
						
						cg.updateNodeCardinality(x, 1);
						allNewNodes.addAll(newNodes);
					}
					
				}
				otherNodes.addAll(allNewNodes);
			}
			
			//needs merging
		//	System.err.println("otherNodes.size() "+otherNodes.size() +" ni.size "+niNodes.size());
			 
			int i = 0;
			while(i < otherNodes.size()) {
				for(int j = 0; j < niNodes.size(); j++) {
					if(i < otherNodes.size()){
					//	System.err.println("merging...");
					//	System.err.println( otherNodes.get(i).getId()+ "into" +niNodes.get(j).getId() );
						this.mergeNodes(otherNodes.get(i), niNodes.get(j), ds);
						i++;
					}
					else
						break;
				}
				for(int l = 0; l < niNodes.size(); l++) {
					processForAll(niNodes.get(l));
				//	processAtMost(niNodes.get(l));
				}
			}
		}
		
			
			
		
		
	}
	
	public void applyForAllRule(Node from, OWLObjectAllValuesFrom objAV, DependencySet ds) {
		System.out.println("Applying for all Rule..." + from.getId());
		if(!from.isBlocked()) {
			OWLObjectPropertyExpression role = objAV.getProperty();
			OWLClassExpression filler = objAV.getFiller();
			//System.out.println("outgoing edges: "+ from.getOutgoingEdges().size());
			//System.out.println("incoming edges: "+ from.getIncomingEdges().size());
			Set<Edge> edges = this.cg.getEdge(from, role);
		//	Set<Edge> newEdges = new HashSet<>();
			if(edges.size()!=0) {
				boolean hasNominal = this.hasNominal(filler);
				for(Edge e : edges) {
					Node n = e.getToNode();
					int nodeCard = n.getCardinality();
					/// FIXME : reset in case of nominal propagation 
					if(hasNominal && nodeCard > 1) {
						reset(n);
						this.splitNode(n);
						return;
					/*	List<Node> newNodes = new ArrayList<>();
						for(int i = 0; i < nodeCard-1; i++) {
							Node newNode = cg.addNode(NodeType.BLOCKABLE, ds);
						//	this.absorbRule1(df.getOWLThing(), newNode, ds);
							newNodes.add(newNode);
							newNode.addDisjointNode(n);
							n.addDisjointNode(newNode);
							
							for(ConceptNDepSet cnds : n.getnLabel().getCndList().getCdSet()) {
								cg.addConceptToNode(newNode, cnds);
							}
							//newEdges.add(cg.addEdge(from, newNode, e.getLabel(), e.getDepSet(), e.isSuccEdge()));
							for(Edge outE : n.getOutgoingEdges()) {
								newEdges.add(cg.addEdge(newNode, outE.getToNode(), outE.getLabel(), outE.getDepSet(), outE.isSuccEdge()));
							}
						}
						for(int i = 0; i < newNodes.size(); i++) {
							Node nn = newNodes.get(i);
							for(int k = 0; k < i; k++) {
								nn.addDisjointNode(newNodes.get(k));
							}
							for(int k = i+1; k < newNodes.size(); k++) {
								nn.addDisjointNode(newNodes.get(k));
							}
						}
						
						cg.updateNodeCardinality(n, 1);*/
					}
				}
			}
			
		//	edges.addAll(newEdges);
			if(edges.size()!=0) {
			for(Edge e : edges) {
				Node n = e.getToNode();
					boolean flag = false;
					if(isConceptExist(n, filler)) {
						flag = true;
						updateConceptDepSet(n, updateDepSetForAll(e, ds), filler);
						if(!((filler instanceof OWLClass) || (filler instanceof OWLObjectOneOf) || (filler instanceof OWLObjectComplementOf)))
							updateToDoEntryDepSet(n, filler, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).iterator().next().getDs());
					}
					/*else if(filler instanceof OWLObjectUnionOf) {
						for(OWLClassExpression dj : filler.asDisjunctSet()) {
							if(isConceptExist(n, dj)) {
								flag  = true;
								updateConceptDepSet(n, updateDepSetForAll(e, ds), dj);
								if(!(dj instanceof OWLClass))
									updateToDoEntryDepSet(n, dj, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(dj)).iterator().next().getDs());
								break;
							}
							
						}
					}*/
					else if(filler instanceof OWLObjectOneOf) {
						flag = true;
						OWLClassExpression ci = df.getOWLObjectOneOf(((OWLObjectOneOf)filler).individuals().iterator().next());
						Node nom = findNominalNode(ci);
						DependencySet depSet =  updateDepSetForAll(e, ds);
						ConceptNDepSet cnds = new ConceptNDepSet(filler, depSet);
						if(nom == null) {
							this.cg.addConceptToNode(n, cnds);
							cg.checkBlockedStatus(n);
							if(n.getCardinality()>1) {
								System.err.println("cannot make nomial node");
							}
							n.makeNominalNode();
							if(!checkClash(n, filler)) {
								absorbNominal(filler, n, depSet);
								Set<Node> resetNodes = needNomPredReset(n);
								System.err.println("# of pred reset nodes " +resetNodes.size());
								if(!resetNodes.isEmpty()) {
									for(Node resetNode : resetNodes) {
										reset(resetNode);
										splitNode(resetNode);
									}
									return;
								}
								if(needNomReset(n)) {
									reset(n);
									this.addToDoEntries(n);
									return;
								}
								//this.processAtMost(n);
							}
							else {
								DependencySet clashSet = getClashSet(n, filler, filler.getComplementNNF());
								if(!clashSet.isEmpty()) {
									clashSet.setCe(filler);
									clashSet.setCeNNF(filler.getComplementNNF());
									if(!clashHandler(clashSet, n))
										isInconsistent(n);
								}
								else
									isInconsistent(n);
								return;
							}
						}
						else {
							if(nom.equals(n)) {
								updateConceptDepSet(n, depSet, filler);
							}
							else {
								System.out.println("Needs Merging! " );//+ n.getId() + " into "+nom.getId());
							//	if(n.getLabel().size() < nom.getLabel().size())
									mergeNodes(n, nom, filler, depSet);
							//	else
							//		mergeNodes2(nom, n, filler, depSet);
								////  new code 27-oct-2019
									reset(nom);
									this.addToDoEntries(nom);
									return;
									////
									
							//	processForAll(nom);
							//	processAtMost(nom);
							}
							/*System.err.println("Sorry! it needs Merging!");
							Main.getExecutionTime();
							System.exit(0);*/
						}
					}
					else if(filler instanceof OWLObjectCardinalityRestriction) {
						flag = true;
						if(needToAdd((OWLObjectCardinalityRestriction)filler, n)) {
							DependencySet depSet =  updateDepSetForAll(e, ds);
							ConceptNDepSet cnds = new ConceptNDepSet(filler, depSet);
							this.cg.addConceptToNode(n, cnds);
							if(!checkClash(n, filler)) {
								if(needReset(filler,n)) {
									reset(n);
									addToDoEntries(n);
								}
								else
									addToDoEntry(n, filler, cnds);
							}
							else {
								DependencySet clashSet = getClashSet(n, filler, filler.getComplementNNF());
								if(!clashSet.isEmpty()) {
									clashSet.setCe(filler);
									clashSet.setCeNNF(filler.getComplementNNF());
									if(!clashHandler(clashSet, n))
										isInconsistent(n);
								}
								else
									isInconsistent(n);
								return;
							}
						}
					}
					if(!flag) {
						//// 25-Oct-2019
						if(e.isPredEdge()) {
							n.addBackPropagatedLabel(filler);
						}
						////
						DependencySet depSet =  updateDepSetForAll(e, ds);
						ConceptNDepSet cnds = new ConceptNDepSet(filler, depSet);
						this.cg.addConceptToNode(n, cnds);
						//cg.checkBlockedStatus(n);
						if(!checkClash(n, filler)) {
							if(filler instanceof OWLClass) {
								n.addSimpleLabel(filler);
								absorbRule1(filler, n, depSet);
								absorbRule2(n);
							}
							else {
								addToDoEntry(n, filler, cnds);
							}
								
						}
						else {
							//System.out.println("clash "+ filler.getComplementNNF() + ""+ n.getnLabel().getCndList().getCdSet().stream().filter(cn -> cn.getCe().equals(filler.getComplementNNF())).iterator().next().getDs().getbpList());
							DependencySet clashSet = getClashSet(n, filler, filler.getComplementNNF());
							if(!clashSet.isEmpty()) {
								clashSet.setCe(filler);
								clashSet.setCeNNF(filler.getComplementNNF());
								if(!clashHandler(clashSet, n))
									isInconsistent(n);
							}
							else
								isInconsistent(n);
							return;
								
						}
					}
				}
			}
		}
		//else we cannot apply forAll rule
	}
	
	private Set<Node> needNomPredReset(Node n) {
		Set<Node> nodesToReset = new HashSet<>();
		if(n.isNominalNode()) {
			for(OWLObjectOneOf nominal : n.getLabel().stream().filter(ce -> ce instanceof OWLObjectOneOf).map(ce -> (OWLObjectOneOf)ce).collect(Collectors.toSet())) {
				ConceptNDepSet cnd = n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(nominal)).iterator().next();
				if(cnd.getDs().isEmpty())
					return nodesToReset;
			}
			for(OWLObjectMaxCardinality mc : n.getLabel().stream().filter(ce -> ce instanceof OWLObjectMaxCardinality).map(ce -> (OWLObjectMaxCardinality)ce).collect(Collectors.toSet())) {
				OWLObjectPropertyExpression role = mc.getProperty();
				OWLClassExpression filler = mc.getFiller();
				int cardinality = mc.getCardinality();
				for(Edge e : n.getOutgoingEdges()) {
					if(!e.isReset() && e.getLabel().contains(role)) {
						Node to = e.getToNode();
						if((to.getLabel().contains(filler) || 
								(filler instanceof OWLObjectIntersectionOf && to.getLabel().containsAll(filler.asConjunctSet())) || 
								(filler instanceof OWLObjectUnionOf && to.getLabel().stream().anyMatch(filler.asDisjunctSet()::contains))) 
								&& !to.isReset()) {
							System.err.println("to "+ to.getId() +" card "+to.getCardinality());
							if(cardinality < to.getCardinality()) {
								nodesToReset.add(to);
							}
						}
					}
				}
			}
		}
		return nodesToReset;
	}
	
	private boolean needNomReset(Node n) {
		if(n.getLabel().stream().anyMatch(ce -> ce instanceof OWLObjectMaxCardinality)) {
			for(OWLObjectMaxCardinality mxCard : n.getLabel().stream().filter(ce -> ce instanceof OWLObjectMaxCardinality).map(ce -> (OWLObjectMaxCardinality)ce).collect(Collectors.toSet())) {
				OWLObjectPropertyExpression role = mxCard.getProperty();
				if(n.getOutgoingEdges().stream().anyMatch(e-> !e.isReset() && e.getLabel().contains(role))) {
					return true;
				}
			}
		}
		return false;
	}
	private void processAtMost(Node n) {
		System.out.println("process at most"+ n.getId());
		if(needToApplyAtMost(n)) {

			//System.err.println("mxds ");
		/*if(n.isNominalNode() && n.getLabel().stream().anyMatch(ce -> ce instanceof OWLObjectMaxCardinality) && n.getOutgoingEdges().stream().anyMatch(e -> e.isPredEdge())) {
			if(isNIRuleApplicable(n))
				this.applyNIRule(n);
			this.applyAtMostNomRule(n);
		}
		else*/
			if(n.getLabel().stream().anyMatch(ce -> ce instanceof OWLObjectMaxCardinality)) {
			for(OWLObjectMaxCardinality mxCard : n.getLabel().stream().filter(ce -> ce instanceof OWLObjectMaxCardinality).map(ce -> (OWLObjectMaxCardinality)ce).collect(Collectors.toSet())) {
				ConceptNDepSet cnd = n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(mxCard)).iterator().next();
				
				this.applyGERule(n, mxCard, cnd.getDs());	
			}
		}
		}
	}
	private void processAtMost(Node n, DependencySet ds) {
		System.out.println("process at most"+ n.getId());
		if(needToApplyAtMost(n)) {

			//System.err.println("mxds ");
		/*if(n.isNominalNode() && n.getLabel().stream().anyMatch(ce -> ce instanceof OWLObjectMaxCardinality) && n.getOutgoingEdges().stream().anyMatch(e -> e.isPredEdge())) {
			if(isNIRuleApplicable(n))
				this.applyNIRule(n);
			this.applyAtMostNomRule(n);
		}*/
		//else 
			if(n.getLabel().stream().anyMatch(ce -> ce instanceof OWLObjectMaxCardinality)) {
			for(OWLObjectMaxCardinality mxCard : n.getLabel().stream().filter(ce -> ce instanceof OWLObjectMaxCardinality).map(ce -> (OWLObjectMaxCardinality)ce).collect(Collectors.toSet())) {
				ConceptNDepSet cnd = n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(mxCard)).iterator().next();
				
				this.applyGERule(n, mxCard, cnd.getDs());	
			}
		}
		}
	}
	private boolean needToApplyAtMost(Node n) {
		if(n.isNominalNode()) {
			for(OWLObjectMaxCardinality mc : n.getLabel().stream().filter(ce -> ce instanceof OWLObjectMaxCardinality).map(ce -> (OWLObjectMaxCardinality)ce).collect(Collectors.toSet())) {
				DependencySet ds = n.getnLabel().getCndList().getCdSet().stream().filter(ce -> ce.getCe().equals(mc)).iterator().next().getDs();
				
				OWLObjectPropertyExpression role = mc.getProperty();
				OWLClassExpression filler = mc.getFiller();
				int cardinality = mc.getCardinality();
				int nodesCard = 0;
				int maxCard = 0;
				DependencySet maxDs = DependencySet.create();
				for(Edge e : n.getOutgoingEdges()) {
					if(!e.isReset() && e.getLabel().contains(role)) {
						Node to = e.getToNode();
						if((to.getLabel().contains(filler) || 
								(filler instanceof OWLObjectIntersectionOf && to.getLabel().containsAll(filler.asConjunctSet())) || 
								(filler instanceof OWLObjectUnionOf && to.getLabel().stream().anyMatch(filler.asDisjunctSet()::contains))) 
								&& !to.isReset()) {
					//	System.err.println("to "+ to.getId());
						int card = to.getCardinality();
						nodesCard += card;
						if(maxCard < card) {
							maxCard = card;
							if(filler instanceof OWLObjectIntersectionOf) {
								for(OWLClassExpression cj : filler.asConjunctSet()) {
									maxDs.add(to.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(cj)).iterator().next().getDs());
								}
							}
							else if(filler instanceof OWLObjectUnionOf) {
								for(OWLClassExpression dj : filler.asDisjunctSet()) {
									maxDs.add(to.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(dj)).iterator().next().getDs());
								}
							}
							else {
								maxDs = to.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(filler)).iterator().next().getDs();
								
							}
						}
					}
				}
				}

				if(maxCard > cardinality) {
					System.err.println("mxds "+ maxDs.getMax() +" "+filler);
					//FIXME: check dependency set 
					if(!ds.isEmpty() || !maxDs.isEmpty()) {
						System.err.println("mxds "+ maxDs.getMax() +" "+filler);
						if(!clashHandler(DependencySet.plus(DependencySet.create(ds), DependencySet.create(maxDs)), n))
							isInconsistent(n);
					}
					else
						isInconsistent(n);
					return false;
					
				}
				if(cardinality < nodesCard) {
					return true;
				}
			}
			return false;
		}
		else {
		for(OWLObjectMaxCardinality mc : n.getLabel().stream().filter(ce -> ce instanceof OWLObjectMaxCardinality).map(ce -> (OWLObjectMaxCardinality)ce).collect(Collectors.toSet())) {
			DependencySet ds = n.getnLabel().getCndList().getCdSet().stream().filter(ce -> ce.getCe().equals(mc)).iterator().next().getDs();
			
			OWLObjectPropertyExpression role = mc.getProperty();
			OWLClassExpression filler = mc.getFiller();
			int cardinality = mc.getCardinality();
			int nodesCard = 0;
			int maxCard = 0;
			DependencySet maxDs = DependencySet.create();
			for(Edge e : n.getOutgoingEdges()) {
				if(!e.isReset() && e.getLabel().contains(role) ) {
					Node to = e.getToNode();
					if((to.getLabel().contains(filler) || 
							(filler instanceof OWLObjectIntersectionOf && to.getLabel().containsAll(filler.asConjunctSet())) || 
							(filler instanceof OWLObjectUnionOf && to.getLabel().stream().anyMatch(filler.asDisjunctSet()::contains))) 
							&& !to.isReset()) {
						if(e.isPredEdge()) {
							nodesCard++;
						}
						else {
							
							System.err.println("to "+ to.getId());
							int card = to.getCardinality();
							nodesCard += card;
							if(maxCard < card) {
								maxCard = card;
								if(filler instanceof OWLObjectIntersectionOf) {
									for(OWLClassExpression cj : filler.asConjunctSet()) {
										maxDs.add(to.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(cj)).iterator().next().getDs());
									}
								}
								else if(filler instanceof OWLObjectUnionOf) {
									for(OWLClassExpression dj : filler.asDisjunctSet()) {
										maxDs.add(to.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(dj)).iterator().next().getDs());
									}
								}
								else {
									maxDs = to.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(filler)).iterator().next().getDs();
									
								}
							}
						}
					}
				}
			}

			if(maxCard > cardinality) {
				System.err.println("mxds "+ maxDs.getMax() +" "+filler);
				//FIXME: check dependency set 
				if(!ds.isEmpty() || !maxDs.isEmpty()) {
					System.err.println("mxds "+ maxDs.getMax() +" "+filler);
					if(!clashHandler(DependencySet.plus(DependencySet.create(ds), DependencySet.create(maxDs)), n))
						isInconsistent(n);
				}
				else
					isInconsistent(n);
				return false;
				
			}
			if(cardinality < nodesCard) {
				return true;
			}
		}
		return false;
		}
	}
	private boolean needToApplyAtMost(Node n, OWLObjectMaxCardinality mc, DependencySet ds) {
		if(n.isNominalNode()) {
			OWLObjectPropertyExpression role = mc.getProperty();
				OWLClassExpression filler = mc.getFiller();
				int cardinality = mc.getCardinality();
				int nodesCard = 0;
				int maxCard = 0;
				DependencySet maxDs = DependencySet.create();
				for(Edge e : n.getOutgoingEdges()) {
					if(!e.isReset() && e.getLabel().contains(role) && e.getToNode().getLabel().contains(filler)) {
						Node to = e.getToNode();
						//System.err.println("to "+ to.getId());
						int card = to.getCardinality();
						nodesCard += card;
						if(maxCard < card) {
							maxCard = card;
							maxDs = to.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(filler)).iterator().next().getDs();
							
						}
					}
				}

				if(maxCard > cardinality) {
					//System.err.println("mxds "+ maxDs.getMax() +" "+filler);
					//FIXME: check dependency set 
					if(!ds.isEmpty() || !maxDs.isEmpty()) {
					//	System.err.println("mxds "+ maxDs.getMax() +" "+filler);
						if(!clashHandler(DependencySet.plus(DependencySet.create(ds), DependencySet.create(maxDs)), n))
							isInconsistent(n);
					}
					else
						isInconsistent(n);
					return false;
					
				}
				if(cardinality < nodesCard) {
					return true;
				}
			return false;
		}
		else {
			OWLObjectPropertyExpression role = mc.getProperty();
			OWLClassExpression filler = mc.getFiller();
			int cardinality = mc.getCardinality();
			int nodesCard = 0;
			int maxCard = 0;
			DependencySet maxDs = DependencySet.create();
			for(Edge e : n.getOutgoingEdges()) {
				if(!e.isReset() && e.getLabel().contains(role) && e.getToNode().getLabel().contains(filler)) {
					if(e.isPredEdge()) {
						nodesCard++;
					}
					else {
						Node to = e.getToNode();
						//System.err.println("to "+ to.getId());
						int card = to.getCardinality();
						nodesCard += card;
						if(maxCard < card) {
							maxCard = card;
							maxDs = to.getnLabel().getCndList().getCdSet().stream().filter(cnd -> cnd.getCe().equals(filler)).iterator().next().getDs();
							
						}
					}
				}
			}

			if(maxCard > cardinality) {
				//System.err.println("mxds "+ maxDs.getMax() +" "+filler);
				//FIXME: check dependency set 
				if(!ds.isEmpty() || !maxDs.isEmpty()) {
					//System.err.println("mxds "+ maxDs.getMax() +" "+filler);
					if(!clashHandler(DependencySet.plus(DependencySet.create(ds), DependencySet.create(maxDs)), n))
						isInconsistent(n);
				}
				else
					isInconsistent(n);
				return false;
				
			}
			if(cardinality < nodesCard) {
				return true;
			}
		return false;
		}
	}
	public void applyAndRule(Node n1, OWLObjectIntersectionOf objIn, DependencySet ds) {
	//	System.out.println("Applying and Rule...");
		Node n = n1;
		if(!n.isBlocked()) {
			for(OWLClassExpression ce : objIn.asConjunctSet()) {
			//	System.out.println("AND RULE ce "+ ce);
				boolean flag = false;
				if(isConceptExist(n, ce)) {
					flag = true;
					updateConceptDepSet(n, ds, ce);
					if(!(ce instanceof OWLClass || ce instanceof OWLObjectOneOf || ce instanceof OWLObjectComplementOf))
						updateToDoEntryDepSet(n, ce, ds);
						//updateToDoEntryDepSet(n, ce, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(ce)).iterator().next().getDs());
				}
				/*else if(ce instanceof OWLObjectUnionOf) {
					for(OWLClassExpression dj : ce.asDisjunctSet()) {
						if(isConceptExist(n, dj)) {
							flag = true;
							updateConceptDepSet(n, ds, dj);
							if(!(dj instanceof OWLClass || dj instanceof OWLObjectOneOf || dj instanceof OWLObjectComplementOf))
								updateToDoEntryDepSet(n, dj, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(dj)).iterator().next().getDs());
							break;
						}
						
					}
				}*/
				if(!flag) {
					ConceptNDepSet cnds = new ConceptNDepSet(ce,ds);
					if(ce instanceof OWLObjectOneOf) {
						Node mergeN = processNominal(ce, n, cnds, ds);
						if( mergeN != null) {
							n = mergeN; // remaining conjuncts will be applied on merged node
							processForAll(n);
							//processAtMost(n);
						}
						else
							return;
					}
					else if(ce instanceof OWLObjectCardinalityRestriction) {
						if(needToAdd((OWLObjectCardinalityRestriction)ce, n)) {
							this.cg.addConceptToNode(n, cnds);
							if(!checkClash(n, ce)) {
								if(needReset(ce,n)) {
									reset(n);
									addToDoEntries(n);
								}
								else
									addToDoEntry(n, ce, cnds);
							}
							else {
								DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
								if(!clashSet.isEmpty()) {
									clashSet.setCe(ce);
									clashSet.setCeNNF(ce.getComplementNNF());
									if(!clashHandler(clashSet, n))
										isInconsistent(n);
								}
								else
									isInconsistent(n);
								return;
							}
						}
					}
					else {
						this.cg.addConceptToNode(n, cnds);
						if(!checkClash(n, ce)) {
							if(ce instanceof OWLClass) {
								n.addSimpleLabel(ce);
								absorbRule1(ce, n, ds);
								absorbRule2(n);
							}
							else {addToDoEntry(n, ce, cnds);
							}
						}
						else {
							DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
							if(!clashSet.isEmpty()) {
								clashSet.setCe(ce);
								clashSet.setCeNNF(ce.getComplementNNF());
								if(!clashHandler(clashSet, n))
									isInconsistent(n);
							}
							else
								isInconsistent(n);
							return;
						}
					}
				}
			}
		}
	}
	public void applyOrRule(Node n, OWLObjectUnionOf objUn, ConceptNDepSet cn) {
		DependencySet ds = cn.getDs();
		System.out.println("Applying or Rule..."+ n.getId() + objUn + " ds "+ds.getMax());
		//System.out.println("Applying or Rule: ds "+ds.getMax());
		
		if(!n.isBlocked()) {
			if(objUn.asDisjunctSet().size()==1) {
				applyOr(n, objUn.asDisjunctSet().iterator().next(), ds);
				return;
			}
			DependencySet newDs = DependencySet.plus(DependencySet.create(ds), DependencySet.create(getCurLevel()));
			BranchHandler bh = new BranchHandler(objUn, cn, newDs, n);
			this.branches.put(getCurLevel(), bh);
			save(n);
			incCurLevel();
			
			/// updated 14 sep, 2019
			
			if(bh.hasNextOption()) {
				applyOr(n, bh.getNextOption(),newDs);
			}
			/// update end
			
			
			//// commented 14 sep, 2019
			/*boolean flag = false;
			for(OWLClassExpression dj : objUn.asDisjunctSet()) {
				if(isConceptExist(n, dj)) {
					//System.err.println("exists : " + dj);
					flag = true;
					bh.disjunctTaken(dj);
					updateConceptDepSet(n, newDs, dj);
					if(!(dj instanceof OWLClass) || !(dj instanceof OWLObjectOneOf) || !(dj instanceof OWLObjectComplementOf))
						updateToDoEntryDepSet(n, dj, newDs);
				
					plusConceptDepSet(n, ds, dj);
					if(!(dj instanceof OWLClass) || !(dj instanceof OWLObjectOneOf) || !(dj instanceof OWLObjectComplementOf))
						plusToDoEntryDepSet(n, dj, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(dj)).iterator().next().getDs());
					break;
				}	
			}
			if(!flag) {
				
				//BranchHandler bh = new BranchHandler(objUn, cn, DependencySet.plus(DependencySet.create(ds), DependencySet.create(getCurLevel())), n);
				//this.branches.put(getCurLevel(), bh);
				
				//--ds.add(DependencySet.create(getCurLevel()));
				//--copyGraph(n);
			//	DependencySet newDs = DependencySet.plus(DependencySet.create(ds), DependencySet.create(getCurLevel()));
				
			//	save(n);
			//	incCurLevel();
				
				if(bh.hasNextOption()) {
					applyOr(n, bh.getNextOption(),newDs);
				}
			}*/ 
			/// end
		}
	}
	
	public void applyOr(Node n, OWLClassExpression ce, DependencySet ds) {
		System.out.println("node  "+n.getId()+" or expression selected : "+ce);
			System.out.println(" ds "+ds.getbpList());
		//	System.out.println("node  "+n.getLabel());
		if(ce != null) {
		boolean flag = false;
		if(isConceptExist(n, ce)) {
			flag = true;
			//cg.saveN(n);
		//	System.err.println("flag  ");
			updateConceptDepSet(n, ds, ce);
			if(!((ce instanceof OWLClass) || !(ce instanceof OWLObjectOneOf) || !(ce instanceof OWLObjectComplementOf)))
				updateToDoEntryDepSet(n, ce, ds);
				//updateToDoEntryDepSet(n, ce, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(ce)).iterator().next().getDs());
		}
		/*else if(ce instanceof OWLObjectUnionOf) {
			for(OWLClassExpression dj : ce.asDisjunctSet()) {
				if(isConceptExist(n, dj)) {
					flag = true;
					updateConceptDepSet(n, ds, dj);
					if(!(dj instanceof OWLClass))
						updateToDoEntryDepSet(n, dj, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(dj)).iterator().next().getDs());
					break;
				}				
			}
		}*/
		if(!flag) {
			//cg.save();
			ConceptNDepSet cnds = new ConceptNDepSet(ce, ds);
			if(ce instanceof OWLObjectOneOf) {
				if(processNominal(ce, n, cnds, ds) == null )
				 return;
			}
			else if(ce instanceof OWLObjectCardinalityRestriction) {
				if(needToAdd((OWLObjectCardinalityRestriction)ce, n)) {
					this.cg.addConceptToNode(n, cnds);
					if(!checkClash(n, ce)) {
						if(needReset(ce,n)) {
							reset(n);
							addToDoEntries(n);
						}
						else
							addToDoEntry(n, ce, cnds);
					}
					else {
						DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
						if(!clashSet.isEmpty()) {
							clashSet.setCe(ce);
							clashSet.setCeNNF(ce.getComplementNNF());
							if(!clashHandler(clashSet, n))
								isInconsistent(n);
						}
						else
							isInconsistent(n);
						return;
					}
				}
			}
			else {
				this.cg.addConceptToNode(n, cnds);
				if(!checkClash(n, ce)) {
					if(ce instanceof OWLClass) {
						n.addSimpleLabel(ce);
						absorbRule1(ce, n, ds);
						absorbRule2(n);
					}
					else { 
						addToDoEntry(n, ce, cnds);
					}
				}
				else {
					DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
					if(!clashSet.isEmpty()) {
						clashSet.setCe(ce);
						clashSet.setCeNNF(ce.getComplementNNF());
						if(!clashHandler(clashSet, n))
							isInconsistent(n);
					}
					else
						isInconsistent(n);
					return;
				}
			}
			/*for(Edge e : n.getIncomingEdges()) {
				this.processAtMost(e.getFromNode());
			}*/
		}
		}
	}
	
	
	private void processForAll(Node node) {
		//node.getLabel().stream().filter(l -> l instanceof OWLObjectAllValuesFrom).
		//	forEach(l -> applyForAllRule(node, (OWLObjectAllValuesFrom)l, node.getnLabel().getCndList().getCdSet().stream().filter(cds -> cds.getCe().equals(l)).iterator().next().getDs()));
		
		Set<OWLObjectAllValuesFrom> forAll= node.getLabel().stream().filter(l -> l instanceof OWLObjectAllValuesFrom).map(l -> (OWLObjectAllValuesFrom)l).collect(Collectors.toSet());
		for(OWLObjectAllValuesFrom fa : forAll) {
			applyForAllRule(node, fa, node.getnLabel().getCndList().getCdSet().stream().filter(cds -> cds.getCe().equals(fa)).iterator().next().getDs());
		}
	}
	
	private Node processNominal(OWLClassExpression ce, Node n, ConceptNDepSet cnds, DependencySet ds) {
		OWLClassExpression ci = df.getOWLObjectOneOf(((OWLObjectOneOf)ce).individuals().iterator().next());
		//System.out.println("process nominal : "+ ci);
		if(n.getCardinality() > 1) {
			reset(n);
			this.splitNode(n);
			return null;
		}
		Node nom = findNominalNode(ci);
		if(nom == null) {
			this.cg.addConceptToNode(n, cnds);
			if(n.getCardinality()>1) {
				System.err.println("cannot make nomial node");
			}
			n.makeNominalNode();
			if(!checkClash(n, ce)) {
				absorbNominal(ce, n, ds);
				Set<Node> resetNodes = needNomPredReset(n);
				System.err.println("# of pred reset nodes " +resetNodes.size());
				if(!resetNodes.isEmpty()) {
					for(Node resetNode : resetNodes) {
						reset(resetNode);
						splitNode(resetNode);
					}
					return null;
				}
				if(needNomReset(n)) {
					reset(n);
					this.addToDoEntries(n);
					return null;
				}
			}
			else {
				DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
				if(!clashSet.isEmpty()) {
					clashSet.setCe(ce);
					clashSet.setCeNNF(ce.getComplementNNF());
					if(!clashHandler(clashSet, n))
						isInconsistent(n);
				}
				else
					isInconsistent(n);
			}
			//processAtMost(n, ds);
			return null;
		}
		else {
			if(nom.equals(n)) {
				updateConceptDepSet(n, ds, ci);
				return null;
			}
			else {
				this.cg.addConceptToNode(n, cnds);
			//	if(n.getLabel().size() < nom.getLabel().size()) {
					System.out.println("Needs Merging! " + n.getId() + " into "+nom.getId());
					System.out.println("Node " + n.getLabel() + " into "+nom.getLabel());
					
					Node to = mergeNodes(n, nom, ci, ds);
				////  new code 27-oct-2019
					reset(to);
					this.addToDoEntries(to);
					////
					//processForAll(to);
					//processAtMost(to);
					return to;
			//	}
			/*	else{
					System.out.println("Needs Merging! " + nom.getId() + " into "+n.getId());
					System.out.println("Node " + nom.getLabel() + " into "+n.getLabel());
					Node to = mergeNodes2(nom, n, ci, ds);
					processForAll(to);
					return to;
				}*/
			}
			/*System.err.println("Sorry! it needs Merging!");
			Main.getExecutionTime();
			System.exit(0);*/
		}
		
	}

	private Node mergeNodes(Node from, Node to, OWLClassExpression ce, DependencySet depSet) {
		/// newcode 14 jul 2k19
		if(from.getDisjointNodes().contains(to)) {
			if(!depSet.isEmpty()) {
				if(!clashHandler(depSet, to))
					isInconsistent(to);
			}
			else
				isInconsistent(to);
			return null;
		}
		/// end new code
		//checkMergeClash(from, to);
		ConceptNDepSet cnd = to.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(ce)).iterator().next();
		DependencySet newDS = DependencySet.create();
		
		
		/////
		
		if(!depSet.isEmpty()) {
			newDS.add(DependencySet.create(depSet));
		}
		if(!cnd.getDs().isEmpty()) {
			newDS.add(DependencySet.create(cnd.getDs()));
		}
		
		/*if(!depSet.isEmpty()) {
			newDS = DependencySet.create(depSet);
			for(OWLClassExpression c : from.getLabel()) {
				plusConceptDepSet(from, depSet, c);
			}
		}
		else if(depSet.isEmpty() && !cnd.getDs().isEmpty()) {
			newDS = DependencySet.create(cnd.getDs());
			for(OWLClassExpression c : from.getLabel()) {
				plusConceptDepSet(from, cnd.getDs(), c);
			}
		}
		*/
		mergeLabels(from, to, newDS);
		/*cg.setCurrNode(from);
		cg.save();
		incCurLevel();*/
		cg.merge(from, to, depSet);
		//processForAll(to);
		//processAtMost(to);
		System.out.println("after merge "+to.getOutgoingEdges().size());
		return to;
	}
	/*private Node mergeNodes2(Node from, Node to, OWLClassExpression ce, DependencySet depSet) {
		//checkMergeClash(from, to);
		ConceptNDepSet cnd = from.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(ce)).iterator().next();
		DependencySet newDS = null;
		if(!depSet.isEmpty()) {
			newDS = DependencySet.create(depSet);
			for(OWLClassExpression c : from.getLabel()) {
				plusConceptDepSet(from, depSet, c);
			}
		}
		else if(depSet.isEmpty() && !cnd.getDs().isEmpty()) {
			newDS = DependencySet.create(cnd.getDs());
			for(OWLClassExpression c : from.getLabel()) {
				plusConceptDepSet(from, cnd.getDs(), c);
			}
		}
		mergeLabels(from, to, newDS);
		cg.setCurrNode(from);
		cg.save();
		incCurLevel();
		cg.merge(from, to, depSet);
		return to;
	}*/
	private Node mergeNodes(Node from, Node to, DependencySet depSet) {
		/// newcode 14 jul 2k19
		
		if(from.getDisjointNodes().contains(to)) {
			if(!depSet.isEmpty()) {
				if(!clashHandler(depSet, to))
					isInconsistent(to);
			}
			else
				isInconsistent(to);
			return null;
		}
		/// end new code
		
		//checkMergeClash(from, to);
		/*if(!depSet.isEmpty()) {
			for(OWLClassExpression c : from.getLabel()) {
				plusConceptDepSet(from, depSet, c);
			}
			for(OWLClassExpression c : to.getLabel()) {
				plusConceptDepSet(to, depSet, c);
			}
		}*/
		System.out.println("before merge "+to.getOutgoingEdges().size());
		if(!from.equals(to)) {
			mergeLabels(from, to, depSet);
			cg.merge(from, to, depSet); 
		}
	//	processForAll(to);
	//	processAtMost(to);
		System.out.println("after merge "+to.getOutgoingEdges().size());
		
		return to;
	}
	private void mergeLabels(Node from, Node to, DependencySet depSet) { 
		System.out.println("Merging labels! " + from.getId() + " into "+to.getId());
		Set<OWLClassExpression> label = from.getLabel();
		if(depSet!=null  && !depSet.isEmpty()) {
			for(OWLClassExpression c : label) {
				ConceptNDepSet cnd = from.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(c)).iterator().next();		
				ConceptNDepSet newCnd = new ConceptNDepSet(c, DependencySet.plus(DependencySet.create(depSet), DependencySet.create(cnd.getDs())));
				
				//ConceptNDepSet cnd = from.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(c)).iterator().next();		
				System.out.println("before merge "+ cnd.getCe() +" ds "+ cnd.getDs().getbpList());
				if(isConceptExist(to, c)) {
					
					updateConceptDepSet(to, newCnd.getDs(), c);
					if(!(c instanceof OWLClass) || !(c instanceof OWLObjectOneOf) || !(c instanceof OWLObjectComplementOf))
						updateToDoEntryDepSet(to, c, newCnd.getDs());
					System.out.println(" after addlabel "+ newCnd.getCe() +" ds "+ newCnd.getDs().getbpList());
					
				}
				else {
					this.cg.addConceptToNode(to, newCnd);
				
					if(!checkClash(to, c)) {
						if(c instanceof OWLClass || c instanceof OWLObjectOneOf || c instanceof OWLObjectComplementOf) {
							to.addSimpleLabel(c);
						}
//						else {
//							//addToDoEntry(to, c, cnd);
//							/*if(isToDoEntryDepSet(from, c, newCnd.getDs())) {
//								//System.err.println("find entry "+ c);
//								addToDoEntry(to, c, newCnd);
//							}*/
//							isToDoEntryDepSet(from, c, newCnd.getDs());
//							addToDoEntry(to, c, newCnd);
//						}
					}
					else {
						//System.out.println("clash check "+ c);
						DependencySet clashSet = getClashSet(to, c, c.getComplementNNF());
					//	System.out.println("clash set "+ clashSet.getbpList());
						if(!clashSet.isEmpty()) {
							clashSet.setCe(c);
							clashSet.setCeNNF(c.getComplementNNF());
							if(!clashHandler(clashSet, to))
								isInconsistent(to);
						}
						else
							isInconsistent(to);
						return;
					}
				}
			}
		}
		else {

			for(OWLClassExpression c : label) {
				ConceptNDepSet cnd = from.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(c)).iterator().next();		
						
			//	System.out.println("before merge "+ cnd.getCe() +" ds "+ cnd.getDs().getbpList());
				if(isConceptExist(to, c)) {
					updateConceptDepSet(to, cnd.getDs(), c);
					if(!(c instanceof OWLClass) || !(c instanceof OWLObjectOneOf) || !(c instanceof OWLObjectComplementOf))
						updateToDoEntryDepSet(to, c, cnd.getDs());
				}
				else {
					this.cg.addConceptToNode(to, cnd);
					if(!checkClash(to, c)) {
						if(c instanceof OWLClass) {
							to.addSimpleLabel(c);
						}
//						else {
//							//addToDoEntry(to, c, cnd);
//							if(isToDoEntryDepSet(from, c, cnd.getDs())) {
//								addToDoEntry(to, c, cnd);
//							}
//						}
					}
					else {
						DependencySet clashSet = getClashSet(to, c, c.getComplementNNF());
						if(!clashSet.isEmpty()) {
							clashSet.setCe(c);
							clashSet.setCeNNF(c.getComplementNNF());
							if(!clashHandler(clashSet, to))
								isInconsistent(to);
						}
						else
							isInconsistent(to);
						return;
					}
				}
				
			}
		}
	}
	
	/*private boolean checkMergeClash(Node from, Node to) {
		for(OWLClassExpression ce : from.getLabel()) {
			if(checkClash(to, ce))
				return true;
		}
		return false;
	}*/

	private void isInconsistent(Node n) {
		//if(n.isNominalNode()) {
			System.err.println("Your ontology is inconsistent");
			TestReasoner.getExecutionTime();
			System.exit(0);
		//}
		
	}
	private boolean clashHandler(DependencySet clashSet, Node node) {
		
		System.out.println("Clash handler...");
		
		/*/////
		if(!clashSet.isEmpty()) {
		for(int l= 0; l < clashSet.getbpList().size(); l++) {
			int level = clashSet.getMax();
			
			System.out.println("level" + level);
			//System.out.println(cg.getTotalNodes());
			//System.out.println(branches.get(level));
			if( branches.get(level).hasNextOption()) {
				restore(level);
				//save(cg.getCurrNode());
			//	System.out.println("restoring currentBranchingPoint : "+level +" Neighbour : "+cg.getCurrNode().getOutgoingEdges().size()+" total nodes : "+ cg.getTotalNodes());
			//	System.out.println("branch node" + branches.get(level).getNode().getId());
			//	System.out.println("graph curr node" + cg.getCurrNode().getId());
			//	System.out.println("curr node label after" + cg.getCurrNode().getLabel());
				boolean flag = false;
				for(OWLClassExpression ce :branches.get(level).getAllNextOptions()) {
					if(isConceptExist(cg.getCurrNode(), ce)) {
						flag = true;
						branches.get(level).disjunctTaken(ce);
						updateConceptDepSet(cg.getCurrNode(), branches.get(level).getDs(), ce);
						if(!(ce instanceof OWLClass) || !(ce instanceof OWLObjectOneOf) || !(ce instanceof OWLObjectComplementOf))
							updateToDoEntryDepSet(cg.getCurrNode(), ce, branches.get(level).getDs());
						break;
					
					}
				}
				if(!flag)
					applyOr(cg.getCurrNode(), branches.get(level).getNextOption(), branches.get(level).getDs());
				//applyOr(branches.get(level).getNode(), branches.get(level).getNextOption(), branches.get(level).ds);
			}
			else {
				branches.get(level).reset();
				//branches.remove(level);
				clashSet.removeLevel(level);
				if(!clashHandler(clashSet))
					return false;
			}
		}
		
		}
		else {
			return false;
		}
		////	
*/		if(!clashSet.isEmpty()) {
			
			int level = clashSet.getMax();
			
			System.out.println("level" + level);
			//System.out.println(cg.getTotalNodes());
			//System.err.println(branches.get(level).getDs().getbpList());
			
			//// added 25-oct-2019
			if(branches.get(level).ILPBranching) {
				Set<OWLSubClassOfAxiom> subAx = new HashSet<>();
				Node n = branches.get(level).getNode();
				System.err.println("n: "+ n.getId()+ " node: "+node.getId());
				if(!n.equals(node) && n.getId() < node.getId()) {
					 Set<OWLClassExpression> relatedConcepts = branches.get(level).getRelatedConcepts(node);
					System.err.println("relatedConcepts: "+ relatedConcepts.size() +" node.getBackPropagatedLabel() "+ node.getBackPropagatedLabel());
					 OWLClassExpression ce = clashSet.getCe();
					 OWLClassExpression ceNNF = clashSet.getCeNNF();
					 System.err.println("ce "+ ce +" ceNNF "+ ceNNF);
						
					 if(!node.getSimpleILPLabel().contains(ce) && node.getSimpleILPLabel().contains(ceNNF)) {
						 for(OWLClassExpression bpl : node.getBackPropagatedLabel()) {
							 if(bpl.equals(ce)) {
								 for(OWLClassExpression rc : relatedConcepts) {
									 subAx.add(df.getOWLSubClassOfAxiom(rc, bpl));
								 }
							 }
							 else if(bpl instanceof OWLObjectIntersectionOf) {
								 if(bpl.asConjunctSet().contains(ce)) {
									 for(OWLClassExpression rc : relatedConcepts) {
										 subAx.add(df.getOWLSubClassOfAxiom(rc, bpl));
									 }
								 }
							 }
							 else if(bpl instanceof OWLObjectUnionOf) {
								 if(bpl.asDisjunctSet().contains(ce)) {
									 for(OWLClassExpression rc : relatedConcepts) {
										 subAx.add(df.getOWLSubClassOfAxiom(rc, bpl));
									 }
								 }
									 
							 }
						 }
					 }
					 else if(!node.getSimpleILPLabel().contains(ceNNF) && node.getSimpleILPLabel().contains(ce)) {
						 for(OWLClassExpression bpl : node.getBackPropagatedLabel()) {
							 if(bpl.equals(ceNNF)) {
								 for(OWLClassExpression rc : relatedConcepts) {
									 subAx.add(df.getOWLSubClassOfAxiom(rc, bpl));
								 }
							 }
							 else if(bpl instanceof OWLObjectIntersectionOf) {
								 if(bpl.asConjunctSet().contains(ceNNF)) {
									 for(OWLClassExpression rc : relatedConcepts) {
										 subAx.add(df.getOWLSubClassOfAxiom(rc, bpl));
									 }
								 }
							 }
							 else if(bpl instanceof OWLObjectUnionOf) {
								 if(bpl.asDisjunctSet().contains(ceNNF)) {
									 for(OWLClassExpression rc : relatedConcepts) {
										 subAx.add(df.getOWLSubClassOfAxiom(rc, bpl));
									 }
								 }
									 
							 }
						 }
					 }
					 
					 if(!subAx.isEmpty()){
						 System.err.println("subAx "+ subAx);
						 restore(level);
						// reset(n);
						 subAx.addAll(branches.get(level).getSubsumption());
						 this.callILP(n, branches.get(level).getAllEntries(), subAx, null);
					 }
					 else {
					 
						// branches.get(level).reset2();
							//branches.remove(level);
						 restore(level);
						clashSet.removeLevel(level);
						if(!clashHandler(clashSet, n))
							return false;
					 }
					 
				}
				else {
					if(n.getId() > node.getId()) {
						restore(level);
						//reset(node);
						clashSet.removeLevel(level);
						if(!clashHandler(clashSet, node))
							return false;
					}
					else {
				//	branches.get(level).reset2();
					//branches.remove(level);
					restore(level);
					clashSet.removeLevel(level);
					if(!clashHandler(clashSet, n))
						return false;
					}
				}
			}
			
			
			///
			
			else {
			 if( branches.get(level).hasNextOption()) {
				restore(level);
				DependencySet newDS = DependencySet.create(clashSet);
				//applyOr(cg.getCurrNode(), branches.get(level).getNextOption(), DependencySet.plus(newDS, branches.get(level).getDs()));
				applyOr(cg.getCurrNode(), branches.get(level).getNextOption(), DependencySet.create(branches.get(level).getDs()));
			//	applyOr(cg.getCurrNode(), branches.get(level).getNextOption(), newDS);
				
				//save(cg.getCurrNode());
			//	System.out.println("restoring currentBranchingPoint : "+level +" Neighbour : "+cg.getCurrNode().getOutgoingEdges().size()+" total nodes : "+ cg.getTotalNodes());
			//	System.out.println("branch node" + branches.get(level).getNode().getId());
			//	System.out.println("graph curr node" + cg.getCurrNode().getId());
			//	System.out.println("curr node label after" + cg.getCurrNode().getLabel());
				
				/// comment start 15 sep, 2019
				/*boolean flag = false;
				for(OWLClassExpression ce :branches.get(level).getAllNextOptions()) {
					if(isConceptExist(cg.getCurrNode(), ce)) {
						flag = true;
						branches.get(level).disjunctTaken(ce);
						updateConceptDepSet(cg.getCurrNode(), DependencySet.plus(newDS, branches.get(level).getDs()), ce);
						// commented on 4 march 2019
						//updateConceptDepSet(cg.getCurrNode(), branches.get(level).getDs(), ce);
						if(!(ce instanceof OWLClass) || !(ce instanceof OWLObjectOneOf) || !(ce instanceof OWLObjectComplementOf)) {
							updateToDoEntryDepSet(cg.getCurrNode(), ce, DependencySet.plus(newDS, branches.get(level).getDs()));
							// commented on 4 march 2019
							//updateToDoEntryDepSet(cg.getCurrNode(), ce, branches.get(level).getDs());
						}
						break;
					
					}
				}
				if(!flag) {
					applyOr(cg.getCurrNode(), branches.get(level).getNextOption(), DependencySet.plus(newDS, branches.get(level).getDs()));
					// commented on 4 march 2019
					//applyOr(cg.getCurrNode(), branches.get(level).getNextOption(), branches.get(level).getDs());
				//applyOr(branches.get(level).getNode(), branches.get(level).getNextOption(), branches.get(level).ds);
				}*/
				/// comment end 15 sep, 2019
			}
			else {
				Node n = branches.get(level).getNode();
				branches.get(level).reset();
				//branches.remove(level);
				clashSet.removeLevel(level);
				if(!clashHandler(clashSet, n))
					return false;
			}
		 }
		}
		else {
			return false;
		}
		return true;
	}
	public void copyGraph(Node n) {
		
		cg.copyNodes();
		try {
			cg.setCurrNode(n);
			copies.put(getCurLevel(), (CompletionGraph)cg.clone());
		} catch (CloneNotSupportedException e) {
			e.printStackTrace();
		} 
		//System.out.println("saving currentBranchingPoint : "+getCurLevel() +" Node id: "+cg.getCurrNode().getId()+" total nodes : "+ cg.getTotalNodes());
	}
	public void restoreGraph(int level) {
		cg.restore(level);
		//this.cg = copies.get(level);
		//cg.restoreNode(cg.getCurrNode());
		//System.out.println("Restoring level : "+level + "Node id "+cg.getCurrNode().getId()+" total nodes : "+ cg.getTotalNodes());
	}

	public boolean checkClash(Node n, OWLClassExpression c) {
	//	System.err.println("check clash "+c);

		if(c.isOWLNothing()) {
		//	System.err.println("clash "+c +" "+ c.getComplementNNF());
			return true;
		}
		if(n.getLabel().contains(c.getComplementNNF())) {
		//	System.err.println("clash "+c);
			return true;
		}
		
		return false;
	}
	
	public Set<Set<OWLClassExpression>> checkDisjointGroups(Node n) {
		return ontology.getDisjointGroups(n.getLabel());
	}
	
	public Node findBlocker(Node n) {
		
		return cg.findBlocker(n);
	}
	
	public void processUnblockedNode(Node node) {
        //if (direct) {
            // not blocked -- clear blocked cache
            // re-apply all the generating rules
          //  applyAllGeneratingRules(node);
       // } else {
            redoNodeLabel(node);
        //}
    }
	
	
	
	private void redoNodeLabel(Node node) {
		
		node.getLabel().stream().forEach(l -> addToDoEntry(node, l, 
				node.getnLabel().getCndList().getCdSet().stream().filter(cds -> cds.getCe().equals(l)).iterator().next()));
		
	}

/*	private void applyAllGeneratingRules(Node node) {
		node.getLabel().stream().filter(l -> l instanceof OWLObjectSomeValuesFrom).forEach(l -> addToDoEntry(node, l, 
				node.getnLabel().getCndList().getCdSet().stream().filter(cds -> cds.getCe().equals(l)).iterator().next()));
		
	}

	private AddConceptResult tryAddConcept(Node n,  OWLClassExpression ce) {
       
		boolean canC = isConceptExist(n, ce);
        boolean canNegC = isConceptExist(n, ce.getComplementNNF());
       
        if (canC) 
        		return AddConceptResult.EXIST;
        else if (canNegC)
        		return AddConceptResult.CLASH;
        else 
        		return AddConceptResult.DONE;
         
    }*/
	
	
	public DependencySet getClashSet(Node n, Set<Set<OWLClassExpression>> djGrp) {
		List<ConceptNDepSet> cndList = n.getnLabel().getCndList().getCdSet();
		List<ConceptNDepSet> cndSets = new ArrayList<ConceptNDepSet>(); 
		
		for(ConceptNDepSet cnds : cndList){
			if(cnds != null) {
				OWLClassExpression ce = cnds.getCe();
				for(Set<OWLClassExpression> djg : djGrp) {
					if(djg.contains(ce) && !cnds.getDs().isEmpty()) {
						cndSets.add(cnds);
						break;
					}
				}
			}
		}
		DependencySet ds = DependencySet.create();
		for(ConceptNDepSet cnds : cndSets) {
			ds = DependencySet.plus(ds,DependencySet.create(cnds.getDs()));	
		}
			return ds;
	}
	public DependencySet getClashSet2(Node n, Set<OWLClassExpression> djGrp) {
		List<ConceptNDepSet> cndList = n.getnLabel().getCndList().getCdSet();
		List<ConceptNDepSet> cndSets = new ArrayList<ConceptNDepSet>(); 
		
		for(ConceptNDepSet cnds : cndList){
			if(cnds != null) {
				OWLClassExpression ce = cnds.getCe();
				if(djGrp.contains(ce) && !cnds.getDs().isEmpty()) 
					cndSets.add(cnds);
			}
		}
		DependencySet ds = DependencySet.create();
		for(ConceptNDepSet cnds : cndSets) {
			ds = DependencySet.plus(ds,DependencySet.create(cnds.getDs()));	
		}
			return ds;
	}
	
	public DependencySet getClashSet(Node n, OWLClassExpression ce, OWLClassExpression ceNNF) {
		List<ConceptNDepSet> cndList = n.getnLabel().getCndList().getCdSet();
		ConceptNDepSet cnd1 = null;
		ConceptNDepSet cnd2 = null;
		for(ConceptNDepSet cnds : cndList){
			if(cnds != null) {
				if(cnds.getCe().equals(ce)) {
					cnd1 = cnds;
				}
				else if(cnds.getCe().equals(ceNNF)){
					cnd2 = cnds;
				}
			}
		}
		
		
	//	ConceptNDepSet cnd1 = n.getnLabel().getCndList().getCdSet().stream().filter(cds -> cds.getCe().equals(ce)).iterator().next();
	//	ConceptNDepSet cnd2 = n.getnLabel().getCndList().getCdSet().stream().filter(cds -> cds.getCe().equals(ceNNF)).iterator().next();
		//System.out.println("exp "+ cnd1.getCe() + " ds "+ cnd1.getDs().getMax());
		//System.out.println("exp "+ ceNNF + " ds "+ cnd2.getDs().getMax());
		if(ce.isOWLNothing()) {
			if(cnd1.getDs().isEmpty())
				return DependencySet.create();
			else 
				return DependencySet.plus(DependencySet.create(cnd1.getDs()), DependencySet.create());
		}
		else if(ceNNF != null) {
			if(cnd1.getDs().isEmpty() && cnd2.getDs().isEmpty())
				return DependencySet.create();
			else 
				return DependencySet.plus(DependencySet.create(cnd1.getDs()), DependencySet.create(cnd2.getDs()));
		}
		else {
			if(cnd1.getDs().isEmpty())
				return DependencySet.create();
			else 
				return DependencySet.plus(DependencySet.create(cnd1.getDs()), DependencySet.create());
		}
	}
	
	
	
	
	public DependencySet getOtherOption(Node n, OWLClassExpression ce1, OWLClassExpression ce2) {
		DependencySet dsUnion = null;
		if(n.getConceptsDependencies().get(ce1).stream().filter(d -> d.isEmpty()).iterator().hasNext() &&
				n.getConceptsDependencies().get(ce2).stream().filter(d -> d.isEmpty()).iterator().hasNext()) {
			return null;
		}
		else if(n.getConceptsDependencies().get(ce1).stream().filter(d -> d.isEmpty()).iterator().hasNext()) {
			for (DependencySet ds : n.getConceptsDependencies().get(ce2)) {
				dsUnion = DependencySet.plus(dsUnion, ds);
			}
			
		}
		else if(n.getConceptsDependencies().get(ce2).stream().filter(d -> d.isEmpty()).iterator().hasNext()){
			for (DependencySet ds : n.getConceptsDependencies().get(ce1)) {
				dsUnion = DependencySet.plus(dsUnion, ds);
			}
		}
		else {
			for (DependencySet ds : n.getConceptsDependencies().get(ce2)) {
				dsUnion = DependencySet.plus(dsUnion, ds);
			}
			for (DependencySet ds : n.getConceptsDependencies().get(ce1)) {
				dsUnion = DependencySet.plus(dsUnion, ds);
			}
		}
		
		return dsUnion;
		
	}
	
	
	public void absorbRule1(OWLClassExpression ce, Node n, DependencySet ds) {
	//	System.out.println("applying absorbRule 1 : "+ ce +" nid "+n.getId());
	//	System.out.println("concept ds : "+ ds.getMax());
		Set<OWLClassExpression> sup = this.intl.findConcept(ce);
		if(sup.size()!=0) {
			for(OWLClassExpression c : sup) {
			//	System.out.println(sup.size()+" absorb : "+ c);
				if(c.isOWLNothing()) {
					DependencySet clashSet = getClashSet(n, ce, null);
					if(!clashSet.isEmpty()) {
						if(!clashHandler(clashSet, n))
							isInconsistent(n);
					}
					else
						isInconsistent(n);
					return;
				}
				boolean flag = false;
				if(isConceptExist(n, c)) {
					flag = true;
					updateConceptDepSet(n, ds, c);
					if(!((c instanceof OWLClass) || (c instanceof OWLObjectOneOf) || (c instanceof OWLObjectComplementOf)))
						updateToDoEntryDepSet(n, c, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(c)).iterator().next().getDs());
				}
				/*else if(c instanceof OWLObjectUnionOf) {
					for(OWLClassExpression dj : c.asDisjunctSet()) {
						if(isConceptExist(n, dj)) {
							flag = true;
							updateConceptDepSet(n, ds, dj);
							if(!(dj instanceof OWLClass))
								updateToDoEntryDepSet(n, dj, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(dj)).iterator().next().getDs());
							break;
						}
						
					}
				}*/
				if(!flag) {
					ConceptNDepSet cnds = new ConceptNDepSet(c, ds);
					if(c instanceof OWLObjectOneOf) {
						
						if(processNominal(c, n, cnds, ds) == null)
							return;
					}
					else if(c instanceof OWLObjectCardinalityRestriction) {
						if(needToAdd((OWLObjectCardinalityRestriction)c, n)) {
							this.cg.addConceptToNode(n, cnds);
							if(!checkClash(n, c)) {
								if(needReset(c,n)) {
									reset(n);
									addToDoEntries(n);
								}
								else
									addToDoEntry(n, c, cnds);
							}
							else {
								DependencySet clashSet = getClashSet(n, c, c.getComplementNNF());
								if(!clashSet.isEmpty()) {
									clashSet.setCe(c);
									clashSet.setCeNNF(c.getComplementNNF());
									if(!clashHandler(clashSet, n))
										isInconsistent(n);
								}
								else
									isInconsistent(n);
								return;
							}
						}
					}
					else {
						cg.addConceptToNode(n, cnds);
						if(!checkClash(n, c)) {
						//	System.err.println("no clash: "+ c+" label "+ n.getLabel());
						//	Set<Set<OWLClassExpression>> djGrp = checkDisjointGroups(n);
						//	if(djGrp.isEmpty()) {
								if(c instanceof OWLClass) { 
									n.addSimpleLabel(c);
									absorbRule1(c, n, ds);
									absorbRule2(n);
								}
								else {
									addToDoEntry(n, c, cnds);
								}
						//	}
						/*	else {
								DependencySet clashSet = getClashSet(n, djGrp);
								if(!clashSet.isEmpty()) {
									if(!clashHandler(clashSet))
										isInconsistent(n);
								}
								else
									isInconsistent(n);
								return;
							}*/
						}
						else {
							DependencySet clashSet = getClashSet(n, c, c.getComplementNNF());
							if(!clashSet.isEmpty()) {
								clashSet.setCe(c);
								clashSet.setCeNNF(c.getComplementNNF());
								if(!clashHandler(clashSet, n))
									isInconsistent(n);
							}
							else
								isInconsistent(n);
							return;
						}
					}
				}
			}
		}
	}
	public void absorbRule2(Node n) {
		Set<OWLSubClassOfAxiom> sbAx = this.intl.getTui();
		Set<OWLClassExpression> classes = n.getSimpleLabel();
		//Set<OWLClassExpression> classes = n.getLabel();
		for(OWLSubClassOfAxiom sb : sbAx) {
			DependencySet dep = DependencySet.create();
			boolean flag = true;
			for(OWLClassExpression cn :sb.getSubClass().asConjunctSet()) {
				if(!classes.contains(cn)) {
					flag = false;
					break;
				}
				else {
					n.getnLabel().getCndList().getCdSet().stream().
							filter(cnds -> cnds.getCe().equals(cn)).forEach(cnd -> dep.add(cnd.getDs()));
				} 
			}
			if(flag) {
				boolean flag2 = false;
				OWLClassExpression c = sb.getSuperClass();
			//	System.err.println(c);
				if(c.isOWLNothing()) {
					DependencySet clashSet = getClashSet2(n, sb.getSubClass().asConjunctSet());
					if(!clashSet.isEmpty()) {
						if(!clashHandler(clashSet, n))
							isInconsistent(n);
					}
					else
						isInconsistent(n);
					return;
				}
				if(isConceptExist(n, c)) {
					flag2 = true;
					updateConceptDepSet(n, dep, c);
					if(!((c instanceof OWLClass) || (c instanceof OWLObjectOneOf) || (c instanceof OWLObjectComplementOf)))
						updateToDoEntryDepSet(n, c, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(c)).iterator().next().getDs());
				}
				/*else if(c instanceof OWLObjectUnionOf) {
					for(OWLClassExpression dj : c.asDisjunctSet()) {
						if(isConceptExist(n, dj)) {
							flag2 = true;
							updateConceptDepSet(n, dep, dj);
							if(!(dj instanceof OWLClass))
								updateToDoEntryDepSet(n, dj, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(dj)).iterator().next().getDs());
							break;
						}
						
					}
				}*/
				if(!flag2) {
					ConceptNDepSet cnds = new ConceptNDepSet(c, dep);
					if(c instanceof OWLObjectOneOf) {
						if(processNominal(c, n, cnds, dep) == null)
							return;
					}
					else if(c instanceof OWLObjectCardinalityRestriction) {
						if(needToAdd((OWLObjectCardinalityRestriction)c, n)) {
							this.cg.addConceptToNode(n, cnds);
							if(!checkClash(n, c)) {
								if(needReset(c,n)) {
									reset(n);
									addToDoEntries(n);
								}
								else
									addToDoEntry(n, c, cnds);
							}
							else {
								DependencySet clashSet = getClashSet(n, c, c.getComplementNNF());
								if(!clashSet.isEmpty()) {
									clashSet.setCe(c);
									clashSet.setCeNNF(c.getComplementNNF());
									if(!clashHandler(clashSet, n))
										isInconsistent(n);
								}
								else
									isInconsistent(n);
								return;
							}
						}
					}
					else {
						cg.addConceptToNode(n, cnds);
						if(!checkClash(n, c)) {
						//	Set<Set<OWLClassExpression>> djGrp = checkDisjointGroups(n);
						//	if(djGrp.isEmpty()) {
								if(c instanceof OWLClass) { 
									n.addSimpleLabel(c);
									absorbRule1(c, n, dep);
									absorbRule2(n);
								}

								else {
									addToDoEntry(n, c, cnds);
								}
							}
						/*	else {
								DependencySet clashSet = getClashSet(n, djGrp);
								if(!clashSet.isEmpty()) {
									if(!clashHandler(clashSet))
										isInconsistent(n);
								}
								else
									isInconsistent(n);
								return;
							}
						}*/
						else {
							DependencySet clashSet = getClashSet(n, c, c.getComplementNNF());
							if(!clashSet.isEmpty()) {
								clashSet.setCe(c);
								clashSet.setCeNNF(c.getComplementNNF());
								if(!clashHandler(clashSet, n))
									isInconsistent(n);
							}
							else
								isInconsistent(n);
							return;
						}
					}
				}
			}
		}
	}
	private Node findNominalNode(OWLClassExpression ce) {
		return cg.findNominalNode(ce);
	}

	private void absorbNominal(OWLClassExpression ce, Node n, DependencySet ds) {
		//System.out.println("applying absorb Nominal : "+ ce +"node "+ n.getId());
		Set<OWLClassExpression> sup = this.intl.findIndividual(ce);
		//System.out.println("contains "+ sup.size());
		
		if(sup.size()!=0) {
			for(OWLClassExpression c : sup) {
			//	System.out.println("super "+ c);
				boolean flag = false;
				if(isConceptExist(n, c)) {
					flag = true;
					updateConceptDepSet(n, ds, c);
					if(!((c instanceof OWLClass) || (c instanceof OWLObjectOneOf) || (c instanceof OWLObjectComplementOf)))
						updateToDoEntryDepSet(n, c, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(c)).iterator().next().getDs());
				}
				/*else if(c instanceof OWLObjectUnionOf) {
					for(OWLClassExpression dj : c.asDisjunctSet()) {
						if(isConceptExist(n, dj)) {
							flag = true;
							updateConceptDepSet(n, ds, dj);
							if(!(dj instanceof OWLClass))
								updateToDoEntryDepSet(n, dj, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(dj)).iterator().next().getDs());
							break;
						}
						
					}
				}*/
				if(!flag) {
					ConceptNDepSet cnds = new ConceptNDepSet(c, ds);
					if(c instanceof OWLObjectOneOf) {
						if(processNominal(c, n, cnds, ds) == null)
							return;
					}
					else if(c instanceof OWLObjectCardinalityRestriction) {
						if(needToAdd((OWLObjectCardinalityRestriction)c, n)) {
							this.cg.addConceptToNode(n, cnds);
							if(!checkClash(n, c)) {
								if(needReset(c,n)) {
									reset(n);
									addToDoEntries(n);
								}
								else
									addToDoEntry(n, c, cnds);
							}
							else {
								DependencySet clashSet = getClashSet(n, c, c.getComplementNNF());
								if(!clashSet.isEmpty()) {
									clashSet.setCe(c);
									clashSet.setCeNNF(c.getComplementNNF());
									if(!clashHandler(clashSet, n))
										isInconsistent(n);
								}
								else
									isInconsistent(n);
								return;
							}
						}
					}
					else {
						cg.addConceptToNode(n, cnds);
						if(!checkClash(n, c)) {
						//	Set<Set<OWLClassExpression>> djGrp = checkDisjointGroups(n);
						//	if(djGrp.isEmpty()) {
								if(c instanceof OWLClass) { 
									n.addSimpleLabel(c);
									absorbRule1(c, n, ds);
									absorbRule2(n);
								}
								else {
									addToDoEntry(n, c, cnds);
								}
						//		}
						/*	else {
								DependencySet clashSet = getClashSet(n, djGrp);
								if(!clashSet.isEmpty()) {
									if(!clashHandler(clashSet))
										isInconsistent(n);
								}
								else
									isInconsistent(n);
								return;
							}*/
						}
						else {
							DependencySet clashSet = getClashSet(n, c, c.getComplementNNF());
							if(!clashSet.isEmpty()) {
								clashSet.setCe(c);
								clashSet.setCeNNF(c.getComplementNNF());
								if(!clashHandler(clashSet, n))
									isInconsistent(n);
							}
							else
								isInconsistent(n);
							return;
						}
					}
				}
			}
		}
		
	}
	
	 private int getCurLevel() {
	        return currentBranchingPoint;
	    }
	 private void setCurLevel(int level) {
	        currentBranchingPoint = level;
	    }
	 private void incCurLevel() {
		 ++currentBranchingPoint;
	 }
	
	public boolean findClash() {
		return false;
	}
	
	public boolean isConceptExist(Node n, OWLClassExpression ce) {
		//n.getLabel().stream().forEach(lb -> System.out.println(lb));
		if(n.getLabel().contains(ce))
			return true;
		return false;
	}
	
	/*public void updateDepSet(Node n, DependencySet ds, OWLClassExpression filler, Edge e) {
		ConceptNDepSet cnd = n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).iterator().next();
		if(cnd.getDs().isEmpty() || ds.isEmpty()) {
			n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).forEach(cnds -> cnds.setDs(DependencySet.create()));
			//cnd.setDs(DependencySet.create());
		}
		else {
			n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).forEach(cnds -> cnds.setDs(DependencySet.plus(cnds.getDs(), ds)));
			//cnd.setDs(DependencySet.plus(cnd.getDs(), ds));
		}
		if(e.getDepSet().isEmpty() || ds.isEmpty())
			e.setDepSet(DependencySet.create());
		else
			e.setDepSet(DependencySet.plus(e.getDepSet(), ds));
		updateToDoEntryDepSet(n, filler, ds);
	}*/
	public void updateConceptDepSet(Node n, DependencySet ds, OWLClassExpression filler) {
		//System.out.println("node "+n.getId() +"filler "+ filler+" node label "+ n.getLabel());
		cg.saveN(n);
		List<ConceptNDepSet> cndList = n.getnLabel().getCndList().getCdSet();
		ConceptNDepSet cnd = null;
		for(ConceptNDepSet cnds : cndList){
			if(cnds != null) {
				if(cnds.getCe().equals(filler)) {
					cnd = cnds;
				}
			}
		}
		//ConceptNDepSet cnd = n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).iterator().next();
		if(cnd.getDs().isEmpty() || ds.isEmpty()) {
			n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).forEach(cnds -> cnds.setDs(DependencySet.create()));
			//cnd.setDs(DependencySet.create());
		}
		else {
			List<ConceptNDepSet> cndList1 = n.getnLabel().getCndList().getCdSet();
			for(ConceptNDepSet cnds : cndList1){
				if(cnds != null && cnds.getCe() != null && cnds.getCe().equals(filler)) {
					//FIXME check if below line should be commented??? 
					cnds.setDs(DependencySet.plus(DependencySet.create(cnds.getDs()), DependencySet.create(ds)));
				}
			}
			//n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).forEach(cnds -> cnds.setDs(DependencySet.plus(DependencySet.create(cnds.getDs()), DependencySet.create(ds))));
			//cnd.setDs(DependencySet.plus(cnd.getDs(), ds));
		}
		
		/*Optional<ConceptNDepSet> opcnds = n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).findFirst();//.iterator().next();
		if(opcnds.isPresent()) {
			//System.out.println("node "+n.getId() +"filler "+ filler);
			ConceptNDepSet cnd = opcnds.get();
		if(cnd.getDs().isEmpty() || ds.isEmpty()) {
			n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).forEach(cnds -> cnds.setDs(DependencySet.create()));
			//cnd.setDs(DependencySet.create());
		}
		else {
			n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).forEach(cnds -> cnds.setDs(DependencySet.plus(cnds.getDs(), ds)));
			//cnd.setDs(DependencySet.plus(cnd.getDs(), ds));
		}
		}*/
	}
	public void plusConceptDepSet(Node n, DependencySet ds, OWLClassExpression filler) {
		
		n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).forEach(cnds -> cnds.setDs(DependencySet.plus(DependencySet.create(cnds.getDs()), DependencySet.create(ds))));
			
	}
	public DependencySet updateDepSetForAll(Edge e, DependencySet ds) {
		DependencySet depSet = DependencySet.create(ds);
		if(!e.getDepSet().isEmpty())
			depSet = DependencySet.plus(depSet, DependencySet.create(e.getDepSet()));
		//return ds;
		return depSet;
	}
	
	public void updateEdgeDepSet(DependencySet ds, Edge e) {
		if(e.getDepSet() == null || ds ==null)
			e.setDepSet(DependencySet.create());
		else if(e.getDepSet().isEmpty() || ds.isEmpty())
			e.setDepSet(DependencySet.create());
		else
			e.setDepSet(DependencySet.plus(e.getDepSet(), DependencySet.create(ds)));
		
	}
	private void updateToDoEntryDepSet(Node n, OWLClassExpression c, DependencySet ds) {
		
		if(c instanceof OWLObjectIntersectionOf)
			todo.updateToDoEntry(n, NodeTag.AND, c, ds);
		else if(c instanceof OWLObjectUnionOf)
			todo.updateToDoEntry(n, NodeTag.OR, c, ds);
		else if(c instanceof OWLObjectSomeValuesFrom || c instanceof OWLObjectHasValue)
			todo.updateToDoEntry(n, NodeTag.EXISTS, c, ds);
		else if(c instanceof OWLObjectAllValuesFrom)
			todo.updateToDoEntry(n, NodeTag.FORALL, c, ds);
		else if(c instanceof OWLObjectMinCardinality)
			todo.updateToDoEntry(n, NodeTag.LE, c, ds);
		else if(c instanceof OWLObjectMaxCardinality)
			todo.updateToDoEntry(n, NodeTag.GE, c, ds);
		
		
	}
	private void plusToDoEntryDepSet(Node n, OWLClassExpression c, DependencySet ds) {
		
		if(c instanceof OWLObjectIntersectionOf)
			todo.plusToDoEntry(n, NodeTag.AND, c, ds);
		else if(c instanceof OWLObjectUnionOf)
			todo.plusToDoEntry(n, NodeTag.OR, c, ds);
		else if(c instanceof OWLObjectSomeValuesFrom || c instanceof OWLObjectHasValue)
			todo.plusToDoEntry(n, NodeTag.EXISTS, c, ds);
		else if(c instanceof OWLObjectAllValuesFrom)
			todo.plusToDoEntry(n, NodeTag.FORALL, c, ds);
		else if(c instanceof OWLObjectMinCardinality)
			todo.plusToDoEntry(n, NodeTag.LE, c, ds);
		else if(c instanceof OWLObjectMaxCardinality)
			todo.plusToDoEntry(n, NodeTag.GE, c, ds);
		
		
	}
	private boolean isToDoEntryDepSet(Node n, OWLClassExpression c, DependencySet ds) {
		
		if(c instanceof OWLObjectIntersectionOf)
			return todo.hasToDoEntry(n, NodeTag.AND, c, ds);
		else if(c instanceof OWLObjectUnionOf)
			return todo.hasToDoEntry(n, NodeTag.OR, c, ds);
		else if(c instanceof OWLObjectSomeValuesFrom || c instanceof OWLObjectHasValue)
			return todo.hasToDoEntry(n, NodeTag.EXISTS, c, ds);
		else if(c instanceof OWLObjectAllValuesFrom)
			return todo.hasToDoEntry(n, NodeTag.FORALL, c, ds);
		else if(c instanceof OWLObjectMinCardinality)
			return todo.hasToDoEntry(n, NodeTag.LE, c, ds);
		else if(c instanceof OWLObjectMaxCardinality)
			return todo.hasToDoEntry(n, NodeTag.GE, c, ds);
		return false;
		
	}

	public void addToDoEntry(Node n, OWLClassExpression c, ConceptNDepSet cnds) {
		if(c instanceof OWLObjectIntersectionOf)
			todo.addEntry(n, NodeTag.AND, cnds);
		else if(c instanceof OWLObjectMinCardinality)
			todo.addEntry(n, NodeTag.LE, cnds);
		else if(c instanceof OWLObjectMaxCardinality)
			todo.addEntry(n, NodeTag.GE, cnds);
		else if(c instanceof OWLObjectUnionOf)
			todo.addEntry(n, NodeTag.OR, cnds);
		else if(c instanceof OWLObjectSomeValuesFrom || c instanceof OWLObjectHasValue)
			todo.addEntry(n, NodeTag.EXISTS, cnds);
		else if(c instanceof OWLObjectAllValuesFrom) {
			todo.addEntry(n, NodeTag.FORALL, cnds);
		}
	}
	
	 protected void save(Node n) {
		 cg.setCurrNode(n);
		// System.out.println("saving currentBranchingPoint : "+getCurLevel() +" Neighbour : "+cg.getCurrNode().getNeighbour().size()+" total nodes : "+ cg.getTotalNodes());
		// System.out.println("saving currentBP : "+getCurLevel() +" current node : "+n.getId());

		 cg.save();
		 todo.save(getCurLevel());
		 if(aboxReasoning) {
			 ar.save(getCurLevel());
		 }
		 
		//copyGraph(n);
		// currentBranchingPoint = currentBranchingPoint+1;
		// System.out.println("currentBranchingPoint : "+currentBranchingPoint);
	 }
	 protected void restore(int level) {
		// restoreBranchHandlers(getCurLevel(), level);
		// setCurLevel(level);
		 currRestore = level;
		 restoreGraph(level);
		 todo.restore(level);
	 }
	
	private void restoreBranchHandlers(int curLevel, int level) {
		if(level < curLevel) {
			for(int i = curLevel; i > level; i--)
				branches.remove(i);
		}
	}

	class BranchHandler{
		private List<OWLClassExpression> applicableOrEntries = new ArrayList<>();
		private List<OWLClassExpression> djTaken = new ArrayList<>();
		private int size;
		private int branchIndex;
		private OWLObjectUnionOf objUn;
		private DependencySet ds;
		private Node n;
		private ConceptNDepSet cnds;
		private Set<ToDoEntry> entries;
		private boolean ILPBranching = false;
		Set<Edge> outgoingEdges = new HashSet<>();
		Set<OWLSubClassOfAxiom> subsumption = new HashSet<>();
		protected BranchHandler(OWLObjectUnionOf objUn, ConceptNDepSet cnds, DependencySet ds , Node n) {
			objUn.asDisjunctSet().stream().forEach(ce -> applicableOrEntries.add(ce));
			this.size = applicableOrEntries.size();
			this.branchIndex = 0;
			this.objUn = objUn;
			this.ds = DependencySet.create(ds);
			this.n = n;
			this.cnds = cnds;
		}
		public Set<OWLSubClassOfAxiom> getSubsumption() {
			return this.subsumption;
		}
		protected BranchHandler(Set<ToDoEntry> entries, DependencySet ds , Node n, Set<Edge> outgoingEdges, Set<OWLSubClassOfAxiom> subsumption) {
			this.entries = entries;
			this.ds = DependencySet.create(ds);
			this.n = n;
			this.ILPBranching = true;
			this.outgoingEdges = outgoingEdges;
			this.subsumption.addAll(subsumption);
		}
		protected ConceptNDepSet getCnds() {
			return this.cnds;
		}
		protected OWLObjectUnionOf getObjUn() {
			return this.objUn;
		}
		protected void disjunctTaken(OWLClassExpression ce) {
			this.djTaken.add(ce);
		}
		protected List<OWLClassExpression> getAllNextOptions() {
			List<OWLClassExpression> ce = new ArrayList<>();
			for(int i = branchIndex; i< this.size; i++)
					ce.add(applicableOrEntries.get(i));
			ce.removeAll(this.djTaken);
			return ce;
		}
		protected OWLClassExpression getNextOption() {
			if(this.size >= branchIndex + 1){
				
			
			OWLClassExpression ce = applicableOrEntries.get(branchIndex);
			if(this.djTaken.contains(ce)) {
				++branchIndex;
				getNextOption();
			}
			//applicableOrEntries.remove(ce);
			++branchIndex;
			return ce;
		}
			return null;
		}
		protected Node getNode() {
			return this.n;
		}
		protected DependencySet getDs() {
			return this.ds;
		}
		protected boolean isLastOrEntry() {
            return size == branchIndex + 1;
        }
		protected boolean hasNextOption() {
            return size >= branchIndex + 1;
        }
		protected void reset() {
			branchIndex = 0;
			applicableOrEntries.clear();
			this.djTaken.clear();
			this.objUn.asDisjunctSet().stream().forEach(ce -> applicableOrEntries.add(ce));
			
		}
		
		public List<OWLClassExpression> getApplicableOrEntries() {
			return applicableOrEntries;
		}


		public void setApplicableOrEntries(List<OWLClassExpression> applicableOrEntries) {
			this.applicableOrEntries = applicableOrEntries;
		}
		public boolean isILPBranching(){
			return this.ILPBranching;
		}
		public Set<ToDoEntry> getAllEntries(){
			return this.entries;
		}
		public Set<OWLClassExpression> getRelatedConcepts(Node node){
			Set<OWLClassExpression> relatedConcepts = new HashSet<>();
			for(ToDoEntry entry : this.entries) {
				if(entry.getType().equals(NodeTag.LE)) {
					OWLObjectMinCardinality minCard = (OWLObjectMinCardinality) entry.getClassExpression();
					OWLClassExpression filler = minCard.getFiller();
					if(filler instanceof OWLClass || filler instanceof OWLObjectOneOf || filler instanceof OWLObjectComplementOf) {
						if(node.getSimpleILPLabel().contains(filler))
							relatedConcepts.add(filler);
					}
					else if(filler instanceof OWLObjectUnionOf) {
						for(OWLClassExpression ce : filler.asDisjunctSet()) {
							if(node.getSimpleILPLabel().contains(ce))
								relatedConcepts.add(ce);
						}
					}
					else if(filler instanceof OWLObjectIntersectionOf) {
						for(OWLClassExpression ce : filler.asConjunctSet()) {
							if(node.getSimpleILPLabel().contains(ce))
								relatedConcepts.add(ce);
						}
					}
				}
				if(entry.getType().equals(NodeTag.EXISTS)) {
					OWLObjectSomeValuesFrom someValue = (OWLObjectSomeValuesFrom) entry.getClassExpression();
					OWLClassExpression filler = someValue.getFiller();
					if(filler instanceof OWLClass || filler instanceof OWLObjectOneOf || filler instanceof OWLObjectComplementOf) {
						if(node.getSimpleILPLabel().contains(filler))
							relatedConcepts.add(filler);
					}
					else if(filler instanceof OWLObjectUnionOf) {
						for(OWLClassExpression ce : filler.asDisjunctSet()) {
							if(node.getSimpleILPLabel().contains(ce))
								relatedConcepts.add(ce);
						}
					}
					else if(filler instanceof OWLObjectIntersectionOf) {
						for(OWLClassExpression ce : filler.asConjunctSet()) {
							if(node.getSimpleILPLabel().contains(ce))
								relatedConcepts.add(ce);
						}
					}
					
				}
			}
			return relatedConcepts;
		}
	}
	

	    public void checkAboxConsistency(Set<OWLSubClassOfAxiom> aboxClassAss, OWLClassExpression tgAxiom) {
			this.tgAxiom = tgAxiom;
			for(OWLSubClassOfAxiom asb : aboxClassAss) {
				createAboxNode(asb,tgAxiom);
				processToDoList();
			}
		}

		/*public void checkAboxConsistency(Set<OWLSubClassOfAxiom> aboxClassAss, OWLClassExpression tgAxiom) {
			this.tgAxiom = tgAxiom;
			aboxReasoning = true;
			ar = new AboxReasoner(aboxClassAss);
			for(OWLSubClassOfAxiom asb : aboxClassAss) {
				ar.addProcessed(asb);
				createAboxNode(asb,tgAxiom);
				processToDoList();
			/*	while(!todo.isEmpty()) {
		    	 //	System.out.println("while loop "+ todo.entries());
			    	 	ToDoEntry entry = todo.getNextEntry();
			    	 	if(entry!=null)
			    	 			this.applyRules(entry);
				}
			}....*./
			if(currRestore != 0 && ar.needRestore(currRestore)){
				checkAboxConsistency2(ar.restore(currRestore), tgAxiom);
				currRestore = 0;
			}
		}*/
		public void checkAboxConsistency2(Set<OWLSubClassOfAxiom> aboxClassAss, OWLClassExpression tgAxiom) {
			ar.removeProcessed(aboxClassAss);
			for(OWLSubClassOfAxiom asb : aboxClassAss) {
				ar.addProcessed(asb);
				createAboxNode(asb,tgAxiom);
				processToDoList();
			/*	while(!todo.isEmpty()) {
		    	 //	System.out.println("while loop "+ todo.entries());
			    	 	ToDoEntry entry = todo.getNextEntry();
			    	 	if(entry!=null)
			    	 			this.applyRules(entry);
				}*/
			}
			
		}

		private void createAboxNode(OWLSubClassOfAxiom asb, OWLClassExpression tgAxiom) {
			OWLClassExpression sb =  asb.getSubClass();
		//	OWLClassExpression sp =  asb.getSuperClass();
			DependencySet ds = DependencySet.create();
			OWLClassExpression ci = df.getOWLObjectOneOf(((OWLObjectOneOf)sb).individuals().iterator().next());
		//	System.err.println("nominal "+ ci);
			Node nom = findNominalNode(ci);
			
			if(nom == null) {
				Node n = cg.addNode(NodeType.NOMINAL, ci, ds);
				System.err.println("nominal "+ ci + " node id "+ n.getId());
				this.absorbRule1(df.getOWLThing(), n, ds);
				addTGAxiom(n, ds);
				ConceptNDepSet cnds = new ConceptNDepSet(ci, ds);
				cg.addConceptToNode(n, cnds);
				absorbNominal(ci, n, ds);
			}
			else {
			//	System.out.println("nominal "+ ci + nom.getId());
				updateConceptDepSet(nom, ds, ci);
			}
			
		}
		
	 public boolean indLeft(Set<OWLSubClassOfAxiom> set) {
		
		 for(OWLSubClassOfAxiom asb : set) {
			 OWLClassExpression sb =  asb.getSubClass();
			 OWLClassExpression ci = df.getOWLObjectOneOf(((OWLObjectOneOf)sb).individuals().iterator().next());
				
				Node nom = findNominalNode(ci);
				if(nom == null) {
					System.out.println("nominal "+ ci);
					return true;
				}
		 }
		 return false;
	 }
	 /*
	  * process forall check if it has nominal
	  * 
	  */
}

