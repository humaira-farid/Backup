package reasoner; 

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.semanticweb.owlapi.model.*;
import com.google.common.collect.Multimap;

import ilog.concert.IloException;
import reasoner.Dependencies.DependencySet;
import reasoner.graph.*;
import reasoner.graph.Node.NodeType;
import reasoner.ilp.EdgeInformation;
import reasoner.ilp.ILPPreprocessor;
import reasoner.ilp.ILPSolution;
import reasoner.preprocessing.Internalization;
import reasoner.state.SaveStack;
import reasoner.todolist.ToDoEntry;
import reasoner.todolist.ToDoList;

public class RuleEngine1 {
	Internalization intl;
	CompletionGraph cg;
	ToDoList todo;
	private int currentBranchingPoint;
	OWLDataFactory df;
	boolean forAllCheck = false;
	boolean isExistential = false;
	Map<Integer, BranchHandler> branches = new HashMap<Integer, BranchHandler>();
	Map<Integer, CompletionGraph> copies = new HashMap<Integer, CompletionGraph>();
	Map<Integer, Multimap<Integer,OWLClassExpression>> branches2 = new HashMap<Integer, Multimap<Integer,OWLClassExpression>>();
	
	public RuleEngine1(Internalization i, ToDoList todo, OWLDataFactory df) {
		this.intl= i;
		this.todo = todo;
		this.cg = null;//new CompletionGraph(this);
		this.df = df;
	}
	
	public void checkConsistency(OWLClassExpression tgAxiom) {
		createFirstNode(tgAxiom);
		if(!todo.isEmpty()) {
			ToDoEntry entry = todo.getNextEntry();
			this.applyRules(entry);
		}
			
		while(!todo.isEmpty()) {
	    	 	//System.out.println("while loop "+ todo.entries());
	    	 	ToDoEntry entry = todo.getNextEntry();
	    	 	if(entry!=null) {
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
	    	 	}
		}
		//System.out.println("No. of nodes : "+ cg.getTotalNodes());
	}
	public boolean needILPModule(ToDoEntry entry) {
		/* if AND : get conjuncts and check ---->
		 * 1) if Exists then check fillers, if any one has nominal then we will call ilp, 
		 * 2) check for universal 
		 * 3) if OR 
		 */
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
			//return isNominal(filler);
			System.out.println("class expression "+filler);
			if(intl.getOntology().hasNominal(filler))
				return true;
			//System.out.println("class expression "+filler+ " size: "+ sup.size());
			/*if(sup.size()!=0) {
				for(OWLClassExpression c : sup) {
					if(c instanceof OWLObjectOneOf) {
						return true;
					}
					else if(c instanceof OWLClass) {
						return hasNominal(c);
					}
					else if(c instanceof OWLObjectIntersectionOf) {
						for(OWLClassExpression objIn : c.asConjunctSet()) {
							if(hasNominal(objIn))
									return true;
						}
					}
					else if(c instanceof OWLObjectUnionOf) {
						for(OWLClassExpression objUn : c.asDisjunctSet()) {
							if(hasNominal(objUn))
								return true;
						}
					}
				}
			}*/
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

	/*private boolean isNominal(OWLClassExpression ce) {
		if(ce instanceof OWLObjectOneOf) {
			return true; 
		}
		else {
			Set<OWLClassExpression> sup = this.intl.findConcept(ce);
		
			if(sup.size()!=0) {
				for(OWLClassExpression c : sup) {
					if(c instanceof OWLObjectOneOf) {
						return true;
					}
					else if(c instanceof OWLClass) {
						return isNominal(c);
					}
					else if(c instanceof OWLObjectIntersectionOf) {
						for(OWLClassExpression objIn : c.asConjunctSet()) {
							if(isNominal(objIn))
									return true;
						}
					}
					else if(c instanceof OWLObjectUnionOf) {
						for(OWLClassExpression objUn : c.asDisjunctSet()) {
							if(isNominal(objUn))
								return true;
						}
					}
				}
			}
		}
		return false;
	}*/

	public void callILP(ToDoEntry entry) {
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
				Edge e = this.cg.getEdge(n, ei.getFillers(), roles);
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
								e = this.cg.addEdge(n, to, roles, ds);
							}
							else {
								System.err.println("Sorry! it needs Merging!");
								Main.getExecutionTime();
								System.exit(0);
							}
						}
						else {
							to =this.cg.addNode(NodeType.NOMINAL);
							e = this.cg.addEdge(n, to, roles, ds);
						}
					}
					else {
						to =this.cg.addNode(NodeType.BLOCKABLE);
						e = this.cg.addEdge(n, to, roles, ds);
					}
					
				}
				else {
					to = e.getToNode();
					updateEdgeDepSet(ds, e);
					
				}
				addLabel(to, ei.getFillers(), ds);
			}
		}
		else {
			isInconsistent(n);
		}
	}
	private void addLabel(Node n, Set<OWLClassExpression> fillers, DependencySet ds) {
		for(OWLClassExpression ce : fillers) {
			if(isConceptExist(n, ce)) {
				updateConceptDepSet(n, ds, ce);
				if(!((ce instanceof OWLClass) || (ce instanceof OWLObjectOneOf)))
					updateToDoEntryDepSet(n, ce, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(ce)).iterator().next().getDs());
			}
			else {
				ConceptNDepSet cnds = new ConceptNDepSet(ce,ds);
				if(ce instanceof OWLObjectOneOf) {
					this.cg.addConceptToNode(n, cnds);
					if(!checkClash(n, ce)) {
						absorbNominal(ce, n, ds);
					}
					else {
						DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
						if(!clashSet.isEmpty()) {
							if(!clashHandler(clashSet))
								isInconsistent(n);
						}
						else
							isInconsistent(n);
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
						else 
							addToDoEntry(n, ce, cnds);
						}
					else {
						DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
						if(!clashSet.isEmpty()) {
							if(!clashHandler(clashSet))
								isInconsistent(n);
							break;
						}
						else
							isInconsistent(n);
					}
				}
			}
		}
	}

	public void createFirstNode(OWLClassExpression tgAxiom) {
		
		Node from = cg.addNode(NodeType.NOMINAL, tgAxiom);
		ConceptNDepSet cnds = new ConceptNDepSet(tgAxiom, DependencySet.create());
		cg.addConceptToNode(from, cnds);
		todo.addEntry(from, NodeTag.AND, cnds);
	}
	
	public void applyRules(ToDoEntry entry) {
		
		Node n = entry.getNode();
		NodeTag nt = entry.getType();
		switch(nt) {
		case AND:
			applyAndRule(n, (OWLObjectIntersectionOf)entry.getClassExpression(), entry.getDs());
			break;
		case OR:
			applyOrRule(n, (OWLObjectUnionOf)entry.getClassExpression(), entry.getDs());
			break;
		case EXISTS:
			if(entry.getClassExpression() instanceof OWLObjectSomeValuesFrom)
				applyExistentialRule(n, (OWLObjectSomeValuesFrom)entry.getClassExpression(), entry.getDs());
			else 
				applyExistentialRule(n, (OWLObjectHasValue)entry.getClassExpression(), entry.getDs());
			break;
		case FORALL:
			applyForAllRule(n, (OWLObjectAllValuesFrom)entry.getClassExpression(), entry.getDs());
			break;
		default:
			break;
		}
		
	}

	public void applyExistentialRule(Node from, OWLObjectSomeValuesFrom objSV, DependencySet ds) {
		System.out.println("Applying exist Rule...");
		if(!from.isBlocked()) {
			OWLObjectPropertyExpression role = objSV.getProperty();
			OWLClassExpression filler = objSV.getFiller();
			Edge e = this.cg.getEdge(from, filler, role);
			if(e == null) {
				Node blocker =  findBlocker(from);
				if(blocker != null) {
					cg.setNodeBlocked(from, blocker);
					return;
				}
				if(filler instanceof OWLObjectOneOf) {
					OWLClassExpression ci = df.getOWLObjectOneOf(((OWLObjectOneOf)filler).individuals().iterator().next());
					Node nom = findNominalNode(ci);
					if(nom != null) {
						e = this.cg.addEdge(from, nom, role, ds);
						updateConceptDepSet(nom, ds, ci);
						processForAll(from);
						processForAll(nom);
					}
					else {
						Node to =this.cg.addNode(NodeType.NOMINAL, ci);
						to.setConceptsDependencies(ci, ds);
						ConceptNDepSet cnds = new ConceptNDepSet(ci, ds);
						e = this.cg.addEdge(from, to, role, ds);
						this.cg.addConceptToNode(to, cnds);
						processForAll(from);
						absorbNominal(ci, to, ds);
						
					}
				}
				
				else {
					Node to =this.cg.addNode(NodeType.BLOCKABLE, filler);
					to.setConceptsDependencies(filler, ds);
					ConceptNDepSet cnds = new ConceptNDepSet(filler, ds);
					e = this.cg.addEdge(from, to, role, ds);
					this.cg.addConceptToNode(to, cnds);
					processForAll(from);
					if(filler instanceof OWLClass) { 
						to.addSimpleLabel(filler);
						absorbRule1(filler, to, ds);
						absorbRule2(to);
					}
					else 
						addToDoEntry(to, filler, cnds);
				}
			}
			else {
				Node to = e.getToNode();
				updateConceptDepSet(to, ds, filler);
				updateEdgeDepSet(ds, e);
				if(!(filler instanceof OWLClass))
					updateToDoEntryDepSet(to, filler, to.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).iterator().next().getDs());
				
			}
		}
	}
	public void applyExistentialRule(Node from, OWLObjectHasValue objSV, DependencySet ds) {
		System.out.println("Applying has value Rule...");
		if(!from.isBlocked()) {
		OWLObjectPropertyExpression role = objSV.getProperty();
		OWLClassExpression filler = df.getOWLObjectOneOf(objSV.getFiller());
		Edge e = this.cg.getEdge(from, filler, role);
		
		if(e == null) {
			Node blocker = findBlocker(from);
			if(blocker != null) {
				cg.setNodeBlocked(from, blocker);
				return;
			}
			OWLClassExpression ci = df.getOWLObjectOneOf(((OWLObjectOneOf)filler).individuals().iterator().next());
			Node nom = findNominalNode(ci);
			if(nom != null) {
				e = this.cg.addEdge(from, nom, role, ds);
				updateConceptDepSet(nom, ds, filler);
				processForAll(from);
				processForAll(nom);
			}
			else {
				Node to =this.cg.addNode(NodeType.NOMINAL, filler);
				to.setConceptsDependencies(filler, ds);
				ConceptNDepSet cnds = new ConceptNDepSet(filler, ds);
				e = this.cg.addEdge(from, to, role, ds);
				this.cg.addConceptToNode(to, cnds);
				processForAll(from);
				absorbNominal(filler, to, ds);
			}
		}
		else {
			Node to = e.getToNode();
			updateConceptDepSet(to, ds, filler);
			updateEdgeDepSet(ds, e);
		}
		}
	}
	
	
	private void processExistentialRestriction(Node from, OWLObjectSomeValuesFrom objSV, DependencySet ds) {
		System.out.println("Processing exist Rule...");
		if(!from.isBlocked()) {
			Node blocker =  findBlocker(from);
			if(blocker != null) {
				cg.setNodeBlocked(from, blocker);
				return;
			}
			OWLObjectPropertyExpression role = objSV.getProperty();
			OWLClassExpression filler = objSV.getFiller();
			from.addqLE(this.df.getOWLObjectMinCardinality(1, role, filler), ds);
			//Edge e = this.cg.getEdge(from, filler, role);
			//if(e == null) {
				
			//	if(filler instanceof OWLObjectOneOf) {
			//		OWLClassExpression ci = df.getOWLObjectOneOf(((OWLObjectOneOf)filler).individuals().iterator().next());
			//		Node nom = findNominalNode(ci);
			//		if(nom != null) {
			//			e = this.cg.addEdge(from, nom, role, ds);
			//			updateConceptDepSet(nom, ds, ci);
			//			processForAll(from);
			//			processForAll(nom);
			//		}
			//		else {
			//			Node to =this.cg.addNode(NodeType.NOMINAL, ci);
			//			to.setConceptsDependencies(ci, ds);
			//			ConceptNDepSet cnds = new ConceptNDepSet(ci, ds);
			//			e = this.cg.addEdge(from, to, role, ds);
			//			this.cg.addConceptToNode(to, cnds);
			//			processForAll(from);
			//			absorbNominal(ci, to, ds);
						
			//		}
			//	}
				
			//	else {
			//		Node to =this.cg.addNode(NodeType.BLOCKABLE, filler);
			//		to.setConceptsDependencies(filler, ds);
			//		ConceptNDepSet cnds = new ConceptNDepSet(filler, ds);
			//		e = this.cg.addEdge(from, to, role, ds);
			//		this.cg.addConceptToNode(to, cnds);
			//		processForAll(from);
			//		if(filler instanceof OWLClass) { 
			//			to.addSimpleLabel(filler);
			//			absorbRule1(filler, to, ds);
			//			absorbRule2(to);
			//		}
			//		else 
			//			addToDoEntry(to, filler, cnds);
			//	}
		//	}
		//	else {
			//	Node to = e.getToNode();
			//	updateConceptDepSet(to, ds, filler);
			//	updateEdgeDepSet(ds, e);
			//	if(!(filler instanceof OWLClass))
			//		updateToDoEntryDepSet(to, filler, to.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).iterator().next().getDs());
				
		//	}
		}

	}

	private void processForAll(Node node) {
		node.getLabel().stream().filter(l -> l instanceof OWLObjectAllValuesFrom).
			forEach(l -> applyForAllRule(node, (OWLObjectAllValuesFrom)l, node.getnLabel().getCndList().getCdSet().stream().filter(cds -> cds.getCe().equals(l)).iterator().next().getDs()));
		
	}

	public void applyForAllRule(Node from, OWLObjectAllValuesFrom objAV, DependencySet ds) {
		System.out.println("Applying for all Rule...");
		if(!from.isBlocked()) {
			OWLObjectPropertyExpression role = objAV.getProperty();
			OWLClassExpression filler = objAV.getFiller();
			
			Set<Edge> edges = this.cg.getEdge(from, role);
			if(edges.size()!=0) {
				for(Edge e : edges) {
					Node n = e.getToNode();
					if(isConceptExist(n, filler)) {
						updateConceptDepSet(n, updateDepSetForAll(e, ds), filler);
						if(!(filler instanceof OWLClass))
							updateToDoEntryDepSet(n, filler, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).iterator().next().getDs());
					}
					else if(filler instanceof OWLObjectOneOf) {
						OWLClassExpression ci = df.getOWLObjectOneOf(((OWLObjectOneOf)filler).individuals().iterator().next());
						Node nom = findNominalNode(ci);
						if(nom == null) {
							DependencySet depSet =  updateDepSetForAll(e, ds);
							ConceptNDepSet cnds = new ConceptNDepSet(filler, depSet);
							this.cg.addConceptToNode(n, cnds);
							cg.checkBlockedStatus(n);
							n.makeNominalNode();
							if(!checkClash(n, filler)) {
								absorbNominal(filler, n, depSet);
							}
							else {
								DependencySet clashSet = getClashSet(n, filler, filler.getComplementNNF());
								if(!clashSet.isEmpty()) {
									if(!clashHandler(clashSet))
										isInconsistent(n);
								}
								else
									isInconsistent(n);
							}
						}
						else {
							System.err.println("Sorry! it needs Merging!");
							Main.getExecutionTime();
							System.exit(0);
						}
					}
					else {
						DependencySet depSet =  updateDepSetForAll(e, ds);
						ConceptNDepSet cnds = new ConceptNDepSet(filler, depSet);
						this.cg.addConceptToNode(n, cnds);
						cg.checkBlockedStatus(n);
						if(!checkClash(n, filler)) {
							if(filler instanceof OWLClass) {
								n.addSimpleLabel(filler);
								absorbRule1(filler, n, depSet);
								absorbRule2(n);
							}
							else 
								addToDoEntry(n, filler, cnds);
						}
						else {
							DependencySet clashSet = getClashSet(n, filler, filler.getComplementNNF());
							if(!clashSet.isEmpty()) {
								if(!clashHandler(clashSet))
									isInconsistent(n);
							}
							else
								isInconsistent(n);
								
						}
					}
				}
			}
		}
		//else we cannot apply forAll rule
	}
	
	private void isInconsistent(Node n) {
		//if(n.isNominalNode()) {
			System.err.println("Your ontology is inconsistent");
			Main.getExecutionTime();
			System.exit(0);
		//}
		
	}

	public void applyAndRule(Node n, OWLObjectIntersectionOf objIn, DependencySet ds) {
		System.out.println("Applying and Rule...");
		if(!n.isBlocked()) {
			for(OWLClassExpression ce : objIn.asConjunctSet()) {
				if(isConceptExist(n, ce)) {
					updateConceptDepSet(n, ds, ce);
					if(!(ce instanceof OWLClass))
						updateToDoEntryDepSet(n, ce, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(ce)).iterator().next().getDs());
				}
				else {
					ConceptNDepSet cnds = new ConceptNDepSet(ce,ds);
					if(ce instanceof OWLObjectOneOf) {
						processNominal(ce, n, cnds, ds);
					}
					else {
						this.cg.addConceptToNode(n, cnds);
						if(!checkClash(n, ce)) {
							if(ce instanceof OWLClass) {
								n.addSimpleLabel(ce);
								absorbRule1(ce, n, ds);
								absorbRule2(n);
							}
							else 
								addToDoEntry(n, ce, cnds);
							}
						else {
							DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
							if(!clashSet.isEmpty()) {
								if(!clashHandler(clashSet))
									isInconsistent(n);
								break;
							}
							else
								isInconsistent(n);
						}
					}
				}
			}
		}
	}
	public void applyOrRule(Node n, OWLObjectUnionOf objUn, DependencySet ds) {
		System.out.println("Applying or Rule...");
		if(!n.isBlocked()) {
			BranchHandler bh = new BranchHandler(objUn, ds);
			incCurLevel();
			//copyGraph(n);
			save(n);
			
			this.branches.put(getCurLevel(), bh);
			ds.add(DependencySet.create(getCurLevel()));
			if(bh.hasNextOption()) {
				applyOr(n,bh.getNextOption(),ds);
			}
		}
	}
	
	public void applyOr(Node n, OWLClassExpression ce, DependencySet ds) {
			//System.out.println("or expression selected : "+ce);
			if(isConceptExist(n, ce)) {
				updateConceptDepSet(n, ds, ce);
				if(!(ce instanceof OWLClass))
					updateToDoEntryDepSet(n, ce, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(ce)).iterator().next().getDs());
			}
			else {
			ConceptNDepSet cnds = new ConceptNDepSet(ce, ds);
			if(ce instanceof OWLObjectOneOf) {
				processNominal(ce, n, cnds, ds);
			}
			else {
				this.cg.addConceptToNode(n, cnds);
				if(!checkClash(n, ce)) {
					if(ce instanceof OWLClass) {
						n.addSimpleLabel(ce);
						absorbRule1(ce, n, ds);
						absorbRule2(n);
					}
					else 
						addToDoEntry(n, ce, cnds);
				}
				else {
					DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
					if(!clashSet.isEmpty()) {
						if(!clashHandler(clashSet))
							isInconsistent(n);
					}
					else
						isInconsistent(n);
				}
			}
		}
	}
		
	
	private void processNominal(OWLClassExpression ce, Node n, ConceptNDepSet cnds, DependencySet ds) {
		OWLClassExpression ci = df.getOWLObjectOneOf(((OWLObjectOneOf)ce).individuals().iterator().next());
		Node nom = findNominalNode(ci);
		if(nom == null) {
			this.cg.addConceptToNode(n, cnds);
			n.makeNominalNode();
			if(!checkClash(n, ce)) {
				absorbNominal(ce, n, ds);
			}
			else {
				DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
				if(!clashSet.isEmpty()) {
					if(!clashHandler(clashSet))
						isInconsistent(n);
				}
				else
					isInconsistent(n);
			}
		}
		else {
			System.err.println("Sorry! it needs Merging!");
			Main.getExecutionTime();
			System.exit(0);
		}
		
	}

	private boolean clashHandler(DependencySet clashSet) {
		
		System.out.println("Clash handler...");
		if(!clashSet.isEmpty()) {
		
			int level = clashSet.getMax();
			System.out.println("level" + level);
			System.out.println(cg.getTotalNodes());
			restore(level);
			if( branches.get(level).hasNextOption()) {
				save(cg.getCurrNode());
				//System.out.println("restoring currentBranchingPoint : "+getCurLevel() +" Neighbour : "+cg.getCurrNode().getOutgoingEdges().size()+" total nodes : "+ cg.getTotalNodes());

				applyOr(cg.getCurrNode(), branches.get(level).getNextOption(), branches.get(level).ds);
			}
			else {
				branches.get(level).reset();
				branches.remove(level);
				clashSet.removeLevel(level);
				if(!clashHandler(clashSet))
					return false;
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

	public void applyNominalRule() {
		
	}
	
	public boolean checkClash(Node n, OWLClassExpression c) {
		if(n.getLabel().contains(c.getComplementNNF())) {
			//n.addLabel(OWLFunctionalSyntaxFactory.OWLNothing());
			return true;
		}
		return false;
	}
	
	public Node findBlocker(Node n) {
		return cg.findAnywhereBlocker(n);
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

	private void applyAllGeneratingRules(Node node) {
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
         
    }
	public DependencySet getClashSet(Node n, OWLClassExpression ce, OWLClassExpression ceNNF) {
		ConceptNDepSet cnd1 = n.getnLabel().getCndList().getCdSet().stream().filter(cds -> cds.getCe().equals(ce)).iterator().next();
		ConceptNDepSet cnd2 = n.getnLabel().getCndList().getCdSet().stream().filter(cds -> cds.getCe().equals(ceNNF)).iterator().next();
		if(cnd1.getDs().isEmpty() && cnd2.getDs().isEmpty())
			return DependencySet.create();
		else 
			return DependencySet.plus(cnd1.getDs(), cnd2.getDs());
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
		//System.out.println("applying absorbRule 1 : "+ ce);
		Set<OWLClassExpression> sup = this.intl.findConcept(ce);
		
		if(sup.size()!=0) {
			for(OWLClassExpression c : sup) {
				if(isConceptExist(n, c)) {
					updateConceptDepSet(n, ds, c);
					if(!(c instanceof OWLClass))
						updateToDoEntryDepSet(n, c, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(c)).iterator().next().getDs());
				}
				else {
					ConceptNDepSet cnds = new ConceptNDepSet(c, ds);
					if(ce instanceof OWLObjectOneOf) {
						processNominal(c, n, cnds, ds);
					}
					else {
						cg.addConceptToNode(n, cnds);
						if(!checkClash(n, c)) {
							if(c instanceof OWLClass) { 
								n.addSimpleLabel(c);
								absorbRule1(c, n, ds);
							}
							else 
								addToDoEntry(n, c, cnds);
						}
						else {
							DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
							if(!clashSet.isEmpty()) {
								if(!clashHandler(clashSet))
									isInconsistent(n);
							}
							else
								isInconsistent(n);
						}
					}
				}
			}
		}
	}
	public void absorbRule2(Node n) {
		Set<OWLSubClassOfAxiom> sbAx = this.intl.getTui();
		Set<OWLClassExpression> classes = n.getSimpleLabel();
		
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
				OWLClassExpression c = sb.getSuperClass();
				if(isConceptExist(n, c)) {
					updateConceptDepSet(n, dep, c);
					if(!(c instanceof OWLClass))
						updateToDoEntryDepSet(n, c, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(c)).iterator().next().getDs());
				}
				else {
					ConceptNDepSet cnds = new ConceptNDepSet(c, dep);
					if(c instanceof OWLObjectOneOf) {
						processNominal(c, n, cnds, dep);
					}
					else {
						cg.addConceptToNode(n, cnds);
						if(!checkClash(n, c)) {
							if(c instanceof OWLClass) { 
							n.addSimpleLabel(c);
							absorbRule1(c, n, dep);
							absorbRule2(n);
						}
						else 
							addToDoEntry(n, c, cnds);
						}
						else {
							DependencySet clashSet = getClashSet(n, c, c.getComplementNNF());
							if(!clashSet.isEmpty()) {
								if(!clashHandler(clashSet))
									isInconsistent(n);
							}
							else
								isInconsistent(n);
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
		//System.out.println("applying absorb Nominal : "+ ce);
		Set<OWLClassExpression> sup = this.intl.findIndividual(ce);
		//System.out.println("contains "+ sup.size());
		
		if(sup.size()!=0) {
			for(OWLClassExpression c : sup) {
				if(isConceptExist(n, c)) {
					updateConceptDepSet(n, ds, c);
					if(!(c instanceof OWLClass))
						updateToDoEntryDepSet(n, c, n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(c)).iterator().next().getDs());
				}
				else {
					ConceptNDepSet cnds = new ConceptNDepSet(c, ds);
					if(c instanceof OWLObjectOneOf) {
						processNominal(c, n, cnds, ds);
					}
					else {
						cg.addConceptToNode(n, cnds);
						if(!checkClash(n, c)) {
							if(c instanceof OWLClass) { 
								n.addSimpleLabel(c);
								absorbRule1(c, n, ds);
								absorbRule2(n);
							}
							else 
								addToDoEntry(n, c, cnds);
						}
						else {
							DependencySet clashSet = getClashSet(n, c, c.getComplementNNF());
							if(!clashSet.isEmpty()) {
								if(!clashHandler(clashSet))
									isInconsistent(n);
							}
							else
								isInconsistent(n);
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
		ConceptNDepSet cnd = n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).iterator().next();
		if(cnd.getDs().isEmpty() || ds.isEmpty()) {
			n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).forEach(cnds -> cnds.setDs(DependencySet.create()));
			//cnd.setDs(DependencySet.create());
		}
		else {
			n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).forEach(cnds -> cnds.setDs(DependencySet.plus(cnds.getDs(), ds)));
			//cnd.setDs(DependencySet.plus(cnd.getDs(), ds));
		}
	}
	public DependencySet updateDepSetForAll(Edge e, DependencySet ds) {
		DependencySet depSet = DependencySet.create(ds);
		if(!e.getDepSet().isEmpty())
			DependencySet.plus(depSet, e.getDepSet());
		return ds;
	}
	
	public void updateEdgeDepSet(DependencySet ds, Edge e) {
		
		if(e.getDepSet().isEmpty() || ds.isEmpty())
			e.setDepSet(DependencySet.create());
		else
			e.setDepSet(DependencySet.plus(e.getDepSet(), ds));
		
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
		
		
	}

	public void addToDoEntry(Node n, OWLClassExpression c, ConceptNDepSet cnds) {
		if(c instanceof OWLObjectIntersectionOf)
			todo.addEntry(n, NodeTag.AND, cnds);
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

		 cg.save();
		 todo.save();
		// currentBranchingPoint = currentBranchingPoint+1;
		// System.out.println("currentBranchingPoint : "+currentBranchingPoint);
	 }
	 protected void restore(int level) {
		 restoreBranchHandlers(getCurLevel(), level);
		 setCurLevel(level);
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
		private int size;
		private int branchIndex;
		private OWLObjectUnionOf objUn;
		private DependencySet ds;
		protected BranchHandler(OWLObjectUnionOf objUn, DependencySet ds) {
			objUn.asDisjunctSet().stream().forEach(ce -> applicableOrEntries.add(ce));
			size = applicableOrEntries.size();
			branchIndex = 0;
			this.objUn = objUn;
			this.ds = ds;
		}
		
		
		protected OWLClassExpression getNextOption() {
			OWLClassExpression ce = applicableOrEntries.get(branchIndex);
			//applicableOrEntries.remove(ce);
			branchIndex++;
			return ce;
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
			this.objUn.asDisjunctSet().stream().forEach(ce -> applicableOrEntries.add(ce));
			
		}

		public List<OWLClassExpression> getApplicableOrEntries() {
			return applicableOrEntries;
		}


		public void setApplicableOrEntries(List<OWLClassExpression> applicableOrEntries) {
			this.applicableOrEntries = applicableOrEntries;
		}
	}
	
	
	    
	    public enum AddConceptResult {
	        /** acrClash */
	        CLASH,
	        /** acrExist */
	        EXIST,
	        /** acrDone */
	        DONE
	    }



		public void checkAboxConsistency(Set<OWLSubClassOfAxiom> aboxClassAss) {
			for(OWLSubClassOfAxiom asb : aboxClassAss) {
				createAboxNode(asb);
				while(!todo.isEmpty()) {
		    	 //	System.out.println("while loop "+ todo.entries());
			    	 	ToDoEntry entry = todo.getNextEntry();
			    	 	if(entry!=null)
			    	 			this.applyRules(entry);
				}
			}
			
		}

		private void createAboxNode(OWLSubClassOfAxiom asb) {
			OWLClassExpression sb =  asb.getSubClass();
			OWLClassExpression sp =  asb.getSuperClass();
			DependencySet ds = DependencySet.create();
			OWLClassExpression ci = df.getOWLObjectOneOf(((OWLObjectOneOf)sb).individuals().iterator().next());
			Node nom = findNominalNode(ci);
			if(nom == null) {
				Node n = cg.addNode(NodeType.NOMINAL, ci);
				ConceptNDepSet cnds = new ConceptNDepSet(ci, ds);
				cg.addConceptToNode(n, cnds);
				absorbNominal(ci, n, ds);
			}
			else
				updateConceptDepSet(nom, ds, ci);
			
		}
	
}

