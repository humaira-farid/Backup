package reasoner;

import static reasoner.Helper.INITBRANCHINGLEVELVALUE;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;
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

public class RuleEngine {

	Internalization intl;
	Ontology ontology;
	CompletionGraph cg;
	ToDoList todo;
	private int currentBranchingPoint;
	OWLDataFactory df;
	boolean forAllCheck = false;
	boolean isExistential = false;
	boolean aboxReasoning = false;
	boolean consistencyCheckGE = true;
	Map<Integer, BranchHandler> branches = new HashMap<Integer, BranchHandler>();
	SetMultimap<Node, ToDoEntry> nodeEntries = HashMultimap.create();
	List<ToDoEntry> entries = new ArrayList<>();
	SetMultimap<Node, OWLObjectPropertyExpression> axiomRoles = HashMultimap.create();
	SetMultimap<Node, ToDoEntry> nodeExistEntries = HashMultimap.create();
	SetMultimap<Node, ToDoEntry> nodeMinEntries = HashMultimap.create();
	SetMultimap<Node, ToDoEntry> nodeMaxEntries = HashMultimap.create();
	SetMultimap<Node, ToDoEntry> nodeForAllEntries = HashMultimap.create();
	SetMultimap<Node, ToDoEntry> relatedForAllEntries = HashMultimap.create();
	SetMultimap<Node, ToDoEntry> relatedMaxEntries = HashMultimap.create();
	SetMultimap<Node, ToDoEntry> unrelatedMaxEntries = HashMultimap.create();
	SetMultimap<Node, ToDoEntry> unrelatedForAllEntries = HashMultimap.create();
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
	Logger LOG;
	Set<OWLObjectPropertyExpression> symmRoles = new HashSet<>();

	public RuleEngine(Internalization i, ToDoList todo, OWLDataFactory df, Configuration config, Logger LOG) {
		this.intl = i;
		this.todo = todo;
		this.df = df;
		this.cg = new CompletionGraph(this, config, df);
		this.config = config;
		currentBranchingPoint = INITBRANCHINGLEVELVALUE;
		this.ontology = this.intl.getOntology();
		this.prefixManager = intl.getPrefixManager();
		this.base = this.prefixManager.getDefaultPrefix();
		this.todo.initPriorities("01");
		this.LOG = LOG;
		
		
	}

	public void setTransitiveRoles(Set<OWLObjectPropertyExpression> trans) {
		this.transitiveRoles = trans;

	}

	/**
	 * checking ontology consistency
	 * 
	 * @param tgAxiom
	 */
	public void checkConsistency(OWLClassExpression tgAxiom) {
		this.tgAxiom = tgAxiom;
		if(!createFirstNode(tgAxiom))
			return;
		if (config.isALC() || config.isSHI()) {
			while (!todo.isEmpty()) {
				ToDoEntry entry = todo.getNextEntry();
				 System.out.println("node id "+ entry.getNode().getId());
				 System.out.println("while loop "+ entry.getClassExpression());
				if (entry != null && !entry.getNode().isReset()) {
					this.applyRules(entry);
				}
			}
		} else {
			processToDoList();
		}
		// LOG.severe("No. of nodes : "+ cg.getTotalNodes());
		// System.out.println("No. of nodes : "+ cg.getTotalNodes());
	}

	public boolean createFirstNode(OWLClassExpression tgAxiom) {
		Node from = cg.addNode(NodeType.NOMINAL, DependencySet.create());
		from = addConcept(from, tgAxiom, DependencySet.create(), false);
		if (from == null) {
			return false;
		} else if (from.getId() == -1) {
			return true;
		}
	// }
	return true;
		/*Node from = cg.addNode(NodeType.NOMINAL, tgAxiom, DependencySet.create());
		  if (!this.absorbRule1(df.getOWLThing(), from, DependencySet.create()))
			return;
		ConceptNDepSet cnds = new ConceptNDepSet(tgAxiom, DependencySet.create());
		cg.addConceptToNode(from, cnds);
		addToDoEntry(from, tgAxiom, cnds);*/
		// todo.addEntry(from, NodeTag.AND, cnds);
	}

	private void processToDoList() {
		// System.out.println("while loop empty? "+ todo.isEmpty());
		while (!todo.isEmpty()) {
			// System.out.println("while loop "+ todo.entries() );
			ToDoEntry entry = todo.getNextEntry();
			// System.out.println(" node reset? "+entry.getNode().isReset());
			// System.out.println("processToDoList ");
			if (entry != null && !entry.getNode().isReset()) {
				Node n = entry.getNode();
				if (currNode == null)
					currNode = n;
				// System.err.println("n "+ n.getId() +" entry "+ entry.getClassExpression() +" curr node "+ currNode.getId());

				if (currNode != null && currNode.equals(n))
					processEntry(entry);

				else {
					if (!proceedWithProcessedEntries())
						continue;
					if (cg.getNodeBase().contains(entry.getNode())) {
						LOG.log(Level.WARNING, "process entry here... ");
						currNode = entry.getNode();
						processEntry(entry);
					}
				}
			}
		}
		// System.err.println("outside while");
		proceedWithProcessedEntries();
		if (!todo.isEmpty())
			processToDoList();
	}

	private boolean proceedWithProcessedEntries() {
		if (!nodeExistEntries.get(currNode).isEmpty() || !nodeMinEntries.get(currNode).isEmpty()) {
			if (isNIRuleApplicable(currNode)) {
				LOG.log(Level.INFO, "ni applicable 1, Node: " + currNode.getId());
				addExistentialRestrictions(currNode);
			}
			addRangeRestrictions(this.axiomRoles.get(currNode));
			checkRelatedForAll(currNode, nodeForAllEntries.get(currNode), this.axiomRoles.get(currNode));
			checkRelatedMax(currNode, nodeMaxEntries.get(currNode), this.axiomRoles.get(currNode));
			if (!relatedMaxEntries.get(currNode).isEmpty())
				checkOutgoingEdges(currNode, relatedMaxEntries.get(currNode));
			if (needILPModule(currNode)) {
				Set<ToDoEntry> entries = new HashSet<>();
				if (!nodeExistEntries.get(currNode).isEmpty())
					entries.addAll(nodeExistEntries.get(currNode));
				if (!nodeMinEntries.get(currNode).isEmpty())
					entries.addAll(nodeMinEntries.get(currNode));
				if (!relatedMaxEntries.get(currNode).isEmpty())
					entries.addAll(relatedMaxEntries.get(currNode));
				if (!relatedForAllEntries.get(currNode).isEmpty())
					entries.addAll(relatedForAllEntries.get(currNode));
				nodeExistEntries.get(currNode).clear();
				nodeMinEntries.get(currNode).clear();
				nodeMaxEntries.get(currNode).clear();
				nodeForAllEntries.get(currNode).clear();
				relatedForAllEntries.get(currNode).clear();
				relatedMaxEntries.get(currNode).clear();
				if (!callILP(currNode, entries, new HashSet<OWLSubClassOfAxiom>(this.niSubAx), outgoingEdges)) {
					unrelatedForAllEntries.get(currNode).clear();
					unrelatedMaxEntries.get(currNode).clear();
					axiomRoles.get(currNode).clear();
					this.niSubAx.clear();
					return false;
				}
				for (ToDoEntry en : unrelatedMaxEntries.get(currNode))
					if (!applyRules(en)) {
						unrelatedForAllEntries.get(currNode).clear();
						unrelatedMaxEntries.get(currNode).clear();
						axiomRoles.get(currNode).clear();
						this.niSubAx.clear();
						return false;
					}
				for (ToDoEntry en : unrelatedForAllEntries.get(currNode))
					if (!applyRules(en)) {
						unrelatedForAllEntries.get(currNode).clear();
						unrelatedMaxEntries.get(currNode).clear();
						axiomRoles.get(currNode).clear();
						this.niSubAx.clear();
						return false;
					}
				unrelatedForAllEntries.get(currNode).clear();
				unrelatedMaxEntries.get(currNode).clear();
				axiomRoles.get(currNode).clear();
				this.niSubAx.clear();
			} else {
				if (!nodeExistEntries.get(currNode).isEmpty()) {
					for (ToDoEntry en : nodeExistEntries.get(currNode))
						if (!applyRules(en)) {
							nodeMaxEntries.get(currNode).clear();
							unrelatedMaxEntries.get(currNode).clear();
							unrelatedForAllEntries.get(currNode).clear();
							nodeExistEntries.get(currNode).clear();
							nodeForAllEntries.get(currNode).clear();
							axiomRoles.get(currNode).clear();
							return false;
						}
				}
				if (!nodeForAllEntries.get(currNode).isEmpty()) {
					for (ToDoEntry en : nodeForAllEntries.get(currNode))
						if (!applyRules(en)) {
							nodeMaxEntries.get(currNode).clear();
							unrelatedMaxEntries.get(currNode).clear();
							unrelatedForAllEntries.get(currNode).clear();
							nodeExistEntries.get(currNode).clear();
							nodeForAllEntries.get(currNode).clear();
							axiomRoles.get(currNode).clear();
							return false;
						}
				}
				if (!nodeMaxEntries.get(currNode).isEmpty()) {
					for (ToDoEntry en : nodeMaxEntries.get(currNode))
						if (!applyRules(en)) {
							nodeMaxEntries.get(currNode).clear();
							unrelatedMaxEntries.get(currNode).clear();
							unrelatedForAllEntries.get(currNode).clear();
							nodeExistEntries.get(currNode).clear();
							nodeForAllEntries.get(currNode).clear();
							axiomRoles.get(currNode).clear();
							return false;
						}
				}
				nodeMaxEntries.get(currNode).clear();
				unrelatedMaxEntries.get(currNode).clear();
				unrelatedForAllEntries.get(currNode).clear();
				nodeExistEntries.get(currNode).clear();
				nodeForAllEntries.get(currNode).clear();
				axiomRoles.get(currNode).clear();
			}
		} else if (!nodeMaxEntries.get(currNode).isEmpty() || !nodeForAllEntries.get(currNode).isEmpty()) {
			if (isNIRuleApplicable(currNode)) {
				LOG.log(Level.INFO, "ni applicable 2 ");
				addExistentialRestrictions(currNode);
				addRangeRestrictions(this.axiomRoles.get(currNode));
				checkRelatedForAll(currNode, nodeForAllEntries.get(currNode), this.axiomRoles.get(currNode));
				checkRelatedMax(currNode, nodeMaxEntries.get(currNode), this.axiomRoles.get(currNode));

				if (!relatedMaxEntries.get(currNode).isEmpty()) {
					checkOutgoingEdges(currNode, relatedMaxEntries.get(currNode));
				}
				Set<ToDoEntry> entries = new HashSet<>();
				if (!nodeExistEntries.get(currNode).isEmpty())
					entries.addAll(nodeExistEntries.get(currNode));
				if (!relatedMaxEntries.get(currNode).isEmpty())
					entries.addAll(relatedMaxEntries.get(currNode));
				if (!relatedForAllEntries.get(currNode).isEmpty())
					entries.addAll(relatedForAllEntries.get(currNode));
				nodeExistEntries.get(currNode).clear();
				nodeMaxEntries.get(currNode).clear();
				nodeForAllEntries.get(currNode).clear();
				relatedForAllEntries.get(currNode).clear();
				relatedMaxEntries.get(currNode).clear();
				if (!callILP(currNode, entries, new HashSet<OWLSubClassOfAxiom>(this.niSubAx), outgoingEdges))
					return false;
				for (ToDoEntry en : unrelatedMaxEntries.get(currNode))
					if (!applyRules(en)) {
						unrelatedForAllEntries.get(currNode).clear();
						unrelatedMaxEntries.get(currNode).clear();
						axiomRoles.get(currNode).clear();
						this.niSubAx.clear();
						return false;
					}
				for (ToDoEntry en : unrelatedForAllEntries.get(currNode))
					if (!applyRules(en)) {
						unrelatedForAllEntries.get(currNode).clear();
						unrelatedMaxEntries.get(currNode).clear();
						axiomRoles.get(currNode).clear();
						this.niSubAx.clear();
						return false;
					}
				unrelatedForAllEntries.get(currNode).clear();
				unrelatedMaxEntries.get(currNode).clear();
				axiomRoles.get(currNode).clear();
				this.niSubAx.clear();
			} else {
				checkRelatedForAll(currNode, nodeForAllEntries.get(currNode), this.axiomRoles.get(currNode));
				checkRelatedMax(currNode, nodeMaxEntries.get(currNode), this.axiomRoles.get(currNode));

				if (!relatedMaxEntries.get(currNode).isEmpty()) {
					checkOutgoingEdges(currNode, relatedMaxEntries.get(currNode));
				}
				if (!nodeExistEntries.get(currNode).isEmpty() || !this.outgoingEdges.isEmpty()) {
					Set<ToDoEntry> entries = new HashSet<>();
					if (!nodeExistEntries.get(currNode).isEmpty())
						entries.addAll(nodeExistEntries.get(currNode));
					if (!relatedMaxEntries.get(currNode).isEmpty())
						entries.addAll(relatedMaxEntries.get(currNode));
					if (!relatedForAllEntries.get(currNode).isEmpty())
						entries.addAll(relatedForAllEntries.get(currNode));
					nodeExistEntries.get(currNode).clear();
					nodeMaxEntries.get(currNode).clear();
					nodeForAllEntries.get(currNode).clear();
					relatedForAllEntries.get(currNode).clear();
					relatedMaxEntries.get(currNode).clear();
					if (!callILP(currNode, entries, new HashSet<OWLSubClassOfAxiom>(this.niSubAx), outgoingEdges)) {
						unrelatedForAllEntries.get(currNode).clear();
						unrelatedMaxEntries.get(currNode).clear();
						axiomRoles.get(currNode).clear();
						this.niSubAx.clear();
						return false;
					}
					for (ToDoEntry en : unrelatedMaxEntries.get(currNode))
						if (!applyRules(en)) {
							unrelatedForAllEntries.get(currNode).clear();
							unrelatedMaxEntries.get(currNode).clear();
							axiomRoles.get(currNode).clear();
							this.niSubAx.clear();
							return false;
						}
					for (ToDoEntry en : unrelatedForAllEntries.get(currNode))
						if (!applyRules(en)) {
							unrelatedForAllEntries.get(currNode).clear();
							unrelatedMaxEntries.get(currNode).clear();
							axiomRoles.get(currNode).clear();
							this.niSubAx.clear();
							return false;
						}
					unrelatedForAllEntries.get(currNode).clear();
					unrelatedMaxEntries.get(currNode).clear();
					axiomRoles.get(currNode).clear();
					this.niSubAx.clear();
				} else {
					if (!nodeForAllEntries.get(currNode).isEmpty()) {
						for (ToDoEntry en : nodeForAllEntries.get(currNode))
							if (!applyRules(en)) {
								nodeForAllEntries.get(currNode).clear();
								nodeMaxEntries.get(currNode).clear();
								relatedForAllEntries.get(currNode).clear();
								relatedMaxEntries.get(currNode).clear();
								unrelatedForAllEntries.get(currNode).clear();
								unrelatedMaxEntries.get(currNode).clear();
								return false;
							}
					}
					if (!nodeMaxEntries.get(currNode).isEmpty()) {
						for (ToDoEntry en : nodeMaxEntries.get(currNode))
							if (!applyRules(en)) {
								nodeForAllEntries.get(currNode).clear();
								nodeMaxEntries.get(currNode).clear();
								relatedForAllEntries.get(currNode).clear();
								relatedMaxEntries.get(currNode).clear();
								unrelatedForAllEntries.get(currNode).clear();
								unrelatedMaxEntries.get(currNode).clear();
								return false;
							}
					}
					nodeForAllEntries.get(currNode).clear();
					nodeMaxEntries.get(currNode).clear();
					relatedForAllEntries.get(currNode).clear();
					relatedMaxEntries.get(currNode).clear();
					unrelatedForAllEntries.get(currNode).clear();
					unrelatedMaxEntries.get(currNode).clear();
				}
			}
		}
		return true;
	}

	private Set<ConceptNDepSet> addExistentialRestrictions(Node node) {
		DependencySet newDS = DependencySet.create();
		Set<DependencySet> nomDS = new HashSet<>();
		Set<DependencySet> conDS = new HashSet<>();
		Set<ConceptNDepSet> maxCardinalities = new HashSet<>();
		for (OWLObjectOneOf nominal : node.getLabel().stream().filter(ce -> ce instanceof OWLObjectOneOf)
				.map(ce -> (OWLObjectOneOf) ce).collect(Collectors.toSet())) {
			ConceptNDepSet cnd = node.getnLabel().getCndList().getCdSet().stream()
					.filter(cnds -> cnds.getCe().equals(nominal)).iterator().next();
			nomDS.add(cnd.getDs());
		}
		if (!nomDS.stream().anyMatch(ds -> ds.isEmpty())) {
			// FIXME check if it is changing the original ds?? it should not change original
			// ds
			nomDS.stream().forEach(ds -> newDS.add(DependencySet.create(ds)));
		}
		for (OWLObjectMaxCardinality mxCard : node.getLabel().stream()
				.filter(ce -> ce instanceof OWLObjectMaxCardinality).map(ce -> (OWLObjectMaxCardinality) ce)
				.collect(Collectors.toSet())) {
			OWLObjectPropertyExpression role = mxCard.getProperty();
			OWLClassExpression filler = mxCard.getFiller();
			// System.err.println(filler);
			if (node.getOutgoingEdges().stream()
					.anyMatch(e -> e.isPredEdge() && !e.isReset() && e.getLabel().contains(role)
							&& e.getToNode().getLabel().contains(filler) && e.getToNode().isBlockableNode()
							&& !e.getToNode().isReset())) {

				int cardinality = mxCard.getCardinality();
				ConceptNDepSet cnd = node.getnLabel().getCndList().getCdSet().stream()
						.filter(cnds -> cnds.getCe().equals(mxCard)).iterator().next();
				maxCardinalities.add(cnd);
				// FIXME check if it is changing the original ds?? it should not change original
				// ds
				newDS.add(DependencySet.create(cnd.getDs()));

				List<Edge> outgoingEdges = node.getOutgoingEdges().stream()
						.filter(e -> !e.isReset() && e.getLabel().contains(role) /* && e.isSuccEdge() */
								&& e.getToNode().getLabel().contains(filler) && e.getToNode().isNINode())
						.collect(Collectors.toList());

				if (outgoingEdges.size() != 0 && outgoingEdges.size() < cardinality) {
					int diff = cardinality - outgoingEdges.size();
					// System.err.println("diff "+diff);
					List<Edge> predEdges = node.getOutgoingEdges().stream()
							.filter(e -> !e.isReset() && e.getLabel().contains(role) && e.isPredEdge()
									&& e.getToNode().getLabel().contains(filler) && e.getToNode().isBlockableNode()
									&& !e.getToNode().isReset())
							.collect(Collectors.toList());
					for (Edge edge : predEdges) {
						Node to = edge.getToNode();
						ConceptNDepSet cnd2 = to.getnLabel().getCndList().getCdSet().stream()
								.filter(cnds -> cnds.getCe().equals(filler)).iterator().next();
						conDS.add(cnd2.getDs());
						if (to.getCardinality() > 1) {
							this.splitNode2(to);
						}
					}
					if (!conDS.stream().anyMatch(ds -> ds.isEmpty())) {
						// FIXME check if it is changing the original ds?? it should not change original
						// ds
						conDS.stream().forEach(ds -> newDS.add(DependencySet.create(ds)));
					}
					Set<OWLClassExpression> niNominals = new HashSet<>();
					for (int i = 0; i < diff; i++) {
						OWLNamedIndividual namedInd = df
								.getOWLNamedIndividual(IRI.create(base + "#ni_" + niCounter + "_node_" + node.getId()));
						OWLClassExpression ni = df.getOWLObjectOneOf(namedInd);
						niNominals.add(ni);
						ConceptNDepSet cnds = new ConceptNDepSet(
								df.getOWLObjectSomeValuesFrom(role, df.getOWLObjectIntersectionOf(ni, filler)), newDS);
						ToDoEntry entry = new ToDoEntry(node, cnds, NodeTag.EXISTS);
						nodeExistEntries.put(node, entry);
						niCounter++;
					}
					niSubAx.add(df.getOWLSubClassOfAxiom(filler, df.getOWLObjectUnionOf(niNominals)));
					this.axiomRoles.put(node, role);
				} else if (outgoingEdges.size() == 0) {
					List<Edge> predEdges = node.getOutgoingEdges().stream()
							.filter(e -> !e.isReset() && e.getLabel().contains(role) && e.isPredEdge()
									&& e.getToNode().getLabel().contains(filler) && e.getToNode().isBlockableNode()
									&& !e.getToNode().isReset())
							.collect(Collectors.toList());
					for (Edge edge : predEdges) {
						Node to = edge.getToNode();
						ConceptNDepSet cnd2 = to.getnLabel().getCndList().getCdSet().stream()
								.filter(cnds -> cnds.getCe().equals(filler)).iterator().next();
						conDS.add(cnd2.getDs());
						if (to.getCardinality() > 1) {
							this.splitNode2(to);
						}
					}
					if (!conDS.stream().anyMatch(ds -> ds.isEmpty())) {
						// FIXME check if it is changing the original ds?? it should not change original
						// ds
						conDS.stream().forEach(ds -> newDS.add(DependencySet.create(ds)));
					}
					Set<OWLClassExpression> niNominals = new HashSet<>();
					for (int i = 0; i < cardinality; i++) {
						OWLNamedIndividual namedInd = df
								.getOWLNamedIndividual(IRI.create(base + "#ni_" + niCounter + "_node_" + node.getId()));
						OWLClassExpression ni = df.getOWLObjectOneOf(namedInd);
						niNominals.add(ni);
						ConceptNDepSet cnds = new ConceptNDepSet(
								df.getOWLObjectSomeValuesFrom(role, df.getOWLObjectIntersectionOf(ni, filler)), newDS);
						ToDoEntry entry = new ToDoEntry(node, cnds, NodeTag.EXISTS);
						nodeExistEntries.put(node, entry);
						niCounter++;
					}
					niSubAx.add(df.getOWLSubClassOfAxiom(filler, df.getOWLObjectUnionOf(niNominals)));
					this.axiomRoles.put(node, role);
				}
			}
			// no need to make them disjoint...
			/*
			 * for(int i = 0; i < ni.size(); i++) { for(int j = 0; j < ni.size(); j++) {
			 * if(!ni.get(i).equals(ni.get(j))) { ontology.addDiffIndividuals(ni.get(i),
			 * ni.get(j)); } } }
			 * this.intl.addDiffInd(df.getOWLDifferentIndividualsAxiom(namedInds));
			 */
		}
		return maxCardinalities;
	}

	private boolean isNIRuleApplicable(Node n) {
		if (n.isNominalNode()) {
			DependencySet newDS = DependencySet.create();
			Set<DependencySet> nomDS = new HashSet<>();
			for (OWLObjectOneOf nominal : n.getLabel().stream().filter(ce -> ce instanceof OWLObjectOneOf)
					.map(ce -> (OWLObjectOneOf) ce).collect(Collectors.toSet())) {
				ConceptNDepSet cnd = n.getnLabel().getCndList().getCdSet().stream()
						.filter(cnds -> cnds != null && cnds.getCe().equals(nominal)).iterator().next();
				nomDS.add(cnd.getDs());
			}
			if (!nomDS.stream().anyMatch(ds -> ds.isEmpty())) {
				// FIXME check if it is changing the original ds?? it should not change original
				// ds
				nomDS.stream().forEach(ds -> newDS.add(DependencySet.create(ds)));
			}
			Set<OWLObjectMaxCardinality> mxCards = n.getLabel().stream()
					.filter(ce -> ce instanceof OWLObjectMaxCardinality).map(ce -> (OWLObjectMaxCardinality) ce)
					.collect(Collectors.toSet());
			for (OWLObjectMaxCardinality mx : mxCards) {
				OWLObjectPropertyExpression role = mx.getProperty();
				OWLClassExpression filler = mx.getFiller();
				////
				DependencySet ds = n.getnLabel().getCndList().getCdSet().stream().filter(ce -> ce.getCe().equals(mx))
						.iterator().next().getDs();
				newDS.add(DependencySet.create(ds));
				int cardinality = mx.getCardinality();
				int maxCard = 0;
				DependencySet maxDs = DependencySet.create();
				for (Edge e : n.getOutgoingEdges()) {
					if (!e.isReset() && e.getLabel().contains(role) && e.getToNode().getLabel().contains(filler)) {
						Node to = e.getToNode();
						// System.err.println("to "+ to.getId());
						int card = to.getCardinality();
						if (maxCard < card) {
							maxCard = card;
							maxDs = to.getnLabel().getCndList().getCdSet().stream()
									.filter(cnd -> cnd.getCe().equals(filler)).iterator().next().getDs();

						}
					}
				}

				if (maxCard > cardinality) {
					// FIXME: check dependency set
					if (!newDS.isEmpty() || !maxDs.isEmpty()) {
						// System.err.println("mxds "+ maxDs.getMax() +" "+filler);
						if (!clashHandler(DependencySet.plus(DependencySet.create(newDS), DependencySet.create(maxDs)),
								n))
							isInconsistent(n);
					} else
						isInconsistent(n);
					return false;

				}

				/////
				if (n.getOutgoingEdges().stream()
						.anyMatch(e -> e.isPredEdge() && !e.isReset() && e.getLabel().contains(role)
								&& e.getToNode().getLabel().contains(filler) && e.getToNode().isBlockableNode()
								&& !e.getToNode().isReset())) {
					List<Edge> outgoingEdges = n.getOutgoingEdges().stream()
							.filter(e -> !e.isReset() && e.getLabel().contains(role) && e.isSuccEdge()
									&& e.getToNode().getLabel().contains(filler) && e.getToNode().isNINode())
							.collect(Collectors.toList());
					/*
					 * Set<Node> existingNINodes = new HashSet<>(); for(Edge e :outgoingEdges) {
					 * Node to = e.getToNode(); if(to.isNINode()) { existingNINodes.add(to); } }
					 */

					if (outgoingEdges.size() == mx.getCardinality()) {
						return false;
					} else
						return true;
				}
			}
		}
		/*
		 * if(n.isNominalNode() && n.getLabel().stream().anyMatch(ce -> ce instanceof
		 * OWLObjectMaxCardinality) && n.getOutgoingEdges().stream().anyMatch(e ->
		 * e.isPredEdge())) { return true; }
		 */
		return false;
	}

	private void checkOutgoingEdges(Node n, Set<ToDoEntry> maxCardEntries) {
		for (ToDoEntry en : maxCardEntries) {
			// System.out.println("entry for all "+en);
			OWLObjectMaxCardinality av = (OWLObjectMaxCardinality) en.getClassExpression();
			OWLObjectPropertyExpression role = av.getProperty();
			// OWLClassExpression ce = av.getFiller();
			for (Edge e : n.getOutgoingEdges()) {
				// System.err.println("e "+ e.getLabel() +" label "+e.getToNode().getLabel());

				// if(e.getLabel().contains(role) && e.getToNode().getLabel().contains(ce) &&
				// !e.isReset() && !e.getToNode().isReset())
				if (e.getLabel().contains(role) && !e.isReset() && !e.getToNode().isReset()
						&& cg.getNodeBase().contains(e.getToNode()))
					outgoingEdges.add(e);
			}
			// return true;
		}
	}

	private boolean processEntry(ToDoEntry entry) {
		// System.out.println("entry "+ entry.getType());
		if (entry.getType().equals(NodeTag.OR) || entry.getType().equals(NodeTag.AND)) {
			return this.applyRules(entry);
		} else if (entry.getType().equals(NodeTag.EXISTS)) {
			nodeExistEntries.put(currNode, entry);
			if (entry.getClassExpression() instanceof OWLObjectSomeValuesFrom) {
				OWLObjectPropertyExpression obj = ((OWLObjectSomeValuesFrom) entry.getClassExpression()).getProperty();
				// System.out.println("obj pro "+ obj);
				this.axiomRoles.put(currNode, obj);
				this.axiomRoles.get(currNode).addAll(this.getAllSuperRoles(obj));
			} else if (entry.getClassExpression() instanceof OWLObjectHasValue) {
				OWLObjectPropertyExpression obj = ((OWLObjectHasValue) entry.getClassExpression()).getProperty();
				// System.out.println("obj pro "+ obj);
				this.axiomRoles.put(currNode, obj);
				this.axiomRoles.get(currNode).addAll(this.getAllSuperRoles(obj));
			}
		} else if (entry.getType().equals(NodeTag.LE)) {
			nodeMinEntries.put(currNode, entry);
			OWLObjectPropertyExpression obj = ((OWLObjectMinCardinality) entry.getClassExpression()).getProperty();
			// System.out.println("obj pro "+ obj);
			this.axiomRoles.put(currNode, obj);
			this.axiomRoles.get(currNode).addAll(this.getAllSuperRoles(obj));
		} else if (entry.getType().equals(NodeTag.GE)) {
			nodeMaxEntries.put(currNode, entry);
			// OWLObjectPropertyExpression obj = ((OWLObjectMaxCardinality)
			// entry.getClassExpression()).getProperty();
			// System.out.println("obj pro "+ obj);
			// this.axiomRoles.put(currNode, obj);
		} else if (entry.getType().equals(NodeTag.FORALL)) {
			nodeForAllEntries.put(currNode, entry);
		}
		return true;
	}

	public void addRangeRestrictions(Set<OWLObjectPropertyExpression> roles) {
		// System.out.println("forall: "+ nodeForAllEntries.get(currNode).size());
		Set<OWLObjectAllValuesFrom> rangeRes = new HashSet<OWLObjectAllValuesFrom>();
		for (OWLObjectPropertyExpression obj : roles) {
			if (!(intl.getOntology().getRoleRange(obj).isEmpty())) {
				for (OWLObjectAllValuesFrom rr : intl.getOntology().getRoleRange(obj)) {
					if(rangeRes.contains(rr))
						continue;
					// System.out.println("obj pro range "+ rr);
					rangeRes.add(rr);
					ConceptNDepSet cnds = new ConceptNDepSet(rr, DependencySet.create());
					nodeForAllEntries.put(currNode, new ToDoEntry(currNode, cnds, NodeTag.FORALL));
				}
			}
			if (intl.getOntology().getSuperRolesMap().containsKey(obj)) {
				for (OWLObjectPropertyExpression r : intl.getOntology().getSuperRolesMap().get(obj)) {
					if (!(intl.getOntology().getRoleRange(r).isEmpty())) {
						for (OWLObjectAllValuesFrom rr : intl.getOntology().getRoleRange(r)) {
							if(rangeRes.contains(rr))
								continue;
							rangeRes.add(rr);
							ConceptNDepSet cnds = new ConceptNDepSet(rr, DependencySet.create());
							nodeForAllEntries.put(currNode, new ToDoEntry(currNode, cnds, NodeTag.FORALL));
						}
					}
				}
			}
		}
		// System.out.println("after forall: "+ nodeForAllEntries.get(currNode).size());

	}

	public boolean needILPModule(Node n) {
		// forAllCheck = false;
		// isExistential = false;
		// if(!nodeMinEntries.get(n).isEmpty() || !nodeMaxEntries.get(n).isEmpty()) {
		if (!nodeMinEntries.get(n).isEmpty() || !relatedMaxEntries.get(n).isEmpty()) {
			if (!n.isBlocked())
				return true;
		}else if (!n.isBlocked() && (config.isSHO() || config.isSHOI() || config.isSHOIQ() || config.isSHOQ())) {
			for (ToDoEntry entry : nodeExistEntries.get(n)) {
				OWLClassExpression ce = entry.getClassExpression();

				if (ce instanceof OWLObjectSomeValuesFrom) {
					// isExistential = true;
					if (hasNominal((OWLObjectSomeValuesFrom) ce))
						return true;
				} else if (ce instanceof OWLObjectHasValue) {
					return true;
				}
			}
			if (!relatedForAllEntries.get(n).isEmpty()) {
				for (ToDoEntry entry : relatedForAllEntries.get(n)) {
					OWLClassExpression ce = entry.getClassExpression();
					if (ce instanceof OWLObjectAllValuesFrom) {
						if (hasNominal((OWLObjectAllValuesFrom) ce)) {
							// forAllCheck = true;
							return true;
						}
					}
				}
			}
			/*
			 * if(forAllCheck && isExistential) return true;
			 */
		}
		return false;
	}

	private void checkRelatedForAll(Node n, Set<ToDoEntry> forAllEntries, Set<OWLObjectPropertyExpression> roles) {
		// Set<OWLObjectAllValuesFrom> forAll = new HashSet<>();
		outgoingEdges.clear();
		// System.out.println("related forall: "+ forAllEntries.size());
		for (ToDoEntry en : forAllEntries) {
			boolean flag = false;
			// System.out.println("entry for all "+en.getClassExpression());
			OWLObjectAllValuesFrom av = (OWLObjectAllValuesFrom) en.getClassExpression();
			OWLObjectPropertyExpression role = av.getProperty();
			// System.out.println("role "+ role);
			if (roles.contains(role)) {
				// System.out.println("role "+ role);
				// System.out.println("outgoing edges "+ n.getOutgoingEdges());
				relatedForAllEntries.put(n, en);
				flag = true;
				for (Edge e : n.getOutgoingEdges()) {

					// System.out.println("e "+ e.getLabel());
					if (cg.getNodeBase().contains(e.getToNode()) && e.getLabel().contains(role) && !e.isReset()
							&& !e.getToNode().isReset())
						outgoingEdges.add(e);
				}
				// return true;
			} else {
				for (OWLObjectPropertyExpression r : intl.getOntology().getSuperRolesMap().keySet()) {
					if (roles.contains(r)) {
						// System.out.println("role "+ role);
						if (intl.getOntology().getSuperRolesMap().get(r).contains(role)) {
							relatedForAllEntries.put(n, en);
							flag = true;
							for (Edge e : n.getOutgoingEdges()) {
								if (cg.getNodeBase().contains(e.getToNode()) && e.getLabel().contains(role)
										&& !e.isReset() && !e.getToNode().isReset())
									outgoingEdges.add(e);
							}
							// return true;
						}
					}
				}
			}
			if (!flag) {
				unrelatedForAllEntries.put(n, en);
			}
		}
		// System.out.println("after related forall: "+
		// relatedForAllEntries.get(currNode).size());

		// System.out.println("outgoingEdges "+ outgoingEdges.size());
		// return false;
	}

	private void checkRelatedMax(Node n, Set<ToDoEntry> maxEntries, Set<OWLObjectPropertyExpression> roles) {
		// outgoingEdges.clear();
		// System.out.println("related max: "+ relatedMaxEntries.get(currNode).size());
		// System.out.println("roles "+ roles);

		for (ToDoEntry en : maxEntries) {
			boolean flag = false;
			// System.out.println("entry for all "+en);
			OWLObjectMaxCardinality mx = (OWLObjectMaxCardinality) en.getClassExpression();
			OWLObjectPropertyExpression role = mx.getProperty();
			// System.out.println("role "+ role);
			if (roles.contains(role)) {
				// System.out.println("role "+ role);
				relatedMaxEntries.put(n, en);
				flag = true;
				// return true;
			} else {
				for (OWLObjectPropertyExpression r : intl.getOntology().getSuperRolesMap().keySet()) {
					if (roles.contains(r)) {
						if (intl.getOntology().getSuperRolesMap().get(r).contains(role)) {
							relatedMaxEntries.put(n, en);
							flag = true;
							// return true;
						}
					}
				}
			}
			if (!flag) {
				/*
				 * if(n.getOutgoingEdges().stream().anyMatch(e -> !e.isReset() && e.isPredEdge()
				 * && e.getLabel().contains(role))) { relatedMaxEntries.put(n, en); } else
				 */
				unrelatedMaxEntries.put(n, en);
			}
		}
		// System.out.println("after related max: "+
		// relatedMaxEntries.get(currNode).size());

		// System.out.println("outgoingEdges "+ outgoingEdges.size());
		// return false;
	}

	public void blockNode(Node n, Node blocker) {
		cg.setNodeBlocked(n, blocker);
	}
	private boolean hasNominal(OWLObjectAllValuesFrom ce) {
		OWLClassExpression filler = ce.getFiller();
		if (filler instanceof OWLObjectOneOf)
			return true;
		else if (filler instanceof OWLClass)
			return hasNominal(filler);
		else if (filler instanceof OWLObjectIntersectionOf) {
			for (OWLClassExpression c : filler.asConjunctSet()) {
				if (c instanceof OWLClass)
					return hasNominal(c);
				else if (c instanceof OWLObjectOneOf)
					return true;
			}
		} else if (filler instanceof OWLObjectUnionOf) {
			for (OWLClassExpression c : filler.asDisjunctSet()) {
				if (c instanceof OWLClass)
					return hasNominal(c);
				else if (c instanceof OWLObjectOneOf)
					return true;
			}
		}
		return false;
	}

	private boolean hasNominal(OWLObjectSomeValuesFrom ce) {
		OWLClassExpression filler = ce.getFiller();

		if (filler instanceof OWLObjectOneOf)
			return true;
		else if (filler instanceof OWLClass)
			return hasNominal(filler);
		else if (filler instanceof OWLObjectIntersectionOf) {
			for (OWLClassExpression c : filler.asConjunctSet()) {
				if (c instanceof OWLClass)
					return hasNominal(c);
				else if (c instanceof OWLObjectOneOf)
					return true;
			}
		} else if (filler instanceof OWLObjectUnionOf) {
			for (OWLClassExpression c : filler.asDisjunctSet()) {
				if (c instanceof OWLClass)
					return hasNominal(c);
				else if (c instanceof OWLObjectOneOf)
					return true;
			}
		}
		for (OWLObjectAllValuesFrom forAll : this.intl.getRoleRange(ce.getProperty())) {
			if (forAll.getFiller() instanceof OWLObjectOneOf)
				return true;
			else if (forAll.getFiller() instanceof OWLObjectIntersectionOf) {
				if (forAll.getFiller().asConjunctSet().stream().anyMatch(cj -> (cj instanceof OWLObjectOneOf)))
					return true;
			} else if (forAll.getFiller() instanceof OWLObjectUnionOf) {
				if (forAll.getFiller().asDisjunctSet().stream().anyMatch(dj -> (dj instanceof OWLObjectOneOf)))
					return true;
			}
		}
		return false;
	}

	private boolean hasNominal(OWLObjectIntersectionOf ce) {
		for (OWLClassExpression c : ce.asConjunctSet()) {
			if (c instanceof OWLObjectHasValue)
				return true;
			else if (c instanceof OWLObjectIntersectionOf)
				return hasNominal((OWLObjectIntersectionOf) c);
			else if (c instanceof OWLObjectSomeValuesFrom) {
				isExistential = true;
				return hasNominal((OWLObjectSomeValuesFrom) c);
			} else if (c instanceof OWLObjectAllValuesFrom) {
				if (hasNominal((OWLObjectAllValuesFrom) c)) {
					forAllCheck = true;
					return true;
				}
			} else if (c instanceof OWLObjectUnionOf) {
				return hasNominal((OWLObjectUnionOf) c);
			}
		}
		return false;
	}

	private boolean hasNominal(OWLObjectUnionOf ce) {
		for (OWLClassExpression c : ce.asDisjunctSet()) {
			if (c instanceof OWLObjectIntersectionOf)
				return hasNominal((OWLObjectIntersectionOf) c);
			else if (c instanceof OWLObjectHasValue)
				return true;
			else if (c instanceof OWLObjectSomeValuesFrom) {
				isExistential = true;
				return hasNominal((OWLObjectSomeValuesFrom) c);
			} else if (c instanceof OWLObjectAllValuesFrom) {
				if (hasNominal((OWLObjectAllValuesFrom) c)) {
					forAllCheck = true;
					return true;
				}
			} else if (c instanceof OWLObjectUnionOf) {
				return hasNominal((OWLObjectUnionOf) c);
			}
		}
		return false;
	}

	private boolean hasNominal(OWLClassExpression filler) {
		if (filler instanceof OWLObjectOneOf) {
			return true;
		} else if (filler instanceof OWLClass) {
			// System.out.println("class expression "+filler);
			if (intl.getOntology().hasNominal(filler))
				return true;
		} else if (filler instanceof OWLObjectIntersectionOf) {
			for (OWLClassExpression objIn : filler.asConjunctSet()) {
				if (objIn instanceof OWLObjectOneOf) {
					return true;
				} else
					return hasNominal(objIn);
			}
		} else if (filler instanceof OWLObjectUnionOf) {
			for (OWLClassExpression objUn : filler.asDisjunctSet()) {
				if (objUn instanceof OWLObjectOneOf)
					return true;
				else
					return hasNominal(objUn);
			}
		}

		return false;
	}

	public boolean callILP(Node n, Set<ToDoEntry> entries, Set<OWLSubClassOfAxiom> subsumption,
			Set<Edge> outgoingEdges) {
		
	//	entries.stream()
	//			.forEach(en -> System.out.println(en.getDs().getbpList() + " entry: " + en.getClassExpression()));
	//	 for(ToDoEntry en : entries) {
	//		 System.out.println(en.getDs().getbpList()+" entry: "+en.getClassExpression());
	//	 }
		Node blocker = findBlocker(n);
		if (blocker != null && !n.equals(blocker)) {
			blockNode(n, blocker);
			return true;
		}
		System.out.println("Calling ILP module..." + entries.size() + " node id: " + n.getId());
		if (outgoingEdges == null) {
			outgoingEdges = checkOutGoingEdges(n, entries);
		}

		///// added 24-oct-2019
		DependencySet newDs = DependencySet.create(getCurLevel());
		/*for (ToDoEntry entry : entries) {
			entry.setDs(DependencySet.plus(DependencySet.create(newDs), DependencySet.create(entry.getDs())));
		}*/
		BranchHandler bh = new BranchHandler(entries, DependencySet.create(newDs), n, outgoingEdges, subsumption);
		this.branches.put(getCurLevel(), bh);
		save(n);
		// cg.saveN(n);
		incCurLevel();

		/////
		Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> superRolesMap = new HashMap<>();
		for (OWLObjectPropertyExpression r : this.axiomRoles.get(currNode)) {
			if (!getAllSuperRoles(r).isEmpty())
				superRolesMap.put(r, this.getAllSuperRoles(r));
		}
		// System.err.println(""+superRolesMap);
		// if(outgoingEdges.size() > 0)
		// outgoingEdges.stream().forEach(e -> System.err.println(e.getLabel()));

		// System.err.println("inverse edges : "+outgoingEdges.size() +" :
		// "+outgoingEdges.stream().filter(predicate)
		// +outgoingEdges.iterator().next().getLabel());

		ILPPreprocessor ilpPro = new ILPPreprocessor(this.cg, entries, this.intl, this.df, n, outgoingEdges,
				subsumption, superRolesMap);
		ILPSolution sol = null;
		try {
			sol = ilpPro.callILP();
		} catch (IloException e) {
			e.printStackTrace();
		}

		if (sol.isSolved()) {
			Set<Node> oldNodes = new HashSet<>();
			Set<Node> newNodes = new HashSet<>();
			DependencySet ds = DependencySet.create();
			for (EdgeInformation ei : sol.getEdgeInformation()) {
				// ei.getFillers().stream().forEach(f -> System.out.println("filler "+ f ));
				// DependencySet ds = ei.getDs();
				ds = DependencySet.plus(ei.getDs(), DependencySet.create(newDs));
				Set<OWLObjectPropertyExpression> roles = ei.getEdges();
				Set<Integer> nodeIds = ei.getNodeSet();
				// System.out.println("nodeIds.isEmpty() "+ nodeIds.isEmpty());
				Node to = null;
				Node node = null;
				Edge e = null;
				boolean newNode = false;
				boolean niRuleCheck = false;
				if (nodeIds.isEmpty()) {
					/*
					 * Node blocker = findBlocker(n); if(blocker != null) { cg.setNodeBlocked(n,
					 * blocker); return; }
					 */
					if (ei.getFillers().stream().anyMatch(ce -> ce instanceof OWLObjectOneOf)) {
						boolean niNode = false;
						Set<Node> nomNodes = new HashSet<>();
						SetMultimap<OWLClassExpression, Node> nomNodesMap = HashMultimap.create();
						for (OWLClassExpression filler : ei.getFillers().stream()
								.filter(ce -> ce instanceof OWLObjectOneOf).map(ce -> (OWLClassExpression) ce)
								.collect(Collectors.toSet())) {
							// OWLClassExpression ci =
							// df.getOWLObjectOneOf(filler.individuals().iterator().next());
							// System.out.println("nominal "+ filler);
							if (filler.toString().contains("#ni_")) {
								niNode = true;
							}
							Node nom = findNominalNode(filler);
							if (nom != null) {
								nomNodes.add(nom);
								nomNodesMap.put(filler, nom);
							}
							// System.out.println("nom "+ nomNodes.size());
						}
						if (!nomNodes.isEmpty()) {
							if (nomNodes.size() == 1) {
								to = nomNodes.iterator().next();
								e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
								if (!this.absorbRoleRule(getAllRoles(roles), n, to, ds))
									return false;
							} else {

								System.out.println("Needs Merging!");
								List<Node> nomNodesL = new ArrayList<>(nomNodes);
								// boolean needReset = false;
								boolean merged = false;
								for (int i = 0; i < nomNodesL.size() - 1; i++) {
									merged = false;
									if (nomNodesL.get(i).equals(n)) {
										if (canMerge(nomNodesL.get(i), nomNodesL.get(i + 1))) {
											to = mergeNodes(nomNodesL.get(i), nomNodesL.get(i + 1), ds);
											// needReset = checkIfResetRequired(nomNodesL.get(i));
											merged = true;
										} else
											break;
									} else if (nomNodesL.get(i).getLabel().size() < nomNodesL.get(i + 1).getLabel()
											.size()) {
										if (canMerge(nomNodesL.get(i), nomNodesL.get(i + 1))) {
											to = mergeNodes(nomNodesL.get(i), nomNodesL.get(i + 1), ds);
											merged = true;
										} else
											break;
									} else {
										if (canMerge(nomNodesL.get(i), nomNodesL.get(i + 1))) {
											to = mergeNodes(nomNodesL.get(i + 1), nomNodesL.get(i), ds);
											merged = true;
										} else
											break;
									}
								}
								if (!merged) {
									boolean handleClash = false;
									DependencySet clashSet = DependencySet.create();
									// System.out.println("size "+entries.size());
									for (ToDoEntry entry : entries) {
										if (!entry.getDs().isEmpty()) {
											handleClash = true;
											// System.out.println("ds "+entry.getDs().getbpList()+" "+
											// entry.getClassExpression());
											clashSet.add(entry.getDs());
										}
									}
									if (handleClash) {
										if (!clashHandler(clashSet, n))
											isInconsistent(n);
									} else
										isInconsistent(n);
									return false;
								}
								if (to == null) {
									boolean handleClash = false;
									DependencySet clashSet = DependencySet.create();
									// System.out.println("size "+entries.size());
									for (ToDoEntry entry : entries) {
										if (!entry.getDs().isEmpty()) {
											handleClash = true;
											// System.out.println("ds "+entry.getDs().getbpList()+" "+
											// entry.getClassExpression());
											clashSet.add(entry.getDs());
										}
									}
									if (handleClash) {
										if (!clashHandler(clashSet, n))
											isInconsistent(n);
									} else
										isInconsistent(n);
									return false;
								}

								e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
								if (!this.absorbRoleRule(getAllRoles(roles), n, to, ds))
									return false;
								//// new code 27-oct-2019
								// reset(to); //commented April 26, 2020
								this.addToDoEntries(to);
								////
								/*
								 * System.err.println("Sorry! it needs Merging!"); Main.getExecutionTime();
								 * System.exit(0);
								 */
							}

						} else {
							newNode = true;
							to = this.cg.addNode(NodeType.NOMINAL, ds);
							to.setCardinality(ei.getCardinality());
							/*
							 * if(!this.absorbRule1(df.getOWLThing(), to, ds)) return; addTGAxiom(to, ds);
							 */
							e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
							if (!this.absorbRoleRule(getAllRoles(roles), n, to, ds))
								return false;
							// e = this.cg.addEdge(n, to, roles, ds);
						}
						if (niNode) {
							to.makeNINode();
						}
					} else {
						newNode = true;
						to = this.cg.addNode(NodeType.BLOCKABLE, ds);
						to.setCardinality(ei.getCardinality());
						/*
						 * if(!this.absorbRule1(df.getOWLThing(), to, ds)) return; addTGAxiom(to, ds);
						 */
						e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
						if (!this.absorbRoleRule(getAllRoles(roles), n, to, ds))
							return false;
						// e = this.cg.addEdge(n, to, roles, ds);
					}
					// if(!checkAtLeastRestrictions(n))
					// return;
					if (newNode)
						newNodes.add(to);
					else
						oldNodes.add(to);
					if (!addLabel(n, to, ei.getFillers(), ds, newNode, entries))
						return false;
				} else if (nodeIds.size() == 1) {
					// System.err.println("node exists");
					node = cg.getNode(nodeIds.iterator().next());
					if (ei.getFillers().stream().anyMatch(ce -> ce instanceof OWLObjectOneOf)) {
						Set<Node> nomNodes = new HashSet<>();
						boolean niNode = false;
						SetMultimap<OWLClassExpression, Node> nomNodesMap = HashMultimap.create();
						for (OWLClassExpression filler : ei.getFillers().stream()
								.filter(ce -> ce instanceof OWLObjectOneOf).map(ce -> (OWLClassExpression) ce)
								.collect(Collectors.toSet())) {
							// OWLClassExpression ci =
							// df.getOWLObjectOneOf(filler.individuals().iterator().next());
							// System.out.println("nominal "+ filler);
							if (filler.toString().contains("#ni_")) {
								niNode = true;
							}
							Node nom = findNominalNode(filler);
							// System.out.println("nominal node"+ nom);
							if (nom != null) {
								nomNodes.add(nom);
								nomNodesMap.put(filler, nom);
							}
						}
						if (!nomNodes.isEmpty()) {
							if (nomNodes.size() == 1) {
								// System.err.println("nominAl node exists");
								to = nomNodes.iterator().next();
								if (node.getCardinality() > 1) {
									reset(node);
									this.splitNode(node);
									return false;
								}
								if (node != null) {
									if (to.getId() != node.getId()) {
										// System.out.println("Needs Merging!");
										if (canMerge(node, to))
											to = mergeNodes(node, to, ds);
										else {
											boolean handleClash = false;
											DependencySet clashSet = DependencySet.create();
											// System.out.println("size "+entries.size());
											for (ToDoEntry entry : entries) {
												if (!entry.getDs().isEmpty()) {
													handleClash = true;
													// System.out.println("ds "+entry.getDs().getbpList()+" "+
													// entry.getClassExpression());
													clashSet.add(entry.getDs());
												}
											}
											if (handleClash) {
												if (!clashHandler(clashSet, n))
													isInconsistent(n);
											} else
												isInconsistent(n);
											return false;
										}
										//// new code 27-oct-2019
										if (to == null) {
											boolean handleClash = false;
											DependencySet clashSet = DependencySet.create();
											// System.out.println("size "+entries.size());
											for (ToDoEntry entry : entries) {
												if (!entry.getDs().isEmpty()) {
													handleClash = true;
													// System.out.println("ds "+entry.getDs().getbpList()+" "+
													// entry.getClassExpression());
													clashSet.add(entry.getDs());
												}
											}
											if (handleClash) {
												if (!clashHandler(clashSet, n))
													isInconsistent(n);
											} else
												isInconsistent(n);
											return false;
										}

										// reset(to); //commented April 26, 2020
										this.addToDoEntries(to);
										////
									}
								}
								// System.err.println("node label" + to.getLabel());
								e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
								if (!this.absorbRoleRule(getAllRoles(roles), n, to, ds))
									return false;
								// e = this.cg.addEdge(n, to, roles, ds);
							} else {
								if (node.getCardinality() > 1) {
									reset(node);
									this.splitNode(node);
									return false;
								}
								System.out.println("Needs Merging!" /* nomNodes size" + nomNodes.size() */);
								List<Node> nomNodesL = new ArrayList<>(nomNodes);
								boolean merged = false;
								for (int i = 0; i < nomNodesL.size() - 1; i++) {
									merged = false;
									if (nomNodesL.get(i).equals(n)) {
										if (canMerge(nomNodesL.get(i), nomNodesL.get(i + 1))) {
											to = mergeNodes(nomNodesL.get(i), nomNodesL.get(i + 1), ds);
											merged = true;
										} else
											break;
									} else if (nomNodesL.get(i).getLabel().size() < nomNodesL.get(i + 1).getLabel()
											.size()) {
										if (canMerge(nomNodesL.get(i), nomNodesL.get(i + 1))) {
											to = mergeNodes(nomNodesL.get(i), nomNodesL.get(i + 1), ds);
											merged = true;
										} else
											break;
									} else {
										if (canMerge(nomNodesL.get(i + 1), nomNodesL.get(i))) {
											to = mergeNodes(nomNodesL.get(i + 1), nomNodesL.get(i), ds);
											merged = true;
										} else
											break;
									}
								}
								if (!merged) {
									// System.out.println(sol.getInfeasible_set());
									boolean handleClash = false;
									DependencySet clashSet = DependencySet.create();
									// System.out.println("size "+entries.size());
									for (ToDoEntry entry : entries) {
										if (!entry.getDs().isEmpty()) {
											handleClash = true;
											// System.out.println("ds "+entry.getDs().getbpList()+" "+
											// entry.getClassExpression());
											clashSet.add(entry.getDs());
										}
									}
									if (handleClash) {
										if (!clashHandler(clashSet, n))
											isInconsistent(n);
									} else
										isInconsistent(n);
									return false;
								}
								if (node != null) {
									if (to.getId() != node.getId() && !nomNodesL.contains(node)) {
										// System.out.println("Needs Merging! again");
										if (canMerge(node, to)) {
											to = mergeNodes(node, to, ds);
										} else {
											boolean handleClash = false;
											DependencySet clashSet = DependencySet.create();
											// System.out.println("size "+entries.size());
											for (ToDoEntry entry : entries) {
												if (!entry.getDs().isEmpty()) {
													handleClash = true;
													// System.out.println("ds "+entry.getDs().getbpList()+" "+
													// entry.getClassExpression());
													clashSet.add(entry.getDs());
												}
											}
											if (handleClash) {
												if (!clashHandler(clashSet, n))
													isInconsistent(n);
											} else
												isInconsistent(n);
											return false;
										}
									}
								}
								if (to == null) {
									boolean handleClash = false;
									DependencySet clashSet = DependencySet.create();
									// System.out.println("size "+entries.size());
									for (ToDoEntry entry : entries) {
										if (!entry.getDs().isEmpty()) {
											handleClash = true;
											// System.out.println("ds "+entry.getDs().getbpList()+" "+
											// entry.getClassExpression());
											clashSet.add(entry.getDs());
										}
									}
									if (handleClash) {
										if (!clashHandler(clashSet, n))
											isInconsistent(n);
									} else
										isInconsistent(n);
									return false;
								}

								e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
								if (!this.absorbRoleRule(getAllRoles(roles), n, to, ds))
									return false;
								//// new code 27-oct-2019
								// reset(to); //commented April 26, 2020
								this.addToDoEntries(to);
								////
							}
							if (niNode) {
								to.makeNINode();
							}
						} else {
							if (node.getCardinality() > 1) {
								reset(node);
								this.splitNode(node);
								return false;
							}
							if (niNode) {
								node.makeNINode();
							}
							if (!makeNominalNode(node, ds))
								return false;
							niRuleCheck = true;
							to = node;
							e = cg.findEdge(n, to.getId());
							updateEdgeDepSet(ds, e);
							// node.setCardinality(ei.getCardinality());
						}
					} else {
						// node.setCardinality(ei.getCardinality());
						to = node;
						e = cg.findEdge(n, to.getId());
						updateEdgeDepSet(ds, e);
					}
					// addLabel(n, to, ei.getFillers(), ds);

					// System.out.println("edge "+ e);
					// updateEdgeDepSet(ds, e);
					// if(!checkAtLeastRestrictions(n))
					// return;
					Set<OWLClassExpression> newCE = new HashSet<>();
					for (OWLClassExpression c : ei.getFillers()) {
						if (!to.getLabel().contains(c))
							newCE.add(c);
					}
					if (!newCE.isEmpty()) {
						if (newNode)
							newNodes.add(to);
						else
							oldNodes.add(to);

						if (!addLabel(n, to, newCE, ds, newNode, entries))
							return false;
					}

				} else if (nodeIds.size() > 1) {
					// System.out.println("nodeIds.size() "+ nodeIds.size());
					// FIXME: merge nodes
					List<Node> nodes = new ArrayList<>();
					for (int nid : nodeIds) {
						nodes.add(cg.getNode(nid));
					}
					/*
					 * for(Edge edge : cg.findEdges(n, nodeIds)) { nodes.add(edge.getToNode()); }
					 */

					System.out.println("Needs Merging! " + nodes.size());
					boolean merged = false;
					for (int i = 0; i < nodes.size() - 1; i++) {
						merged = false;
						// System.out.println("Nodes "+ nodes.get(i).getNodeId() + " and"+
						// nodes.get(i+1).getNodeId());
						if ((nodes.get(i + 1).isNominalNode() || nodes.get(i + 1).isNINode())
								&& (!nodes.get(i).isNominalNode() || !nodes.get(i).isNINode())) {
							if (canMerge(nodes.get(i), nodes.get(i + 1))) {
								node = mergeNodes(nodes.get(i), nodes.get(i + 1), ds);
								merged = true;
							} else
								break;

						} else if ((!nodes.get(i + 1).isNominalNode() || !nodes.get(i + 1).isNINode())
								&& (nodes.get(i).isNominalNode() || nodes.get(i).isNINode())) {
							if (canMerge(nodes.get(i + 1), nodes.get(i))) {
								node = mergeNodes(nodes.get(i + 1), nodes.get(i), ds);
								merged = true;
							} else
								break;
						} else if (nodes.get(i).getLabel().size() < nodes.get(i + 1).getLabel().size()) {
							if (canMerge(nodes.get(i), nodes.get(i + 1))) {
								node = mergeNodes(nodes.get(i), nodes.get(i + 1), ds);
								merged = true;
							} else
								break;
						} else {
							if (canMerge(nodes.get(i), nodes.get(i + 1))) {
								node = mergeNodes(nodes.get(i + 1), nodes.get(i), ds);
								merged = true;
							} else
								break;
						}
					}
					// System.out.println("node "+ node);
					if (!merged) {
						boolean handleClash = false;
						DependencySet clashSet = DependencySet.create();
						// System.out.println("size "+entries.size());
						for (ToDoEntry entry : entries) {
							if (!entry.getDs().isEmpty()) {
								handleClash = true;
								// System.out.println("ds "+entry.getDs().getbpList()+" "+
								// entry.getClassExpression());
								clashSet.add(entry.getDs());
							}
						}
						if (handleClash) {
							if (!clashHandler(clashSet, n))
								isInconsistent(n);
						} else
							isInconsistent(n);
						return false;
					}
					if (node == null) {
						boolean handleClash = false;
						DependencySet clashSet = DependencySet.create();
						// System.out.println("size "+entries.size());
						for (ToDoEntry entry : entries) {
							if (!entry.getDs().isEmpty()) {
								handleClash = true;
								// System.out.println("ds "+entry.getDs().getbpList()+" "+
								// entry.getClassExpression());
								clashSet.add(entry.getDs());
							}
						}
						if (handleClash) {
							if (!clashHandler(clashSet, n))
								isInconsistent(n);
						} else
							isInconsistent(n);
						return false;
					}
					////
					e = cg.findEdge(n, node.getNodeId());
					if (e == null) {
						e = this.cg.addEdge(n, node, getAllRoles(roles), ds);
						if (!this.absorbRoleRule(getAllRoles(roles), n, node, ds))
							return false;
					}
					//

					//
					if (ei.getFillers().stream().anyMatch(ce -> ce instanceof OWLObjectOneOf)) {
						Set<Node> nomNodes = new HashSet<>();
						boolean niNode = false;
						SetMultimap<OWLClassExpression, Node> nomNodesMap = HashMultimap.create();
						for (OWLClassExpression filler : ei.getFillers().stream()
								.filter(ce -> ce instanceof OWLObjectOneOf).map(ce -> (OWLClassExpression) ce)
								.collect(Collectors.toSet())) {
							// OWLClassExpression ci =
							// df.getOWLObjectOneOf(filler.individuals().iterator().next());
							// System.out.println("nominal "+ filler);
							if (filler.toString().contains("#ni_")) {
								niNode = true;
							}
							Node nom = findNominalNode(filler);
							if (nom != null) {
								nomNodes.add(nom);
								nomNodesMap.put(filler, nom);
							}
						}
						if (!nomNodes.isEmpty()) {
							if (nomNodes.size() == 1) {

								// System.err.println("node exists");
								to = nomNodes.iterator().next();
								if (node.getCardinality() > 1) {
									reset(node);
									this.splitNode(node);
									return false;
								}
								if (node != null) {
									if (to.getId() != node.getId()) {
										System.out.println("Needs Merging!");
										if (canMerge(node, to))
											to = mergeNodes(node, to, ds);
										else {
											boolean handleClash = false;
											DependencySet clashSet = DependencySet.create();
											// System.out.println("size "+entries.size());
											for (ToDoEntry entry : entries) {
												if (!entry.getDs().isEmpty()) {
													handleClash = true;
													// System.out.println("ds "+entry.getDs().getbpList()+" "+
													// entry.getClassExpression());
													clashSet.add(entry.getDs());
												}
											}
											if (handleClash) {
												if (!clashHandler(clashSet, n))
													isInconsistent(n);
											} else
												isInconsistent(n);
											return false;
										}
									}
								}
								if (to == null) {
									boolean handleClash = false;
									DependencySet clashSet = DependencySet.create();
									// System.out.println("size "+entries.size());
									for (ToDoEntry entry : entries) {
										if (!entry.getDs().isEmpty()) {
											handleClash = true;
											// System.out.println("ds "+entry.getDs().getbpList()+" "+
											// entry.getClassExpression());
											clashSet.add(entry.getDs());
										}
									}
									if (handleClash) {
										if (!clashHandler(clashSet, n))
											isInconsistent(n);
									} else
										isInconsistent(n);
									return false;
								}

								// System.err.println("node label" + to.getLabel());
								e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
								if (!this.absorbRoleRule(getAllRoles(roles), n, to, ds))
									return false;
								//// new code 27-oct-2019
								// reset(to); //commented April 26, 2020
								this.addToDoEntries(to);
								////
								// e = this.cg.addEdge(n, to, roles, ds);
							} else {
								if (node.getCardinality() > 1) {
									reset(node);
									this.splitNode(node);
									return false;
								}
								System.out.println("Needs Merging!");
								List<Node> nomNodesL = new ArrayList<>(nomNodes);
								boolean merged2 = false;
								for (int i = 0; i < nomNodesL.size() - 1; i++) {
									merged2 = false;
									if (nomNodesL.get(i).equals(n)) {
										if (canMerge(nomNodesL.get(i), nomNodesL.get(i + 1))) {
											to = mergeNodes(nomNodesL.get(i), nomNodesL.get(i + 1), ds);
											merged2 = true;
										} else
											break;
									} else if (nomNodesL.get(i).getLabel().size() < nomNodesL.get(i + 1).getLabel()
											.size()) {
										if (canMerge(nomNodesL.get(i), nomNodesL.get(i + 1))) {
											to = mergeNodes(nomNodesL.get(i), nomNodesL.get(i + 1), ds);
											merged2 = true;
										} else
											break;
									} else {
										if (canMerge(nomNodesL.get(i + 1), nomNodesL.get(i))) {
											to = mergeNodes(nomNodesL.get(i + 1), nomNodesL.get(i), ds);
											merged2 = true;
										} else
											break;
									}
								}
								if (!merged2) {
									boolean handleClash = false;
									DependencySet clashSet = DependencySet.create();
									// System.out.println("size "+entries.size());
									for (ToDoEntry entry : entries) {
										if (!entry.getDs().isEmpty()) {
											handleClash = true;
											// System.out.println("ds "+entry.getDs().getbpList()+" "+
											// entry.getClassExpression());
											clashSet.add(entry.getDs());
										}
									}
									if (handleClash) {
										if (!clashHandler(clashSet, n))
											isInconsistent(n);
									} else
										isInconsistent(n);
									return false;
								}
								if (node != null) {
									if (to.getId() != node.getId() && !nomNodesL.contains(node)) {
										// System.out.println("Needs Merging!");
										if (canMerge(node, to))
											to = mergeNodes(node, to, ds);
										else {
											boolean handleClash = false;
											DependencySet clashSet = DependencySet.create();
											// System.out.println("size "+entries.size());
											for (ToDoEntry entry : entries) {
												if (!entry.getDs().isEmpty()) {
													handleClash = true;
													// System.out.println("ds "+entry.getDs().getbpList()+" "+
													// entry.getClassExpression());
													clashSet.add(entry.getDs());
												}
											}
											if (handleClash) {
												if (!clashHandler(clashSet, n))
													isInconsistent(n);
											} else
												isInconsistent(n);
											return false;
										}
									}
								}
								if (to == null) {
									boolean handleClash = false;
									DependencySet clashSet = DependencySet.create();
									// System.out.println("size "+entries.size());
									for (ToDoEntry entry : entries) {
										if (!entry.getDs().isEmpty()) {
											handleClash = true;
											// System.out.println("ds "+entry.getDs().getbpList()+" "+
											// entry.getClassExpression());
											clashSet.add(entry.getDs());
										}
									}
									if (handleClash) {
										if (!clashHandler(clashSet, n))
											isInconsistent(n);
									} else
										isInconsistent(n);
									return false;
								}

								e = this.cg.addEdge(n, to, getAllRoles(roles), ds);
								if (!this.absorbRoleRule(getAllRoles(roles), n, to, ds))
									return false;
								//// new code 27-oct-2019
								// reset(to); //commented April 26, 2020
								this.addToDoEntries(to);
								////
							}

						} else {
							if (node.getCardinality() > 1) {
								reset(node);
								this.splitNode(node);
								return false;
							}
							if (!makeNominalNode(node, ds))
								return false;
							niRuleCheck = true;
							to = node;
							e = cg.findEdge(n, to.getId());
							// System.err.println("edge "+e);
							updateEdgeDepSet(ds, e);
							// node.setCardinality(ei.getCardinality());
						}
						if (niNode) {
							to.makeNINode();
						}
					} else {
						// node.setCardinality(ei.getCardinality());
						to = node;
						e = cg.findEdge(n, to.getId());
						updateEdgeDepSet(ds, e);
					}
					// addLabel(n, to, ei.getFillers(), ds);

					Set<OWLClassExpression> newCE = new HashSet<>();
					for (OWLClassExpression c : ei.getFillers()) {
						if (!to.getLabel().contains(c))
							newCE.add(c);
					}

					if (!newCE.isEmpty()) {
						/// new code start
						boolean resetRequired = newCE.stream().anyMatch(
								ce -> ce instanceof OWLObjectMinCardinality || ce instanceof OWLObjectMaxCardinality);
						if (!resetRequired) {
							for (OWLClassExpression ce : newCE) {
								resetRequired = ontology.getAllSubsumers(ce).stream()
										.anyMatch(sub -> sub instanceof OWLObjectMinCardinality
												|| sub instanceof OWLObjectMaxCardinality);

								if (resetRequired)
									break;
							}
						}

						if (resetRequired) {
							reset(to);
							addToDoEntries(to);
							return false;
						}
						/// new code end
						if (newNode)
							newNodes.add(to);
						else
							oldNodes.add(to);
						if (!addLabel(n, to, newCE, ds, newNode, entries))
							return false;

					}

				}
				if (niRuleCheck) {
					if (isNIRuleApplicable(to))
						addForNIRule(to);
				}
				/*
				 * // if to is nominal node and has atmost restriction then apply NI rule
				 * if(to.isNominalNode() && to.getLabel().stream().anyMatch(lb -> lb instanceof
				 * OWLObjectMaxCardinality)) { applyNIRule2(to); }
				 */
			}

			for (Node to : oldNodes) {
				checkAtMost(to);
				processForAll(to);
				Edge e = cg.getEdge(n, to);
				if (e != null)
					if (!applyTransitiveRule(n, to, e.getLabel(), ds))
						return false;
			}
			for (Node to : newNodes) {
				checkAtMost(to);
				Edge e = cg.getEdge(n, to);
				if (e != null)
					if (!applyTransitiveRule(n, to, e.getLabel(), ds))
						return false;
			}
			// if(!checkAtLeastRestrictions(n))
			// return;
			/*
			 * for(Edge e : n.getOutgoingEdges()) { if(e.isSuccEdge())
			 * System.out.println("node "+e.getToNode().getId()+" label "+e.getToNode().
			 * getLabel()); }
			 */
			return true;
		} else {
			// System.out.println(sol.getInfeasible_set());
			boolean handleClash = false;
			DependencySet clashSet = DependencySet.create();
			// System.out.println("size "+entries.size());
			for (ToDoEntry entry : entries) {
				if (!entry.getDs().isEmpty()) {
					handleClash = true;
					// System.out.println("ds "+entry.getDs().getbpList()+" "+
					// entry.getClassExpression());
					clashSet.add(entry.getDs());
				}
			}
			if (handleClash) {
				if (!clashHandler(clashSet, n)) {
				//	System.out.println("here ");
					isInconsistent(n);
				}
			} else
				isInconsistent(n);
			return false;
		}

	}

	private void addForNIRule(Node to) {
		System.err.println("ni applicable 6");
		for (ConceptNDepSet cnds : to.getnLabel().getCndList().getCdSet()) {
			if ((cnds.getCe() instanceof OWLObjectAllValuesFrom) || (cnds.getCe() instanceof OWLObjectMaxCardinality)) {
				this.addToDoEntry(to, cnds.getCe(), cnds);
			}
		}

	}

	private boolean makeNominalNode(Node node, DependencySet ds) {
		Set<Node> resetNodes = needNomPredReset(node, ds);
		System.err.println("# of pred reset nodes " + resetNodes.size());
		if (!resetNodes.isEmpty()) {
			for (Node resetNode : resetNodes) {
				reset(resetNode);
				splitNode(resetNode);
			}
			return false;
		}
		node.makeNominalNode();
		return true;
	}

	private Set<Edge> checkOutGoingEdges(Node n, Set<ToDoEntry> entries2) {
		Set<Edge> outEdges = new HashSet<>();
		for (ToDoEntry en : entries2) {
			if (en.getType().equals(NodeTag.GE)) {
				// System.out.println("entry for all "+en);
				OWLObjectMaxCardinality av = (OWLObjectMaxCardinality) en.getClassExpression();
				OWLObjectPropertyExpression role = av.getProperty();
				for (Edge e : n.getOutgoingEdges()) {
					if (cg.getNodeBase().contains(e.getToNode()) && e.getLabel().contains(role) && !e.isReset()
							&& !e.getToNode().isReset())
						outEdges.add(e);
				}
			} else if (en.getType().equals(NodeTag.FORALL)) {
				// System.out.println("entry for all "+en);
				OWLObjectAllValuesFrom av = (OWLObjectAllValuesFrom) en.getClassExpression();
				OWLObjectPropertyExpression role = av.getProperty();
				for (Edge e : n.getOutgoingEdges()) {
					if (cg.getNodeBase().contains(e.getToNode()) && e.getLabel().contains(role) && !e.isReset()
							&& !e.getToNode().isReset())
						outEdges.add(e);
				}
			}
		}
		return outEdges;
	}

	private void splitNode2(Node x) {
		System.err.println("split Node2" + x.getId());
		List<Node> newNodes = new ArrayList<>();
		List<OWLClassExpression> classExp = new ArrayList<>();
		for (int i = 0; i < x.getCardinality(); i++) {
			classExp.add(df.getOWLClass("#re_aux_" + ++counter, prefixManager));
		}
		for (int i = 0; i < x.getCardinality() - 1; i++) {
			// FIXME: check dependency set
			Node newNode = cg.addNode(NodeType.BLOCKABLE, DependencySet.create(x.getDs()));
			// this.absorbRule1(df.getOWLThing(), newNode, DependencySet.create(x.getDs()));
			newNodes.add(newNode);
			newNode.addDisjointNode(x);
			x.addDisjointNode(newNode);
			// System.err.println("concept added "+ classExp.get(i));
			cg.addConceptToNode(newNode, new ConceptNDepSet(classExp.get(i), DependencySet.create(x.getDs())));
			for (ConceptNDepSet cnds : x.getnLabel().getCndList().getCdSet()) {
				cg.addConceptToNode(newNode, cnds);
			}
			// newEdges.add(cg.addEdge(from, newNode, e.getLabel(), e.getDepSet(),
			// e.isSuccEdge()));
			for (Edge outE : x.getOutgoingEdges()) {
				if (!outE.isReset())
					cg.addEdge(newNode, outE.getToNode(), outE.getLabel(), outE.getDepSet(), outE.isSuccEdge());
			}
			for (int k = 0; k < i; k++) {
				cg.addConceptToNode(newNode,
						new ConceptNDepSet(classExp.get(k).getComplementNNF(), DependencySet.create(x.getDs())));
			}
			for (int k = i + 1; k < x.getCardinality(); k++) {
				cg.addConceptToNode(newNode,
						new ConceptNDepSet(classExp.get(k).getComplementNNF(), DependencySet.create(x.getDs())));
			}
		}

		for (int i = 0; i < newNodes.size(); i++) {
			Node nn = newNodes.get(i);
			// addToDoEntries(nn);
			for (int k = 0; k < i; k++) {
				nn.addDisjointNode(newNodes.get(k));
			}
			for (int k = i + 1; k < newNodes.size(); k++) {
				nn.addDisjointNode(newNodes.get(k));
			}
		}

		// System.err.println("concept added "+ classExp.get(x.getCardinality()-1));
		cg.addConceptToNode(x,
				new ConceptNDepSet(classExp.get(x.getCardinality() - 1), DependencySet.create(x.getDs())));
		for (int k = 0; k < x.getCardinality() - 1; k++) {
			cg.addConceptToNode(x,
					new ConceptNDepSet(classExp.get(k).getComplementNNF(), DependencySet.create(x.getDs())));
		}
		cg.updateNodeCardinality(x, 1);
		newNodes.add(x);
		// addToDoEntries(x);
		for (int i = 0; i < classExp.size(); i++) {
			for (int j = 0; j < classExp.size(); j++) {
				if (!classExp.get(i).equals(classExp.get(j))) {
					ontology.addDiffIndividuals(classExp.get(i), classExp.get(j));
				}
			}
		}

	}

	private void splitNode(Node x) {
		System.err.println("split Node " + x.getId());
		List<Node> newNodes = new ArrayList<>();
		List<OWLClassExpression> classExp = new ArrayList<>();
		for (int i = 0; i < x.getCardinality(); i++) {
			classExp.add(df.getOWLClass("#re_aux_" + ++counter, prefixManager));
		}
		for (int i = 0; i < x.getCardinality() - 1; i++) {
			// FIXME: check dependency set
			Node newNode = cg.addNode(NodeType.BLOCKABLE, DependencySet.create(x.getDs()));
			// this.absorbRule1(df.getOWLThing(), newNode, DependencySet.create(x.getDs()));
			newNodes.add(newNode);
			newNode.addDisjointNode(x);
			x.addDisjointNode(newNode);
			// System.err.println("concept added "+ classExp.get(i));
			cg.addConceptToNode(newNode, new ConceptNDepSet(classExp.get(i), DependencySet.create(x.getDs())));
			for (ConceptNDepSet cnds : x.getnLabel().getCndList().getCdSet()) {
				cg.addConceptToNode(newNode, cnds);
			}
			// newEdges.add(cg.addEdge(from, newNode, e.getLabel(), e.getDepSet(),
			// e.isSuccEdge()));
			for (Edge outE : x.getOutgoingEdges()) {
				if (!outE.isReset())
					cg.addEdge(newNode, outE.getToNode(), outE.getLabel(), outE.getDepSet(), outE.isSuccEdge());
			}
			for (int k = 0; k < i; k++) {
				cg.addConceptToNode(newNode,
						new ConceptNDepSet(classExp.get(k).getComplementNNF(), DependencySet.create(x.getDs())));
			}
			for (int k = i + 1; k < x.getCardinality(); k++) {
				cg.addConceptToNode(newNode,
						new ConceptNDepSet(classExp.get(k).getComplementNNF(), DependencySet.create(x.getDs())));
			}
		}

		for (int i = 0; i < newNodes.size(); i++) {
			Node nn = newNodes.get(i);
			addToDoEntries(nn);
			for (int k = 0; k < i; k++) {
				nn.addDisjointNode(newNodes.get(k));
			}
			for (int k = i + 1; k < newNodes.size(); k++) {
				nn.addDisjointNode(newNodes.get(k));
			}
		}

		// System.err.println("concept added "+ classExp.get(x.getCardinality()-1));
		cg.addConceptToNode(x,
				new ConceptNDepSet(classExp.get(x.getCardinality() - 1), DependencySet.create(x.getDs())));
		for (int k = 0; k < x.getCardinality() - 1; k++) {
			cg.addConceptToNode(x,
					new ConceptNDepSet(classExp.get(k).getComplementNNF(), DependencySet.create(x.getDs())));
		}
		cg.updateNodeCardinality(x, 1);
		newNodes.add(x);
		// System.err.println("new nodes: "+newNodes.size());
		addToDoEntries(x);
		for (int i = 0; i < classExp.size(); i++) {
			for (int j = 0; j < classExp.size(); j++) {
				if (!classExp.get(i).equals(classExp.get(j))) {
					ontology.addDiffIndividuals(classExp.get(i), classExp.get(j));
				}
			}
		}

	}

	private boolean needReset(OWLClassExpression ce, Node n) {
		if (ce instanceof OWLObjectMinCardinality || ce instanceof OWLObjectMaxCardinality) {
			OWLObjectPropertyExpression role = ((OWLObjectCardinalityRestriction) ce).getProperty();
			// OWLClassExpression c = ((OWLObjectCardinalityRestriction) ce).getFiller();
			// System.out.println("size"+ n.getSuccEdges().size());

			for (Edge e : n.getOutgoingEdges()) {
				/*
				 * if (e.isSuccEdge() && !e.isReset() && e.getLabel().contains(role) &&
				 * e.getToNode().getLabel().contains(c))
				 */
				if (e.isSuccEdge() && !e.isReset()) {
					Set<OWLObjectPropertyExpression> result = new HashSet<>(e.getLabel());
					result.retainAll(this.getAllRoles(role));
					if (!result.isEmpty() && !e.getToNode().isNominalNode() && !e.getToNode().isReset()) {
						return true;
					}
				}
			}
		}
		return false;
	}

	private boolean needReset(OWLObjectSomeValuesFrom ce, Node n) {
		if (n.getLabel().stream().anyMatch(c -> c instanceof OWLObjectMaxCardinality)) {
			OWLObjectPropertyExpression role = ce.getProperty();
			// OWLClassExpression c = ((OWLObjectCardinalityRestriction) ce).getFiller();
			// System.out.println("size"+ n.getSuccEdges().size());

			for (Edge e : n.getOutgoingEdges()) {
				/*
				 * if (e.isSuccEdge() && !e.isReset() && e.getLabel().contains(role) &&
				 * e.getToNode().getLabel().contains(c))
				 */
				if (e.isSuccEdge() && !e.isReset()) {
					Set<OWLObjectPropertyExpression> result = new HashSet<>(e.getLabel());
					result.retainAll(this.getAllRoles(role));
					if (!result.isEmpty() && !e.getToNode().isNominalNode() && !e.getToNode().isReset()) {
						return true;
					}
				}
			}
		}

		return false;
	}

	private void addToDoEntries(Node to) {
		List<ConceptNDepSet> cndList = to.getnLabel().getCndList().getCdSet();
		for (ConceptNDepSet cnds : cndList) {
			// System.err.println("add to do entry "+to.getId()+" -- " +cnds.getCe());

			if (!(cnds.getCe() instanceof OWLObjectIntersectionOf) && !(cnds.getCe() instanceof OWLObjectUnionOf)) {
				// System.err.println("add to do entry "+cnds.getCe());
				this.addToDoEntry(to, cnds.getCe(), cnds);
			}
		}

	}

	private void reset(Node n) {
		System.err.println("reset " + n.getId() /*
												 * +" out edges"+n.getOutgoingEdges().stream().filter(e ->
												 * e.isSuccEdge()).count()
												 */);
		for (Edge e : n.getOutgoingEdges()) {
			// System.err.println("n id "+n.getId() +" "+e.isSuccEdge() +" id "+
			// e.getToNode().getId());
			if (e.isSuccEdge() && !e.isReset()) {
				e.setReset(true);
				Node to = e.getToNode();
				if (!to.isNominalNode()) {
					// System.err.println("reset to node " + to.getId());
					to.setReset(true);
					if (cg.getEdge(to, n) != null)
						cg.getEdge(to, n).setReset(true);
					reset(to);
				}
				// if(cg.getEdge(to, n)!=null)
				// cg.getEdge(to, n).setReset(true);
			}
		}
		/*
		 * for(Edge e : n.getOutgoingEdges()) { if(e.isPredEdge()) { e.setReset(true);
		 * Node from = e.getFromNode(); if(!from.isNominalNode()){ from.setReset(true);
		 * reset(from); } } }
		 */
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

	private boolean addLabel(Node from, Node to, Set<OWLClassExpression> fillers, DependencySet ds, boolean newNode,
			Set<ToDoEntry> entries) {
		if (newNode)
			return addLabelNewNode(from, to, fillers, ds, entries);
		else
			return addLabelOldNode(from, to, fillers, ds, entries);

		// if(!applyAbsorption(to, fillers, ds))
		// return false;
		// checkAtMost(to);
		// processAtMost(to);
		// if (!newNode)
		// processForAll(to);
		// System.out.println("to label "+ to .getLabel());

		// Edge e = cg.getEdge(from, to);
		// if (e != null)
		// applyTransitiveRule(from, to, e.getLabel(), ds);
		// processForAll(from);
	}

	private boolean addLabelOldNode(Node from, Node to, Set<OWLClassExpression> fillers, DependencySet ds, Set<ToDoEntry> entries) {
		addBackPropagatedConcepts(to, entries, fillers);
		for (OWLClassExpression ce : fillers) {
			Node nn = addConcept(to, ce, ds, true);
			if (nn.getId() == -1)
				return false;
			else {
				if (((ce instanceof OWLClass) || (ce instanceof OWLObjectOneOf)
						|| (ce instanceof OWLObjectComplementOf))) {
					to.addSimpleILPLabel(ce);
				}
			}
		}
		return true;
	}

	private boolean addLabelNewNode(Node from, Node to, Set<OWLClassExpression> fillers, DependencySet ds, Set<ToDoEntry> entries) {
		addTGAxiom(to, ds);
		for (OWLClassExpression ce : fillers) {
			if (!isConceptExist(to, ce)) {
			//	System.out.println("add label : "+ ce);
				ConceptNDepSet cnds = new ConceptNDepSet(ce, ds);
				if (ce instanceof OWLObjectOneOf) {
					to.addSimpleILPLabel(ce);
					this.cg.addConceptToNode(to, cnds);
					if (!addApplicableGCIs(to, ce, ds))
						return false;
					if (ce.toString().contains("#ni_")) {
						to.makeNINode();
					}
					if (checkClash(to, ce)) {
						DependencySet clashSet = getClashSet(to, ce, ce.getComplementNNF());
						if (!clashSet.isEmpty()) {
							clashSet.setCe(ce);
							clashSet.setCeNNF(ce.getComplementNNF());
							if (!clashHandler(clashSet, to))
								isInconsistent(to);
						} else
							isInconsistent(to);
						return false;
					}
				} else if (ce instanceof OWLObjectCardinalityRestriction || ce instanceof OWLObjectSomeValuesFrom || ce instanceof OWLObjectAllValuesFrom) {
					this.cg.addConceptToNode(to, cnds);
					if (!checkClash(to, ce)) {
						addToDoEntry(to, ce, cnds);
					} else {
						DependencySet clashSet = getClashSet(to, ce, ce.getComplementNNF());
						if (!clashSet.isEmpty()) {
							clashSet.setCe(ce);
							clashSet.setCeNNF(ce.getComplementNNF());
							if (!clashHandler(clashSet, to))
								isInconsistent(to);
						} else
							isInconsistent(to);
						return false;
					}
					if(ce instanceof OWLObjectCardinalityRestriction) {
						if (!addApplicableGCIs(to, ((OWLObjectCardinalityRestriction) ce).getProperty(), ds))
							return false;
					}
					else if(ce instanceof OWLObjectSomeValuesFrom) {
						if (!addApplicableGCIs(to, ((OWLObjectSomeValuesFrom) ce).getProperty(), ds))
							return false;
					}
					else if(ce instanceof OWLObjectAllValuesFrom) {
						if (!addApplicableGCIs(to, ((OWLObjectAllValuesFrom) ce).getProperty(), ds))
							return false;
					}
				} else {
					this.cg.addConceptToNode(to, cnds);
					if (!checkClash(to, ce)) {
						if (ce instanceof OWLClass) {
							to.addSimpleLabel(ce);
							to.addSimpleILPLabel(ce);
							if (!addApplicableGCIs(to, ce, ds))
								return false;
						} else if (ce instanceof OWLObjectComplementOf) {
							to.addSimpleILPLabel(ce);
							if (!addApplicableGCIs(to, ce, ds))
								return false;
						} else {
							addToDoEntry(to, ce, cnds);
						}
					} else {
						DependencySet clashSet = getClashSet(to, ce, ce.getComplementNNF());
						if (!clashSet.isEmpty()) {
							clashSet.setCe(ce);
							clashSet.setCeNNF(ce.getComplementNNF());
							if (!clashHandler(clashSet, to))
								isInconsistent(to);
						} else
							isInconsistent(to);
						return false;
					}
				}
			}
		}
		return true;
	}

	private void addBackPropagatedConcepts(Node to, Set<ToDoEntry> entries2, Set<OWLClassExpression> fillers) {

		for (ToDoEntry entry : entries2) {
			if (entry.getType().equals(NodeTag.EXISTS)) {
				if (entry.getClassExpression() instanceof OWLObjectHasValue) {
					OWLObjectHasValue someValue = (OWLObjectHasValue) entry.getClassExpression();
					OWLClassExpression fil = df.getOWLObjectOneOf(someValue.getFiller());
					if (fillers.contains(fil) && !isConceptExist(to, fil)) {
						to.addBackPropagatedLabel(fil);
					}
				} else {
					OWLObjectSomeValuesFrom exist = (OWLObjectSomeValuesFrom) entry.getClassExpression();
					OWLClassExpression fil = exist.getFiller();
					if (fil instanceof OWLClass || fil instanceof OWLObjectOneOf
							|| fil instanceof OWLObjectComplementOf) {
						if (fillers.contains(fil) && !isConceptExist(to, fil)) {
							to.addBackPropagatedLabel(fil);
						}
					} else if (fil instanceof OWLObjectIntersectionOf) {
						if (fillers.containsAll(fil.asConjunctSet()) /*
																		 * && fil.asConjunctSet().stream().allMatch(cj
																		 * -> !isConceptExist(to, cj))
																		 */) {
							to.addBackPropagatedLabel(fil);
						}
					} else if (fil instanceof OWLObjectUnionOf) {
						if (fil.asDisjunctSet().stream().anyMatch(dj -> fillers.contains(dj))) {
							to.addBackPropagatedLabel(fil);
						}
					}
				}
			} else if (entry.getType().equals(NodeTag.LE)) {
				OWLObjectMinCardinality minCard = (OWLObjectMinCardinality) entry.getClassExpression();
				OWLClassExpression fil = minCard.getFiller();
				if (fil instanceof OWLClass || fil instanceof OWLObjectOneOf || fil instanceof OWLObjectComplementOf) {
					if (fillers.contains(fil) && !isConceptExist(to, fil)) {
						to.addBackPropagatedLabel(fil);
					}
				} else if (fil instanceof OWLObjectIntersectionOf) {
					if (fillers.containsAll(fil.asConjunctSet()) /*
																	 * && fil.asConjunctSet().stream().allMatch(cj ->
																	 * !isConceptExist(to, cj))
																	 */) {
						to.addBackPropagatedLabel(fil);
					}
				} else if (fil instanceof OWLObjectUnionOf) {
					if (fil.asDisjunctSet().stream().anyMatch(dj -> fillers.contains(dj))) {
						to.addBackPropagatedLabel(fil);
					}
				}
			} else if (entry.getType().equals(NodeTag.FORALL)) {
				OWLObjectAllValuesFrom forAll = (OWLObjectAllValuesFrom) entry.getClassExpression();
				OWLClassExpression fil = forAll.getFiller();
				if (fil instanceof OWLClass || fil instanceof OWLObjectOneOf || fil instanceof OWLObjectComplementOf) {
					if (fillers.contains(fil) && !isConceptExist(to, fil)) {
						to.addBackPropagatedLabel(fil);
					}
				} else if (fil instanceof OWLObjectIntersectionOf) {
					if (fillers.containsAll(fil.asConjunctSet()) /*
																	 * && fil.asConjunctSet().stream().allMatch(cj ->
																	 * !isConceptExist(to, cj))
																	 */) {
						to.addBackPropagatedLabel(fil);
					}
				} else if (fil instanceof OWLObjectUnionOf) {
					if (fil.asDisjunctSet().stream().anyMatch(dj -> fillers.contains(dj))) {
						to.addBackPropagatedLabel(fil);
					}
				}
			}
		}

	}

	private void checkAtMost(Node to) {
		if (to.isNominalNode()) {
			Set<ToDoEntry> relatedMaxCardEntries = new HashSet<>();
			Set<ToDoEntry> relatedForAllEntries = new HashSet<>();
			Set<OWLObjectMaxCardinality> mxCards = to.getLabel().stream()
					.filter(ce -> ce instanceof OWLObjectMaxCardinality).map(ce -> (OWLObjectMaxCardinality) ce)
					.collect(Collectors.toSet());
			for (OWLObjectMaxCardinality mx : mxCards) {
				ConceptNDepSet cnd = to.getnLabel().getCndList().getCdSet().stream()
						.filter(cnds -> cnds.getCe().equals(mx)).iterator().next();
				OWLObjectPropertyExpression role = mx.getProperty();
				OWLClassExpression filler = mx.getFiller();
				if (to.getOutgoingEdges().stream()
						.anyMatch(e -> e.isPredEdge() && !e.isReset() && e.getLabel().contains(role)
								&& e.getToNode().getLabel().contains(filler) && e.getToNode().isBlockableNode()
								&& !e.getToNode().isReset())) {
					List<Edge> outgoingEdges = to.getOutgoingEdges().stream()
							.filter(e -> e.getLabel().contains(role) && e.isSuccEdge()
									&& e.getToNode().getLabel().contains(filler) && e.getToNode().isNINode())
							.collect(Collectors.toList());

					if ((outgoingEdges.size() == mx.getCardinality()) && this.needToApplyAtMost(to, mx, cnd.getDs())) {
						this.atMostNomRule(to, mx);
					} else if (outgoingEdges.size() != mx.getCardinality()) {
						ToDoEntry mxEntry = new ToDoEntry(to, cnd, NodeTag.GE);
						relatedMaxCardEntries.add(mxEntry);
						Set<OWLObjectAllValuesFrom> forAll = to.getLabel().stream()
								.filter(ce -> ce instanceof OWLObjectAllValuesFrom)
								.map(ce -> (OWLObjectAllValuesFrom) ce).collect(Collectors.toSet());
						for (OWLObjectAllValuesFrom fa : forAll) {
							ConceptNDepSet facnd = to.getnLabel().getCndList().getCdSet().stream()
									.filter(cnds -> cnds.getCe().equals(fa)).iterator().next();
							if (fa.getProperty().equals(role)) {
								ToDoEntry faEntry = new ToDoEntry(to, facnd, NodeTag.FORALL);
								relatedForAllEntries.add(faEntry);
							}
						}
					}
				} else if (to.getOutgoingEdges().stream()
						.anyMatch(e -> e.isPredEdge() && !e.isReset() && e.getLabel().contains(role))) {
					ToDoEntry mxEntry = new ToDoEntry(to, cnd, NodeTag.GE);
					relatedMaxCardEntries.add(mxEntry);
					Set<OWLObjectAllValuesFrom> forAll = to.getLabel().stream()
							.filter(ce -> ce instanceof OWLObjectAllValuesFrom).map(ce -> (OWLObjectAllValuesFrom) ce)
							.collect(Collectors.toSet());
					for (OWLObjectAllValuesFrom fa : forAll) {
						ConceptNDepSet facnd = to.getnLabel().getCndList().getCdSet().stream()
								.filter(cnds -> cnds.getCe().equals(fa)).iterator().next();
						if (fa.getProperty().equals(role)) {
							ToDoEntry faEntry = new ToDoEntry(to, facnd, NodeTag.FORALL);
							relatedForAllEntries.add(faEntry);
						}
					}
				}
			}
			if (!relatedMaxCardEntries.isEmpty()) {
				applyNIRule(to, relatedMaxCardEntries, relatedForAllEntries);
			}
		}
	}

	private void applyNIRule(Node to, Set<ToDoEntry> relatedMaxCardEntries, Set<ToDoEntry> relatedForAllEntries2) {
		if (isNIRuleApplicable(to)) {
			System.err.println("ni applicable 5");
			addExistentialRestrictions(to);
			addRangeRestrictions(this.axiomRoles.get(to));
			// checkRelatedForAll(to, nodeForAllEntries.get(currNode),
			// this.axiomRoles.get(currNode));
			// checkRelatedMax(currNode, nodeMaxEntries.get(currNode),
			// this.axiomRoles.get(currNode));
			outgoingEdges.clear();
			if (!relatedMaxCardEntries.isEmpty()) {
				checkOutgoingEdges(to, relatedMaxCardEntries);
			}
			Set<ToDoEntry> entries = new HashSet<>();
			if (!nodeExistEntries.get(to).isEmpty())
				entries.addAll(nodeExistEntries.get(to));
			if (!relatedMaxCardEntries.isEmpty())
				entries.addAll(relatedMaxCardEntries);
			if (!relatedForAllEntries2.isEmpty())
				entries.addAll(relatedForAllEntries2);
			nodeExistEntries.get(to).clear();
			callILP(to, entries, new HashSet<OWLSubClassOfAxiom>(this.niSubAx), outgoingEdges);

			axiomRoles.get(to).clear();
			this.niSubAx.clear();
		}

	}

	private boolean needToAdd(OWLObjectCardinalityRestriction c, Node to) {
		for (OWLObjectCardinalityRestriction cr : to.getLabel().stream()
				.filter(ce -> ce instanceof OWLObjectCardinalityRestriction)
				.map(ce -> (OWLObjectCardinalityRestriction) ce).collect(Collectors.toSet())) {
			if (cr.equals(c)) {
				return false;
			} else if (cr instanceof OWLObjectMinCardinality && c instanceof OWLObjectMinCardinality) {
				if (cr.getProperty().equals(c.getProperty()) && cr.getFiller().equals(c.getFiller())) {
					if (cr.getCardinality() >= c.getCardinality())
						return false;
				}
			} else if (cr instanceof OWLObjectMaxCardinality && c instanceof OWLObjectMaxCardinality) {
				if (cr.getProperty().equals(c.getProperty()) && cr.getFiller().equals(c.getFiller())) {
					if (cr.getCardinality() <= c.getCardinality())
						return false;
				}
			}
		}
		return true;
	}

	private boolean checkQCRClash(OWLObjectCardinalityRestriction c, Node to) {
		if (c.isOWLNothing()) {
			return true;
		}
		if (to.getLabel().contains(c.getComplementNNF())) {
			// System.err.println("clash "+c);
			return true;
		}
		for (OWLObjectCardinalityRestriction cr : to.getLabel().stream()
				.filter(ce -> ce instanceof OWLObjectCardinalityRestriction)
				.map(ce -> (OWLObjectCardinalityRestriction) ce).collect(Collectors.toSet())) {
			//System.err.println("clash "+c);
			if (cr instanceof OWLObjectMinCardinality && c instanceof OWLObjectMaxCardinality) {
				if (cr.getProperty().equals(c.getProperty()) && cr.getFiller().equals(c.getFiller())) {
					if (cr.getCardinality() > c.getCardinality())
						return true;
				}
			} else if (cr instanceof OWLObjectMaxCardinality && c instanceof OWLObjectMinCardinality) {
				if (cr.getProperty().equals(c.getProperty()) && cr.getFiller().equals(c.getFiller())) {
					if (cr.getCardinality() < c.getCardinality())
						return true;;
				}
			}
		}
		return false;
	}
	private DependencySet getQCRClashSet(OWLObjectCardinalityRestriction c, Node to) {
		if (to.getLabel().contains(c.getComplementNNF())) {
			// System.err.println("clash "+c);
			return getClashSet(to, c, c.getComplementNNF());
		}
		for (OWLObjectCardinalityRestriction cr : to.getLabel().stream()
				.filter(ce -> ce instanceof OWLObjectCardinalityRestriction)
				.map(ce -> (OWLObjectCardinalityRestriction) ce).collect(Collectors.toSet())) {
			if (cr instanceof OWLObjectMinCardinality && c instanceof OWLObjectMaxCardinality) {
				if (cr.getProperty().equals(c.getProperty()) && cr.getFiller().equals(c.getFiller())) {
					if (cr.getCardinality() >= c.getCardinality())
						return getClashSet(to, c, cr);
				}
			} else if (cr instanceof OWLObjectMaxCardinality && c instanceof OWLObjectMinCardinality) {
				if (cr.getProperty().equals(c.getProperty()) && cr.getFiller().equals(c.getFiller())) {
					if (cr.getCardinality() <= c.getCardinality())
						return getClashSet(to, c, cr);
				}
			}
		}
		return null;
	}

	private boolean addTGAxiom(Node n, DependencySet ds) {
		if (this.tgAxiom != null) {
		//	System.err.println("adding tg "+ ds.getbpList());
			n = addConcept(n, tgAxiom, ds, false);
			if (n == null) {
				return false;
			} else if (n.getId() == -1) {
				return true;
			}
			
			//ConceptNDepSet cnds = new ConceptNDepSet(tgAxiom, ds);
			
			//cg.addConceptToNode(n, cnds);
			//addToDoEntry(n, tgAxiom, cnds);
			// todo.addEntry(n, NodeTag.AND, cnds);
		}

		return true;
	}

	// --- Rule Application ---//
	public boolean applyRules(ToDoEntry entry) {

		Node n = entry.getNode();
		if(!cg.getNodeBase().contains(n)) {
			return true;
		}
		if(n.isReset())
			return true;
		NodeTag nt = entry.getType();
		switch (nt) {
		case AND:
			System.out.println("Applying 'AND' expansion Rule... ");
			return applyAndRule(n, (OWLObjectIntersectionOf) entry.getClassExpression(), entry.getDs());
		// break;
		case OR:
			System.out.println("Applying 'OR' expansion Rule... ");
			return applyOrRule(n, (OWLObjectUnionOf) entry.getClassExpression(), entry.getCnds());
		// break;
		case EXISTS:
			System.out.println("Applying 'EXISTS' expansion Rule...");
			if (entry.getClassExpression() instanceof OWLObjectSomeValuesFrom)
				return applyExistentialRule(n, (OWLObjectSomeValuesFrom) entry.getClassExpression(), entry.getDs());
			else
				return applyExistentialRule(n, (OWLObjectHasValue) entry.getClassExpression(), entry.getDs());
			// break;
		case FORALL:
			System.out.println("Applying 'FORALL' expansion Rule... ");
			return applyForAllRule(n, (OWLObjectAllValuesFrom) entry.getClassExpression(), entry.getDs());
		// break;
		case GE:
			System.out.println("Applying 'GE' expansion Rule...");
			return applyGERule(n, (OWLObjectMaxCardinality) entry.getClassExpression(), entry.getDs());
		// break;
		default:
			return true;
		// break;
		}

	}

	private boolean applyGERule(Node n, OWLObjectMaxCardinality mc, DependencySet ds) {
		if(!cg.getNodeBase().contains(n)) {
			return true;
		}
		if (n.isNominalNode() && this.needToApplyAtMost(n, mc, ds) && needAtMostNomRule(n, mc)) {
			return this.atMostNomRule(n, mc);
		}
		if (!n.isBlocked() && this.needToApplyAtMost(n, mc, ds)) {

			OWLObjectPropertyExpression role = mc.getProperty();
			OWLClassExpression filler = mc.getFiller();
			int cardinality = mc.getCardinality();
			List<Node> otherNodes = new ArrayList<>();
			// Map<Node, DependencySet> dsMap = new HashMap<>();
			List<List<Node>> splitNodes = new ArrayList<>();
			List<Node> allNodes = new ArrayList<>();
			int nodesCard = 0;
			int maxCard = 0;
			DependencySet maxDs = DependencySet.create();
			int predEdges = 0;

			List<Edge> outgoingEdges = n.getOutgoingEdges();

			/*
			 * if(n.isNominalNode()) { for(Edge e : outgoingEdges) { if(e.isPredEdge() &&
			 * e.getLabel().contains(role)) { Node to = e.getToNode();
			 * if((to.getLabel().contains(filler) || (filler instanceof
			 * OWLObjectIntersectionOf && to.getLabel().containsAll(filler.asConjunctSet()))
			 * || (filler instanceof OWLObjectUnionOf &&
			 * to.getLabel().stream().anyMatch(filler.asDisjunctSet()::contains))) &&
			 * !to.isReset()) { this.applyNIRule(n, mc, ds); this.atMostNomRule(n, mc); } }
			 * } } else if(n.isBlockableNode() ) {
			 */
			for (Edge e : outgoingEdges) {
				if (e.getLabel().contains(role)) {
					Node to = e.getToNode();
					if ((to.getLabel().contains(filler)
							|| (filler instanceof OWLObjectIntersectionOf
									&& to.getLabel().containsAll(filler.asConjunctSet()))
							|| (filler instanceof OWLObjectUnionOf
									&& to.getLabel().stream().anyMatch(filler.asDisjunctSet()::contains)))
							&& !to.isReset()) {
						if (e.isPredEdge()) {
							predEdges++;
							otherNodes.add(to);
						} else if (e.isSuccEdge()) {
							int card = to.getCardinality();
							nodesCard += card;
							if (maxCard < card) {
								maxCard = card;
								if (filler instanceof OWLObjectIntersectionOf) {
									for (OWLClassExpression cj : filler.asConjunctSet()) {
										maxDs.add(to.getnLabel().getCndList().getCdSet().stream()
												.filter(cnd -> cnd.getCe().equals(cj)).iterator().next().getDs());
									}
								} else if (filler instanceof OWLObjectUnionOf) {
									for (OWLClassExpression dj : filler.asDisjunctSet()) {
										maxDs.add(to.getnLabel().getCndList().getCdSet().stream()
												.filter(cnd -> cnd.getCe().equals(dj)).iterator().next().getDs());
									}
								} else {
									maxDs = to.getnLabel().getCndList().getCdSet().stream()
											.filter(cnd -> cnd.getCe().equals(filler)).iterator().next().getDs();

								}
							}
							otherNodes.add(to);
						}
					}
				}
			}
			// }
			if (maxCard > cardinality) {
				// FIXME: check dependency set
				if (!ds.isEmpty() || !maxDs.isEmpty()) {
					// System.err.println("mxds "+ maxDs.getMax());
					if (!clashHandler(DependencySet.plus(DependencySet.create(ds), DependencySet.create(maxDs)), n))
						isInconsistent(n);
				} else
					isInconsistent(n);
				return false;

			}
			// System.err.println("otherNodes "+ otherNodes.size());
			if (cardinality < (nodesCard + predEdges)) {
				for (Node x : otherNodes) {
					if (x.getCardinality() > 1) {
						List<Node> newNodes = new ArrayList<>();
						for (int i = 0; i < x.getCardinality() - 1; i++) {
							// FIXME: check dependency set --- checked 14 sep 2019
							Node newNode = cg.addNode(NodeType.BLOCKABLE, DependencySet.create(x.getDs()));
							newNodes.add(newNode);
							newNode.addDisjointNode(x);
							x.addDisjointNode(newNode);

							for (ConceptNDepSet cnds : x.getnLabel().getCndList().getCdSet()) {
								if (cnds != null)
									cg.addConceptToNode(newNode, cnds);
							}
							// newEdges.add(cg.addEdge(from, newNode, e.getLabel(), e.getDepSet(),
							// e.isSuccEdge()));
							for (Edge outE : x.getOutgoingEdges()) {
								cg.addEdge(newNode, outE.getToNode(), outE.getLabel(), outE.getDepSet(),
										outE.isSuccEdge());
							}
						}
						for (int i = 0; i < newNodes.size(); i++) {
							Node nn = newNodes.get(i);
							for (int k = 0; k < i; k++) {
								nn.addDisjointNode(newNodes.get(k));
							}
							for (int k = i + 1; k < newNodes.size(); k++) {
								nn.addDisjointNode(newNodes.get(k));
							}
						}

						cg.updateNodeCardinality(x, 1);
						newNodes.add(x);
						splitNodes.add(newNodes);
						allNodes.addAll(newNodes);
					} else
						allNodes.add(x);
				}

				// needs merging
				// System.err.println("splitNodes "+ splitNodes.size() + "cardinality "+
				// cardinality);

				while (allNodes.size() > cardinality) {
					for (int i = 0; i < allNodes.size() - 1; i++) {
						for (int j = i + 1; j < allNodes.size(); j++) {
							if (!allNodes.get(i).equals(allNodes.get(j))) {
								if (canMerge(allNodes.get(j), allNodes.get(i))) {
									mergeNodes(allNodes.get(j), allNodes.get(i), ds);
									allNodes.remove(allNodes.get(j));
									if (allNodes.size() <= cardinality)
										break;
								}
							}
						}
						if (allNodes.size() <= cardinality)
							break;
					}
					break;
				}

				if (allNodes.size() > cardinality) {
					// not able to satisfy at-most restriction
					// FIXME: Check dependencySet ds
					if (!ds.isEmpty()) {
						if (!clashHandler(ds, n))
							isInconsistent(n);
					} else
						isInconsistent(n);
					return true;// return false;//FIXME: check if its correct
				}

			}
		}
		return true;
	}

	private boolean needAtMostNomRule(Node n, OWLObjectMaxCardinality mx) {
		OWLObjectPropertyExpression role = mx.getProperty();
		OWLClassExpression filler = mx.getFiller();
		List<Edge> outgoingEdges = n
				.getOutgoingEdges().stream().filter(e -> e.getLabel().contains(role) && e.isSuccEdge()
						&& e.getToNode().getLabel().contains(filler) && e.getToNode().isNINode())
				.collect(Collectors.toList());

		if (outgoingEdges.size() == mx.getCardinality())
			return true;
		else
			return false;
	}

	private boolean canMerge(Node from, Node to) {
	//	System.err.println("can merge");
		if (from.getDisjointNodes().contains(to)) {
			return false;
		}
		/*
		 * if(config.isSHOIQ() && to.isNominalNode()) { Set<ConceptNDepSet> maxCards =
		 * new HashSet<>();
		 * maxCards.addAll(from.getnLabel().getCndList().getCdSet().stream() .filter(cnd
		 * -> cnd.getCe() instanceof
		 * OWLObjectMaxCardinality).collect(Collectors.toSet()));
		 * maxCards.addAll(to.getnLabel().getCndList().getCdSet().stream() .filter(cnd
		 * -> cnd.getCe() instanceof
		 * OWLObjectMaxCardinality).collect(Collectors.toSet())); if(!checkAtMost(from ,
		 * to , maxCards)) { return false; } }
		 */
		//System.err.println("from.getLabel() " + from.getLabel());
		//System.err.println("to.getLabel() " + to.getLabel());
		for (OWLClassExpression c : from.getLabel()) {
			if (to.getLabel().contains(c.getComplementNNF())) {
				ConceptNDepSet cnds = from.getnLabel().getCndList().getCdSet().stream()
						.filter(cnd -> cnd.getCe().equals(c)).iterator().next();
				ConceptNDepSet cnds2 = to.getnLabel().getCndList().getCdSet().stream()
						.filter(cnd -> cnd.getCe().equals(c.getComplementNNF())).iterator().next();
				if (cnds.getDs().isEmpty() && cnds2.getDs().isEmpty()) {
					return false;
				}
			}
		}
		return true;
	}

	public boolean applyExistentialRule(Node from, OWLObjectSomeValuesFrom objSV, DependencySet ds) {
		if(!cg.getNodeBase().contains(from)) {
			return true;
		}
		System.out.println("Applying exist Rule...");
	//	System.out.println("nid: " + from.getId() + " blocked " + from.isBlocked());
		/*
		 * for(OWLClassExpression oc : from.getLabel()) {
		 * System.out.println("exist before "+ oc + " ds "+
		 * from.getnLabel().getCndList().getCdSet().stream().filter(cnds ->
		 * cnds.getCe().equals(oc)).iterator().next().getDs().getbpList()); }
		 */
		if (!from.isBlocked()) {
			OWLObjectPropertyExpression role = objSV.getProperty();
			OWLClassExpression filler = objSV.getFiller();
			Edge e = this.cg.getEdge(from, filler, role);
			if (e == null) {
				// System.out.println("nid: "+from.getId()+" role " + role);
				Node blocker = findBlocker(from);
				if (blocker != null && !from.equals(blocker)) {
					blockNode(from, blocker);
					// cg.setNodeBlocked(from, blocker);
					return true;
				}
				if (filler instanceof OWLObjectOneOf) {
					OWLClassExpression ci = df
							.getOWLObjectOneOf(((OWLObjectOneOf) filler).individuals().iterator().next());
					Node nom = findNominalNode(ci);
					if (nom != null) {
						e = this.cg.addEdge(from, nom, getAllRoles(role), ds);
						if (!this.absorbRoleRule(getAllRoles(role), from, nom, ds))
							return false;
						// e = this.cg.addEdge(from, nom, role, ds);
						updateConceptDepSet(nom, ds, ci);
						processForAll(from);
						processForAll(nom);
						// processAtMost(from);
						processAtMost(nom);
						// applyTransitiveRule(from, nom, e.getLabel(), ds);
						if (!applyTransitiveRule(from, nom, e.getLabel(), ds))
							return false;

					} else {
						Node to = this.cg.addNode(NodeType.NOMINAL, ci, ds);
						if (!this.absorbRule1(df.getOWLThing(), to, ds))
							return false;
						addTGAxiom(to, ds);
						to.setConceptsDependencies(ci, ds);
						ConceptNDepSet cnds = new ConceptNDepSet(ci, ds);
						e = this.cg.addEdge(from, to, getAllRoles(role), ds);
						if (!this.absorbRoleRule(getAllRoles(role), from, to, ds))
							return false;
						// e = this.cg.addEdge(from, to, role, ds);
						this.cg.addConceptToNode(to, cnds);
						if (!addApplicableGCIs(to, ci, ds))
							return false;
						processForAll(from);
						// processAtMost(from);
						if (!absorbNominal(ci, to, ds))
							return false;
						if (!applyTransitiveRule(from, to, e.getLabel(), ds))
							return false;

					}
				}

				else {
					Node to = this.cg.addNode(NodeType.BLOCKABLE, filler, ds);
					if (!this.absorbRule1(df.getOWLThing(), to, ds))
						return false;
					addTGAxiom(to, ds);
					to.setConceptsDependencies(filler, ds);
					ConceptNDepSet cnds = new ConceptNDepSet(filler, ds);
					e = this.cg.addEdge(from, to, getAllRoles(role), ds);
					if (!this.absorbRoleRule(getAllRoles(role), from, to, ds))
						return false;
					// e = this.cg.addEdge(from, to, role, ds);
					this.cg.addConceptToNode(to, cnds);
					
					// processAtMost(from);
					if (filler instanceof OWLClass) {
						to.addSimpleLabel(filler);
						if (!absorbRule1(filler, to, ds))
							return false;
						if (!absorbRule2(to))
							return false;
						if (!addApplicableGCIs(to, filler, ds))
							return false;
					} else if (filler instanceof OWLObjectComplementOf) {
						if (!absorbRule3(filler, to, ds))
							return false;
						if (!addApplicableGCIs(to, filler, ds))
							return false;
					} else if (filler instanceof OWLObjectCardinalityRestriction) {
						addToDoEntry(to, filler, cnds);
						if (!addApplicableGCIs(to, ((OWLObjectCardinalityRestriction) filler).getProperty(), ds))
							return false;
					} else if (filler instanceof OWLObjectSomeValuesFrom) {
						addToDoEntry(to, filler, cnds);
						if (!addApplicableGCIs(to, ((OWLObjectSomeValuesFrom) filler).getProperty(), ds))
							return false;
					} else if (filler instanceof OWLObjectAllValuesFrom) {
						addToDoEntry(to, filler, cnds);
						if (!addApplicableGCIs(to, ((OWLObjectAllValuesFrom) filler).getProperty(), ds))
							return false;
					} else {
						addToDoEntry(to, filler, cnds);
					}
					processForAll(from);
					if (!applyTransitiveRule(from, to, e.getLabel(), ds))
						return false;
				}
			} else {

				Node to = e.getToNode();
				// System.out.println("nid: "+from.getId()+" nid exists "+to.getId()+" node
				// label " + from.getLabel());
				updateConceptDepSet(to, ds, filler);
				updateEdgeDepSet(ds, e);

				// updateToDoEntryDepSet(to, filler,
				// to.getnLabel().getCndList().getCdSet().stream().filter(cnds ->
				// cnds.getCe().equals(filler)).iterator().next().getDs());

			}
		}
		return true;
	}

	public boolean applyExistentialRule(Node from, OWLObjectHasValue objSV, DependencySet ds) {
		// System.out.println("Applying has value Rule...");
		if(!cg.getNodeBase().contains(from)) {
			return true;
		}
		if (!from.isBlocked()) {
			OWLObjectPropertyExpression role = objSV.getProperty();
			OWLClassExpression filler = df.getOWLObjectOneOf(objSV.getFiller());
			Edge e = this.cg.getEdge(from, filler, role);

			if (e == null) {
				Node blocker = findBlocker(from);
				if (blocker != null && !from.equals(blocker)) {
					blockNode(from, blocker);
					// cg.setNodeBlocked(from, blocker);
					return true;
				}
				OWLClassExpression ci = df.getOWLObjectOneOf(((OWLObjectOneOf) filler).individuals().iterator().next());
				Node nom = findNominalNode(ci);
				if (nom != null) {
					e = this.cg.addEdge(from, nom, getAllRoles(role), ds);
					if (!this.absorbRoleRule(getAllRoles(role), from, nom, ds))
						return false;
					// e = this.cg.addEdge(from, nom, role, ds);

					updateConceptDepSet(nom, ds, ci);
					processForAll(from);
					processForAll(nom);
					// processAtMost(from);
					processAtMost(nom);
					if (!applyTransitiveRule(from, nom, e.getLabel(), ds))
						return false;
				} else {
					Node to = this.cg.addNode(NodeType.NOMINAL, ci, ds);
					if (!this.absorbRule1(df.getOWLThing(), to, ds))
						return false;
					addTGAxiom(to, ds);
					to.setConceptsDependencies(ci, ds);
					ConceptNDepSet cnds = new ConceptNDepSet(ci, ds);
					e = this.cg.addEdge(from, to, getAllRoles(role), ds);
					if (!this.absorbRoleRule(getAllRoles(role), from, to, ds))
						return false;
					// e = this.cg.addEdge(from, to, role, ds);
					this.cg.addConceptToNode(to, cnds);
					if (!addApplicableGCIs(to, ci, ds))
						return false;
					// processAtMost(from);
					if (!absorbNominal(ci, to, ds))
						return false;
					processForAll(from);
					if (!applyTransitiveRule(from, to, e.getLabel(), ds))
						return false;
				}
			} else {
				Node to = e.getToNode();
				updateConceptDepSet(to, ds, filler);
				updateEdgeDepSet(ds, e);
			}
		}
		return true;
	}

	private boolean applyTransitiveRule(Node from, Node to, Set<OWLObjectPropertyExpression> edgeLabel,
			DependencySet ds) {
		// System.out.println("transitive roles");
		if(!cg.getNodeBase().contains(from)) {
			return true;
		}
		if (!this.transitiveRoles.isEmpty()) {
			for (OWLObjectPropertyExpression role : edgeLabel) {
				// System.out.println("role "+role+" inverse "+ role.getInverseProperty());
				if (this.transitiveRoles.contains(role) || this.transitiveRoles.contains(role.getInverseProperty())) {
					Set<OWLObjectPropertyExpression> supRoles = this.getAllRoles(role);
					for (OWLObjectAllValuesFrom forAll : from.getLabel().stream()
							.filter(l -> l instanceof OWLObjectAllValuesFrom).map(l -> (OWLObjectAllValuesFrom) l)
							.collect(Collectors.toSet())) {
						if (supRoles.contains(forAll.getProperty())) {
							OWLObjectAllValuesFrom fa = df.getOWLObjectAllValuesFrom(role, forAll.getFiller());
							ConceptNDepSet cnds = new ConceptNDepSet(fa, ds);
							this.cg.addConceptToNode(to, cnds);
							if (!checkClash(to, fa)) {
								addToDoEntry(to, fa, cnds);
								if (!addApplicableGCIs(to, fa.getProperty(), ds))
									return false;
							} else {
								DependencySet clashSet = getClashSet(to, fa, fa.getComplementNNF());
								if (!clashSet.isEmpty()) {
									clashSet.setCe(fa);
									clashSet.setCeNNF(fa.getComplementNNF());
									if (!clashHandler(clashSet, to))
										isInconsistent(to);
								} else
									isInconsistent(to);
								return false;
							}
						}
					}
				}
			}
		}
		return true;
	}

	public void applyAtMostNomRule(Node n) {
		Set<OWLObjectMaxCardinality> maxCards = n.getLabel().stream()
				.filter(ce -> ce instanceof OWLObjectMaxCardinality).map(ce -> (OWLObjectMaxCardinality) ce)
				.collect(Collectors.toSet());
		for (OWLObjectMaxCardinality mc : maxCards) {
			atMostNomRule(n, mc);
		}
	}

	public boolean atMostNomRule(Node n, OWLObjectMaxCardinality mc) {
		DependencySet ds = n.getnLabel().getCndList().getCdSet().stream().filter(ce -> ce.getCe().equals(mc)).iterator()
				.next().getDs();
		OWLObjectPropertyExpression role = mc.getProperty();
		OWLClassExpression filler = mc.getFiller();
		int cardinality = mc.getCardinality();
		List<Node> niNodes = new ArrayList<>();
		List<Node> otherNodes = new ArrayList<>();
		int nodesCard = 0;
		int maxCard = 0;
		DependencySet maxDs = DependencySet.create();

		for (Edge e : n.getOutgoingEdges()) {
			if (e.getLabel().contains(role) && !e.isReset()) {
				Node to = e.getToNode();
				if ((to.getLabel().contains(filler)
						|| (filler instanceof OWLObjectIntersectionOf
								&& to.getLabel().containsAll(filler.asConjunctSet()))
						|| (filler instanceof OWLObjectUnionOf
								&& to.getLabel().stream().anyMatch(filler.asDisjunctSet()::contains)))
						&& !to.isReset()) {
					int card = to.getCardinality();
					nodesCard += card;
					if (maxCard < card) {
						maxCard = card;
						if (filler instanceof OWLObjectIntersectionOf) {
							for (OWLClassExpression cj : filler.asConjunctSet()) {
								maxDs.add(to.getnLabel().getCndList().getCdSet().stream()
										.filter(cnd -> cnd.getCe().equals(cj)).iterator().next().getDs());
							}
						} else if (filler instanceof OWLObjectUnionOf) {
							for (OWLClassExpression dj : filler.asDisjunctSet()) {
								maxDs.add(to.getnLabel().getCndList().getCdSet().stream()
										.filter(cnd -> cnd.getCe().equals(dj)).iterator().next().getDs());
							}
						} else {
							maxDs = to.getnLabel().getCndList().getCdSet().stream()
									.filter(cnd -> cnd.getCe().equals(filler)).iterator().next().getDs();

						}
					}
					if (to.isNINode()) {
						niNodes.add(to);
					} else {
						otherNodes.add(to);
					}
				} /*
					 * if(to.getLabel().contains(filler) && !to.isReset()) { int card =
					 * to.getCardinality(); nodesCard += card; if(maxCard < card) { maxCard = card;
					 * maxDs =
					 * DependencySet.create(to.getnLabel().getCndList().getCdSet().stream().filter(
					 * ce -> ce.getCe().equals(filler)).iterator().next().getDs()); }
					 * if(to.isNINode()) { niNodes.add(to); } else { otherNodes.add(to); } }
					 */
			}
		}
		if (maxCard > cardinality) {
			// FIXME: check dependency set
			DependencySet clashSet = DependencySet.plus(DependencySet.create(ds), maxDs);
			if (!clashSet.isEmpty()) {
				if (!clashHandler(clashSet, n))
					isInconsistent(n);
			} else
				isInconsistent(n);
			return false;

		}
		if (cardinality < nodesCard) {
			if (maxCard > 1) {
				List<Node> allNewNodes = new ArrayList<>();
				for (Node x : otherNodes) {
					if (x.getCardinality() > 1) {
						List<Node> newNodes = new ArrayList<>();
						for (int i = 0; i < x.getCardinality() - 1; i++) {
							Node newNode = cg.addNode(NodeType.BLOCKABLE, ds);
							// this.absorbRule1(df.getOWLThing(), newNode, ds);
							newNodes.add(newNode);
							newNode.addDisjointNode(x);
							x.addDisjointNode(newNode);

							for (ConceptNDepSet cnds : x.getnLabel().getCndList().getCdSet()) {
								cg.addConceptToNode(newNode, cnds);
							}
							// newEdges.add(cg.addEdge(from, newNode, e.getLabel(), e.getDepSet(),
							// e.isSuccEdge()));
							for (Edge outE : x.getOutgoingEdges()) {
								cg.addEdge(newNode, outE.getToNode(), outE.getLabel(), outE.getDepSet(),
										outE.isSuccEdge());
								if (!this.absorbRoleRule(outE.getLabel(), newNode, outE.getToNode(), outE.getDepSet()))
									return false;
							}
						}
						for (int i = 0; i < newNodes.size(); i++) {
							Node nn = newNodes.get(i);
							for (int k = 0; k < i; k++) {
								nn.addDisjointNode(newNodes.get(k));
							}
							for (int k = i + 1; k < newNodes.size(); k++) {
								nn.addDisjointNode(newNodes.get(k));
							}
						}

						cg.updateNodeCardinality(x, 1);
						allNewNodes.addAll(newNodes);
					}

				}
				otherNodes.addAll(allNewNodes);
			}

			// needs merging
			// System.err.println("otherNodes.size() "+otherNodes.size() +" ni.size
			// "+niNodes.size());

			int i = 0;
			while (i < otherNodes.size()) {
				for (int j = 0; j < niNodes.size(); j++) {
					if (i < otherNodes.size()) {
						// System.err.println("merging...");
						// System.err.println( otherNodes.get(i).getId()+ "into" +niNodes.get(j).getId()
						// );
						this.mergeNodes(otherNodes.get(i), niNodes.get(j), ds);
						i++;
					} else
						break;
				}
				for (int l = 0; l < niNodes.size(); l++) {
					processForAll(niNodes.get(l));
					// processAtMost(niNodes.get(l));
				}
			}
		}
		return true;
	}

	public boolean applyForAllRule(Node from, OWLObjectAllValuesFrom objAV, DependencySet ds) {
		if(!cg.getNodeBase().contains(from)) {
			return true;
		}
		System.out.println("Applying for all Rule..." + from.getNodeId());
		/*
		 * if(from.isBlocked()) { System.out.println(from.getNodeId() +" "+
		 * from.isBlocked()+" blocker "+ from.getBlocker().getId());
		 * 
		 * }
		 */
		// if(!from.isBlocked()) {
		OWLObjectPropertyExpression role = objAV.getProperty();
		OWLClassExpression filler = objAV.getFiller();
		// System.out.println("outgoing edges: " + from.getOutgoingEdges().size());
		// System.out.println("incoming edges: "+ from.getIncomingEdges().size());
		Set<Edge> edges = this.cg.getEdge(from, role);
		if (edges.size() != 0) {
			boolean hasNominal = false;
			if (config.isSHO() || config.isSHOI() || config.isSHOIQ() || config.isSHOQ())
				hasNominal = this.hasNominal(filler);
			for (Edge e : edges) {
				Node n = e.getToNode();
				// System.out.println("outgoing edge:node " + n.getId() + "filler "+ filler);

				int nodeCard = n.getCardinality();
				// System.out.println("add for all concept to node: "+ n.getId() +" nodeCard? "+
				// nodeCard);
				/// FIXME : reset in case of nominal propagation
				if (hasNominal && nodeCard > 1) {
					reset(n);
					this.splitNode(n);
					continue;
				}
				boolean flag = false;
				DependencySet depSet = updateDepSetForAll(e, ds);
				ConceptNDepSet cnds = new ConceptNDepSet(filler, depSet);
				if (isConceptExist(n, filler)) {
					// System.out.println("outgoing edges: "+ from.getOutgoingEdges().size());
					flag = true;
					updateConceptDepSet(n, depSet, filler);
					/*
					 * if (!((filler instanceof OWLClass) || (filler instanceof OWLObjectOneOf) ||
					 * (filler instanceof OWLObjectComplementOf))) { ConceptNDepSet cnd =
					 * n.getnLabel().getCndList().getCdSet().stream() .filter(cnds1 -> cnds1 != null
					 * && cnds1.getCe().equals(filler)).iterator().next(); if (cnd != null)
					 * updateToDoEntryDepSet(n, filler, cnd.getDs()); }
					 */
				} else if (filler instanceof OWLObjectOneOf) {
					flag = true;
					if (processNominal(filler, n, cnds, depSet) == null)
						return false;
				} else if (filler instanceof OWLObjectCardinalityRestriction) {
					flag = true;
					if (needToAdd((OWLObjectCardinalityRestriction) filler, n)) {
						this.cg.addConceptToNode(n, cnds);
						//if (!checkClash(n, filler)) {
						if (!checkQCRClash((OWLObjectCardinalityRestriction) filler, n)) {
							if (needReset(filler, n)) {
								reset(n);
								addToDoEntries(n);
							} else {
								addToDoEntry(n, filler, cnds);
								if (filler instanceof OWLObjectMinCardinality)
									checkExistingEntries(n, filler);
							}
							if (!addApplicableGCIs(n, ((OWLObjectCardinalityRestriction) filler).getProperty(), ds))
								return false;
						} else {
							//DependencySet clashSet = getClashSet(n, filler, filler.getComplementNNF());
							DependencySet clashSet = getQCRClashSet((OWLObjectCardinalityRestriction) filler, n);
							if (!clashSet.isEmpty()) {
								clashSet.setCe(filler);
								clashSet.setCeNNF(filler.getComplementNNF());
								if (!clashHandler(clashSet, n))
									isInconsistent(n);
							} else
								isInconsistent(n);
							return false;
						}
					}
				} else if (filler instanceof OWLObjectSomeValuesFrom) {
					flag = true;
					this.cg.addConceptToNode(n, cnds);
					if (!checkClash(n, filler)) {
						if (needReset((OWLObjectSomeValuesFrom) filler, n)) {
							reset(n);
							addToDoEntries(n);
						} else {
							addToDoEntry(n, filler, cnds);
							checkExistingEntries(n, filler);
						}
						if (!addApplicableGCIs(n, ((OWLObjectSomeValuesFrom) filler).getProperty(), ds))
							return false;
					} else {
						DependencySet clashSet = getClashSet(n, filler, filler.getComplementNNF());
						if (!clashSet.isEmpty()) {
							clashSet.setCe(filler);
							clashSet.setCeNNF(filler.getComplementNNF());
							if (!clashHandler(clashSet, n))
								isInconsistent(n);
						} else
							isInconsistent(n);
						return false;
					}
				} else if (filler instanceof OWLObjectAllValuesFrom) {
					flag = true;
					this.cg.addConceptToNode(n, cnds);
					if (!checkClash(n, filler)) {
						addToDoEntry(n, filler, cnds);
						if (!addApplicableGCIs(n, ((OWLObjectAllValuesFrom) filler).getProperty(), ds))
							return false;
					} else {
						DependencySet clashSet = getClashSet(n, filler, filler.getComplementNNF());
						if (!clashSet.isEmpty()) {
							clashSet.setCe(filler);
							clashSet.setCeNNF(filler.getComplementNNF());
							if (!clashHandler(clashSet, n))
								isInconsistent(n);
						} else
							isInconsistent(n);
						return false;
					}
				}
				if (!flag) {
					//// 25-Oct-2019
					if (e.isPredEdge()) {
						n.addBackPropagatedLabel(filler);
					}
					////
					this.cg.addConceptToNode(n, cnds);
					// cg.checkBlockedStatus(n);
					if (!checkClash(n, filler)) {
						if (filler instanceof OWLClass) {
							n.addSimpleLabel(filler);
							if (!absorbRule1(filler, n, depSet))
								return false;
							if (!absorbRule2(n))
								return false;
							if (!addApplicableGCIs(n, filler, ds))
								return false;
						} else if (filler instanceof OWLObjectComplementOf) {
							if (!absorbRule3(filler, n, depSet))
								return false;
							if (!addApplicableGCIs(n, filler, ds))
								return false;
						} else {
							addToDoEntry(n, filler, cnds);
						}

					} else {
						// System.out.println("clash "+ filler.getComplementNNF() + ""+
						// n.getnLabel().getCndList().getCdSet().stream().filter(cn ->
						// cn.getCe().equals(filler.getComplementNNF())).iterator().next().getDs().getbpList());
						DependencySet clashSet = getClashSet(n, filler, filler.getComplementNNF());
						if (!clashSet.isEmpty()) {
							clashSet.setCe(filler);
							clashSet.setCeNNF(filler.getComplementNNF());
							if (!clashHandler(clashSet, n))
								isInconsistent(n);
						} else
							isInconsistent(n);
						return false;
					}
				}
			}
		}
		// }
		// else we cannot apply forAll rule
		return true;
	}

	private void checkExistingEntries(Node n, OWLClassExpression filler) {
		Set<OWLObjectPropertyExpression> s1 = null;
		if (filler instanceof OWLObjectCardinalityRestriction) {
			s1 = new HashSet<>(this.getAllRoles(((OWLObjectCardinalityRestriction) filler).getProperty()));
		} else if (filler instanceof OWLObjectSomeValuesFrom) {
			s1 = new HashSet<>(this.getAllRoles(((OWLObjectSomeValuesFrom) filler).getProperty()));
		}
		List<ConceptNDepSet> cndList = n.getnLabel().getCndList().getCdSet();
		for (ConceptNDepSet cnd : cndList) {
			OWLClassExpression ce = cnd.getCe();
			// System.err.println("ce "+ ce);
			if (ce instanceof OWLObjectMaxCardinality) {
				Set<OWLObjectPropertyExpression> s2 = new HashSet<>(
						this.getAllRoles(((OWLObjectCardinalityRestriction) ce).getProperty()));
				s2.retainAll(s1);
				if (!s2.isEmpty()) {
					if (!todo.hasToDoEntry(n, NodeTag.GE, ce)) {
						// System.err.println("no entry");
						todo.addEntry(n, NodeTag.GE, cnd);
					}
				}
			} else if (ce instanceof OWLObjectAllValuesFrom) {
				Set<OWLObjectPropertyExpression> s2 = new HashSet<>(
						this.getAllRoles(((OWLObjectAllValuesFrom) ce).getProperty()));
				s2.retainAll(s1);
				if (!s2.isEmpty()) {
					if (!todo.hasToDoEntry(n, NodeTag.FORALL, ce)) {
						// System.err.println("no entry");
						todo.addEntry(n, NodeTag.FORALL, cnd);
					}
				}
			}
		}

	}

	private Set<Node> needNomPredReset(Node n, DependencySet ds) {

		Set<Node> nodesToReset = new HashSet<>();

		if (ds.isEmpty())
			return nodesToReset;

		for (OWLObjectMaxCardinality mc : n.getLabel().stream().filter(ce -> ce instanceof OWLObjectMaxCardinality)
				.map(ce -> (OWLObjectMaxCardinality) ce).collect(Collectors.toSet())) {
			OWLObjectPropertyExpression role = mc.getProperty();
			OWLClassExpression filler = mc.getFiller();
			int cardinality = mc.getCardinality();
			for (Edge e : n.getOutgoingEdges()) {
				if (!e.isReset() && e.getLabel().contains(role)) {
					Node to = e.getToNode();
					if ((to.getLabel().contains(filler)
							|| (filler instanceof OWLObjectIntersectionOf
									&& to.getLabel().containsAll(filler.asConjunctSet()))
							|| (filler instanceof OWLObjectUnionOf
									&& to.getLabel().stream().anyMatch(filler.asDisjunctSet()::contains)))
							&& !to.isReset()) {
						System.err.println("to " + to.getId() + " card " + to.getCardinality());
						if (cardinality < to.getCardinality()) {
							nodesToReset.add(to);
						}
					}
				}
			}
		}

		return nodesToReset;

		//////
		/*
		 * Set<Node> nodesToReset = new HashSet<>(); if(n.isNominalNode()) {
		 * for(OWLObjectOneOf nominal : n.getLabel().stream().filter(ce -> ce instanceof
		 * OWLObjectOneOf).map(ce -> (OWLObjectOneOf)ce).collect(Collectors.toSet())) {
		 * ConceptNDepSet cnd =
		 * n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds!=null &&
		 * cnds.getCe().equals(nominal)).iterator().next(); if(cnd.getDs().isEmpty())
		 * return nodesToReset; } for(OWLObjectMaxCardinality mc :
		 * n.getLabel().stream().filter(ce -> ce instanceof
		 * OWLObjectMaxCardinality).map(ce ->
		 * (OWLObjectMaxCardinality)ce).collect(Collectors.toSet())) {
		 * OWLObjectPropertyExpression role = mc.getProperty(); OWLClassExpression
		 * filler = mc.getFiller(); int cardinality = mc.getCardinality(); for(Edge e :
		 * n.getOutgoingEdges()) { if(!e.isReset() && e.getLabel().contains(role)) {
		 * Node to = e.getToNode(); if((to.getLabel().contains(filler) || (filler
		 * instanceof OWLObjectIntersectionOf &&
		 * to.getLabel().containsAll(filler.asConjunctSet())) || (filler instanceof
		 * OWLObjectUnionOf &&
		 * to.getLabel().stream().anyMatch(filler.asDisjunctSet()::contains))) &&
		 * !to.isReset()) { //System.err.println("to "+ to.getId()
		 * +" card "+to.getCardinality()); if(cardinality < to.getCardinality()) {
		 * nodesToReset.add(to); } } } } } } return nodesToReset;
		 */
	}

	private boolean processAtMost(Node n) {
		System.out.println("process at most"+ n.getId());
		consistencyCheckGE = true;
		if (needToApplyAtMost(n)) {

			// System.err.println("mxds ");
			/*
			 * if(n.isNominalNode() && n.getLabel().stream().anyMatch(ce -> ce instanceof
			 * OWLObjectMaxCardinality) && n.getOutgoingEdges().stream().anyMatch(e ->
			 * e.isPredEdge())) { if(isNIRuleApplicable(n)) this.applyNIRule(n);
			 * this.applyAtMostNomRule(n); } else
			 */
			if (n.getLabel().stream().anyMatch(ce -> ce instanceof OWLObjectMaxCardinality)) {
				for (OWLObjectMaxCardinality mxCard : n.getLabel().stream()
						.filter(ce -> ce instanceof OWLObjectMaxCardinality).map(ce -> (OWLObjectMaxCardinality) ce)
						.collect(Collectors.toSet())) {
					ConceptNDepSet cnd = n.getnLabel().getCndList().getCdSet().stream()
							.filter(cnds -> cnds.getCe().equals(mxCard)).iterator().next();

					if (!this.applyGERule(n, mxCard, cnd.getDs()))
						return false;
				}
			}
		} else {
			if (!consistencyCheckGE)
				return false;

		}
		return true;
	}

	private boolean needToApplyAtMost(Node n) {
		for (OWLObjectMaxCardinality mc : n.getLabel().stream().filter(ce -> ce instanceof OWLObjectMaxCardinality)
				.map(ce -> (OWLObjectMaxCardinality) ce).collect(Collectors.toSet())) {
			DependencySet ds = n.getnLabel().getCndList().getCdSet().stream().filter(ce -> ce.getCe().equals(mc))
					.iterator().next().getDs();
			if (!needToApplyAtMost(n, mc, ds))
				return false;
		}
		return true;
	}

/*	private boolean getConsistencyCheckGE() {
		return consistencyCheckGE;
	}*/

	private boolean needToApplyAtMost(Node n, OWLObjectMaxCardinality mc, DependencySet ds) {
		if (n.isNominalNode()) {
			OWLObjectPropertyExpression role = mc.getProperty();
			OWLClassExpression filler = mc.getFiller();
			int cardinality = mc.getCardinality();
			int nodesCard = 0;
			int maxCard = 0;
			int maxAdded = 0;
			Set<Node> nodes = new HashSet<>();
			Set<Node> djNodes = new HashSet<>();
			DependencySet maxDs = DependencySet.create();
			DependencySet djDs = DependencySet.create();
			for (Edge e : n.getOutgoingEdges()) {
				if (!e.isReset() && e.getLabel().contains(role) && e.getToNode().getLabel().contains(filler)) {
					Node to = e.getToNode();
					//// System.err.println("to "+ to.getId());
					int card = to.getCardinality();
					nodes.add(to);
					for (Node dn : to.getDisjointNodes()) {
						if (nodes.contains(dn)) {
							djNodes.add(to);
							djNodes.add(dn);
							// maxAdded += card;
							// maxDs = DependencySet.create(n.getDs());
							// maxAdded += dn.getCardinality();
						}
					}
					nodesCard += card;
					if (maxCard < card) {
						maxCard = card;
						maxDs = DependencySet.create(n.getDs());
						// maxDs = to.getnLabel().getCndList().getCdSet().stream().filter(cnd ->
						// cnd.getCe().equals(filler)).iterator().next().getDs();

					}
				}
			}
			for (Node djn : djNodes) {
				maxAdded += djn.getCardinality();
				djDs.add(DependencySet.create(djn.getDs()));

			}
			if (maxCard > cardinality) {
				// System.err.println("mxds "+ maxDs.getMax() +" "+filler);
				// FIXME: check dependency set
				if (!ds.isEmpty() || !maxDs.isEmpty()) {
					// System.err.println("mxds "+ maxDs.getMax() +" "+filler);
					if (!clashHandler(DependencySet.plus(DependencySet.create(ds), DependencySet.create(maxDs)), n))
						isInconsistent(n);
				} else
					isInconsistent(n);
				consistencyCheckGE = false;
				return false;

			}
			if (cardinality < maxAdded) {
				if (!ds.isEmpty() || !djDs.isEmpty()) {
					// System.err.println("mxds "+ maxDs.getMax() +" "+filler);
					if (!clashHandler(DependencySet.plus(DependencySet.create(ds), DependencySet.create(maxDs)), n))
						isInconsistent(n);
				} else
					isInconsistent(n);
				consistencyCheckGE = false;
				return false;
			}
			if (cardinality < nodesCard) {
				return true;
			}
			return false;
		} else {
			OWLObjectPropertyExpression role = mc.getProperty();
			OWLClassExpression filler = mc.getFiller();
			int cardinality = mc.getCardinality();
			int nodesCard = 0;
			int maxCard = 0;
			DependencySet maxDs = DependencySet.create();
			for (Edge e : n.getOutgoingEdges()) {
				if (!e.isReset() && e.getLabel().contains(role) && e.getToNode().getLabel().contains(filler)) {
					if (e.isPredEdge()) {
						nodesCard++;
					} else {
						Node to = e.getToNode();
						// System.err.println("to "+ to.getId());
						int card = to.getCardinality();
						nodesCard += card;
						if (maxCard < card) {
							maxCard = card;
							maxDs = to.getnLabel().getCndList().getCdSet().stream()
									.filter(cnd -> cnd.getCe().equals(filler)).iterator().next().getDs();

						}
					}
				}
			}

			if (maxCard > cardinality) {
				// System.err.println("mxds "+ maxDs.getMax() +" "+filler);
				// FIXME: check dependency set
				if (!ds.isEmpty() || !maxDs.isEmpty()) {
					// System.err.println("mxds "+ maxDs.getMax() +" "+filler);
					if (!clashHandler(DependencySet.plus(DependencySet.create(ds), DependencySet.create(maxDs)), n))
						isInconsistent(n);
				} else
					isInconsistent(n);
				consistencyCheckGE = false;
				return false;

			}
			if (cardinality < nodesCard) {
				return true;
			}
			return false;
		}
	}

	public boolean applyAndRule(Node n, OWLObjectIntersectionOf objIn, DependencySet ds) {
		// System.out.println("Applying and Rule...");
		// Node n = n1;
		// System.out.println("is blocked "+ n.isBlocked());
		// if(!n.isBlocked()) {
		for (OWLClassExpression ce : objIn.asConjunctSet()) {
			// System.out.println("AND RULE ce "+ ce);
			n = addConcept(n, ce, ds, false);
			if (n == null) {
				return false;
			} else if (n.getId() == -1) {
				return true;
			}
		}
		// }
		return true;
	}

	public boolean applyOrRule(Node n, OWLObjectUnionOf objUn, ConceptNDepSet cn) {
		DependencySet ds = cn.getDs();
		 System.out.println("Applying or Rule..."+ n.getId() + objUn + " ds "+ds.getMax());
		// System.out.println("Applying or Rule: ds "+ds.getMax());

		// if(!n.isBlocked()) {
		if (objUn.asDisjunctSet().size() == 1) {
			return applyOr(n, objUn.asDisjunctSet().iterator().next(), ds);
		}
		DependencySet newDs = DependencySet.plus(DependencySet.create(ds), DependencySet.create(getCurLevel()));
		BranchHandler bh = new BranchHandler(objUn, cn, newDs, n);
		this.branches.put(getCurLevel(), bh);
		save(n);
		incCurLevel();

		boolean flag = false;
		for (OWLClassExpression dj : objUn.asDisjunctSet()) {
			if (isConceptExist(n, dj)) {
			//	System.err.println("exists : " + dj);
				flag = true;
				bh.disjunctTaken(dj);
				updateConceptDepSet(n, newDs, dj);
				/*
				 * if (!(dj instanceof OWLClass) || !(dj instanceof OWLObjectOneOf) || !(dj
				 * instanceof OWLObjectComplementOf)) updateToDoEntryDepSet(n, dj, newDs);
				 */
				break;
			}
		}
		if (!flag) {

			// BranchHandler bh = new BranchHandler(objUn, cn,
			// DependencySet.plus(DependencySet.create(ds),
			// DependencySet.create(getCurLevel())), n);
			// this.branches.put(getCurLevel(), bh);

			// --ds.add(DependencySet.create(getCurLevel()));
			// --copyGraph(n);
			// DependencySet newDs = DependencySet.plus(DependencySet.create(ds),
			// DependencySet.create(getCurLevel()));

			// save(n);
			// incCurLevel();
			//System.out.println("here");
			if (bh.hasNextOption()) {
				return applyOr(n, bh.getNextOption(), newDs);
			}
		}
		/// end uncommented 15 june 2020
		/// end commented
		// }
		return true;
	}

	public boolean applyOr(Node n, OWLClassExpression ce, DependencySet ds) {
	//	System.out.println("node  " + n.getId() + " or expression selected : " + ce);
		// System.out.println(" ds "+ds.getbpList());
		// System.out.print("label "+n.getLabel());
		// n.getnLabel().getCndList().getCdSet().stream().forEach(lb ->
		// System.out.print("label "+lb.getCe()));
		if (ce != null) {
			Node nn = addConcept(n, ce, ds, false);
			if (nn == null)
				return false;
			else if (nn.getId() == -1)
				return true;
		}
		return true;
	}

	private Node addConcept(Node n, OWLClassExpression ce, DependencySet ds, boolean isILPLabel) {
		if(!cg.getNodeBase().contains(n)) {
			return new Node();
		}
	//	System.err.println("addConcept : " + ce);
		if (isConceptExist(n, ce)) {
		//	System.err.println("exists : " + ce);
			// cg.saveN(n);
			updateConceptDepSet(n, ds, ce);
			/*if (!(ce instanceof OWLClass) || !(ce instanceof OWLObjectOneOf) || !(ce instanceof OWLObjectComplementOf)){
				ConceptNDepSet cnd = n.getnLabel().getCndList().getCdSet().stream()
						 .filter(cnds -> cnds != null && cnds.getCe().equals(ce)).iterator().next();
				if(!isEntryExist(n, ce)) {
					System.err.println("not exist : " + ce);
					return addConceptNEntry(n, ce, ds, isILPLabel);
				}
				
			}*/
			
			
			/*
			 * if (!((ce instanceof OWLClass) || !(ce instanceof OWLObjectOneOf) || !(ce
			 * instanceof OWLObjectComplementOf))) updateToDoEntryDepSet(n, ce, ds);
			 */
			/*
			 * ConceptNDepSet cnd = n.getnLabel().getCndList().getCdSet().stream()
			 * .filter(cnds -> cnds != null && cnds.getCe().equals(ce)).iterator().next();
			 * if (cnd != null) updateToDoEntryDepSet(n, ce, cnd.getDs());
			 */
			// updateToDoEntryDepSet(n, ce,
			// n.getnLabel().getCndList().getCdSet().stream().filter(cnds ->
			// cnds.getCe().equals(ce)).iterator().next().getDs());
		} else {
			// cg.save();
			ConceptNDepSet cnds = new ConceptNDepSet(ce, ds);
			if (ce instanceof OWLObjectOneOf) {
				if(isILPLabel) {
					this.cg.addConceptToNode(n, cnds);
					if (!addApplicableGCIs(n, ce, ds))
						return new Node();
					if (ce.toString().contains("#ni_")) {
						n.makeNINode();
					}
				}else{
					Node mergedNode = processNominal(ce, n, cnds, ds);
					if (mergedNode == null)
						return new Node();
					else
						n = mergedNode;
				}
			} else if (ce instanceof OWLObjectCardinalityRestriction) {
				if (needToAdd((OWLObjectCardinalityRestriction) ce, n)) {
					this.cg.addConceptToNode(n, cnds);
					//if (!checkClash(n, ce)) {
					if (!checkQCRClash((OWLObjectCardinalityRestriction) ce, n)) {
						if (needReset(ce, n)) {
							reset(n);
							addToDoEntries(n);
						} else {
							addToDoEntry(n, ce, cnds);
							if (ce instanceof OWLObjectMinCardinality)
								checkExistingEntries(n, ce);
						}
						if (!addApplicableGCIs(n, ((OWLObjectCardinalityRestriction) ce).getProperty(), ds))
							return new Node();
					} else {
						//DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
						DependencySet clashSet = getQCRClashSet((OWLObjectCardinalityRestriction) ce, n);
						if (!clashSet.isEmpty()) {
							clashSet.setCe(ce);
							clashSet.setCeNNF(ce.getComplementNNF());
							if (!clashHandler(clashSet, n))
								isInconsistent(n);
						} else
							isInconsistent(n);
						return new Node();
					}
				}
			} else if (ce instanceof OWLObjectSomeValuesFrom) {
				this.cg.addConceptToNode(n, cnds);
				if (!checkClash(n, ce)) {
					if (needReset((OWLObjectSomeValuesFrom) ce, n)) {
						reset(n);
						addToDoEntries(n);
					} else {
						addToDoEntry(n, ce, cnds);
						checkExistingEntries(n, ce);
					}
					if (!addApplicableGCIs(n, ((OWLObjectSomeValuesFrom) ce).getProperty(), ds))
						return new Node();
				} else {
					DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
					if (!clashSet.isEmpty()) {
						clashSet.setCe(ce);
						clashSet.setCeNNF(ce.getComplementNNF());
						if (!clashHandler(clashSet, n))
							isInconsistent(n);
					} else
						isInconsistent(n);
					return new Node();
				}
			} else if (ce instanceof OWLObjectAllValuesFrom) {
				this.cg.addConceptToNode(n, cnds);
				if (!checkClash(n, ce)) {
					addToDoEntry(n, ce, cnds);
					if (!addApplicableGCIs(n, ((OWLObjectAllValuesFrom) ce).getProperty(), ds))
						return new Node();
				} else {
					DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
					if (!clashSet.isEmpty()) {
						clashSet.setCe(ce);
						clashSet.setCeNNF(ce.getComplementNNF());
						if (!clashHandler(clashSet, n))
							isInconsistent(n);
					} else
						isInconsistent(n);
					return new Node();
				}
			} else {
				this.cg.addConceptToNode(n, cnds);
				if (!checkClash(n, ce)) {
					if (ce instanceof OWLClass) {
						n.addSimpleLabel(ce);
						if(!isILPLabel) {
							if (!absorbRule1(ce, n, ds))
								return new Node();
							if (!absorbRule2(n))
								return new Node();
						}
						if (!addApplicableGCIs(n, ce, ds))
							return new Node();
					} else if (ce instanceof OWLObjectComplementOf) {
						if(!isILPLabel) {
							if (!absorbRule3(ce, n, ds))
								return new Node();
						}
						if (!addApplicableGCIs(n, ce, ds))
							return new Node();
					} else {
						addToDoEntry(n, ce, cnds);
					}
				} else {
					/*
					 * StackTraceElement[] el = Thread.currentThread().getStackTrace(); for
					 * (StackTraceElement e : el) { System.out.println(e.toString()); }
					 */
					DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
					if (!clashSet.isEmpty()) {
						clashSet.setCe(ce);
						clashSet.setCeNNF(ce.getComplementNNF());
						if (!clashHandler(clashSet, n))
							isInconsistent(n);
					} else
						isInconsistent(n);
					return new Node();
				}
			}
			/*
			 * for(Edge e : n.getIncomingEdges()) { this.processAtMost(e.getFromNode()); }
			 */
		}
		return n;
	}

	private Node addConceptNEntry(Node n, OWLClassExpression ce, DependencySet ds, boolean isILPLabel) {
		if(!cg.getNodeBase().contains(n)) {
			return new Node();
		}
		ConceptNDepSet cnds = new ConceptNDepSet(ce, ds);
		/*if (ce instanceof OWLObjectOneOf) {
			if(isILPLabel) {
				this.cg.addConceptToNode(n, cnds);
				if (!addApplicableGCIs(n, ce, ds))
					return new Node();
				if (ce.toString().contains("#ni_")) {
					n.makeNINode();
				}
			}else{
				Node mergedNode = processNominal(ce, n, cnds, ds);
				if (mergedNode == null)
					return new Node();
				else
					n = mergedNode;
			}
		} else*/ if (ce instanceof OWLObjectCardinalityRestriction) {
			if (needToAdd((OWLObjectCardinalityRestriction) ce, n)) {
				this.cg.addConceptToNode(n, cnds);
				//if (!checkClash(n, ce)) {
				if (!checkQCRClash((OWLObjectCardinalityRestriction) ce, n)) {
					if (needReset(ce, n)) {
						reset(n);
						addToDoEntries(n);
					} else {
						addToDoEntry(n, ce, cnds);
						if (ce instanceof OWLObjectMinCardinality)
							checkExistingEntries(n, ce);
					}
					if (!addApplicableGCIs(n, ((OWLObjectCardinalityRestriction) ce).getProperty(), ds))
						return new Node();
				} else {
					//DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
					DependencySet clashSet = getQCRClashSet((OWLObjectCardinalityRestriction) ce, n);
					if (!clashSet.isEmpty()) {
						clashSet.setCe(ce);
						clashSet.setCeNNF(ce.getComplementNNF());
						if (!clashHandler(clashSet, n))
							isInconsistent(n);
					} else
						isInconsistent(n);
					return new Node();
				}
			}
		} else if (ce instanceof OWLObjectSomeValuesFrom) {
			this.cg.addConceptToNode(n, cnds);
			if (!checkClash(n, ce)) {
				if (needReset((OWLObjectSomeValuesFrom) ce, n)) {
					reset(n);
					addToDoEntries(n);
				} else {
					addToDoEntry(n, ce, cnds);
					checkExistingEntries(n, ce);
				}
				if (!addApplicableGCIs(n, ((OWLObjectSomeValuesFrom) ce).getProperty(), ds))
					return new Node();
			} else {
				DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
				if (!clashSet.isEmpty()) {
					clashSet.setCe(ce);
					clashSet.setCeNNF(ce.getComplementNNF());
					if (!clashHandler(clashSet, n))
						isInconsistent(n);
				} else
					isInconsistent(n);
				return new Node();
			}
		} else if (ce instanceof OWLObjectAllValuesFrom) {
			this.cg.addConceptToNode(n, cnds);
			if (!checkClash(n, ce)) {
				addToDoEntry(n, ce, cnds);
				if (!addApplicableGCIs(n, ((OWLObjectAllValuesFrom) ce).getProperty(), ds))
					return new Node();
			} else {
				DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
				if (!clashSet.isEmpty()) {
					clashSet.setCe(ce);
					clashSet.setCeNNF(ce.getComplementNNF());
					if (!clashHandler(clashSet, n))
						isInconsistent(n);
				} else
					isInconsistent(n);
				return new Node();
			}
		} else {
			this.cg.addConceptToNode(n, cnds);
			if (!checkClash(n, ce)) {/*
				if (ce instanceof OWLClass) {
					n.addSimpleLabel(ce);
					if(!isILPLabel) {
						if (!absorbRule1(ce, n, ds))
							return new Node();
						if (!absorbRule2(n))
							return new Node();
					}
					if (!addApplicableGCIs(n, ce, ds))
						return new Node();
				} else if (ce instanceof OWLObjectComplementOf) {
					if(!isILPLabel) {
						if (!absorbRule3(ce, n, ds))
							return new Node();
					}
					if (!addApplicableGCIs(n, ce, ds))
						return new Node();
				} else {*/
					addToDoEntry(n, ce, cnds);
				//}
			} else {
				/*
				 * StackTraceElement[] el = Thread.currentThread().getStackTrace(); for
				 * (StackTraceElement e : el) { System.out.println(e.toString()); }
				 */
				DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
				if (!clashSet.isEmpty()) {
					clashSet.setCe(ce);
					clashSet.setCeNNF(ce.getComplementNNF());
					if (!clashHandler(clashSet, n))
						isInconsistent(n);
				} else
					isInconsistent(n);
				return new Node();
			}
		}
		return n;
	}

	private boolean isEntryExist(Node n, OWLClassExpression ce) {
		if(checkType(ce) != null)
			return todo.hasToDoEntry(n, checkType(ce), ce);
		else 
			return false;
		
	}

	private NodeTag checkType(OWLClassExpression ce) {
		if (ce instanceof OWLObjectIntersectionOf)
			return NodeTag.AND;
		else if (ce instanceof OWLObjectUnionOf)
			return NodeTag.OR;
		else if (ce instanceof OWLObjectSomeValuesFrom || ce instanceof OWLObjectHasValue)
			return NodeTag.EXISTS;
		else if (ce instanceof OWLObjectAllValuesFrom)
			return NodeTag.FORALL;
		else if (ce instanceof OWLObjectMinCardinality)
			return NodeTag.LE;
		else if (ce instanceof OWLObjectMaxCardinality)
			return NodeTag.GE;
		return null;
	}

	private boolean addApplicableGCIs(Node n, OWLClassExpression ce, DependencySet ds) {
		for (OWLClassExpression gci : intl.getApplicableGCIs(ce.getComplementNNF())) {
			//System.out.println("node " + n.getId() +" OWLClass GCI added: "+ gci);
			Node nn = addConcept(n, gci.getComplementNNF(), ds, false);
			if (nn.getId() == -1)
				return false;
		}
		return true;
	}

	private boolean addApplicableGCIs(Node n, OWLObjectPropertyExpression property, DependencySet ds) {
		Set<OWLObjectPropertyExpression> roles = this.getAllRoles(property);
		Set<OWLClassExpression> gcis = new HashSet<OWLClassExpression>();
	//	System.out.println("Role GCI for : "+ property);
		for (OWLObjectPropertyExpression r : roles) {
			if(n.getAbsorbedRoles().contains(r)) {
				continue;
			}
			n.getAbsorbedRoles().add(r);
			gcis.addAll(intl.getExtendedDomainRestrictions(r));
		}
	//	System.out.println("Role GCI added: "+ gcis.size());
		for (OWLClassExpression gci : gcis) {
		//	System.out.println("Role GCI added: "+ gci);
			Node nn = addConcept(n, gci, ds, false);
			if (nn.getId() == -1)
				return false;
		}
		return true;
	}

	private void processForAll(Node node) {
		// node.getLabel().stream().filter(l -> l instanceof OWLObjectAllValuesFrom).
		// forEach(l -> applyForAllRule(node, (OWLObjectAllValuesFrom)l,
		// node.getnLabel().getCndList().getCdSet().stream().filter(cds ->
		// cds.getCe().equals(l)).iterator().next().getDs()));

		/*
		 * Set<OWLObjectAllValuesFrom> forAll = node.getLabel().stream().filter(l -> l
		 * instanceof OWLObjectAllValuesFrom) .map(l -> (OWLObjectAllValuesFrom)
		 * l).collect(Collectors.toSet()); for (OWLObjectAllValuesFrom fa : forAll) {
		 * applyForAllRule(node, fa, node.getnLabel().getCndList().getCdSet().stream()
		 * .filter(cds -> cds.getCe().equals(fa)).iterator().next().getDs()); }
		 */
		Set<ConceptNDepSet> forAllCnds = node.getnLabel().getCndList().getCdSet().stream()
				.filter(cds -> cds.getCe() instanceof OWLObjectAllValuesFrom).map(l -> (ConceptNDepSet) l)
				.collect(Collectors.toSet());
		for (ConceptNDepSet fa : forAllCnds) {
			applyForAllRule(node, (OWLObjectAllValuesFrom) fa.getCe(), fa.getDs());
		}
	}

	private Node processNominal(OWLClassExpression ce, Node n, ConceptNDepSet cnds, DependencySet ds) {
		OWLClassExpression ci = df.getOWLObjectOneOf(((OWLObjectOneOf) ce).individuals().iterator().next());
		// System.out.println("process nominal : "+ ci);
		if (n.getCardinality() > 1) {
			reset(n);
			this.splitNode(n);
			return null;
		}
		if (!checkClash(n, ce)) {
			Node nom = findNominalNode(ci);
			if (nom == null) {
				if (makeNominalNode(n, cnds.getDs())) {
					this.cg.addConceptToNode(n, cnds);
					if (!addApplicableGCIs(n, ce, ds))
						return null;
				//	System.err.println("nominal node" + n.getId());
					cg.checkBlockedStatus(n);
					if (!absorbNominal(ce, n, ds))
						return null;
					/*
					 * if(needNomReset(n)) { reset(n); this.addToDoEntries(n); return null; }
					 */
					return n;
				} else
					return null;
			} else {
				if (nom.equals(n)) {
					updateConceptDepSet(n, ds, ci);
					return n;
				} else {

					System.out.println("Needs Merging! " + n.getId() + " into " + nom.getId() + " concept " + ci);
					// System.out.println("Node " + n.getLabel() + " into "+nom.getLabel());
					if (this.canMerge(n, nom)) {
						// System.out.println("can Merge! " + n.getId() + " into "+nom.getId());
						Node to = mergeNodes(n, nom, ci, ds);
					//	System.out.println("after Merge! " + to);
						//// new code 27-oct-2019
						// reset(to); //commented April 26, 2020
						if (to == null)
							return null;
						// this.addToDoEntries(to);
						////
						// processForAll(to);
						// processAtMost(to);
						return to;
					} else
						return null;

				}
			}
		} else {

			DependencySet clashSet = getClashSet(n, ce, ce.getComplementNNF());
			clashSet.add(DependencySet.create(ds));
		//	System.err.println("clashSet " + clashSet.getbpList());
			if (!clashSet.isEmpty()) {
				clashSet.setCe(ce);
				clashSet.setCeNNF(ce.getComplementNNF());
				if (!clashHandler(clashSet, n))
					isInconsistent(n);
			} else
				isInconsistent(n);
			return null;
		}
	}

	private Node mergeNodes(Node from, Node to, OWLClassExpression ce, DependencySet depSet) {
		/// newcode 14 jul 2k19
		if (from.getDisjointNodes().contains(to)) {
			if (!depSet.isEmpty()) {
				if (!clashHandler(depSet, to))
					isInconsistent(to);
			} else
				isInconsistent(to);
			return null;
		}
		/// end new code
		// checkMergeClash(from, to);
		ConceptNDepSet cnd = to.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(ce))
				.iterator().next();
		DependencySet newDS = DependencySet.create();
		System.out.println("merging " + from.getId() + " to " + to.getId());
		//to.getnLabel().getCndList().getCdSet().stream().forEach(cnds -> System.out.println(cnds.getCe()+" "+cnds.getDs().getbpList()));
		/////

		if (!depSet.isEmpty()) {
			newDS.add(DependencySet.create(depSet));
		}
		if (!cnd.getDs().isEmpty()) {
			newDS.add(DependencySet.create(cnd.getDs()));
		}
		newDS = DependencySet.plus(DependencySet.create(newDS), DependencySet.create(getCurLevel()));
		BranchHandler bh = new BranchHandler(newDS, to, from, to);
		this.branches.put(getCurLevel(), bh);
		save(to);
		// cg.saveN(to);
		incCurLevel();
		/*
		 * if(!depSet.isEmpty()) { newDS = DependencySet.create(depSet);
		 * for(OWLClassExpression c : from.getLabel()) { plusConceptDepSet(from, depSet,
		 * c); } } else if(depSet.isEmpty() && !cnd.getDs().isEmpty()) { newDS =
		 * DependencySet.create(cnd.getDs()); for(OWLClassExpression c :
		 * from.getLabel()) { plusConceptDepSet(from, cnd.getDs(), c); } }
		 */
		if (!mergeLabels(from, to, newDS)) {
			//to.getnLabel().getCndList().getCdSet().stream().forEach(cnds -> System.out.println(cnds.getCe()+" "+cnds.getDs().getbpList()));		
			return null;
		}
		/*
		 * cg.setCurrNode(from); cg.save(); incCurLevel();
		 */
		cg.merge(from, to, depSet);
		processForAll(to);
		if (!processAtMost(to))
			return null;
		// System.out.println("after merge "+to.getOutgoingEdges().size());
		return to;
	}

	/*
	 * private Node mergeNodes2(Node from, Node to, OWLClassExpression ce,
	 * DependencySet depSet) { //checkMergeClash(from, to); ConceptNDepSet cnd =
	 * from.getnLabel().getCndList().getCdSet().stream().filter(cnds ->
	 * cnds.getCe().equals(ce)).iterator().next(); DependencySet newDS = null;
	 * if(!depSet.isEmpty()) { newDS = DependencySet.create(depSet);
	 * for(OWLClassExpression c : from.getLabel()) { plusConceptDepSet(from, depSet,
	 * c); } } else if(depSet.isEmpty() && !cnd.getDs().isEmpty()) { newDS =
	 * DependencySet.create(cnd.getDs()); for(OWLClassExpression c :
	 * from.getLabel()) { plusConceptDepSet(from, cnd.getDs(), c); } }
	 * mergeLabels(from, to, newDS); cg.setCurrNode(from); cg.save(); incCurLevel();
	 * cg.merge(from, to, depSet); return to; }
	 */
	private Node mergeNodes(Node from, Node to, DependencySet depSet) {
		/// newcode 14 jul 2k19

		if (from.getDisjointNodes().contains(to)) {
			if (!depSet.isEmpty()) {
				if (!clashHandler(depSet, to))
					isInconsistent(to);
			} else
				isInconsistent(to);
			return null;
		}
		/// end new code

		// checkMergeClash(from, to);
		/*
		 * if(!depSet.isEmpty()) { for(OWLClassExpression c : from.getLabel()) {
		 * plusConceptDepSet(from, depSet, c); } for(OWLClassExpression c :
		 * to.getLabel()) { plusConceptDepSet(to, depSet, c); } }
		 */
		// System.out.println("before merge "+to.getOutgoingEdges().size());
		System.out.println("merging2 " + from.getId() + " to " + to.getId());
		if (!from.equals(to)) {
			DependencySet newDS = DependencySet.plus(DependencySet.create(depSet), DependencySet.create(getCurLevel()));
			BranchHandler bh = new BranchHandler(newDS, to, from, to);
			this.branches.put(getCurLevel(), bh);
			save(to);
			// cg.saveN(to);
			incCurLevel();
			if (!mergeLabels(from, to, depSet))
				return null;
			cg.merge(from, to, depSet);
		}
		processForAll(to);
		processAtMost(to);
		// System.out.println("after merge "+to.getOutgoingEdges().size());

		return to;
	}

	private boolean mergeLabels(Node from, Node to, DependencySet depSet) {
		// System.out.println("Merging labels! " + from.getId() + " into "+to.getId());
		Map<OWLClassExpression, ConceptNDepSet> todoEntries = new HashMap<>();
		Set<OWLClassExpression> label = from.getLabel();
		if (depSet != null && !depSet.isEmpty()) {
			for (OWLClassExpression c : label) {
				ConceptNDepSet cnd = from.getnLabel().getCndList().getCdSet().stream()
						.filter(cnds -> cnds.getCe().equals(c)).iterator().next();
				ConceptNDepSet newCnd = new ConceptNDepSet(c,
						DependencySet.plus(DependencySet.create(depSet), DependencySet.create(cnd.getDs())));

				// ConceptNDepSet cnd =
				// from.getnLabel().getCndList().getCdSet().stream().filter(cnds ->
				// cnds.getCe().equals(c)).iterator().next();
				// System.out.println("before merge "+ cnd.getCe() +" ds "+
				// cnd.getDs().getbpList());
				if (isConceptExist(to, c)) {

					updateConceptDepSetMerge(to, newCnd.getDs(), c);
					if (!(c instanceof OWLClass) || !(c instanceof OWLObjectOneOf)
							|| !(c instanceof OWLObjectComplementOf))
						updateToDoEntryDepSet(to, c, newCnd.getDs());
					// System.out.println(" after addlabel "+ newCnd.getCe() +" ds "+
					// newCnd.getDs().getbpList());

				} else {
					this.cg.addConceptToNode(to, newCnd);

					if (!checkClash(to, c)) {
						if (c instanceof OWLClass || c instanceof OWLObjectOneOf
								|| c instanceof OWLObjectComplementOf) {
							to.addSimpleLabel(c);
						} else {
							todoEntries.put(c, newCnd);
							// addToDoEntry(to, c, cnd);
							/*
							 * if(isToDoEntryDepSet(from, c, newCnd.getDs())) {
							 * //System.err.println("find entry "+ c); addToDoEntry(to, c, newCnd); }
							 */

						}
					} else {
						// System.out.println("clash check "+ c);
						DependencySet clashSet = getClashSet(to, c, c.getComplementNNF());
						// System.out.println("clash set "+ clashSet.getbpList());
						if (!clashSet.isEmpty()) {
							clashSet.setCe(c);
							clashSet.setCeNNF(c.getComplementNNF());
							if (!clashHandler(clashSet, to))
								isInconsistent(to);
						} else
							isInconsistent(to);
						return false;
					}
				}
			}
		} else {

			for (OWLClassExpression c : label) {
				ConceptNDepSet cnd = from.getnLabel().getCndList().getCdSet().stream()
						.filter(cnds -> cnds.getCe().equals(c)).iterator().next();

				// System.out.println("before merge "+ cnd.getCe() +" ds "+
				// cnd.getDs().getbpList());
				if (isConceptExist(to, c)) {
					updateConceptDepSetMerge(to, cnd.getDs(), c);
					if (!(c instanceof OWLClass) || !(c instanceof OWLObjectOneOf)
							|| !(c instanceof OWLObjectComplementOf))
						updateToDoEntryDepSet(to, c, cnd.getDs());
				} else {
					this.cg.addConceptToNode(to, cnd);
					if (!checkClash(to, c)) {
						if ((c instanceof OWLClass) || !(c instanceof OWLObjectOneOf)
								|| !(c instanceof OWLObjectComplementOf)) {
							to.addSimpleLabel(c);
						} else {
							todoEntries.put(c, cnd);
							// //addToDoEntry(to, c, cnd);
							/*
							 * if(isToDoEntryDepSet(from, c, cnd.getDs())) { addToDoEntry(to, c, cnd); }
							 */
						}
					} else {
						DependencySet clashSet = getClashSet(to, c, c.getComplementNNF());
						if (!clashSet.isEmpty()) {
							clashSet.setCe(c);
							clashSet.setCeNNF(c.getComplementNNF());
							if (!clashHandler(clashSet, to))
								isInconsistent(to);
						} else
							isInconsistent(to);
						return false;
					}
				}

			}
		}
		for (OWLClassExpression ce : todoEntries.keySet()) {
			// System.err.println("find entry "+ c);
			if (isToDoEntryDepSet(from, ce, todoEntries.get(ce).getDs())) {
				// System.err.println("entry found"+ ce);
				addToDoEntry(to, ce, todoEntries.get(ce));
			}
		}
		// to.getnLabel().getCndList().getCdSet().stream().forEach(cnds ->
		// System.out.println("after merging ce "+cnds.getCe() +" ds "
		// +cnds.getDs().getbpList()));
		return true;
	}

	/*
	 * private boolean checkMergeClash(Node from, Node to) { for(OWLClassExpression
	 * ce : from.getLabel()) { if(checkClash(to, ce)) return true; } return false; }
	 */

	private void isInconsistent(Node n) {
		// if(n.isNominalNode()) {
		System.err.println("Your ontology is inconsistent");
		TestReasoner.getExecutionTime();
		System.exit(0);
		// }

	}

	private boolean clashHandler(DependencySet clashSet, Node node) {
		LOG.info("Clash handler...");
		System.out.println("Clash handler..." + node.getId());

		if (!clashSet.isEmpty()) {
			int level = clashSet.getMax();
			System.out.println("level" + level);
			// System.out.println(cg.getTotalNodes());
			// System.err.println(branches.get(level).getDs().getbpList());
			// System.err.println(clashSet.getbpList());

			//// added 25-oct-2019
			if (branches.get(level) != null) {

				if (branches.get(level).ILPBranching) {
					Set<OWLSubClassOfAxiom> subAx = new HashSet<>();
					Node n = branches.get(level).getNode();
					System.err.println("ILPBranching n: " + n.getId() + " node: " + node.getId());
					if (!n.equals(node) && n.getId() < node.getId()) {
						Set<OWLClassExpression> relatedConcepts = branches.get(level).getRelatedConcepts(node);
						// System.err.println("relatedConcepts: "+ relatedConcepts.size() +"
						// node.getBackPropagatedLabel() "+ node.getBackPropagatedLabel());
						OWLClassExpression ce = clashSet.getCe();
						OWLClassExpression ceNNF = clashSet.getCeNNF();
						// System.err.println("ce "+ ce +" ceNNF "+ ceNNF);

						if (!node.getSimpleILPLabel().contains(ce) && node.getSimpleILPLabel().contains(ceNNF)) {
							for (OWLClassExpression bpl : node.getBackPropagatedLabel()) {
								if (bpl.equals(ce)) {
									for (OWLClassExpression rc : relatedConcepts) {
										subAx.add(df.getOWLSubClassOfAxiom(rc, bpl));
									}
								} else if (bpl instanceof OWLObjectIntersectionOf) {
									if (bpl.asConjunctSet().contains(ce)) {
										for (OWLClassExpression rc : relatedConcepts) {
											subAx.add(df.getOWLSubClassOfAxiom(rc, bpl));
										}
									}
								} else if (bpl instanceof OWLObjectUnionOf) {
									if (bpl.asDisjunctSet().contains(ce)) {
										for (OWLClassExpression rc : relatedConcepts) {
											subAx.add(df.getOWLSubClassOfAxiom(rc, bpl));
										}
									}
								}
							}
						} else if (!node.getSimpleILPLabel().contains(ceNNF) && node.getSimpleILPLabel().contains(ce)) {
							for (OWLClassExpression bpl : node.getBackPropagatedLabel()) {
								if (bpl.equals(ceNNF)) {
									for (OWLClassExpression rc : relatedConcepts) {
										subAx.add(df.getOWLSubClassOfAxiom(rc, bpl));
									}
								} else if (bpl instanceof OWLObjectIntersectionOf) {
									if (bpl.asConjunctSet().contains(ceNNF)) {
										for (OWLClassExpression rc : relatedConcepts) {
											subAx.add(df.getOWLSubClassOfAxiom(rc, bpl));
										}
									}
								} else if (bpl instanceof OWLObjectUnionOf) {
									if (bpl.asDisjunctSet().contains(ceNNF)) {
										for (OWLClassExpression rc : relatedConcepts) {
											subAx.add(df.getOWLSubClassOfAxiom(rc, bpl));
										}
									}
								}
							}
						}

						if (!subAx.isEmpty()) {
							// System.err.println("subAx "+ subAx);
							restore(level, true, false, false);
							// reset(n);
							subAx.addAll(branches.get(level).getSubsumption());
							// save(n);
							this.callILP(n, branches.get(level).getAllEntries(), subAx, null);

						} else {

							// branches.get(level).reset2();
							// branches.remove(level);
							restore(level, true, false, false);
							// System.out.println("clashSet before " + clashSet.getbpList());
							clashSet.removeLevel(level);
							// System.out.println("clashSet after " + clashSet.getbpList());
							if (!clashHandler(clashSet, n))
								return false;
						}

					} else {
						if (n.getId() > node.getId()) {
							restore(level, true, false, false);
							// reset(node);
							clashSet.removeLevel(level);
							if (!clashHandler(clashSet, node))
								return false;
						} else {
							// branches.get(level).reset2();
							// branches.remove(level);
							restore(level, true, false, false);
							clashSet.removeLevel(level);
							if (!clashHandler(clashSet, n)) {
								// System.out.println("ClashSet");
								return false;
							}
						}
					}
				}

				///
				else if (branches.get(level).mergeBranching) {
					System.err.println(
							"mergeBranching n: " + branches.get(level).mergeFrom.getId() + " node To: " + node.getId());
					// undoDepSet(node, branches.get(level).mergeFrom);
					// node.getnLabel().getCndList().getCdSet().stream().forEach(cnds ->
					// System.out.println(cnds.getCe()+" "+cnds.getDs().getbpList()));
					node = branches.get(level).originalTo;
					// node.getnLabel().getCndList().getCdSet().stream().forEach(cnds ->
					// System.out.println(cnds.getCe()+" "+cnds.getDs().getbpList()));

					cg.updateReset(branches.get(level).mergeFrom);

					restore(level, false, true, false);
					clashSet.removeLevel(level);
					if (!clashHandler(clashSet, cg.getCurrNode()))
						return false;
				}

				else {
					System.err.println("disjunction branching ");
					if (branches.get(level).hasNextOption()) {
						restore(level, false, false, true);
						DependencySet branchClashSet = branches.get(level).getClashSet();
						branches.get(level).setClashSet(DependencySet.plus(DependencySet.create(clashSet),
								DependencySet.create(branchClashSet)));
						// applyOr(cg.getCurrNode(), branches.get(level).getNextOption(),
						// DependencySet.plus(newDS, branches.get(level).getDs()));
						save(cg.getCurrNode());
						incCurLevel();
						// return applyOr(cg.getCurrNode(), branches.get(level).getNextOption(),
						// DependencySet.plus(newDS,
						// DependencySet.create(branches.get(level).getDs())));
						boolean result = applyOr(cg.getCurrNode(), branches.get(level).getNextOption(),
								DependencySet.create(branches.get(level).getDs()));
						// System.err.println("clash set "+ clashSet.getbpList());

						return result;

					} else {
						restore(level, false, false, true);
						Node n = branches.get(level).getNode();
						// this.addToDoEntry(n, branches.get(level).getObjUn(),
						// branches.get(level).getCnds());

						// branches.remove(level);
						branches.get(level).getClashSet().removeLevel(level);
						branches.get(level).reset();
						branches.remove(level);
						clashSet.removeLevel(level);
						// addOREntry(n, branches.get(level).objUn, branches.get(level).ds,
						// branches.get(level).cnds);
						if (!clashHandler(clashSet, n))
							return false;
					}
				}
			} else {
				clashSet.removeLevel(level);
				// System.out.println("clashSet after " + clashSet.getbpList());
				if (!clashHandler(clashSet, node))
					return false;

			}
		} else {
			return false;
		}
		return true;
	}
	
	/*private void undoDepSet(Node node, Node from) {
		Set<OWLClassExpression> label = from.getLabel();
		for (OWLClassExpression c : label) {
			ConceptNDepSet cnd = from.getnLabel().getCndList().getCdSet().stream()
					.filter(cnds -> cnds.getCe().equals(c)).iterator().next();
		}
		
	}*/

	/*private void addOREntry(Node n, OWLObjectUnionOf objUn, DependencySet ds, ConceptNDepSet cnds) {
		if(!todo.hasToDoEntry(n, NodeTag.OR, objUn, ds)) {
			System.err.println("adding " + cnds.getCe() +" node "+ n.getId());
			todo.addEntry(n, NodeTag.OR, cnds);
		}
		
	}*/

	/*
	 * public void copyGraph(Node n) {
	 * 
	 * cg.copyNodes(); try { cg.setCurrNode(n); copies.put(getCurLevel(),
	 * (CompletionGraph)cg.clone()); } catch (CloneNotSupportedException e) {
	 * e.printStackTrace(); }
	 * //System.out.println("saving currentBranchingPoint : "+getCurLevel()
	 * +" Node id: "+cg.getCurrNode().getId()+" total nodes : "+
	 * cg.getTotalNodes()); }
	 */
	public void restoreGraph(int level, boolean ilp, boolean merge, boolean disjunction) {
		cg.restore(level, ilp, merge, disjunction);
		// this.cg = copies.get(level);
		// cg.restoreNode(cg.getCurrNode());
		// System.out.println("Restoring level : "+level + "Node id
		// "+cg.getCurrNode().getId()+" total nodes : "+ cg.getTotalNodes());
	}

	public boolean checkClash(Node n, OWLClassExpression c) {
	//	 System.err.println("check clash "+c);
		// System.err.println(n.getId()+" label "+n.getLabel());
		if (c.isOWLNothing()) {
			// System.err.println("clash "+c +" "+ c.getComplementNNF());
			return true;
		}
		if (n.getLabel().contains(c.getComplementNNF())) {
			 System.err.println("clash "+c);
			return true;
		}
		// System.err.println("check clash here ");
		return false;
	}

	public Set<Set<OWLClassExpression>> checkDisjointGroups(Node n) {
		return ontology.getDisjointGroups(n.getLabel());
	}

	public Node findBlocker(Node n) {
		return cg.findBlocker(n);
	}

	public void processUnblockedNode(Node node) {
		// if (direct) {
		// not blocked -- clear blocked cache
		// re-apply all the generating rules
		// applyAllGeneratingRules(node);
		// } else {
		redoNodeLabel(node);
		// }
	}

	private void redoNodeLabel(Node node) {

		//node.getLabel().stream().forEach(l -> addToDoEntryAgain(node, l, node.getnLabel().getCndList().getCdSet()
		//		.stream().filter(cds -> cds.getCe().equals(l)).iterator().next()));

		for(OWLClassExpression ce : node.getLabel()) {
			ConceptNDepSet cnds = node.getnLabel().getCndList().getCdSet()
					.stream().filter(cds -> cds.getCe().equals(ce)).iterator().next();
			if(!todo.hasToDoEntry(node, ce))
				addToDoEntryAgain(node, ce, cnds);
		}
	}

	/*public DependencySet getClashSet(Node n, Set<Set<OWLClassExpression>> djGrp) {
		List<ConceptNDepSet> cndList = n.getnLabel().getCndList().getCdSet();
		List<ConceptNDepSet> cndSets = new ArrayList<ConceptNDepSet>();

		for (ConceptNDepSet cnds : cndList) {
			if (cnds != null) {
				OWLClassExpression ce = cnds.getCe();
				for (Set<OWLClassExpression> djg : djGrp) {
					if (djg.contains(ce) && !cnds.getDs().isEmpty()) {
						cndSets.add(cnds);
						break;
					}
				}
			}
		}
		DependencySet ds = DependencySet.create();
		for (ConceptNDepSet cnds : cndSets) {
			ds = DependencySet.plus(ds, DependencySet.create(cnds.getDs()));
		}
		return ds;
	}*/

	public DependencySet getClashSet2(Node n, Set<OWLClassExpression> djGrp) {
		List<ConceptNDepSet> cndList = n.getnLabel().getCndList().getCdSet();
		List<ConceptNDepSet> cndSets = new ArrayList<ConceptNDepSet>();

		for (ConceptNDepSet cnds : cndList) {
			if (cnds != null) {
				OWLClassExpression ce = cnds.getCe();
				if (djGrp.contains(ce) && !cnds.getDs().isEmpty())
					cndSets.add(cnds);
			}
		}
		DependencySet ds = DependencySet.create();
		for (ConceptNDepSet cnds : cndSets) {
			ds = DependencySet.plus(ds, DependencySet.create(cnds.getDs()));
		}
		return ds;
	}
	public DependencySet getClashSet(Node n, OWLClassExpression ce, OWLClassExpression ceNNF) {
		// System.err.println("clash set exp "+ ce );
		DependencySet clashSet;
		List<ConceptNDepSet> cndList = n.getnLabel().getCndList().getCdSet();
		ConceptNDepSet cnd1 = null;
		ConceptNDepSet cnd2 = null;
		for (ConceptNDepSet cnds : cndList) {
			if (cnds != null) {
				if (cnds.getCe().equals(ce)) {
					cnd1 = cnds;
				} else if (cnds.getCe().equals(ceNNF)) {
					cnd2 = cnds;
				}
			}
		}

		// ConceptNDepSet cnd1 =
		// n.getnLabel().getCndList().getCdSet().stream().filter(cds -> cds !=null &&
		// cds.getCe().equals(ce)).iterator().next();
		// ConceptNDepSet cnd2 =
		// n.getnLabel().getCndList().getCdSet().stream().filter(cds -> cds !=null &&
		// cds.getCe().equals(ceNNF)).iterator().next();
		// System.out.println("exp "+ cnd1.getCe() + " ds "+ cnd1.getDs().getMax());
		// System.out.println("exp "+ ceNNF + " ds "+ cnd2.getDs().getMax());

		if (cnd1 == null && cnd2 == null) {
			clashSet = DependencySet.create();
		} else if (ce.isOWLNothing() || ceNNF == null) {
			if (cnd1 == null || cnd1.getDs().isEmpty())
				clashSet = DependencySet.create();
			else
				clashSet = DependencySet.plus(DependencySet.create(cnd1.getDs()), DependencySet.create());
		} else {
			if (cnd1 == null) {
				if (cnd2 != null && !cnd2.getDs().isEmpty())
					clashSet = DependencySet.create(cnd2.getDs());
				else
					clashSet = DependencySet.create();
			} else if (cnd2 == null) {
				if (cnd1 != null && !cnd1.getDs().isEmpty())
					clashSet = DependencySet.create(cnd1.getDs());
				else
					clashSet = DependencySet.create();
			} else if (cnd1.getDs().isEmpty() && cnd2.getDs().isEmpty())
				clashSet = DependencySet.create();
			else {
				// System.err.println("return clash set
				// "+DependencySet.plus(DependencySet.create(cnd1.getDs()),
				// DependencySet.create(cnd2.getDs())).getbpList());
				clashSet = DependencySet.plus(DependencySet.create(cnd1.getDs()), DependencySet.create(cnd2.getDs()));
			}
		}
	//	System.out.println("clashSet: "+clashSet.getbpList());
		
		if(branches.get(clashSet.getMax()) != null) {
			clashSet.add(DependencySet.create(branches.get(clashSet.getMax()).getClashSet()));
			//System.out.println("clashSet Exists: "+branches.get(clashSet.getMax()).getClashSet().getbpList());
		}
	//	System.out.println("clashSet After: "+clashSet.getbpList());
		return clashSet;
	}


	/*public DependencySet getClashSet(Node n, OWLClassExpression ce, OWLClassExpression ceNNF) {
		// System.err.println("clash set exp "+ ce );
		//DependencySet clashSet;
		List<ConceptNDepSet> cndList = n.getnLabel().getCndList().getCdSet();
		ConceptNDepSet cnd1 = null;
		ConceptNDepSet cnd2 = null;
		for (ConceptNDepSet cnds : cndList) {
			if (cnds != null) {
				if (cnds.getCe().equals(ce)) {
					cnd1 = cnds;
				} else if (cnds.getCe().equals(ceNNF)) {
					cnd2 = cnds;
				}
			}
		}

		// ConceptNDepSet cnd1 =
		// n.getnLabel().getCndList().getCdSet().stream().filter(cds -> cds !=null &&
		// cds.getCe().equals(ce)).iterator().next();
		// ConceptNDepSet cnd2 =
		// n.getnLabel().getCndList().getCdSet().stream().filter(cds -> cds !=null &&
		// cds.getCe().equals(ceNNF)).iterator().next();
		// System.out.println("exp "+ cnd1.getCe() + " ds "+ cnd1.getDs().getMax());
		// System.out.println("exp "+ ceNNF + " ds "+ cnd2.getDs().getMax());

		if (cnd1 == null && cnd2 == null) {
			return DependencySet.create();
		} else if (ce.isOWLNothing() || ceNNF == null) {
			if (cnd1 == null || cnd1.getDs().isEmpty())
				return DependencySet.create();
			else
				return DependencySet.plus(DependencySet.create(cnd1.getDs()), DependencySet.create());
		} else {
			if (cnd1 == null) {
				if (cnd2 != null && !cnd2.getDs().isEmpty())
					return DependencySet.create(cnd2.getDs());
				else
					return DependencySet.create();
			} else if (cnd2 == null) {
				if (cnd1 != null && !cnd1.getDs().isEmpty())
					return DependencySet.create(cnd1.getDs());
				else
					return DependencySet.create();
			} else if (cnd1.getDs().isEmpty() && cnd2.getDs().isEmpty())
				return DependencySet.create();
			else {
				// System.err.println("return clash set
				// "+DependencySet.plus(DependencySet.create(cnd1.getDs()),
				// DependencySet.create(cnd2.getDs())).getbpList());
				return DependencySet.plus(DependencySet.create(cnd1.getDs()), DependencySet.create(cnd2.getDs()));
			}
		}

	}
*/
	public DependencySet getOtherOption(Node n, OWLClassExpression ce1, OWLClassExpression ce2) {
		DependencySet dsUnion = null;
		if (n.getConceptsDependencies().get(ce1).stream().filter(d -> d.isEmpty()).iterator().hasNext()
				&& n.getConceptsDependencies().get(ce2).stream().filter(d -> d.isEmpty()).iterator().hasNext()) {
			return null;
		} else if (n.getConceptsDependencies().get(ce1).stream().filter(d -> d.isEmpty()).iterator().hasNext()) {
			for (DependencySet ds : n.getConceptsDependencies().get(ce2)) {
				dsUnion = DependencySet.plus(dsUnion, ds);
			}

		} else if (n.getConceptsDependencies().get(ce2).stream().filter(d -> d.isEmpty()).iterator().hasNext()) {
			for (DependencySet ds : n.getConceptsDependencies().get(ce1)) {
				dsUnion = DependencySet.plus(dsUnion, ds);
			}
		} else {
			for (DependencySet ds : n.getConceptsDependencies().get(ce2)) {
				dsUnion = DependencySet.plus(dsUnion, ds);
			}
			for (DependencySet ds : n.getConceptsDependencies().get(ce1)) {
				dsUnion = DependencySet.plus(dsUnion, ds);
			}
		}

		return dsUnion;

	}

	public boolean absorbRule1(OWLClassExpression ce, Node n, DependencySet ds) {
	//	 System.out.println("applying absorbRule 1 : " + ce + " nid " + n.getId());
		// System.out.println("concept ds : "+ ds.getMax());
		Set<OWLClassExpression> sup = this.intl.findConcept(ce);
		for (OWLClassExpression c : sup) {
		//	 System.out.println(sup.size() + " absorb : " + c );
			if (c.isOWLNothing()) {
				DependencySet clashSet = getClashSet(n, ce, null);
				if (!clashSet.isEmpty()) {
					if (!clashHandler(clashSet, n))
						isInconsistent(n);
				} else {
					isInconsistent(n);
				}
				return false;
			}
			n = addConcept(n, c, ds, false);
			if (n == null || n.getId() == -1)
				return false;
		}
		return true;
	}

	public boolean absorbRule2(Node n) {
		Set<OWLSubClassOfAxiom> sbAx = this.intl.getTui();
		Set<OWLClassExpression> classes = n.getSimpleLabel();
		// Set<OWLClassExpression> classes = n.getLabel();
		for (OWLSubClassOfAxiom sb : sbAx) {
			DependencySet dep = DependencySet.create();
			boolean flag = true;
			for (OWLClassExpression cn : sb.getSubClass().asConjunctSet()) {
				if (!classes.contains(cn)) {
					flag = false;
					break;
				} else {
					n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(cn))
							.forEach(cnd -> dep.add(cnd.getDs()));
				}
			}
			if (flag) {
				OWLClassExpression c = sb.getSuperClass();
				// System.err.println(c);
				if (c.isOWLNothing()) {
					DependencySet clashSet = getClashSet2(n, sb.getSubClass().asConjunctSet());
					if (!clashSet.isEmpty()) {
						if (!clashHandler(clashSet, n))
							isInconsistent(n);
					} else
						isInconsistent(n);
					return false;
				}
				n = addConcept(n, c, dep, false);
				if (n == null || n.getId() == -1)
					return false;
			}
		}
		return true;
	}

	public boolean absorbRule3(OWLClassExpression ce, Node n, DependencySet ds) {
		// System.out.println("applying absorbRule 3 : " + ce + " nid " + n.getId());
		// System.out.println("concept ds : "+ ds.getMax());
		Set<OWLClassExpression> eq = this.intl.findConceptEq(ce.getComplementNNF());
		// eq.addAll(ontology.getAllComplementEq(ce.getComplementNNF()));
		for (OWLClassExpression ceEq : eq) {
			OWLClassExpression c = ceEq.getComplementNNF();
			// System.out.println(eq.size() + " absorb : " + c);
			if (c.isOWLNothing()) {
				DependencySet clashSet = getClashSet(n, ce, null);
				if (!clashSet.isEmpty()) {
					if (!clashHandler(clashSet, n))
						isInconsistent(n);
				} else {
					isInconsistent(n);
				}
				return false;
			}
			n = addConcept(n, c, ds, false);
			if (n == null || n.getId() == -1)
				return false;
		}
		return true;
	}

	private Node findNominalNode(OWLClassExpression ce) {
		return cg.findNominalNode(ce);
	}

	private boolean absorbNominal(OWLClassExpression ce, Node n, DependencySet ds) {
		// System.out.println("applying absorb Nominal : "+ ce +"node "+ n.getId());
		Set<OWLClassExpression> sup = this.intl.findIndividual(ce);
		// System.out.println("contains "+ sup.size());

		if (sup.size() != 0) {
			for (OWLClassExpression c : sup) {
				// System.out.println("super "+ c);
				n = addConcept(n, c, ds, false);
				if (n == null || n.getId() == -1)
					return false;
			}
		}
		return true;
	}

	/**
	 * Both Basic and Extended Role Absorption --- L(<x,y>) = {R} , exist_R.Top -> C
	 * --- L(<x,y>) = {R} , exist_R.D -> C ~~>> exist_R.Top -> (C or forAll_R.neg_D)
	 */
	private boolean absorbRoleRule(Set<OWLObjectPropertyExpression> roles, Node x, Node y, DependencySet ds) {

	//	System.err.println("absorbRoleRule "+ roles);
		Set<OWLClassExpression> domain = new HashSet<OWLClassExpression>();
		Set<OWLClassExpression> range = new HashSet<OWLClassExpression>();
		for (OWLObjectPropertyExpression r : roles) {
			domain.addAll(intl.getDomainRestriction(r));
			domain.addAll(intl.getExtendedDomainRestrictions(r));
			range.addAll(intl.getRangeRestriction(r));
		}
		for (OWLClassExpression ce : domain) {
			Node nn = addConcept(x, ce, ds, false);
			if (nn.getId() == -1)
				return false;
		}
		for (OWLClassExpression ce : range) {
		//	System.err.println("add range  "+ ce);
			Node nn = addConcept(y, ce, ds, false);
			if (nn.getId() == -1)
				return false;
		}
		return true;
	}

	/*
	 * // --- L(<x,y>) = {R} , exist_R.Top -> C private boolean
	 * absorbRoleBasicRule(Set<OWLObjectPropertyExpression> roles, Node x, Node y,
	 * DependencySet ds) { Set<OWLClassExpression> domain = new
	 * HashSet<OWLClassExpression>(); Set<OWLClassExpression> range = new
	 * HashSet<OWLClassExpression>(); for(OWLObjectPropertyExpression r : roles) {
	 * domain.addAll(intl.getDomainRestriction(r));
	 * domain.addAll(intl.getExtendedDomainRestrictions(r));
	 * range.addAll(intl.getRangeRestriction(r)); } for(OWLClassExpression ce :
	 * domain) { Node nn = addConcept(x, ce, ds); if( nn.getId() == -1) return
	 * false; } for(OWLClassExpression ce : range) { Node nn = addConcept(y, ce,
	 * ds); if( nn.getId() == -1) return false; } return true; } // --- L(<x,y>) =
	 * {R} , exist_R.D -> C ~~>> exist_R.Top -> (C or forAll_R.neg_D) private
	 * boolean absorbRoleExtendedRule(Set<OWLObjectPropertyExpression> roles, Node
	 * x, DependencySet ds) { Set<OWLClassExpression> domain = new
	 * HashSet<OWLClassExpression>(); for(OWLObjectPropertyExpression r : roles) {
	 * domain.addAll(intl.getExtendedDomainRestrictions(r)); }
	 * 
	 * for(OWLClassExpression ce : domain) { Node nn = addConcept(x, ce, ds); if(
	 * nn.getId() == -1) return false; } return true; }
	 */
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
		// n.getLabel().stream().forEach(lb -> System.out.println(lb));
		if (n.getLabel().contains(ce))
			return true;
		return false;
	}

	public void updateConceptDepSet(Node n, DependencySet ds, OWLClassExpression filler) {
		// System.out.println("node "+n.getId() +"filler "+ filler+" node label "+
		// n.getLabel());
		cg.saveN(n);
		List<ConceptNDepSet> cndList = n.getnLabel().getCndList().getCdSet();
		ConceptNDepSet cnd = null;
		for (ConceptNDepSet cnds : cndList) {
			if (cnds != null) {
				if (cnds.getCe().equals(filler)) {
					cnd = cnds;
				}
			}
		}
		// ConceptNDepSet cnd =
		// n.getnLabel().getCndList().getCdSet().stream().filter(cnds ->
		// cnds.getCe().equals(filler)).iterator().next();
		if (cnd.getDs().isEmpty() || ds.isEmpty()) {
			n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds != null && cnds.getCe().equals(filler))
					.forEach(cnds -> cnds.setDs(DependencySet.create()));
			if (!((filler instanceof OWLClass) || (filler instanceof OWLObjectOneOf)
					|| (filler instanceof OWLObjectComplementOf)))
				updateToDoEntryDepSet(n, filler);
			// cnd.setDs(DependencySet.create());
		}
		/*
		 * else { List<ConceptNDepSet> cndList1 = n.getnLabel().getCndList().getCdSet();
		 * for(ConceptNDepSet cnds : cndList1){ if(cnds != null && cnds.getCe() != null
		 * && cnds.getCe().equals(filler)) { //FIXME check if below line should be
		 * commented???
		 * cnds.setDs(DependencySet.plus(DependencySet.create(cnds.getDs()),
		 * DependencySet.create(ds))); } }
		 * //n.getnLabel().getCndList().getCdSet().stream().filter(cnds ->
		 * cnds.getCe().equals(filler)).forEach(cnds ->
		 * cnds.setDs(DependencySet.plus(DependencySet.create(cnds.getDs()),
		 * DependencySet.create(ds)))); //cnd.setDs(DependencySet.plus(cnd.getDs(),
		 * ds)); }
		 */

	}

	public void updateConceptDepSetMerge(Node n, DependencySet ds, OWLClassExpression filler) {
		// System.out.println("node "+n.getId() +"filler "+ filler+" node label "+
		// n.getLabel());
		cg.saveN(n);
		List<ConceptNDepSet> cndList = n.getnLabel().getCndList().getCdSet();
		ConceptNDepSet cnd = null;
		for (ConceptNDepSet cnds : cndList) {
			if (cnds != null) {
				if (cnds.getCe().equals(filler)) {
					cnd = cnds;
				}
			}
		}
		// ConceptNDepSet cnd =
		// n.getnLabel().getCndList().getCdSet().stream().filter(cnds ->
		// cnds.getCe().equals(filler)).iterator().next();
		if (cnd.getDs().isEmpty() || ds.isEmpty()) {
			n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds != null && cnds.getCe().equals(filler))
					.forEach(cnds -> cnds.setDs(DependencySet.create()));
			// cnd.setDs(DependencySet.create());
		} else {
			List<ConceptNDepSet> cndList1 = n.getnLabel().getCndList().getCdSet();
			for (ConceptNDepSet cnds : cndList1) {
				if (cnds != null && cnds.getCe() != null && cnds.getCe().equals(filler)) {
					// FIXME check if below line should be commented???
					cnds.setDs(DependencySet.plus(DependencySet.create(cnds.getDs()), DependencySet.create(ds)));
				}
			}
		}

	}

	public void plusConceptDepSet(Node n, DependencySet ds, OWLClassExpression filler) {
		n.getnLabel().getCndList().getCdSet().stream().filter(cnds -> cnds.getCe().equals(filler)).forEach(
				cnds -> cnds.setDs(DependencySet.plus(DependencySet.create(cnds.getDs()), DependencySet.create(ds))));
	}

	public DependencySet updateDepSetForAll(Edge e, DependencySet ds) {
		DependencySet depSet = DependencySet.create(ds);
		if (!e.getDepSet().isEmpty())
			depSet = DependencySet.plus(depSet, DependencySet.create(e.getDepSet()));
		return depSet;
	}

	public void updateEdgeDepSet(DependencySet ds, Edge e) {
		if (e == null)
			return;
		if (e.getDepSet() == null || ds == null)
			e.setDepSet(DependencySet.create());
		else if (e.getDepSet().isEmpty() || ds.isEmpty())
			e.setDepSet(DependencySet.create());
		else
			e.setDepSet(DependencySet.plus(e.getDepSet(), DependencySet.create(ds)));
	}

	private void updateToDoEntryDepSet(Node n, OWLClassExpression c) {
		if (c instanceof OWLObjectIntersectionOf)
			todo.updateToDoEntry(n, NodeTag.AND, c);
		else if (c instanceof OWLObjectUnionOf)
			todo.updateToDoEntry(n, NodeTag.OR, c);
		else if (c instanceof OWLObjectSomeValuesFrom || c instanceof OWLObjectHasValue)
			todo.updateToDoEntry(n, NodeTag.EXISTS, c);
		else if (c instanceof OWLObjectAllValuesFrom)
			todo.updateToDoEntry(n, NodeTag.FORALL, c);
		else if (c instanceof OWLObjectMinCardinality)
			todo.updateToDoEntry(n, NodeTag.LE, c);
		else if (c instanceof OWLObjectMaxCardinality)
			todo.updateToDoEntry(n, NodeTag.GE, c);
	}

	private void updateToDoEntryDepSet(Node n, OWLClassExpression c, DependencySet ds) {
		if (c instanceof OWLObjectIntersectionOf)
			todo.updateToDoEntry(n, NodeTag.AND, c, ds);
		else if (c instanceof OWLObjectUnionOf)
			todo.updateToDoEntry(n, NodeTag.OR, c, ds);
		else if (c instanceof OWLObjectSomeValuesFrom || c instanceof OWLObjectHasValue)
			todo.updateToDoEntry(n, NodeTag.EXISTS, c, ds);
		else if (c instanceof OWLObjectAllValuesFrom)
			todo.updateToDoEntry(n, NodeTag.FORALL, c, ds);
		else if (c instanceof OWLObjectMinCardinality)
			todo.updateToDoEntry(n, NodeTag.LE, c, ds);
		else if (c instanceof OWLObjectMaxCardinality)
			todo.updateToDoEntry(n, NodeTag.GE, c, ds);
	}

	private boolean isToDoEntryDepSet(Node n, OWLClassExpression c, DependencySet ds) {
		if (c instanceof OWLObjectIntersectionOf)
			return todo.hasToDoEntry(n, NodeTag.AND, c, ds);
		else if (c instanceof OWLObjectUnionOf)
			return todo.hasToDoEntry(n, NodeTag.OR, c, ds);
		else if (c instanceof OWLObjectSomeValuesFrom || c instanceof OWLObjectHasValue)
			return todo.hasToDoEntry(n, NodeTag.EXISTS, c, ds);
		else if (c instanceof OWLObjectAllValuesFrom)
			return todo.hasToDoEntry(n, NodeTag.FORALL, c, ds);
		else if (c instanceof OWLObjectMinCardinality)
			return todo.hasToDoEntry(n, NodeTag.LE, c, ds);
		else if (c instanceof OWLObjectMaxCardinality)
			return todo.hasToDoEntry(n, NodeTag.GE, c, ds);
		return false;
	}

	public void addToDoEntry(Node n, OWLClassExpression c, ConceptNDepSet cnds) {
		// System.err.println("add entry n "+ n.getId() +" "+ c);
		if (c instanceof OWLObjectIntersectionOf)
			todo.addEntry(n, NodeTag.AND, cnds);
		else if (c instanceof OWLObjectMinCardinality)
			todo.addEntry(n, NodeTag.LE, cnds);
		else if (c instanceof OWLObjectMaxCardinality)
			todo.addEntry(n, NodeTag.GE, cnds);
		else if (c instanceof OWLObjectUnionOf)
			todo.addEntry(n, NodeTag.OR, cnds);
		else if (c instanceof OWLObjectSomeValuesFrom || c instanceof OWLObjectHasValue)
			todo.addEntry(n, NodeTag.EXISTS, cnds);
		else if (c instanceof OWLObjectAllValuesFrom) {
			todo.addEntry(n, NodeTag.FORALL, cnds);
		}
	}

	public void addToDoEntryAgain(Node n, OWLClassExpression c, ConceptNDepSet cnds) {
		// System.err.println("add entry again n "+ n.getId() +" "+ c);
		if (c instanceof OWLObjectMinCardinality)
			todo.addEntry(n, NodeTag.LE, cnds);
		else if (c instanceof OWLObjectMaxCardinality)
			todo.addEntry(n, NodeTag.GE, cnds);
		else if (c instanceof OWLObjectSomeValuesFrom || c instanceof OWLObjectHasValue)
			todo.addEntry(n, NodeTag.EXISTS, cnds);
		else if (c instanceof OWLObjectAllValuesFrom) {
			todo.addEntry(n, NodeTag.FORALL, cnds);
		}
	}

	protected void save(Node n) {
		cg.setCurrNode(n);
		cg.save();
		todo.save(getCurLevel());
		if (aboxReasoning) {
			ar.save(getCurLevel());
		}
	}

	protected void restore(int level, boolean ilp, boolean merge, boolean disjunction) {
		// restoreBranchHandlers(getCurLevel(), level);
		setCurLevel(level);
		currRestore = level;
		restoreGraph(level, ilp, merge, disjunction);
		todo.restore(level);
	}

	public void checkAboxConsistency(Set<OWLSubClassOfAxiom> aboxClassAss, OWLClassExpression tgAxiom, boolean b) {
		this.tgAxiom = tgAxiom;
		for (OWLSubClassOfAxiom asb : aboxClassAss) {
			if (!b && asb.getSuperClass().isOWLThing()) {
				continue;
			}
			createAboxNode(asb, tgAxiom);
			processToDoList();
		}
	}

	public void checkAboxConsistency2(Set<OWLSubClassOfAxiom> aboxClassAss, OWLClassExpression tgAxiom) {
		ar.removeProcessed(aboxClassAss);
		for (OWLSubClassOfAxiom asb : aboxClassAss) {
			ar.addProcessed(asb);
			createAboxNode(asb, tgAxiom);
			processToDoList();
			/*
			 * while(!todo.isEmpty()) { // System.out.println("while loop "+
			 * todo.entries()); ToDoEntry entry = todo.getNextEntry(); if(entry!=null)
			 * this.applyRules(entry); }
			 */
		}
	}

	private void createAboxNode(OWLSubClassOfAxiom asb, OWLClassExpression tgAxiom) {
		OWLClassExpression sb = asb.getSubClass();
		// OWLClassExpression sp = asb.getSuperClass();
		DependencySet ds = DependencySet.create();
		OWLClassExpression ci = df.getOWLObjectOneOf(((OWLObjectOneOf) sb).individuals().iterator().next());
	//	System.err.println("nominal " + ci);
		Node nom = findNominalNode(ci);

		if (nom == null) {
			Node n = cg.addNode(NodeType.NOMINAL, ds);
			addConcept(n, ci, ds, false);
			
			addTGAxiom(n, ds);
			// System.err.println("nominal "+ ci + " node id "+ n.getId());
			/*if (!this.absorbRule1(df.getOWLThing(), n, ds))
				return;
			addTGAxiom(n, ds);
			ConceptNDepSet cnds = new ConceptNDepSet(ci, ds);
			cg.addConceptToNode(n, cnds);
			if (!addApplicableGCIs(n, ci, ds))
				return;
			if (!absorbNominal(ci, n, ds))
				return;*/
		} else {
			// System.out.println("nominal "+ ci + nom.getId());
			updateConceptDepSet(nom, ds, ci);
		}

	}

	public boolean indLeft(Set<OWLSubClassOfAxiom> set) {

		for (OWLSubClassOfAxiom asb : set) {
			OWLClassExpression sb = asb.getSubClass();
			OWLClassExpression ci = df.getOWLObjectOneOf(((OWLObjectOneOf) sb).individuals().iterator().next());

			Node nom = findNominalNode(ci);
			if (nom == null) {
			//	System.out.println("nominal " + ci);
				return true;
			}
		}
		return false;
	}

	/*
	 * process forall check if it has nominal
	 * 
	 */
	public boolean hasUnprocessedEntries(Node p) {
		if (this.todo.hasUnprocessedEntries(p))
			return true;
		return false;
	}

	class BranchHandler {
		private List<OWLClassExpression> applicableOrEntries = new ArrayList<>();
		private List<OWLClassExpression> djTaken = new ArrayList<>();
		private int size;
		private int branchIndex;
		private OWLObjectUnionOf objUn;
		private DependencySet ds;
		private DependencySet clashSet;
		private Node n;
		private Node mergeFrom;
		private Node mergeTo;
		private Node originalTo;
		private ConceptNDepSet cnds;
		private Set<ToDoEntry> entries;
		private boolean ILPBranching = false;
		private boolean mergeBranching = false;
		Set<Edge> outgoingEdges = new HashSet<>();
		Set<OWLSubClassOfAxiom> subsumption = new HashSet<>();

		protected BranchHandler(OWLObjectUnionOf objUn, ConceptNDepSet cnds, DependencySet ds, Node n) {
			objUn.asDisjunctSet().stream().forEach(ce -> applicableOrEntries.add(ce));
			this.size = applicableOrEntries.size();
			this.branchIndex = 0;
			this.objUn = objUn;
			this.ds = DependencySet.create(ds);
			this.clashSet = DependencySet.create();
			this.n = n;
			this.cnds = cnds;
		}

		public DependencySet getClashSet() {
			return clashSet;
		}

		public void setClashSet(DependencySet clashSet) {
			this.clashSet = clashSet;
		}

		public Set<OWLSubClassOfAxiom> getSubsumption() {
			return this.subsumption;
		}

		protected BranchHandler(Set<ToDoEntry> entries, DependencySet ds, Node n, Set<Edge> outgoingEdges,
				Set<OWLSubClassOfAxiom> subsumption) {
			this.entries = entries;
			this.ds = DependencySet.create(ds);
			this.n = n;
			this.ILPBranching = true;
			this.outgoingEdges = outgoingEdges;
			this.subsumption.addAll(subsumption);
		}

		protected BranchHandler(DependencySet ds, Node n, Node mergeFrom, Node mergeTo) {
			this.ds = DependencySet.create(ds);
			this.n = n;
			this.mergeFrom = mergeFrom;
			this.mergeTo = mergeTo;
		//	System.out.println("BranchHandler mergeTo"+ mergeTo.getId());
		//	mergeTo.getnLabel().getCndList().getCdSet().stream().forEach(cnds -> System.out.println(cnds.getCe()+" "+cnds.getDs().getbpList()));		
			
			this.originalTo = new Node(mergeTo);
			this.mergeBranching = true;
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
			for (int i = branchIndex; i < this.size; i++)
				ce.add(applicableOrEntries.get(i));
			ce.removeAll(this.djTaken);
			return ce;
		}

		protected OWLClassExpression getNextOption() {
			if (this.size >= branchIndex + 1) {
				OWLClassExpression ce = applicableOrEntries.get(branchIndex);
				if (this.djTaken.contains(ce)) {
					++branchIndex;
					getNextOption();
				}
				// applicableOrEntries.remove(ce);
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

		public boolean isILPBranching() {
			return this.ILPBranching;
		}

		public Set<ToDoEntry> getAllEntries() {
			return this.entries;
		}

		public Set<OWLClassExpression> getRelatedConcepts(Node node) {
			Set<OWLClassExpression> relatedConcepts = new HashSet<>();
			for (ToDoEntry entry : this.entries) {
				if (entry.getType().equals(NodeTag.LE)) {
					OWLObjectMinCardinality minCard = (OWLObjectMinCardinality) entry.getClassExpression();
					OWLClassExpression filler = minCard.getFiller();
					if (filler instanceof OWLClass || filler instanceof OWLObjectOneOf
							|| filler instanceof OWLObjectComplementOf) {
						if (node.getSimpleILPLabel().contains(filler))
							relatedConcepts.add(filler);
					} else if (filler instanceof OWLObjectUnionOf) {
						for (OWLClassExpression ce : filler.asDisjunctSet()) {
							if (node.getSimpleILPLabel().contains(ce))
								relatedConcepts.add(ce);
						}
					} else if (filler instanceof OWLObjectIntersectionOf) {
						for (OWLClassExpression ce : filler.asConjunctSet()) {
							if (node.getSimpleILPLabel().contains(ce))
								relatedConcepts.add(ce);
						}
					}
				}
				if (entry.getType().equals(NodeTag.EXISTS)) {
				//	System.out.println("entry.getClassExpression() " + entry.getClassExpression());
					if (entry.getClassExpression() instanceof OWLObjectHasValue) {
						OWLObjectHasValue someValue = (OWLObjectHasValue) entry.getClassExpression();
						OWLClassExpression filler = df.getOWLObjectOneOf(someValue.getFiller());
						if (node.getSimpleILPLabel().contains(filler))
							relatedConcepts.add(filler);
					} else {
						OWLObjectSomeValuesFrom someValue = (OWLObjectSomeValuesFrom) entry.getClassExpression();
						OWLClassExpression filler = someValue.getFiller();

						if (filler instanceof OWLClass || filler instanceof OWLObjectOneOf
								|| filler instanceof OWLObjectComplementOf) {
							if (node.getSimpleILPLabel().contains(filler))
								relatedConcepts.add(filler);
						} else if (filler instanceof OWLObjectUnionOf) {
							for (OWLClassExpression ce : filler.asDisjunctSet()) {
								if (node.getSimpleILPLabel().contains(ce))
									relatedConcepts.add(ce);
							}
						} else if (filler instanceof OWLObjectIntersectionOf) {
							for (OWLClassExpression ce : filler.asConjunctSet()) {
								if (node.getSimpleILPLabel().contains(ce))
									relatedConcepts.add(ce);
							}
						}
					}
				}
			}
			return relatedConcepts;
		}
	}

	/////////////////////////////////////////////////////////////////////////////////////////////////////////////

	/*
	 * private boolean applyAbsorption(Node to, Set<OWLClassExpression> fillers,
	 * DependencySet ds) { for(OWLClassExpression ce : fillers) { //
	 * System.out.println("node "+to.getId()+" filler "+ce); if(ce instanceof
	 * OWLObjectOneOf) { if(!absorbNominal(ce, to, ds)) return false; } else if(ce
	 * instanceof OWLClass) { if(!absorbRule1b(ce, to, ds)) return false;
	 * if(!absorbRule2(to)) return false; }else if (ce instanceof
	 * OWLObjectComplementOf) { if (!absorbRule3(ce, to, ds)) return false; } }
	 * return true; }
	 */

	/*
	 * private void applyAllGeneratingRules(Node node) {
	 * node.getLabel().stream().filter(l -> l instanceof
	 * OWLObjectSomeValuesFrom).forEach(l -> addToDoEntry(node, l,
	 * node.getnLabel().getCndList().getCdSet().stream().filter(cds ->
	 * cds.getCe().equals(l)).iterator().next()));
	 * 
	 * }
	 * 
	 * private AddConceptResult tryAddConcept(Node n, OWLClassExpression ce) {
	 * 
	 * boolean canC = isConceptExist(n, ce); boolean canNegC = isConceptExist(n,
	 * ce.getComplementNNF());
	 * 
	 * if (canC) return AddConceptResult.EXIST; else if (canNegC) return
	 * AddConceptResult.CLASH; else return AddConceptResult.DONE;
	 * 
	 * }
	 */
	/*
	 * private boolean needNomReset(Node n) { if(n.getLabel().stream().anyMatch(ce
	 * -> ce instanceof OWLObjectMaxCardinality)) { for(OWLObjectMaxCardinality
	 * mxCard : n.getLabel().stream().filter(ce -> ce instanceof
	 * OWLObjectMaxCardinality).map(ce ->
	 * (OWLObjectMaxCardinality)ce).collect(Collectors.toSet())) {
	 * OWLObjectPropertyExpression role = mxCard.getProperty(); OWLClassExpression
	 * filler = mxCard.getFiller(); int card = mxCard.getCardinality();
	 * if(n.getOutgoingEdges().stream().anyMatch(e-> !e.isReset() &&
	 * e.getLabel().contains(role) && !e.getToNode().isReset() &&
	 * e.getToNode().getLabel().contains(filler) && (e.getToNode().getCardinality()
	 * > card))) { return true; } } } return false; }
	 */

	/*
	 * private void plusToDoEntryDepSet(Node n, OWLClassExpression c, DependencySet
	 * ds) {
	 * 
	 * if(c instanceof OWLObjectIntersectionOf) todo.plusToDoEntry(n, NodeTag.AND,
	 * c, ds); else if(c instanceof OWLObjectUnionOf) todo.plusToDoEntry(n,
	 * NodeTag.OR, c, ds); else if(c instanceof OWLObjectSomeValuesFrom || c
	 * instanceof OWLObjectHasValue) todo.plusToDoEntry(n, NodeTag.EXISTS, c, ds);
	 * else if(c instanceof OWLObjectAllValuesFrom) todo.plusToDoEntry(n,
	 * NodeTag.FORALL, c, ds); else if(c instanceof OWLObjectMinCardinality)
	 * todo.plusToDoEntry(n, NodeTag.LE, c, ds); else if(c instanceof
	 * OWLObjectMaxCardinality) todo.plusToDoEntry(n, NodeTag.GE, c, ds);
	 * 
	 * 
	 * }
	 */
	/*
	 * public void updateDepSet(Node n, DependencySet ds, OWLClassExpression filler,
	 * Edge e) { ConceptNDepSet cnd =
	 * n.getnLabel().getCndList().getCdSet().stream().filter(cnds ->
	 * cnds.getCe().equals(filler)).iterator().next(); if(cnd.getDs().isEmpty() ||
	 * ds.isEmpty()) { n.getnLabel().getCndList().getCdSet().stream().filter(cnds ->
	 * cnds.getCe().equals(filler)).forEach(cnds ->
	 * cnds.setDs(DependencySet.create())); //cnd.setDs(DependencySet.create()); }
	 * else { n.getnLabel().getCndList().getCdSet().stream().filter(cnds ->
	 * cnds.getCe().equals(filler)).forEach(cnds ->
	 * cnds.setDs(DependencySet.plus(cnds.getDs(), ds)));
	 * //cnd.setDs(DependencySet.plus(cnd.getDs(), ds)); }
	 * if(e.getDepSet().isEmpty() || ds.isEmpty())
	 * e.setDepSet(DependencySet.create()); else
	 * e.setDepSet(DependencySet.plus(e.getDepSet(), ds)); updateToDoEntryDepSet(n,
	 * filler, ds); }
	 */

	/*
	 * protected void restore(int level) { // restoreBranchHandlers(getCurLevel(),
	 * level); // setCurLevel(level); currRestore = level; restoreGraph(level);
	 * todo.restore(level); }
	 */

	/*
	 * private void restoreBranchHandlers(int curLevel, int level) { if(level <
	 * curLevel) { for(int i = curLevel; i > level; i--) branches.remove(i); } }
	 */

	/*
	 * public void checkAboxConsistency(Set<OWLSubClassOfAxiom> aboxClassAss,
	 * OWLClassExpression tgAxiom) { this.tgAxiom = tgAxiom; aboxReasoning = true;
	 * ar = new AboxReasoner(aboxClassAss); for(OWLSubClassOfAxiom asb :
	 * aboxClassAss) { ar.addProcessed(asb); createAboxNode(asb,tgAxiom);
	 * processToDoList(); /* while(!todo.isEmpty()) { //
	 * System.out.println("while loop "+ todo.entries()); ToDoEntry entry =
	 * todo.getNextEntry(); if(entry!=null) this.applyRules(entry); } }....*./
	 * if(currRestore != 0 && ar.needRestore(currRestore)){
	 * checkAboxConsistency2(ar.restore(currRestore), tgAxiom); currRestore = 0; } }
	 */

	/*
	 * private void checkOutgoingEdges2(Node n, Set<OWLObjectMaxCardinality>
	 * maxCardEntries) { outgoingEdges.clear(); for (OWLObjectMaxCardinality av :
	 * maxCardEntries) { OWLObjectPropertyExpression role = av.getProperty();
	 * OWLClassExpression ce = av.getFiller(); for (Edge e : n.getOutgoingEdges()) {
	 * // System.err.println("e "+ e.getLabel()
	 * +" label "+e.getToNode().getLabel());
	 * 
	 * // if(e.getLabel().contains(role) && e.getToNode().getLabel().contains(ce) &&
	 * // !e.isReset() && !e.getToNode().isReset()) if (e.getLabel().contains(role)
	 * && !e.isReset() && !e.getToNode().isReset()) outgoingEdges.add(e); } //
	 * return true; } }
	 */
	/*
	 * public boolean absorbRule1b(OWLClassExpression ce, Node n, DependencySet ds)
	 * { // System.out.println("applying absorbRule 1 : " + ce + " nid " +
	 * n.getId()); // System.out.println("concept ds : "+ ds.getMax());
	 * Set<OWLClassExpression> sup = this.intl.findConcept(ce); for
	 * (OWLClassExpression c : sup) { // System.out.println(sup.size() +
	 * " absorb : " + c); if (c.isOWLNothing()) { DependencySet clashSet =
	 * getClashSet(n, ce, null); if (!clashSet.isEmpty()) { if
	 * (!clashHandler(clashSet, n)) isInconsistent(n); } else { isInconsistent(n); }
	 * return false; }
	 * 
	 * if (isConceptExist(n, c)) { updateConceptDepSet(n, ds, c); if (!((c
	 * instanceof OWLClass) || (c instanceof OWLObjectOneOf) || (c instanceof
	 * OWLObjectComplementOf))) { ConceptNDepSet cnd =
	 * n.getnLabel().getCndList().getCdSet().stream() .filter(cnds -> cnds != null
	 * && cnds.getCe().equals(c)).iterator().next(); if (cnd != null)
	 * updateToDoEntryDepSet(n, c, cnd.getDs()); } continue; } else { ConceptNDepSet
	 * cnds = new ConceptNDepSet(c, ds); if (c instanceof OWLObjectOneOf) { if
	 * (processNominal(c, n, cnds, ds) == null) return false; } else if (c
	 * instanceof OWLObjectCardinalityRestriction) { if
	 * (needToAdd((OWLObjectCardinalityRestriction) c, n)) {
	 * this.cg.addConceptToNode(n, cnds); if (!checkClash(n, c)) { if (needReset(c,
	 * n)) { reset(n); addToDoEntries(n); } else addToDoEntry(n, c, cnds); } else {
	 * DependencySet clashSet = getClashSet(n, c, c.getComplementNNF()); if
	 * (!clashSet.isEmpty()) { clashSet.setCe(c);
	 * clashSet.setCeNNF(c.getComplementNNF()); if (!clashHandler(clashSet, n))
	 * isInconsistent(n); } else isInconsistent(n); return false; } } } else {
	 * cg.addConceptToNode(n, cnds); if (!checkClash(n, c)) { //
	 * System.err.println("no clash: "+ c+" label "+ n.getLabel()); //
	 * Set<Set<OWLClassExpression>> djGrp = checkDisjointGroups(n); //
	 * if(djGrp.isEmpty()) { if (c instanceof OWLClass) { n.addSimpleLabel(c); if
	 * (!absorbRule1(c, n, ds)) return false; if (!absorbRule2(n)) return false; }
	 * else if (c instanceof OWLObjectComplementOf) { if (!absorbRule3(c, n, ds))
	 * return false; }else { if(c instanceof OWLObjectUnionOf) { boolean exists =
	 * false; for(OWLClassExpression dj : c.asDisjunctSet()) { if(isConceptExist(n,
	 * dj)) { exists = true; break; } } if(exists) continue; } else if(c instanceof
	 * OWLObjectIntersectionOf &&
	 * ((OWLObjectIntersectionOf)c).conjunctSet().allMatch(cj -> cj instanceof
	 * OWLClass || cj instanceof OWLObjectOneOf || cj instanceof
	 * OWLObjectComplementOf)) { continue; } addToDoEntry(n, c, cnds); } // }
	 * 
	 * else { DependencySet clashSet = getClashSet(n, djGrp);
	 * if(!clashSet.isEmpty()) { if(!clashHandler(clashSet)) isInconsistent(n); }
	 * else isInconsistent(n); return; }
	 * 
	 * } else { DependencySet clashSet = getClashSet(n, c, c.getComplementNNF()); if
	 * (!clashSet.isEmpty()) { clashSet.setCe(c);
	 * clashSet.setCeNNF(c.getComplementNNF()); if (!clashHandler(clashSet, n))
	 * isInconsistent(n); } else isInconsistent(n); return false; } } } } return
	 * true; }
	 */

	/*
	 * private boolean checkIfResetRequired(Node node) { if
	 * (node.getLabel().stream().anyMatch(ce -> ce instanceof
	 * OWLObjectMinCardinality || ce instanceof OWLObjectMaxCardinality || ce
	 * instanceof OWLObjectSomeValuesFrom)) {
	 * 
	 * } return false; }
	 */
	/*
	 * private boolean checkAtLeastRestrictions(Node n) { //
	 * System.err.println("here"); if (n.getLabel().stream().anyMatch(ce -> ce
	 * instanceof OWLObjectMinCardinality)) { for (OWLObjectMinCardinality minCard :
	 * n.getLabel().stream() .filter(ce -> ce instanceof
	 * OWLObjectMinCardinality).map(ce -> (OWLObjectMinCardinality) ce)
	 * .collect(Collectors.toSet())) { int card = minCard.getCardinality(); int
	 * totalNodes = 0; OWLObjectPropertyExpression role = minCard.getProperty();
	 * OWLClassExpression filler = minCard.getFiller(); for (Edge edge :
	 * n.getOutgoingEdges().stream().filter(e -> !e.isReset() &&
	 * e.getLabel().contains(role)) .map(e -> (Edge) e).collect(Collectors.toSet()))
	 * { Node to = edge.getToNode(); if ((to.getLabel().contains(filler) || (filler
	 * instanceof OWLObjectIntersectionOf &&
	 * to.getLabel().containsAll(filler.asConjunctSet())) || (filler instanceof
	 * OWLObjectUnionOf &&
	 * to.getLabel().stream().anyMatch(filler.asDisjunctSet()::contains))) &&
	 * !to.isReset()) { if (edge.isPredEdge() && !edge.getToNode().isNominalNode())
	 * { totalNodes++; } else { totalNodes += edge.getToNode().getCardinality(); } }
	 * 
	 * } // System.err.println(""+ totalNodes); if (totalNodes < card) {
	 * DependencySet ds =
	 * DependencySet.create(n.getnLabel().getCndList().getCdSet().stream()
	 * .filter(ce -> ce.getCe().equals(minCard)).iterator().next().getDs()); if
	 * (!ds.isEmpty()) { ds.setCe(minCard); if (!clashHandler(ds, n))
	 * isInconsistent(n); } else isInconsistent(n); return false; } } } return true;
	 * }
	 */

	/*
	 * private void checkAtMostOLD(Node to) { if (to.isNominalNode()) {
	 * Set<OWLObjectMaxCardinality> mxCards = to.getLabel().stream() .filter(ce ->
	 * ce instanceof OWLObjectMaxCardinality).map(ce -> (OWLObjectMaxCardinality)
	 * ce) .collect(Collectors.toSet()); for (OWLObjectMaxCardinality mx : mxCards)
	 * { ConceptNDepSet cnd = to.getnLabel().getCndList().getCdSet().stream()
	 * .filter(cnds -> cnds.getCe().equals(mx)).iterator().next();
	 * OWLObjectPropertyExpression role = mx.getProperty(); OWLClassExpression
	 * filler = mx.getFiller(); if (to.getOutgoingEdges().stream() .anyMatch(e ->
	 * e.isPredEdge() && !e.isReset() && e.getLabel().contains(role) &&
	 * e.getToNode().getLabel().contains(filler) && e.getToNode().isBlockableNode()
	 * && !e.getToNode().isReset())) { List<Edge> outgoingEdges =
	 * to.getOutgoingEdges().stream() .filter(e -> e.getLabel().contains(role) &&
	 * e.isSuccEdge() && e.getToNode().getLabel().contains(filler) &&
	 * e.getToNode().isNINode()) .collect(Collectors.toList());
	 * 
	 * if ((outgoingEdges.size() == mx.getCardinality()) &&
	 * this.needToApplyAtMost(to, mx, cnd.getDs())) { this.atMostNomRule(to, mx); }
	 * else if (outgoingEdges.size() != mx.getCardinality()) { this.addToDoEntry(to,
	 * mx, cnd); Set<OWLObjectAllValuesFrom> forAll = to.getLabel().stream()
	 * .filter(ce -> ce instanceof OWLObjectAllValuesFrom) .map(ce ->
	 * (OWLObjectAllValuesFrom) ce).collect(Collectors.toSet()); for
	 * (OWLObjectAllValuesFrom fa : forAll) { ConceptNDepSet facnd =
	 * to.getnLabel().getCndList().getCdSet().stream() .filter(cnds ->
	 * cnds.getCe().equals(fa)).iterator().next(); if
	 * (fa.getProperty().equals(role)) this.addToDoEntry(to, fa, facnd); }
	 * 
	 * } } else if (to.getOutgoingEdges().stream() .anyMatch(e -> e.isPredEdge() &&
	 * !e.isReset() && e.getLabel().contains(role))) { this.addToDoEntry(to, mx,
	 * cnd); Set<OWLObjectAllValuesFrom> forAll = to.getLabel().stream() .filter(ce
	 * -> ce instanceof OWLObjectAllValuesFrom).map(ce -> (OWLObjectAllValuesFrom)
	 * ce) .collect(Collectors.toSet()); for (OWLObjectAllValuesFrom fa : forAll) {
	 * ConceptNDepSet facnd = to.getnLabel().getCndList().getCdSet().stream()
	 * .filter(cnds -> cnds.getCe().equals(fa)).iterator().next(); if
	 * (fa.getProperty().equals(role)) this.addToDoEntry(to, fa, facnd); } } } } }
	 * 
	 * 
	 * private boolean clashHandler(DependencySet clashSet, Node node) {
	 * LOG.info("Clash handler...");
	 * System.out.println("Clash handler..."+node.getId());
	 * 
	 * /* ///// if(!clashSet.isEmpty()) { for(int l= 0; l <
	 * clashSet.getbpList().size(); l++) { int level = clashSet.getMax();
	 * 
	 * System.out.println("level" + level);
	 * //System.out.println(cg.getTotalNodes());
	 * //System.out.println(branches.get(level)); if(
	 * branches.get(level).hasNextOption()) { restore(level);
	 * //save(cg.getCurrNode()); //
	 * System.out.println("restoring currentBranchingPoint : "+level
	 * +" Neighbour : "+cg.getCurrNode().getOutgoingEdges().size()+" total nodes : "
	 * + cg.getTotalNodes()); // System.out.println("branch node" +
	 * branches.get(level).getNode().getId()); //
	 * System.out.println("graph curr node" + cg.getCurrNode().getId()); //
	 * System.out.println("curr node label after" + cg.getCurrNode().getLabel());
	 * boolean flag = false; for(OWLClassExpression ce
	 * :branches.get(level).getAllNextOptions()) {
	 * if(isConceptExist(cg.getCurrNode(), ce)) { flag = true;
	 * branches.get(level).disjunctTaken(ce); updateConceptDepSet(cg.getCurrNode(),
	 * branches.get(level).getDs(), ce); if(!(ce instanceof OWLClass) || !(ce
	 * instanceof OWLObjectOneOf) || !(ce instanceof OWLObjectComplementOf))
	 * updateToDoEntryDepSet(cg.getCurrNode(), ce, branches.get(level).getDs());
	 * break;
	 * 
	 * } } if(!flag) applyOr(cg.getCurrNode(), branches.get(level).getNextOption(),
	 * branches.get(level).getDs()); //applyOr(branches.get(level).getNode(),
	 * branches.get(level).getNextOption(), branches.get(level).ds); } else {
	 * branches.get(level).reset(); //branches.remove(level);
	 * clashSet.removeLevel(level); if(!clashHandler(clashSet)) return false; } }
	 * 
	 * } else { return false; } //// if (!clashSet.isEmpty()) {
	 * 
	 * int level = clashSet.getMax();
	 * 
	 * System.out.println("level" + level); //
	 * System.out.println(cg.getTotalNodes());
	 * //System.err.println(branches.get(level).getDs().getbpList());
	 * System.err.println(clashSet.getbpList());
	 * 
	 * //// added 25-oct-2019 if (branches.get(level).ILPBranching) {
	 * Set<OWLSubClassOfAxiom> subAx = new HashSet<>(); Node n =
	 * branches.get(level).getNode(); System.err.println("ILPBranching n: " +
	 * n.getId() + " node: " + node.getId()); if (!n.equals(node) && n.getId() <
	 * node.getId()) { Set<OWLClassExpression> relatedConcepts =
	 * branches.get(level).getRelatedConcepts(node); //
	 * System.err.println("relatedConcepts: "+ relatedConcepts.size() +" //
	 * node.getBackPropagatedLabel() "+ node.getBackPropagatedLabel());
	 * OWLClassExpression ce = clashSet.getCe(); OWLClassExpression ceNNF =
	 * clashSet.getCeNNF(); // System.err.println("ce "+ ce +" ceNNF "+ ceNNF);
	 * 
	 * if (!node.getSimpleILPLabel().contains(ce) &&
	 * node.getSimpleILPLabel().contains(ceNNF)) { for (OWLClassExpression bpl :
	 * node.getBackPropagatedLabel()) { if (bpl.equals(ce)) { for
	 * (OWLClassExpression rc : relatedConcepts) {
	 * subAx.add(df.getOWLSubClassOfAxiom(rc, bpl)); } } else if (bpl instanceof
	 * OWLObjectIntersectionOf) { if (bpl.asConjunctSet().contains(ce)) { for
	 * (OWLClassExpression rc : relatedConcepts) {
	 * subAx.add(df.getOWLSubClassOfAxiom(rc, bpl)); } } } else if (bpl instanceof
	 * OWLObjectUnionOf) { if (bpl.asDisjunctSet().contains(ce)) { for
	 * (OWLClassExpression rc : relatedConcepts) {
	 * subAx.add(df.getOWLSubClassOfAxiom(rc, bpl)); } }
	 * 
	 * } } } else if (!node.getSimpleILPLabel().contains(ceNNF) &&
	 * node.getSimpleILPLabel().contains(ce)) { for (OWLClassExpression bpl :
	 * node.getBackPropagatedLabel()) { if (bpl.equals(ceNNF)) { for
	 * (OWLClassExpression rc : relatedConcepts) {
	 * subAx.add(df.getOWLSubClassOfAxiom(rc, bpl)); } } else if (bpl instanceof
	 * OWLObjectIntersectionOf) { if (bpl.asConjunctSet().contains(ceNNF)) { for
	 * (OWLClassExpression rc : relatedConcepts) {
	 * subAx.add(df.getOWLSubClassOfAxiom(rc, bpl)); } } } else if (bpl instanceof
	 * OWLObjectUnionOf) { if (bpl.asDisjunctSet().contains(ceNNF)) { for
	 * (OWLClassExpression rc : relatedConcepts) {
	 * subAx.add(df.getOWLSubClassOfAxiom(rc, bpl)); } }
	 * 
	 * } } }
	 * 
	 * if (!subAx.isEmpty()) { // System.err.println("subAx "+ subAx);
	 * restore(level, true, false, false); // reset(n);
	 * subAx.addAll(branches.get(level).getSubsumption()); // save(n);
	 * this.callILP(n, branches.get(level).getAllEntries(), subAx, null);
	 * 
	 * } else {
	 * 
	 * // branches.get(level).reset2(); // branches.remove(level); restore(level,
	 * true, false, false); // System.out.println("clashSet before " +
	 * clashSet.getbpList()); clashSet.removeLevel(level); //
	 * System.out.println("clashSet after " + clashSet.getbpList()); if
	 * (!clashHandler(clashSet, n)) return false; }
	 * 
	 * } else { if (n.getId() > node.getId()) { restore(level, true, false, false);
	 * // reset(node); clashSet.removeLevel(level); if (!clashHandler(clashSet,
	 * node)) return false; } else { // branches.get(level).reset2(); //
	 * branches.remove(level); restore(level, true, false, false);
	 * clashSet.removeLevel(level); if (!clashHandler(clashSet, n)) {
	 * System.out.println("ClashSet"); return false; } } } }
	 * 
	 * /// else if (branches.get(level).mergeBranching) { System.err.println(
	 * "mergeBranching n: " + branches.get(level).mergeFrom.getId() + " node: " +
	 * node.getId()); cg.updateReset(branches.get(level).mergeFrom); restore(level,
	 * false, true, false); clashSet.removeLevel(level); if (!clashHandler(clashSet,
	 * cg.getCurrNode())) return false; }
	 * 
	 * else { System.err.println("disjunction branching "); if
	 * (branches.get(level).hasNextOption()) { restore(level, false, false, true);
	 * DependencySet newDS = DependencySet.create(clashSet); //
	 * applyOr(cg.getCurrNode(), branches.get(level).getNextOption(), //
	 * DependencySet.plus(newDS, branches.get(level).getDs()));
	 * save(cg.getCurrNode()); incCurLevel(); boolean result =
	 * applyOr(cg.getCurrNode(), branches.get(level).getNextOption(),
	 * DependencySet.plus(newDS,
	 * DependencySet.create(branches.get(level).getDs()))); /*StackTraceElement[] el
	 * = Thread.currentThread().getStackTrace(); for (StackTraceElement e : el) {
	 * System.out.println(e.toString()); } System.out.println("\n\nresult "+result);
	 * return result; // this.incCurLevel(); // applyOr(cg.getCurrNode(),
	 * branches.get(level).getNextOption(), newDS);
	 * 
	 * // save(cg.getCurrNode()); //
	 * System.out.println("restoring currentBranchingPoint : "+level +" Neighbour :
	 * // "+cg.getCurrNode().getOutgoingEdges().size()+" total nodes : "+ //
	 * cg.getTotalNodes()); // System.out.println("branch node" +
	 * branches.get(level).getNode().getId()); //
	 * System.out.println("graph curr node" + cg.getCurrNode().getId()); //
	 * System.out.println("curr node label after" + cg.getCurrNode().getLabel());
	 * 
	 * /// comment start 15 sep, 2019 /* boolean flag = false;
	 * for(OWLClassExpression ce :branches.get(level).getAllNextOptions()) {
	 * if(isConceptExist(cg.getCurrNode(), ce)) { flag = true;
	 * branches.get(level).disjunctTaken(ce); updateConceptDepSet(cg.getCurrNode(),
	 * DependencySet.plus(newDS, branches.get(level).getDs()), ce); // commented on
	 * 4 march 2019 //updateConceptDepSet(cg.getCurrNode(),
	 * branches.get(level).getDs(), ce); if(!(ce instanceof OWLClass) || !(ce
	 * instanceof OWLObjectOneOf) || !(ce instanceof OWLObjectComplementOf)) {
	 * updateToDoEntryDepSet(cg.getCurrNode(), ce, DependencySet.plus(newDS,
	 * branches.get(level).getDs())); // commented on 4 march 2019
	 * //updateToDoEntryDepSet(cg.getCurrNode(), ce, branches.get(level).getDs()); }
	 * break;
	 * 
	 * } } if(!flag) { applyOr(cg.getCurrNode(),
	 * branches.get(level).getNextOption(), DependencySet.plus(newDS,
	 * branches.get(level).getDs())); // commented on 4 march 2019
	 * //applyOr(cg.getCurrNode(), branches.get(level).getNextOption(),
	 * branches.get(level).getDs()); //applyOr(branches.get(level).getNode(),
	 * branches.get(level).getNextOption(), branches.get(level).ds); }
	 * 
	 * /// comment end 15 sep, 2019 } else { Node n = branches.get(level).getNode();
	 * branches.get(level).reset(); // branches.remove(level);
	 * clashSet.removeLevel(level); if (!clashHandler(clashSet, n)) return false; }
	 * } } else { return false; } return true; }
	 * 
	 */

	/*
	 * private boolean needToApplyAtMost(Node n) { if (n.isNominalNode()) { for
	 * (OWLObjectMaxCardinality mc : n.getLabel().stream().filter(ce -> ce
	 * instanceof OWLObjectMaxCardinality) .map(ce -> (OWLObjectMaxCardinality)
	 * ce).collect(Collectors.toSet())) { DependencySet ds =
	 * n.getnLabel().getCndList().getCdSet().stream().filter(ce ->
	 * ce.getCe().equals(mc)) .iterator().next().getDs();
	 * 
	 * OWLObjectPropertyExpression role = mc.getProperty(); OWLClassExpression
	 * filler = mc.getFiller(); int cardinality = mc.getCardinality(); int nodesCard
	 * = 0; int maxCard = 0; DependencySet maxDs = DependencySet.create(); for (Edge
	 * e : n.getOutgoingEdges()) { if (!e.isReset() && e.getLabel().contains(role))
	 * { Node to = e.getToNode(); if ((to.getLabel().contains(filler) || (filler
	 * instanceof OWLObjectIntersectionOf &&
	 * to.getLabel().containsAll(filler.asConjunctSet())) || (filler instanceof
	 * OWLObjectUnionOf &&
	 * to.getLabel().stream().anyMatch(filler.asDisjunctSet()::contains))) &&
	 * !to.isReset()) { // System.err.println("to "+ to.getId()); int card =
	 * to.getCardinality(); nodesCard += card; if (maxCard < card) { maxCard = card;
	 * if (filler instanceof OWLObjectIntersectionOf) { for (OWLClassExpression cj :
	 * filler.asConjunctSet()) {
	 * maxDs.add(to.getnLabel().getCndList().getCdSet().stream() .filter(cnd ->
	 * cnd.getCe().equals(cj)).iterator().next().getDs()); } } else if (filler
	 * instanceof OWLObjectUnionOf) { for (OWLClassExpression dj :
	 * filler.asDisjunctSet()) {
	 * maxDs.add(to.getnLabel().getCndList().getCdSet().stream() .filter(cnd ->
	 * cnd.getCe().equals(dj)).iterator().next().getDs()); } } else { maxDs =
	 * to.getnLabel().getCndList().getCdSet().stream() .filter(cnd ->
	 * cnd.getCe().equals(filler)).iterator().next().getDs();
	 * 
	 * } } } } }
	 * 
	 * if (maxCard > cardinality) { // System.err.println("mxds "+ maxDs.getMax()
	 * +" "+filler); // FIXME: check dependency set if (!ds.isEmpty() ||
	 * !maxDs.isEmpty()) { // System.err.println("mxds "+ maxDs.getMax()
	 * +" "+filler); if (!clashHandler(DependencySet.plus(DependencySet.create(ds),
	 * DependencySet.create(maxDs)), n)) isInconsistent(n); } else
	 * isInconsistent(n); return false;
	 * 
	 * } if (cardinality < nodesCard) { return true; } } return false; } else { for
	 * (OWLObjectMaxCardinality mc : n.getLabel().stream().filter(ce -> ce
	 * instanceof OWLObjectMaxCardinality) .map(ce -> (OWLObjectMaxCardinality)
	 * ce).collect(Collectors.toSet())) { DependencySet ds =
	 * n.getnLabel().getCndList().getCdSet().stream().filter(ce ->
	 * ce.getCe().equals(mc)) .iterator().next().getDs();
	 * 
	 * OWLObjectPropertyExpression role = mc.getProperty(); OWLClassExpression
	 * filler = mc.getFiller(); int cardinality = mc.getCardinality(); int nodesCard
	 * = 0; int maxCard = 0; DependencySet maxDs = DependencySet.create(); for (Edge
	 * e : n.getOutgoingEdges()) { if (!e.isReset() && e.getLabel().contains(role))
	 * { Node to = e.getToNode(); if ((to.getLabel().contains(filler) || (filler
	 * instanceof OWLObjectIntersectionOf &&
	 * to.getLabel().containsAll(filler.asConjunctSet())) || (filler instanceof
	 * OWLObjectUnionOf &&
	 * to.getLabel().stream().anyMatch(filler.asDisjunctSet()::contains))) &&
	 * !to.isReset()) { if (e.isPredEdge()) { nodesCard++; } else {
	 * 
	 * // System.err.println("to "+ to.getId()); int card = to.getCardinality();
	 * nodesCard += card; if (maxCard < card) { maxCard = card; if (filler
	 * instanceof OWLObjectIntersectionOf) { for (OWLClassExpression cj :
	 * filler.asConjunctSet()) {
	 * maxDs.add(to.getnLabel().getCndList().getCdSet().stream() .filter(cnd ->
	 * cnd.getCe().equals(cj)).iterator().next().getDs()); } } else if (filler
	 * instanceof OWLObjectUnionOf) { for (OWLClassExpression dj :
	 * filler.asDisjunctSet()) {
	 * maxDs.add(to.getnLabel().getCndList().getCdSet().stream() .filter(cnd ->
	 * cnd.getCe().equals(dj)).iterator().next().getDs()); } } else { maxDs =
	 * to.getnLabel().getCndList().getCdSet().stream() .filter(cnd ->
	 * cnd.getCe().equals(filler)).iterator().next().getDs();
	 * 
	 * } } } } } }
	 * 
	 * if (maxCard > cardinality) { // System.err.println("mxds "+ maxDs.getMax()
	 * +" "+filler); // FIXME: check dependency set if (!ds.isEmpty() ||
	 * !maxDs.isEmpty()) { // System.err.println("mxds "+ maxDs.getMax()
	 * +" "+filler); if (!clashHandler(DependencySet.plus(DependencySet.create(ds),
	 * DependencySet.create(maxDs)), n)) isInconsistent(n); } else
	 * isInconsistent(n); return false;
	 * 
	 * } if (cardinality < nodesCard) { return true; } } return false; } }
	 */
	

	/*private boolean checkAtMost(Node from, Node to, Set<ConceptNDepSet> maxCards) {
		for (ConceptNDepSet cnds : maxCards) {
			if (!checkAtMost(from, to, (OWLObjectMaxCardinality) cnds.getCe(), cnds.getDs()))
				return false;
		}
		return true;
	}

	private boolean checkAtMost(Node from, Node to, OWLObjectMaxCardinality mc, DependencySet ds) {
		OWLObjectPropertyExpression role = mc.getProperty();
		OWLClassExpression filler = mc.getFiller();
		int cardinality = mc.getCardinality();
		int nodesCard = 0;
		int maxCard = 0;
		int maxAddedFrom = 0;
		int maxAddedTo = 0;
		Set<Node> nodes = new HashSet<>();
		Set<Node> djNodesFrom = new HashSet<>();
		Set<Node> djNodesTo = new HashSet<>();
		DependencySet maxDs = DependencySet.create();
		DependencySet djDsFrom = DependencySet.create();
		DependencySet djDsTo = DependencySet.create();
		for (Edge e : from.getOutgoingEdges()) {
			if (!e.isReset() && (e.isPredEdge() || e.getToNode().isNominalNode()) && e.getLabel().contains(role)
					&& e.getToNode().getLabel().contains(filler)) {
				Node n = e.getToNode();
				//// System.err.println("to "+ to.getId());
				int card = n.getCardinality();
				nodes.add(n);
				for (Node dn : n.getDisjointNodes()) {
					if (nodes.contains(dn)) {
						djNodesFrom.add(dn);
						djNodesFrom.add(n);
					}
				}
				nodesCard += card;
				if (maxCard < card) {
					maxCard = card;
					maxDs = DependencySet.create(n.getDs());

				}
			}
		}
		for (Node djn : djNodesFrom) {
			maxAddedFrom += djn.getCardinality();
			djDsFrom.add(DependencySet.create(djn.getDs()));

		}
		for (Edge e : to.getOutgoingEdges()) {
			if (!e.isReset() && (e.isPredEdge() || e.getToNode().isNominalNode()) && e.getLabel().contains(role)
					&& e.getToNode().getLabel().contains(filler)) {
				Node n = e.getToNode();
				//// System.err.println("to "+ to.getId());
				int card = n.getCardinality();
				nodes.add(n);
				for (Node dn : n.getDisjointNodes()) {
					if (nodes.contains(dn)) {
						djNodesTo.add(dn);
						djNodesTo.add(n);
					}
				}
				nodesCard += card;
				if (maxCard < card) {
					maxCard = card;
					maxDs = DependencySet.create(n.getDs());

				}
			}
		}
		for (Node djn : djNodesTo) {
			maxAddedTo += djn.getCardinality();
			djDsTo.add(DependencySet.create(djn.getDs()));

		}
		if (maxCard > cardinality) {
			// System.err.println("mxds "+ maxDs.getMax() +" "+filler);
			// FIXME: check dependency set
			if (!ds.isEmpty() || !maxDs.isEmpty()) {
				// System.err.println("mxds "+ maxDs.getMax() +" "+filler);
				if (!clashHandler(DependencySet.plus(DependencySet.create(ds), DependencySet.create(maxDs)), from))
					isInconsistent(from);
			} else
				isInconsistent(from);
			return false;

		}
		if (cardinality < maxAddedFrom) {
			if (!ds.isEmpty() || !djDsFrom.isEmpty()) {
				// System.err.println("mxds "+ maxDs.getMax() +" "+filler);
				if (!clashHandler(DependencySet.plus(DependencySet.create(ds), DependencySet.create(maxDs)), from))
					isInconsistent(from);
			} else
				isInconsistent(from);
			return false;
		}
		if (cardinality < maxAddedTo) {
			if (!ds.isEmpty() || !djDsTo.isEmpty()) {
				// System.err.println("mxds "+ maxDs.getMax() +" "+filler);
				if (!clashHandler(DependencySet.plus(DependencySet.create(ds), DependencySet.create(maxDs)), from))
					isInconsistent(from);
			} else
				isInconsistent(from);
			return false;
		}
		if (cardinality < nodesCard) {
			return true;
		}
		return false;

	}
*/

	/*
	 * public boolean needILPModule(ToDoEntry entry) { forAllCheck = false;
	 * isExistential = false; Node n = entry.getNode(); if(!n.isBlocked()) {
	 * 
	 * if(entry.getType().equals(NodeTag.AND)) { for(OWLClassExpression ce :
	 * entry.getClassExpression().asConjunctSet()) { if(ce instanceof
	 * OWLObjectHasValue) return true; else if (ce instanceof
	 * OWLObjectIntersectionOf) return hasNominal((OWLObjectIntersectionOf)ce); else
	 * if (ce instanceof OWLObjectUnionOf) return hasNominal((OWLObjectUnionOf)ce);
	 * else if(ce instanceof OWLObjectSomeValuesFrom) { isExistential = true; return
	 * hasNominal((OWLObjectSomeValuesFrom) ce); } else if(ce instanceof
	 * OWLObjectAllValuesFrom) { if(hasNominal((OWLObjectAllValuesFrom) ce))
	 * forAllCheck = true; } } } else if(entry.getType().equals(NodeTag.EXISTS)) {
	 * OWLClassExpression ce = entry.getClassExpression(); if(ce instanceof
	 * OWLObjectHasValue) return true; else return
	 * hasNominal((OWLObjectSomeValuesFrom) ce); } } if(forAllCheck &&
	 * isExistential) return true; return false; }
	 */

}
