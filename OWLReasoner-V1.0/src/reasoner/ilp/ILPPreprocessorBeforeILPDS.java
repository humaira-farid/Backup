package reasoner.ilp;

import java.util.*;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.util.DefaultPrefixManager;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;

import ilog.concert.IloException;
import reasoner.Ontology;
import reasoner.RuleEngine;
import reasoner.Dependencies.DependencySet;
import reasoner.graph.CompletionGraph;
import reasoner.graph.Edge;
import reasoner.graph.Node;
import reasoner.preprocessing.Internalization;
import reasoner.todolist.ToDoEntry;

public class ILPPreprocessorBeforeILPDS {
	
	List<OWLObjectCardinalityRestriction> cardRes = new ArrayList<>();
	List<OWLObjectCardinalityRestriction> minCardRes = new ArrayList<>();
	List<OWLObjectCardinalityRestriction> maxCardRes = new ArrayList<>();
	Set<OWLSubClassOfAxiom> auxiliaryMaxSubAx = new HashSet<>();
	Set<OWLClassExpression> auxiliaryConcepts = new HashSet<>();
	Set<OWLObjectPropertyExpression> auxiliaryRoles = new HashSet<>();
	Set<OWLClassExpression> subsumptionConcepts = new HashSet<>();
	Set<OWLClassExpression> existingConcepts = new HashSet<>();
	Set<OWLObjectOneOf> tempNom = new HashSet<>();
	Set<OWLObjectOneOf> tempSimple = new HashSet<>();
	Set<OWLObjectMinCardinality> topMinCardinalities = new HashSet<>();
	Set<OWLObjectMaxCardinality> topMaxCardinalities = new HashSet<>();
	SetMultimap<OWLClassExpression, OWLClassExpression> conceptSubsumers = HashMultimap.create();
	SetMultimap<OWLClassExpression, OWLClassExpression> complexCSubsumers = HashMultimap.create(); // complex concept subsumers 
	SetMultimap<OWLClassExpression, OWLClassExpression> complexNSubsumers = HashMultimap.create(); // complex nominal subsumers
	Map<OWLClassExpression, Set<OWLClassExpression>> binarySubsumers = new HashMap<>();
	BiMap<OWLClassExpression, OWLClassExpression> qcrAux = HashBiMap.create();
	SetMultimap<OWLClassExpression, OWLClassExpression> conceptDisjoints = HashMultimap.create();
	SetMultimap<OWLClassExpression, OWLClassExpression> nominalSubsumers = HashMultimap.create();
	SetMultimap<OWLClassExpression, OWLClassExpression> nominalDisjoints = HashMultimap.create();
	SetMultimap<OWLClassExpression, OWLClassExpression> simpleASubsumers = HashMultimap.create();
	SetMultimap<OWLClassExpression, OWLClassExpression> binaryMaxSubsumers = HashMultimap.create();
	SetMultimap<OWLClassExpression, OWLClassExpression> complexASubsumers = HashMultimap.create();
	SetMultimap<OWLClassExpression, OWLClassExpression> extraSubsumers = HashMultimap.create();
	SetMultimap<OWLObjectPropertyExpression, OWLObjectPropertyExpression> auxRoleH = HashMultimap.create();
	Map<OWLClassExpression, Integer> nodeIdMap = new HashMap<>();
	Map<Integer, Set<OWLClassExpression>> nodeLabelMap = new HashMap<>();
	Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> auxRoleHMap = new HashMap<>();
	SetMultimap<OWLClassExpression, DependencySet> conceptDs = HashMultimap.create();
	SetMultimap<OWLObjectOneOf, DependencySet> nominalDs = HashMultimap.create();
	SetMultimap<OWLSubClassOfAxiom, DependencySet> auxiliarySubAxDs = HashMultimap.create();
	SetMultimap<OWLSubClassOfAxiom, DependencySet> auxiliaryMaxSubAxDs = HashMultimap.create();
	SetMultimap<OWLObjectCardinalityRestriction, DependencySet> cardResDs = HashMultimap.create();
	SetMultimap<OWLObjectSomeValuesFrom, DependencySet> existsDs = HashMultimap.create();
	SetMultimap<OWLObjectPropertyExpression, DependencySet> forAllDs = HashMultimap.create();
	SetMultimap<OWLObjectMinCardinality, DependencySet> minDs = HashMultimap.create();
	SetMultimap<OWLObjectMaxCardinality, DependencySet> maxDs = HashMultimap.create();
	SetMultimap<OWLObjectHasValue, DependencySet> hasValueDs = HashMultimap.create();
	
	
	CompletionGraph cg;
	RuleEngine re;
	
	Set<Set<OWLClassExpression>> disjointGroups = new HashSet<>();
	Set<QCR> qcrs = new HashSet<>();
	Map<Integer, OWLObjectCardinalityRestriction> crMap = new HashMap<Integer, OWLObjectCardinalityRestriction>();
	Map<Integer, QCR> qcrMap = new HashMap<Integer, QCR>();
	Map<Integer, OWLClassExpression> qcrQualifiersMap = new HashMap<>();
	SetMultimap<OWLClassExpression, OWLObjectPropertyExpression> qcrMultiMap =  HashMultimap.create();
	Set<OWLObjectOneOf> nominals = new HashSet<>();
	Set<OWLClassExpression> simpleConcepts = new HashSet<>();
	Set<OWLClassExpression> complexConcepts = new HashSet<>();
	int counter = 0;
	OWLDataFactory df;
	OWLOntologyManager man = OWLManager.createOWLOntologyManager();
	Set<OWLObjectPropertyExpression> roles = new HashSet<>();
	Map<OWLObjectPropertyExpression, OWLObjectPropertyExpression> tempRoleH = new HashMap<>();
	//SetMultimap<OWLObjectPropertyExpression, OWLObjectPropertyExpression> superRoles = HashMultimap.create();
	SetMultimap<OWLObjectPropertyExpression, OWLObjectPropertyExpression> sR = HashMultimap.create();
	
	Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> superRolesMap = new HashMap<>();
	Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> sRMap = new HashMap<>();
	
	SetMultimap<OWLObjectPropertyExpression, OWLClassExpression> forAllMap = HashMultimap.create();
	Map<OWLObjectPropertyExpression, OWLClassExpression> topMinMap = new HashMap<>();
	Map<OWLObjectPropertyExpression, OWLClassExpression> topMaxMap = new HashMap<>();
	
	Set<OWLSubClassOfAxiom> learnedSubsumption = new HashSet<>();
	Set<OWLSubClassOfAxiom> atomicGCIs = new HashSet<>();
	
	Set<OWLObjectAllValuesFrom> forAllRes = new HashSet<>();

	Set<OWLSubObjectPropertyOfAxiom> subRoleAxioms = new HashSet<>();
	
	DefaultPrefixManager prefixManager;
	Ontology ontology;
	String base = null;
	Node currNode;
	Set<Edge> outgoingEdges;
	
	public ILPPreprocessorBeforeILPDS(RuleEngine re, CompletionGraph cg, Set<ToDoEntry> entries, Internalization intl, OWLDataFactory df, Node n, Set<Edge> outgoingEdges, Set<OWLSubClassOfAxiom> subsumption, Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> superRolesMap2) {
		counter = 0;
		this.cg = cg;
		this.df = df;
		this.re = re;
		this.currNode = n;
		this.outgoingEdges = outgoingEdges;
		this.prefixManager = intl.getPrefixManager();
		this.ontology = intl.getOntology();
		this.base = this.prefixManager.getDefaultPrefix();
		this.superRolesMap = superRolesMap2;
		this.learnedSubsumption = subsumption;
		this.atomicGCIs = intl.getAtomicGCIs();
		for(ToDoEntry entry : entries)
			processEntry(entry);
		generateQCR();
		processQCRs();
		processExistingOutgoingEdges();
		processConcepts();
		processLearnedSubsumption();
		createInternalRoleHierarchy();
		createMaps();
		processAtomicGCIs();
		addILPBranches();
	}
	public ILPPreprocessorBeforeILPDS(CompletionGraph cg, Set<ToDoEntry> entries, Internalization intl, OWLDataFactory df, Node n, Set<Edge> outgoingEdges, Set<OWLSubClassOfAxiom> subsumption, Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> superRolesMap2) {
		
	}
	
	private void addILPBranches() {
		Set<OWLClassExpression> supConcepts = new HashSet<>();
		supConcepts.addAll(conceptSubsumers.values());
		supConcepts.addAll(nominalSubsumers.values());
		supConcepts.addAll(simpleASubsumers.values());
		for(OWLClassExpression ce : supConcepts) {
			if(ce instanceof OWLObjectUnionOf) {
				//DependencySet newDs = DependencySet.plus(DependencySet.create(ds), DependencySet.create(re.getILPCurLevel()));
				//RuleEngine.BranchHandler bh = re.new BranchHandler();
			}
		}
		
	}


	private void processAtomicGCIs() {
		Set<OWLClassExpression> allConcepts = new HashSet<>();
		allConcepts.addAll(this.simpleConcepts);
		allConcepts.addAll(this.nominals);
		simpleConcepts.stream().forEach(c -> allConcepts.add(c.getComplementNNF()));
		nominals.stream().forEach(o -> allConcepts.add(o.getComplementNNF()));
		for(OWLSubClassOfAxiom aG : this.atomicGCIs) {
			if(allConcepts.containsAll(aG.getSuperClass().asDisjunctSet())) {
				conceptSubsumers.put(df.getOWLThing(), aG.getSuperClass());
			}
		}
		
	}


	private void processEntry(ToDoEntry entry) {
		OWLClassExpression ce = entry.getClassExpression();
		DependencySet ds = entry.getDs();
		if(ce instanceof OWLObjectSomeValuesFrom) {
			existsDs.put((OWLObjectSomeValuesFrom)ce, ds);
		}
		else if(ce instanceof OWLObjectMinCardinality) {
			minDs.put((OWLObjectMinCardinality)ce, ds);
		}
		else if(ce instanceof OWLObjectMaxCardinality) {
			maxDs.put((OWLObjectMaxCardinality)ce, ds);
		}
		else if(ce instanceof OWLObjectHasValue) {
			hasValueDs.put((OWLObjectHasValue)ce, ds);
		}
		else if(ce instanceof OWLObjectAllValuesFrom) {
			processForAll((OWLObjectAllValuesFrom)ce, ds);
		}
	
	}
	
	private void processForAll(OWLObjectAllValuesFrom c, DependencySet ds) {
		OWLObjectPropertyExpression role = c.getProperty();
		OWLClassExpression filler = c.getFiller();
		roles.add(role);
		if(filler instanceof OWLObjectOneOf) {
			nominals.add((OWLObjectOneOf)filler);
			nominalDs.put((OWLObjectOneOf)filler, ds);
			conceptDs.put(filler, ds);
			this.forAllRes.add(c);
			this.forAllDs.put(role, ds);
		}
		else if(filler instanceof OWLClass) {
			simpleConcepts.add(c.getFiller());
			conceptDs.put(filler, ds);
			this.forAllRes.add(c);
			this.forAllDs.put(role, ds);
		}
		else if(filler instanceof OWLObjectComplementOf) {
			simpleConcepts.add(c.getFiller());
			conceptDs.put(filler, ds);
			this.forAllRes.add(c);
			this.forAllDs.put(role, ds);
		}
		else if(filler instanceof OWLObjectIntersectionOf) {
			OWLClassExpression qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
			auxiliaryConcepts.add(qualifier);
			for(OWLClassExpression cj : filler.asConjunctSet()) {
				auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, cj), ds);
				conceptDs.put(cj, ds);
			}
			this.forAllRes.add(df.getOWLObjectAllValuesFrom(c.getProperty(), qualifier));
			this.forAllDs.put(role, ds);
		}
		else if(filler instanceof OWLObjectUnionOf) {
			OWLClassExpression qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
			auxiliaryConcepts.add(qualifier);
			for(OWLClassExpression dj : filler.asDisjunctSet()) {
				conceptDs.put(dj, ds);
			}
			auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
			this.forAllRes.add(df.getOWLObjectAllValuesFrom(c.getProperty(), qualifier));
			this.forAllDs.put(role, ds);
		}
		else if(filler instanceof OWLObjectAllValuesFrom) {
			OWLClassExpression qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
			auxiliaryConcepts.add(qualifier);
			conceptDs.put(filler, ds);
			auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
			this.forAllRes.add(df.getOWLObjectAllValuesFrom(c.getProperty(), qualifier));
			this.forAllDs.put(role, ds);
		}
		else if(filler instanceof OWLObjectSomeValuesFrom) {
			OWLClassExpression qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
			auxiliaryConcepts.add(qualifier);
			conceptDs.put(filler, ds);
			auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
			this.forAllRes.add(df.getOWLObjectAllValuesFrom(c.getProperty(), qualifier));
			this.forAllDs.put(role, ds);
		}
		else if(filler instanceof OWLObjectMinCardinality) {
			OWLClassExpression qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
			auxiliaryConcepts.add(qualifier);
			conceptDs.put(filler, ds);
			auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
			this.forAllRes.add(df.getOWLObjectAllValuesFrom(c.getProperty(), qualifier));
			this.forAllDs.put(role, ds);
		}
		else if(filler instanceof OWLObjectMaxCardinality) {
			OWLClassExpression qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
			auxiliaryConcepts.add(qualifier);
			conceptDs.put(filler, ds);
			auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
			this.forAllRes.add(df.getOWLObjectAllValuesFrom(c.getProperty(), qualifier));
			this.forAllDs.put(role, ds);
		}
		
	}
	public Set<DependencySet> getRoleDS(OWLObjectPropertyExpression role) {
		return this.forAllDs.get(role);
	}
	private void generateQCR() {
		for(OWLObjectSomeValuesFrom ex : this.existsDs.keySet()) {
			DependencySet ds = DependencySet.create();
			DependencySet dsILP = DependencySet.create();
			for(DependencySet d : this.existsDs.get(ex))
				ds.add(d);
			OWLClassExpression filler = ex.getFiller();
			OWLObjectPropertyExpression role = ex.getProperty();
			roles.add(role);
			if(filler instanceof OWLObjectOneOf) {
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(1, role, filler);
				this.cardRes.add(cr);
				cardResDs.put(cr, ds);
				nominals.add((OWLObjectOneOf)filler);
				nominalDs.put((OWLObjectOneOf)filler, ds);
				conceptDs.put(filler, ds);
			}
			else if(filler instanceof OWLClass) {
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(1, role, filler);
				this.cardRes.add(cr);
				cardResDs.put(cr, ds);
				simpleConcepts.add(filler);
				conceptDs.put(filler, ds);
			}
			else if(filler instanceof OWLObjectComplementOf) {
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(1, role, filler);
				this.cardRes.add(cr);
				cardResDs.put(cr, ds);
				simpleConcepts.add(filler);
				conceptDs.put(filler, ds);
			}
			else if(filler instanceof OWLObjectIntersectionOf) {
				OWLClassExpression qualifier = null;
				if(qcrAux.containsValue(filler)) {
					qualifier = qcrAux.inverse().get(filler);
				}
				else {
					qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
					auxiliaryConcepts.add(qualifier);
					this.qcrAux.put(qualifier, filler);
				}
				//boolean isNI = false;
				for(OWLClassExpression cj : filler.asConjunctSet()) {
					/*if(cj.toString().contains("#ni_"))
						isNI = true;*/
					auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, cj), ds);
					conceptDs.put(cj, ds);
				}
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(1, role, qualifier);
				/*if(isNI)
					cr = df.getOWLObjectExactCardinality(1, role, qualifier);
				else
					cr = df.getOWLObjectMinCardinality(1, role, qualifier);*/
				this.cardRes.add(cr);
				cardResDs.put(cr, ds);
			}
			else if(filler instanceof OWLObjectUnionOf) {
				OWLClassExpression qualifier = null;
				if(qcrAux.containsValue(filler)) {
					qualifier = qcrAux.inverse().get(filler);
				}
				else {
					qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
					auxiliaryConcepts.add(qualifier);
					this.qcrAux.put(qualifier, filler);
				}
				for(OWLClassExpression dj : filler.asDisjunctSet()) {
					conceptDs.put(dj, ds);
				}
				auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(1, role, qualifier);
				this.cardRes.add(cr);
				cardResDs.put(cr, ds);
			}
			else if(filler instanceof OWLObjectAllValuesFrom || filler instanceof OWLObjectSomeValuesFrom || filler instanceof OWLObjectCardinalityRestriction) {
				OWLClassExpression qualifier = null;
				if(qcrAux.containsValue(filler)) {
					qualifier = qcrAux.inverse().get(filler);
				}
				else {
					qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
					auxiliaryConcepts.add(qualifier);
					this.qcrAux.put(qualifier, filler);
				}
				conceptDs.put(filler, ds);
				auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(1, role, qualifier);
				this.cardRes.add(cr);
				cardResDs.put(cr, ds);
			}
			/*else if(filler instanceof OWLObjectSomeValuesFrom) {
				OWLClassExpression qualifier = null;
				if(qcrAux.containsValue(filler)) {
					qualifier = qcrAux.inverse().get(filler);
				}
				else {
					qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
					auxiliaryConcepts.add(qualifier);
					this.qcrAux.put(qualifier, filler);
				}
				conceptDs.put(filler, ds);
				auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(1, role, qualifier);
				this.cardRes.add(cr);
				cardResDs.put(cr, ds);
			}*/
		}
		for(OWLObjectHasValue hv : hasValueDs.keySet()) {
			DependencySet ds = DependencySet.create();
			for(DependencySet d : this.hasValueDs.get(hv))
				ds.add(d);
			OWLObjectPropertyExpression role = hv.getProperty();
			roles.add(role);
			OWLIndividual ind = hv.getFiller();
			OWLObjectOneOf o = df.getOWLObjectOneOf(ind);
			nominals.add(o);
			nominalDs.put(o, ds);
			conceptDs.put(o, ds);
			OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(1, role, o);
			this.cardRes.add(cr);
			cardResDs.put(cr, ds);
		}
		
	}
	
	private void processQCRs() {
		for(OWLObjectMinCardinality min : this.minDs.keySet()) {
			DependencySet ds = DependencySet.create();
			for(DependencySet d : this.minDs.get(min))
				ds.add(d);
			OWLClassExpression filler = min.getFiller();
			OWLObjectPropertyExpression role = min.getProperty();
			roles.add(role);
			if(filler instanceof OWLObjectOneOf) {
				this.minCardRes.add(min);
				cardResDs.put(min, ds);
				nominals.add((OWLObjectOneOf)filler);
				nominalDs.put((OWLObjectOneOf)filler, ds);
				conceptDs.put(filler, ds);
			}
			else if(filler instanceof OWLClass) {
				this.minCardRes.add(min);
				cardResDs.put(min, ds);
				simpleConcepts.add(filler);
				conceptDs.put(filler, ds);
			}
			else if(filler.isOWLThing()) {
				this.minCardRes.add(min);
				cardResDs.put(min, ds);
				simpleConcepts.add(filler);
				conceptDs.put(filler, ds);
				topMinCardinalities.add(min);
			}
			else if(filler instanceof OWLObjectComplementOf) {
				this.minCardRes.add(min);
				cardResDs.put(min, ds);
				simpleConcepts.add(filler);
				conceptDs.put(filler, ds);
			}
			else if(filler instanceof OWLObjectIntersectionOf) {
				OWLClassExpression qualifier = null;
				if(qcrAux.containsValue(filler)) {
					qualifier = qcrAux.inverse().get(filler);
				}
				else {
					qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
					auxiliaryConcepts.add(qualifier);
					this.qcrAux.put(qualifier, filler);
				}
				
				for(OWLClassExpression cj : filler.asConjunctSet()) {
					auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, cj), ds);
					conceptDs.put(cj, ds);
				}
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(min.getCardinality(), role, qualifier);
				this.minCardRes.add(cr);
				cardResDs.put(cr, ds);
			}
			else if(filler instanceof OWLObjectUnionOf) {
				OWLClassExpression qualifier = null;
				if(qcrAux.containsValue(filler)) {
					qualifier = qcrAux.inverse().get(filler);
				}
				else {
					qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
					auxiliaryConcepts.add(qualifier);
					this.qcrAux.put(qualifier, filler);
				}
				
				for(OWLClassExpression dj : filler.asDisjunctSet()) {
					conceptDs.put(dj, ds);
				}
				auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(min.getCardinality(), role, qualifier);
				this.minCardRes.add(cr);
				cardResDs.put(cr, ds);
			}
			else if(filler instanceof OWLObjectAllValuesFrom) {
				OWLClassExpression qualifier = null;
				if(qcrAux.containsValue(filler)) {
					qualifier = qcrAux.inverse().get(filler);
				}
				else {
					qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
					auxiliaryConcepts.add(qualifier);
					this.qcrAux.put(qualifier, filler);
				}
				conceptDs.put(filler, ds);
				auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(min.getCardinality(), role, qualifier);
				this.minCardRes.add(cr);
				cardResDs.put(cr, ds);
			}
			else if(filler instanceof OWLObjectSomeValuesFrom) {
				OWLClassExpression qualifier = null;
				if(qcrAux.containsValue(filler)) {
					qualifier = qcrAux.inverse().get(filler);
				}
				else {
					qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
					auxiliaryConcepts.add(qualifier);
					this.qcrAux.put(qualifier, filler);
				}
				conceptDs.put(filler, ds);
				auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(min.getCardinality(), role, qualifier);
				this.minCardRes.add(cr);
				cardResDs.put(cr, ds);
			}
			else if(filler instanceof OWLObjectMinCardinality) {
				OWLClassExpression qualifier = null;
				if(qcrAux.containsValue(filler)) {
					qualifier = qcrAux.inverse().get(filler);
				}
				else {
					qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
					auxiliaryConcepts.add(qualifier);
					this.qcrAux.put(qualifier, filler);
				}
				conceptDs.put(filler, ds);
				auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(min.getCardinality(), role, qualifier);
				this.minCardRes.add(cr);
				cardResDs.put(cr, ds);
			}
			else if(filler instanceof OWLObjectMaxCardinality) {
				OWLClassExpression qualifier = null;
				if(qcrAux.containsValue(filler)) {
					qualifier = qcrAux.inverse().get(filler);
				}
				else {
					qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
					auxiliaryConcepts.add(qualifier);
					this.qcrAux.put(qualifier, filler);
				}
				conceptDs.put(filler, ds);
				auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(min.getCardinality(), role, qualifier);
				this.minCardRes.add(cr);
				cardResDs.put(cr, ds);
			}
		}

		for(OWLObjectMaxCardinality max : this.maxDs.keySet()) {
			DependencySet ds = DependencySet.create();
			for(DependencySet d : this.maxDs.get(max))
				ds.add(d);
			OWLClassExpression filler = max.getFiller();
			OWLObjectPropertyExpression role = max.getProperty();
			roles.add(role);
			if(max.getCardinality() == 0) {// <0R.A --> forAllR.notA
				//roles.add(role);
				
				OWLObjectAllValuesFrom forAll = df.getOWLObjectAllValuesFrom(role, filler.getComplementNNF());
				this.processForAll(forAll, ds);
			}
			else if(filler.isOWLThing()) {
				//System.out.println("top");
				this.maxCardRes.add(max);
				cardResDs.put(max, ds);
				simpleConcepts.add(filler);
				conceptDs.put(filler, ds);
				topMaxCardinalities.add(max);
			}
			else if(filler instanceof OWLObjectOneOf) {
				this.maxCardRes.add(max);
				cardResDs.put(max, ds);
				nominals.add((OWLObjectOneOf)filler);
				nominalDs.put((OWLObjectOneOf)filler, ds);
				conceptDs.put(filler, ds);
				OWLObjectAllValuesFrom forAll = df.getOWLObjectAllValuesFrom(role, df.getOWLObjectUnionOf(filler, filler.getComplementNNF()));
				this.processForAll(forAll, ds);
			}
			else if(filler instanceof OWLClass) {
				this.maxCardRes.add(max);
				cardResDs.put(max, ds);
				simpleConcepts.add(filler);
				conceptDs.put(filler, ds);
				OWLObjectAllValuesFrom forAll = df.getOWLObjectAllValuesFrom(role, df.getOWLObjectUnionOf(filler, filler.getComplementNNF()));
				this.processForAll(forAll, ds);
			}
			
			else if(filler instanceof OWLObjectComplementOf) {
				this.maxCardRes.add(max);
				cardResDs.put(max, ds);
				simpleConcepts.add(filler);
				conceptDs.put(filler, ds);
				OWLObjectAllValuesFrom forAll = df.getOWLObjectAllValuesFrom(role, df.getOWLObjectUnionOf(filler, filler.getComplementNNF()));
				this.processForAll(forAll, ds);
			}
			else if(filler instanceof OWLObjectIntersectionOf) {
				OWLClassExpression qualifier = null;
				if(qcrAux.containsValue(filler)) {
					qualifier = qcrAux.inverse().get(filler);
				}
				else {
					qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
					auxiliaryConcepts.add(qualifier);
					this.qcrAux.put(qualifier, filler);
				}
				//// updated on Sep 12, 2019
				
				if(filler.asConjunctSet().stream().allMatch(cj -> (cj instanceof OWLObjectOneOf) 
						|| (cj instanceof OWLClass) || (cj instanceof OWLObjectComplementOf))) {
					
					this.binaryMaxSubsumers.put(filler, qualifier);
					this.simpleConcepts.addAll(filler.asConjunctSet());
					//// 21 Oct, 2019
					this.simpleConcepts.addAll(filler.getComplementNNF().asDisjunctSet());
					OWLObjectAllValuesFrom forAll = df.getOWLObjectAllValuesFrom(role, df.getOWLObjectUnionOf(qualifier, qualifier.getComplementNNF()));
					this.processForAll(forAll, ds);
					//System.err.println("forall rule "+filler.getComplementNNF());
					this.auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier.getComplementNNF(), filler.getComplementNNF()),ds);
					////
				}
				for(OWLClassExpression cj : filler.asConjunctSet()) {
					auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, cj), ds);
					conceptDs.put(cj, ds);
				}

				OWLObjectCardinalityRestriction cr = df.getOWLObjectMaxCardinality(max.getCardinality(), role, qualifier);
				this.maxCardRes.add(cr);
				cardResDs.put(cr, ds);
				
				
				////// commented Sep 12, 2019 - start 
				/*OWLClassExpression qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
				auxiliaryConcepts.add(qualifier);
				for(OWLClassExpression cj : filler.asConjunctSet()) {
					this.auxiliarySubAx.add(df.getOWLSubClassOfAxiom(qualifier, cj));
					auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, cj), ds);
					conceptDs.put(cj, ds);
				}
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMaxCardinality(ex.getCardinality(), role, qualifier);
				this.maxCardRes.add(cr);
				cardResDs.put(cr, ds);
				roles.add(role);*/
				
				/// end
				
				//filler.asConjunctSet().stream().forEach(cj -> this.auxiliarySubAx.add(df.getOWLSubClassOfAxiom(qualifier, cj)));
			
			}
			else if(filler instanceof OWLObjectUnionOf) {
				
				OWLClassExpression qualifier = null;
				if(qcrAux.containsValue(filler)) {
					qualifier = qcrAux.inverse().get(filler);
				}
				else {
					qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
					auxiliaryConcepts.add(qualifier);
					this.qcrAux.put(qualifier, filler);
				}
				///////
				for(OWLClassExpression dj : filler.asDisjunctSet()) {
					conceptDs.put(dj, ds);
					if((dj instanceof OWLObjectOneOf) || (dj instanceof OWLClass) || (dj instanceof OWLObjectComplementOf)) {
						this.simpleASubsumers.put(dj, qualifier);
						this.simpleConcepts.add(dj);
						/// 21-OCT-2019
						OWLObjectAllValuesFrom forAll = df.getOWLObjectAllValuesFrom(role, df.getOWLObjectUnionOf(dj, dj.getComplementNNF()));
						this.processForAll(forAll, ds);
						///
					}
					
				}
				auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMaxCardinality(max.getCardinality(), role, qualifier);
				this.maxCardRes.add(cr);
				cardResDs.put(cr, ds);
				
				
				////// sep12. 2019 start
				/*OWLClassExpression qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
				auxiliaryConcepts.add(qualifier);
				for(OWLClassExpression dj : filler.asDisjunctSet()) {
					conceptDs.put(dj, ds);
				}
				this.auxiliarySubAx.add(df.getOWLSubClassOfAxiom(qualifier, filler));
				auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMaxCardinality(ex.getCardinality(), role, qualifier);
				this.maxCardRes.add(cr);
				cardResDs.put(cr, ds);
				roles.add(role);*/
				//// end
			}
			else if(filler instanceof OWLObjectAllValuesFrom) {
				OWLClassExpression qualifier = null;
				if(qcrAux.containsValue(filler)) {
					qualifier = qcrAux.inverse().get(filler);
				}
				else {
					qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
					auxiliaryConcepts.add(qualifier);
					this.qcrAux.put(qualifier, filler);
				}
				conceptDs.put(filler, ds);
				auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMaxCardinality(max.getCardinality(), role, qualifier);
				this.maxCardRes.add(cr);
				cardResDs.put(cr, ds);
			}
			else if(filler instanceof OWLObjectSomeValuesFrom) {
				OWLClassExpression qualifier = null;
				if(qcrAux.containsValue(filler)) {
					qualifier = qcrAux.inverse().get(filler);
				}
				else {
					qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
					auxiliaryConcepts.add(qualifier);
					this.qcrAux.put(qualifier, filler);
				}
				conceptDs.put(filler, ds);
				auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMaxCardinality(max.getCardinality(), role, qualifier);
				this.maxCardRes.add(cr);
				cardResDs.put(cr, ds);
			}
			else if(filler instanceof OWLObjectMinCardinality) {
				OWLClassExpression qualifier = null;
				if(qcrAux.containsValue(filler)) {
					qualifier = qcrAux.inverse().get(filler);
				}
				else {
					qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
					auxiliaryConcepts.add(qualifier);
					this.qcrAux.put(qualifier, filler);
				}
				conceptDs.put(filler, ds);
				auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMaxCardinality(max.getCardinality(), role, qualifier);
				this.maxCardRes.add(cr);
				cardResDs.put(cr, ds);
			}
			else if(filler instanceof OWLObjectMaxCardinality) {
				OWLClassExpression qualifier = null;
				if(qcrAux.containsValue(filler)) {
					qualifier = qcrAux.inverse().get(filler);
				}
				else {
					qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
					auxiliaryConcepts.add(qualifier);
					this.qcrAux.put(qualifier, filler);
				}
				conceptDs.put(filler, ds);
				auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMaxCardinality(max.getCardinality(), role, qualifier);
				this.maxCardRes.add(cr);
				cardResDs.put(cr, ds);
			}
		}
		
	}
	
	private void processExistingOutgoingEdges() {
		for(Edge e : outgoingEdges) {
			DependencySet ds = e.getDepSet();
			Set<OWLObjectPropertyExpression> eRoles = e.getLabel();
			Set<OWLClassExpression> fillers = e.getToNode().getLabel();

			OWLClassExpression qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
			nodeIdMap.put(qualifier, e.getToNode().getId());
			OWLObjectPropertyExpression role = df.getOWLObjectProperty("#ilp_auxRole_" + ++counter, prefixManager);
			auxiliaryConcepts.add(qualifier);
			auxiliaryRoles.add(role);
			for(OWLClassExpression c : fillers) {
				if((c instanceof OWLClass) || (c instanceof OWLObjectOneOf) || (c instanceof OWLObjectComplementOf)) {
					auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, c), ds);
				}
				else {
					this.complexASubsumers.put(qualifier, c);
				}
			}
			for(OWLObjectPropertyExpression r : eRoles) {
				roles.add(r);
				this.auxRoleH.put(role, r);
			}
			OWLObjectCardinalityRestriction crExact = null;
			if(this.currNode.isBlockableNode()) {
				crExact = df.getOWLObjectExactCardinality(1, role, qualifier);
			
			}
			else{
				crExact = df.getOWLObjectExactCardinality(e.getToNode().getCardinality(), role, qualifier);
			}
			
			this.cardRes.add(crExact);
			cardResDs.put(crExact, ds);
			
			roles.add(role);
		}
		this.auxRoleHMap = (Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>>) (Map<?, ?>) auxRoleH.asMap();
	}

	private void createInternalRoleHierarchy() {
		
		Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> tempSuperRolesMap = new HashMap<>(superRolesMap);
		tempSuperRolesMap.putAll(auxRoleHMap);
		int k=1;
		for(OWLObjectPropertyExpression role : this.roles) {
			if(!tempRoleH.containsKey(role)) {
				OWLObjectPropertyExpression rh = df.getOWLObjectProperty(IRI.create(base+"#TH"+k));// create Helper Role
				tempRoleH.put(role, rh);
				if(tempSuperRolesMap.keySet().contains(role)) {
					sRMap.put(role, tempSuperRolesMap.get(role));
				}
				k++;
			}
		}
		/*for(OWLObjectPropertyExpression role : this.roles) {
			if(!tempRoleH.containsKey(role)) {
				OWLObjectPropertyExpression rh = df.getOWLObjectProperty(IRI.create(base+"#TH"+k));// create Helper Role
				tempRoleH.put(role, rh);
				System.out.println("1) role "+ role +"H role : "+rh);
				k++;
				for(OWLObjectPropertyExpression r : tempSuperRolesMap.keySet()) {
					if(roles.contains(r)) {
						if(tempSuperRolesMap.get(r).contains(role)) {
							if(!tempRoleH.containsKey(r)) {
								OWLObjectPropertyExpression rh1 = df.getOWLObjectProperty(IRI.create(base+"#H"+k));
								tempRoleH.put(r, rh1);
								k++;
								System.out.println("2) role "+ r +"H role : "+rh1);
								
							}
	
							sR.put(r, role);
						}
					}
				}
			}
		}*/
				
	}

	
	private void processConcepts() {
		for(OWLSubClassOfAxiom sb : this.auxiliarySubAxDs.keySet()) {
			DependencySet ds = DependencySet.create();
			for(DependencySet d : this.auxiliarySubAxDs.get(sb))
				ds.add(d);
			if(sb.getSuperClass() instanceof OWLObjectOneOf) {
				this.simpleASubsumers.put(sb.getSubClass(), sb.getSuperClass());
				nominals.add((OWLObjectOneOf)sb.getSuperClass());
				nominalDs.put((OWLObjectOneOf)sb.getSuperClass(), ds);
				conceptDs.put(sb.getSuperClass(), ds);
			}
			else if(sb.getSuperClass() instanceof OWLClass) {
				this.simpleASubsumers.put(sb.getSubClass(), sb.getSuperClass());
				simpleConcepts.add(sb.getSuperClass());
				conceptDs.put(sb.getSuperClass(), ds);
			}
			else if(sb.getSuperClass() instanceof OWLObjectComplementOf) {
				this.simpleASubsumers.put(sb.getSubClass(), sb.getSuperClass());
				simpleConcepts.add(sb.getSuperClass());
				conceptDs.put(sb.getSuperClass(), ds);
			}
			else if(sb.getSuperClass() instanceof OWLObjectIntersectionOf) {
				addIntersectionConcepts(sb.getSubClass(), sb.getSuperClass(), ds);
			}
			else if(sb.getSuperClass() instanceof OWLObjectUnionOf) {
				if(sb.getSuperClass().asDisjunctSet().stream().allMatch(dj -> (dj instanceof OWLObjectOneOf) || (dj instanceof OWLClass) || (dj instanceof OWLObjectComplementOf))) {
					
					this.simpleASubsumers.put(sb.getSubClass(), sb.getSuperClass());
					for(OWLClassExpression c : sb.getSuperClass().asDisjunctSet()) {
						//System.err.println(" disjunct "+ c);
						if(c instanceof OWLObjectOneOf) {
							nominals.add((OWLObjectOneOf)c);
							nominalDs.put((OWLObjectOneOf)c, ds);
							conceptDs.put(c, ds);
						}
						else if((c instanceof OWLClass) || (c instanceof OWLObjectComplementOf)) {
							simpleConcepts.add(c);
							conceptDs.put(c, ds);
						}
					}
				}
				else
					this.complexASubsumers.put(sb.getSubClass(), sb.getSuperClass());
			}
			else if(sb.getSuperClass() instanceof OWLObjectSomeValuesFrom) {
				this.complexASubsumers.put(sb.getSubClass(), sb.getSuperClass());
			}
			else if(sb.getSuperClass() instanceof OWLObjectMinCardinality) {
				this.complexASubsumers.put(sb.getSubClass(), sb.getSuperClass());
			}
			else if(sb.getSuperClass() instanceof OWLObjectMaxCardinality) {
				this.complexASubsumers.put(sb.getSubClass(), sb.getSuperClass());
			}
			else if(sb.getSuperClass() instanceof OWLObjectAllValuesFrom) {
				this.complexASubsumers.put(sb.getSubClass(), sb.getSuperClass());
			}
			else if(sb.getSuperClass() instanceof OWLObjectHasValue) {
				this.complexASubsumers.put(sb.getSubClass(), sb.getSuperClass());
			}
		}
	
	}


	private void addIntersectionConcepts(OWLClassExpression sb, OWLClassExpression sp, DependencySet ds) {
		for(OWLClassExpression ce : sp.asConjunctSet()) {
			if(ce instanceof OWLClass) {
				this.simpleConcepts.add(ce);
				this.simpleASubsumers.put(sb, ce);
				conceptDs.put(ce, ds);
			}
			else if(ce instanceof OWLObjectOneOf) {
				this.nominals.add((OWLObjectOneOf)ce);
				nominalDs.put((OWLObjectOneOf)ce, ds);
				conceptDs.put(ce, ds);
				this.simpleASubsumers.put(sb, ce);
			}
			else if(ce instanceof OWLObjectComplementOf) {
				this.simpleASubsumers.put(sb, ce);
				simpleConcepts.add(ce);
				conceptDs.put(ce, ds);
			}
			else if(ce instanceof OWLObjectUnionOf) {
				if(ce.asDisjunctSet().stream().allMatch(dj -> (dj instanceof OWLObjectOneOf) || (dj instanceof OWLClass) || (dj instanceof OWLObjectComplementOf))) {
					this.simpleASubsumers.put(sb, ce);
					for(OWLClassExpression c : ce.asDisjunctSet()) {
						if(c instanceof OWLObjectOneOf) {
							nominals.add((OWLObjectOneOf)c);
							nominalDs.put((OWLObjectOneOf)c, ds);
							conceptDs.put(ce, ds);
						}
						else if((c instanceof OWLClass) || (c instanceof OWLObjectComplementOf) ) {
							simpleConcepts.add(c);
							conceptDs.put(ce, ds);
						}
					}
				}
				else
					this.complexASubsumers.put(sb, ce);
			}
			
			else if(ce instanceof OWLObjectIntersectionOf) {
				addIntersectionConcepts(sb, ce, ds);
			}
			else if(ce instanceof OWLObjectSomeValuesFrom) {
				this.complexASubsumers.put(sb, ce);
			}
			else if(ce instanceof OWLObjectAllValuesFrom) {
				this.complexASubsumers.put(sb, ce);
			}
			else if(ce instanceof OWLObjectHasValue) {
				this.complexASubsumers.put(sb, ce);
			}
		}
		
	}


	private void processLearnedSubsumption() {
		if(!this.learnedSubsumption.isEmpty()) {
			for(OWLSubClassOfAxiom subAx : this.learnedSubsumption) {
				OWLClassExpression sb = subAx.getSubClass();
				OWLClassExpression sp = subAx.getSuperClass();
				if(sb instanceof OWLClass) {
					this.simpleConcepts.add(sb);
					if(sp instanceof OWLObjectOneOf) {
						//subsumptionConcepts.add(sp);
						nominals.add((OWLObjectOneOf)sp);
						nominalDs.put((OWLObjectOneOf)sp, DependencySet.create());
						conceptSubsumers.put(sb, sp);
					}
					else if(sp instanceof OWLObjectComplementOf) {
						this.simpleConcepts.add(sp);
						subsumptionConcepts.add(sp);
						conceptSubsumers.put(sb, sp);
					}
					else if(sp instanceof OWLClass) {
						this.simpleConcepts.add(sp);
						subsumptionConcepts.add(sp);
						conceptSubsumers.put(sb, sp);
					}
					else if(sp instanceof OWLObjectUnionOf) {

						if(sp.asDisjunctSet().stream().allMatch(dj -> (dj instanceof OWLObjectOneOf) 
									|| (dj instanceof OWLClass) || (dj instanceof OWLObjectComplementOf))) {
							conceptSubsumers.put(sb, sp);

							for(OWLClassExpression c : sp.asDisjunctSet()) {			
								if(c instanceof OWLObjectOneOf) {
									if(!nominals.contains(c)) {
										nominals.add((OWLObjectOneOf)c);
										nominalDs.put((OWLObjectOneOf)c, DependencySet.create());
										//subsumptionConcepts.add(c);
									}
								}
								else if((c instanceof OWLClass) || (c instanceof OWLObjectComplementOf)) {
									if(!subsumptionConcepts.contains(c)) {
										this.simpleConcepts.add(c);
										subsumptionConcepts.add(c);
									}
								}
								else
									subsumptionConcepts.add(c);
							}
						}
					}
					else if(sp instanceof OWLObjectIntersectionOf)
						checkIntersection2(sb, sp);
				}
				else if(sb instanceof OWLObjectOneOf) {
					nominals.add((OWLObjectOneOf)sb);
					if(sp instanceof OWLObjectOneOf) {
						//subsumptionConcepts.add(sp);
						nominals.add((OWLObjectOneOf)sp);
						nominalDs.put((OWLObjectOneOf)sp, DependencySet.create());
						nominalSubsumers.put(sb, sp);
					}
					else if(sp instanceof OWLObjectComplementOf) {
						this.simpleConcepts.add(sp);
						subsumptionConcepts.add(sp);
						nominalSubsumers.put(sb, sp);
					}
					else if(sp instanceof OWLClass) {
						this.simpleConcepts.add(sp);
						subsumptionConcepts.add(sp);
						nominalSubsumers.put(sb, sp);
					}
					else if(sp instanceof OWLObjectUnionOf) {
						if(sp.asDisjunctSet().stream().allMatch(dj -> (dj instanceof OWLObjectOneOf) 
									|| (dj instanceof OWLClass) || (dj instanceof OWLObjectComplementOf))) {
							nominalSubsumers.put(sb, sp);
							for(OWLClassExpression c : sp.asDisjunctSet()) {			
								if(c instanceof OWLObjectOneOf) {
									if(!nominals.contains(c)) {
										nominals.add((OWLObjectOneOf)c);
										nominalDs.put((OWLObjectOneOf)c, DependencySet.create());
										//subsumptionConcepts.add(c);
									}
								}
								else if((c instanceof OWLClass) || (c instanceof OWLObjectComplementOf)) {
									if(!subsumptionConcepts.contains(c)) {
										this.simpleConcepts.add(c);
										subsumptionConcepts.add(c);
									}
								}
								else
									subsumptionConcepts.add(c);
							}
						}
					}
					else if(sp instanceof OWLObjectIntersectionOf)
						checkIntersection2(sb, sp);
				}
			}
		}
	}

	
	
	
	public Map<OWLClassExpression, Integer> getNodeIdMap() {
		return nodeIdMap;
	}
	

	
	public Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> getSuperRolesMap() {
		return superRolesMap;
	}
	public void setSuperRolesMap(Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> superRolesMap) {
		this.superRolesMap = superRolesMap;
	}
	public Set<OWLObjectPropertyExpression> getAuxiliaryRoles() {
		return auxiliaryRoles;
	}
	public Set<OWLObjectPropertyExpression> getAuxRoleHMap(OWLObjectPropertyExpression r) {
		return auxRoleHMap.get(r);
	}
	public void createMaps() {
		for(OWLObjectMinCardinality topMin : topMinCardinalities) {
			this.topMinMap.put(topMin.getProperty(), topMin.getFiller());
		}
		for(OWLObjectMaxCardinality topMax : topMaxCardinalities) {
			this.topMaxMap.put(topMax.getProperty(), topMax.getFiller());
		}
		for(OWLObjectAllValuesFrom forAll : getForAllRes()) {
			this.forAllMap.put(forAll.getProperty(), forAll.getFiller());
		}
		
		this.simpleConcepts.add(df.getOWLThing());
		
		
		for(OWLClassExpression ce : simpleConcepts) 
			addSubsumption(ce);
		for(OWLObjectOneOf o : nominals)
			addSubsumption(o);

		nominals.addAll(tempNom);
		// disjointness -concepts
		for(OWLClassExpression ce : simpleConcepts) {
			if(!(ce instanceof OWLObjectComplementOf)) {
				if(!ontology.getDisjointConcepts(ce).isEmpty()) {
					ontology.getDisjointConcepts(ce).stream().forEach(d -> conceptDisjoints.put(ce, d));
				}
			}
		}
		// disjointness -nominals
		for(OWLObjectOneOf o : nominals) {
			if(!ontology.getDisjointConcepts(o).isEmpty()) {
				ontology.getDisjointConcepts(o).stream().forEach(d -> nominalDisjoints.put(o, d));
			}
		}
		
		/// --- information about existing nominal nodes 
		existingNomNodes();
		///
		Set<OWLClassExpression> concepts = new  HashSet<>(simpleConcepts);
		concepts.addAll(nominals);
		concepts.addAll(subsumptionConcepts);
		existingConcepts.addAll(concepts);
		subsumptionConcepts.clear();
		nominals.clear();
		tempNom.clear();
		//concepts.stream().forEach(c -> System.out.println("concept "+c));
		this.binarySubsumers = ontology.getBinarySubsumption(concepts);
		processBinarySubsumers(binarySubsumers.keySet());
		this.disjointGroups = ontology.getDisjointGroups(concepts);
		this.binarySubsumers.putAll((Map<OWLClassExpression, Set<OWLClassExpression>>) (Map<?, ?>) binaryMaxSubsumers.asMap());
		
		int i = 0;
		for(OWLObjectCardinalityRestriction q : getCardResDs().keySet()) {
		//	System.out.println("cardRes "+q);
			DependencySet ds = DependencySet.create();
			for(DependencySet d : getCardResDs().get(q))
				ds.add(d);
			crMap.put(i, q);
			if(!isAlreadyExists(q, ds)) {
				QCR qcr = new QCR(q,ds);
				qcrMap.put(i, qcr);
				qcrQualifiersMap.put(i, q.getFiller());
				qcrMultiMap.put(q.getFiller(), q.getProperty());
				if(this.qcrAux.containsKey(q.getFiller())) {
					qcr.setAux(true);
					qcr.setRealQualifier(qcrAux.get(q.getFiller()));
				}
				qcrs.add(qcr);
				++i;
			}
		}
		for(OWLObjectOneOf o : getNominalDs().keySet()) {
			//System.out.println("nominal "+o);
			DependencySet ds = DependencySet.create();
			for(DependencySet d : getNominalDs().get(o))
				ds.add(d);
			QCR qcr = new QCR(o,ds);
			qcrMap.put(i, qcr);
			qcrQualifiersMap.put(i, o);
			qcrMultiMap.put(o, null);
			qcrs.add(qcr);
			++i;
		}
		
	}

	private void processBinarySubsumers(Set<OWLClassExpression> binarySubsumers2) {
		for(OWLClassExpression bs :binarySubsumers2){
			for(OWLClassExpression sup : binarySubsumers.get(bs)) {
				if(!existingConcepts.contains(sup)) {
					addSubsumption(sup);
				}
			}
		}
		nominals.addAll(tempNom);
		Set<OWLClassExpression> tempSubCon = new HashSet<>();
		for(OWLClassExpression ex : subsumptionConcepts ) {
			if(existingConcepts.contains(ex)) {
				tempSubCon.add(ex);
			}
		}
		subsumptionConcepts.removeAll(tempSubCon);
		Set<OWLObjectOneOf> tempNomCon = new HashSet<>();
		for(OWLObjectOneOf ex : nominals ) {
			if(existingConcepts.contains(ex)) {
				tempNomCon.add(ex);
			}
		}
		nominals.removeAll(tempNomCon);
		
		if(subsumptionConcepts.size() > 0 || nominals.size() > 0 ) {
			existingConcepts.addAll(nominals);
			existingConcepts.addAll(subsumptionConcepts);
			//System.err.println(ontology.getBinarySubsumption(existingConcepts).equals(binarySubsumers));
			if(!ontology.getBinarySubsumption(existingConcepts).equals(binarySubsumers)) {
				Set<OWLClassExpression> newBinarySubsumers = new HashSet<>(ontology.getBinarySubsumption(existingConcepts).keySet());
				newBinarySubsumers.removeAll(binarySubsumers.keySet());
				binarySubsumers = ontology.getBinarySubsumption(existingConcepts);
				subsumptionConcepts.clear();
				nominals.clear();
				tempNom.clear();
				processBinarySubsumers(newBinarySubsumers);
			}
		}
	}


	private void existingNomNodes() {
		/// --- information about existing nominal nodes
		SetMultimap<OWLObjectOneOf, DependencySet> tempNominalDs = HashMultimap.create();
		for (OWLObjectOneOf o : getNominalDs().keySet()) {
			Node nomNode = cg.findNominalNode(o);
			if (nomNode != null) {
				Set<OWLClassExpression> fillers = nomNode.getLabel();
				OWLClassExpression qualifier = df.getOWLClass("#ilp_aux_" + ++counter, prefixManager);
				nodeIdMap.put(qualifier, nomNode.getId());
				nodeLabelMap.put(nomNode.getId(), fillers);
				auxiliaryConcepts.add(qualifier);
				this.simpleASubsumers.put(o, qualifier);
				for (OWLClassExpression c : fillers) {
					if ((c instanceof OWLClass) || (c instanceof OWLObjectOneOf)
							|| (c instanceof OWLObjectComplementOf)) {
						DependencySet ds = DependencySet.create();
						for (DependencySet d : getNominalDs().get(o))
							ds.add(d);
						auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, c), ds);
						if (c instanceof OWLObjectOneOf) {
							this.simpleASubsumers.put(qualifier, c);
							nominals.add((OWLObjectOneOf) c);
							tempNominalDs.put((OWLObjectOneOf) c, ds);
							conceptDs.put(c, ds);
						} else if ((c instanceof OWLClass) || (c instanceof OWLObjectComplementOf)) {
							this.simpleASubsumers.put(qualifier, c);
							simpleConcepts.add(c);
							conceptDs.put(c, ds);
						}
					}
				}
			}
		}
		nominalDs.putAll(tempNominalDs);
	}

	private boolean isAlreadyExists(OWLObjectCardinalityRestriction q, DependencySet ds) {
		for(QCR qcr : qcrMap.values()) {
			if(qcr.qualifier.equals(q.getFiller()) && qcr.role.equals(q.getProperty())){
				if((q instanceof OWLObjectMinCardinality && qcr.type.equals("MIN"))
						|| (q instanceof OWLObjectExactCardinality && qcr.type.equals("EXACT"))) {
					if(qcr.cardinality >= q.getCardinality()) {
						return true;
					}
					else {
						qcr.updateCardinality(q.getCardinality());
						qcr.updateDS(ds);
						return true;
					}
				}
				else if(q instanceof OWLObjectMaxCardinality && qcr.type.equals("MAX")) {
					if(qcr.cardinality <= q.getCardinality()) {
						return true;
					}
					else {
						qcr.updateCardinality(q.getCardinality());
						qcr.updateDS(ds);
						return true;
					}
				}
			}
		}
		return false;
	}
	
	private void addSubsumption(OWLClassExpression ce) {
		// subsumption- concepts
	//	System.err.println("concept "+ce);
		if(ce instanceof OWLClass) {
			subsumptionConcepts.add(df.getOWLThing());
			conceptSubsumers.put(ce, df.getOWLThing());
			//System.err.println("concept "+ce);
			if(ontology.getAllSubsumers(ce) != null) {
				for(OWLClassExpression sp : ontology.getAllSubsumers(ce)) {
				  if(!sp.isOWLThing()) {
				//	System.out.println("subsumer "+sp);
					if(sp instanceof OWLObjectOneOf) {
						//subsumptionConcepts.add(sp);
						nominals.add((OWLObjectOneOf)sp);
						nominalDs.put((OWLObjectOneOf)sp, DependencySet.create());
						conceptSubsumers.put(ce, sp);
					}
					if(sp instanceof OWLObjectComplementOf) {
						subsumptionConcepts.add(sp);
						conceptSubsumers.put(ce, sp);
					}
					else if(sp instanceof OWLClass) {
						subsumptionConcepts.add(sp);
						conceptSubsumers.put(ce, sp);
					}
					else if(sp instanceof OWLObjectUnionOf) {
						if(sp.asDisjunctSet().stream().allMatch(dj -> (dj instanceof OWLObjectOneOf) 
								|| (dj instanceof OWLClass) || (dj instanceof OWLObjectComplementOf))) {
							conceptSubsumers.put(ce, sp);
							for(OWLClassExpression c : sp.asDisjunctSet()) {
								
								if(c instanceof OWLObjectOneOf) {
									if(!nominals.contains(c)) {
										nominals.add((OWLObjectOneOf)c);
										nominalDs.put((OWLObjectOneOf)c, DependencySet.create());
										//subsumptionConcepts.add(c);
									}
								}
								else if((c instanceof OWLClass) || (c instanceof OWLObjectComplementOf)) {
									if(!subsumptionConcepts.contains(c)) {
										subsumptionConcepts.add(c);
										addSubsumption(c);
									}
								}
								
								else
									subsumptionConcepts.add(c);
							}
						}
						else {
							complexCSubsumers.put(ce, sp);
						}
					}
					else if(sp instanceof OWLObjectIntersectionOf)
						checkIntersection(ce, sp);
					else
						complexCSubsumers.put(ce, sp);
				} 
			  }
			}
		}
		
		else if(ce instanceof OWLObjectComplementOf) {
			
		//	System.err.println("concept "+ce + " : "+ ontology.getAllComplementEq(ce.getComplementNNF()));
			if(ontology.getAllComplementEq(ce.getComplementNNF()) != null) {
				for(OWLClassExpression sp : ontology.getAllComplementEq(ce.getComplementNNF())) {
				  if(sp.isOWLThing()) {
					  subsumptionConcepts.add(df.getOWLThing());
					  conceptSubsumers.put(ce, df.getOWLThing());
				  }
				//	System.out.println("subsumer "+sp);
					if(sp instanceof OWLObjectOneOf) {
						//subsumptionConcepts.add(sp);
						nominals.add((OWLObjectOneOf)sp);
						nominalDs.put((OWLObjectOneOf)sp, DependencySet.create());
						conceptSubsumers.put(ce, sp);
					}
					if(sp instanceof OWLObjectComplementOf) {
						subsumptionConcepts.add(sp);
						conceptSubsumers.put(ce, sp);
					}
					else if(sp instanceof OWLClass) {
						subsumptionConcepts.add(sp);
						conceptSubsumers.put(ce, sp);
					}
					else if(sp instanceof OWLObjectUnionOf) {
						if(sp.asDisjunctSet().stream().allMatch(dj -> (dj instanceof OWLObjectOneOf) 
								|| (dj instanceof OWLClass) || (dj instanceof OWLObjectComplementOf))) {
							conceptSubsumers.put(ce, sp);
							for(OWLClassExpression c : sp.asDisjunctSet()) {
								
								if(c instanceof OWLObjectOneOf) {
									if(!nominals.contains(c)) {
										nominals.add((OWLObjectOneOf)c);
										nominalDs.put((OWLObjectOneOf)c, DependencySet.create());
										//subsumptionConcepts.add(c);
									}
								}
								else if((c instanceof OWLClass) || (c instanceof OWLObjectComplementOf)) {
									if(!subsumptionConcepts.contains(c)) {
										subsumptionConcepts.add(c);
										addSubsumption(c);
									}
								}
								else
									subsumptionConcepts.add(c);
							}
						}
						else {
							complexCSubsumers.put(ce, sp);
						}
					}
					else if(sp instanceof OWLObjectIntersectionOf)
						checkIntersection(ce, sp);
					else
						complexCSubsumers.put(ce, sp);
					
				//	System.err.println("concept "+ce + " : "+ complexCSubsumers);
			  }
			}
		}
		
				////
				// subsumption - nominals
		else if(ce instanceof OWLObjectOneOf) {	
			subsumptionConcepts.add(df.getOWLThing());
			nominalSubsumers.put(ce, df.getOWLThing());
			//System.out.println("concept "+ce);
					if(!ontology.getAllSubsumers((OWLObjectOneOf)ce).isEmpty()) {
						for(OWLClassExpression sp : ontology.getAllSubsumers((OWLObjectOneOf)ce)) {
					//		System.out.println("subsumer "+sp);
							if(!sp.isOWLThing()) {
							if(sp instanceof OWLObjectOneOf) {
								tempNom.add((OWLObjectOneOf)sp);
								nominalDs.put((OWLObjectOneOf)sp, DependencySet.create());
								//subsumptionConcepts.add(sp);
								nominalSubsumers.put(ce, sp);
							}
							else if(sp instanceof OWLClass) {
								subsumptionConcepts.add(sp);
								nominalSubsumers.put(ce, sp);
							}
							if(sp instanceof OWLObjectComplementOf) {
								subsumptionConcepts.add(sp);
								nominalSubsumers.put(ce, sp);
							}
							else if(sp instanceof OWLObjectUnionOf) {
								if(sp.asDisjunctSet().stream().allMatch(dj -> (dj instanceof OWLObjectOneOf) || 
										(dj instanceof OWLClass) || (dj instanceof OWLObjectComplementOf))) {
									nominalSubsumers.put(ce, sp);
									for(OWLClassExpression c : sp.asDisjunctSet()) {
										if(c instanceof OWLObjectOneOf) {
											if(!nominalDs.containsKey(c)) {
												tempNom.add((OWLObjectOneOf)c);
												nominalDs.put((OWLObjectOneOf)c, DependencySet.create());
												addSubsumption(c);
											}
										}
										else if((c instanceof OWLClass) || (c instanceof OWLObjectComplementOf)) {
											if(!subsumptionConcepts.contains(c)) {
												subsumptionConcepts.add(c);
												addSubsumption(c);
											}
										}
										else
											subsumptionConcepts.add(c);
									}
								}
								else {
									complexNSubsumers.put(ce, sp);
								}
							}
							else if(sp instanceof OWLObjectIntersectionOf)
								checkIntersection(ce, sp);
							else {
								complexNSubsumers.put(ce, sp);
							}
						} 
						}
					}
		
		}
		
	}
	private SetMultimap<OWLObjectOneOf, DependencySet> getNominalDs() {
		return nominalDs;
	}
	private void checkIntersection(OWLClassExpression ce, OWLClassExpression sp) {
		if(ce instanceof OWLClass) {
			for(OWLClassExpression cj : sp.asConjunctSet()) {
				if(cj instanceof OWLObjectOneOf) {
					tempNom.add((OWLObjectOneOf)cj);
					nominalDs.put((OWLObjectOneOf)cj, DependencySet.create());
					subsumptionConcepts.add(cj);
					conceptSubsumers.put(ce, cj);
				}
				else if(cj instanceof OWLClass) {
					subsumptionConcepts.add(cj);
					conceptSubsumers.put(ce, cj);
				}
				else if(cj instanceof OWLObjectComplementOf) {
					subsumptionConcepts.add(cj);
					conceptSubsumers.put(ce, cj);
				}
				else if(cj instanceof OWLObjectUnionOf) {
					if(cj.asDisjunctSet().stream().allMatch(dj -> (dj instanceof OWLObjectOneOf) || (dj instanceof OWLClass) || (dj instanceof OWLObjectComplementOf))) {
						conceptSubsumers.put(ce, cj);
						for(OWLClassExpression c : cj.asDisjunctSet()) {
							if(c instanceof OWLObjectOneOf) {
								tempNom.add((OWLObjectOneOf)c);
								nominalDs.put((OWLObjectOneOf)c, DependencySet.create());
							}
						}
					}
					else {
						complexCSubsumers.put(ce, cj);
					}
				}
				else if(cj instanceof OWLObjectIntersectionOf)
					checkIntersection(ce, cj);
				else {
					complexCSubsumers.put(ce, cj);
				}
			}
		}
		else if(ce instanceof OWLObjectOneOf) {
			for(OWLClassExpression cj : sp.asConjunctSet()) {
				if(cj instanceof OWLObjectOneOf) {
					tempNom.add((OWLObjectOneOf)cj);
					nominalDs.put((OWLObjectOneOf)cj, DependencySet.create());
					subsumptionConcepts.add(cj);
					nominalSubsumers.put(ce, cj);
				}
				else if(cj instanceof OWLClass) {
					subsumptionConcepts.add(cj);
					nominalSubsumers.put(ce, cj);
				}
				else if(cj instanceof OWLObjectComplementOf) {
					subsumptionConcepts.add(cj);
					nominalSubsumers.put(ce, cj);
				}
				else if(cj instanceof OWLObjectUnionOf) {
					if(cj.asDisjunctSet().stream().allMatch(dj -> (dj instanceof OWLObjectOneOf) || (dj instanceof OWLClass) || (dj instanceof OWLObjectComplementOf))) {
						nominalSubsumers.put(ce, cj);
						for(OWLClassExpression c : cj.asDisjunctSet()) {
							if(c instanceof OWLObjectOneOf) {
								tempNom.add((OWLObjectOneOf)c);
								nominalDs.put((OWLObjectOneOf)c, DependencySet.create());
							}
						}
					}
					else {
						complexNSubsumers.put(ce, cj);
					}
				}
				else if(cj instanceof OWLObjectIntersectionOf)
					checkIntersection(ce, cj);
				else {
					complexNSubsumers.put(ce, cj);
				}
			}
		}
	}

	private void checkIntersection2(OWLClassExpression ce, OWLClassExpression sp) {
		if(ce instanceof OWLClass) {
			for(OWLClassExpression cj : sp.asConjunctSet()) {
				if(cj instanceof OWLObjectOneOf) {
					nominals.add((OWLObjectOneOf)cj);
					nominalDs.put((OWLObjectOneOf)cj, DependencySet.create());
					subsumptionConcepts.add(cj);
					conceptSubsumers.put(ce, cj);
				}
				else if(cj instanceof OWLClass) {
					simpleConcepts.add(cj);
					subsumptionConcepts.add(cj);
					conceptSubsumers.put(ce, cj);
				}
				else if(cj instanceof OWLObjectComplementOf) {
					simpleConcepts.add(cj);
					subsumptionConcepts.add(cj);
					conceptSubsumers.put(ce, cj);
				}
				else if(cj instanceof OWLObjectUnionOf) {
					if(cj.asDisjunctSet().stream().allMatch(dj -> (dj instanceof OWLObjectOneOf) || (dj instanceof OWLClass) || (dj instanceof OWLObjectComplementOf))) {
						conceptSubsumers.put(ce, cj);
						for(OWLClassExpression c : cj.asDisjunctSet()) {
							if(c instanceof OWLObjectOneOf) {
								nominals.add((OWLObjectOneOf)c);
								nominalDs.put((OWLObjectOneOf)c, DependencySet.create());
							}
							else if((c instanceof OWLClass)|| (c instanceof OWLObjectComplementOf)) {
								simpleConcepts.add(c);
							}
						}
					}
					else {
						complexCSubsumers.put(ce, cj);
					}
				}
				else if(cj instanceof OWLObjectIntersectionOf)
					checkIntersection2(ce, cj);
				else {
					complexCSubsumers.put(ce, cj);
				}
			}
		}
		else if(ce instanceof OWLObjectOneOf) {
			for(OWLClassExpression cj : sp.asConjunctSet()) {
				if(cj instanceof OWLObjectOneOf) {
					nominals.add((OWLObjectOneOf)cj);
					nominalDs.put((OWLObjectOneOf)cj, DependencySet.create());
					subsumptionConcepts.add(cj);
					nominalSubsumers.put(ce, cj);
				}
				else if(cj instanceof OWLClass) {
					simpleConcepts.add(cj);
					subsumptionConcepts.add(cj);
					nominalSubsumers.put(ce, cj);
				}
				else if(cj instanceof OWLObjectComplementOf) {
					simpleConcepts.add(cj);
					subsumptionConcepts.add(cj);
					nominalSubsumers.put(ce, cj);
				}
				else if(cj instanceof OWLObjectUnionOf) {
					if(cj.asDisjunctSet().stream().allMatch(dj -> (dj instanceof OWLObjectOneOf) || (dj instanceof OWLClass) || (dj instanceof OWLObjectComplementOf))) {
						nominalSubsumers.put(ce, cj);
						for(OWLClassExpression c : cj.asDisjunctSet()) {
							if(c instanceof OWLObjectOneOf) {
								nominals.add((OWLObjectOneOf)c);
								nominalDs.put((OWLObjectOneOf)c, DependencySet.create());
							}
							else if((c instanceof OWLClass) || (c instanceof OWLObjectComplementOf))  {
								simpleConcepts.add(c);
							}
						}
					}
					else {
						complexNSubsumers.put(ce, cj);
					}
				}
				else if(cj instanceof OWLObjectIntersectionOf)
					checkIntersection2(ce, cj);
				else {
					complexNSubsumers.put(ce, cj);
				}
			}
		}
	}
	
	public Set<OWLClassExpression> getAuxiliaryConcepts() {
		return auxiliaryConcepts;
	}
	public Set<OWLClassExpression> getComSubConcepts() {
		return this.complexCSubsumers.keySet();
	}
	public Set<OWLClassExpression> getComSubNom() {
		return this.complexNSubsumers.keySet();
	}
	public SetMultimap<OWLClassExpression, OWLClassExpression> getComplexASubsumers() {
		return complexASubsumers;
	}
	public SetMultimap<OWLObjectPropertyExpression, OWLClassExpression> getForAllMap() {
		return forAllMap;
	}
	public Set<OWLObjectAllValuesFrom> getForAllRes() {
		return forAllRes;
	}
	public Set<OWLSubObjectPropertyOfAxiom> getSubRoleAxioms() {
		return subRoleAxioms;
	}	
	public Map<Integer, OWLObjectCardinalityRestriction> getCRMap() {
		return crMap;
	}
	public Map<Integer, QCR> getQCRMap() {
		return qcrMap;
	}
	public Map<Integer, OWLClassExpression> getQCRQualifiersMap() {
		return qcrQualifiersMap;
	}
	public SetMultimap<OWLClassExpression, OWLObjectPropertyExpression> getQcrMultiMap() {
		return qcrMultiMap;
	}
	public List<OWLObjectCardinalityRestriction> getCardRes() {
		cardRes.addAll(minCardRes);
		cardRes.addAll(maxCardRes);
		return cardRes;
	}
	private SetMultimap<OWLObjectCardinalityRestriction, DependencySet> getCardResDs() {
		return cardResDs;
	}
	public void setCardRes(List<OWLObjectCardinalityRestriction> cardRes) {
		this.cardRes = cardRes;
	}
	public Set<QCR> getQcrs() {
		return qcrs;
	}
	public void setQcrs(Set<QCR> qcrs) {
		this.qcrs = qcrs;
	}
	public Set<OWLObjectOneOf> getNominals() {
		return nominals;
	}

	public void setNominals(Set<OWLObjectOneOf> nominals) {
		this.nominals = nominals;
	}

	public Set<OWLClassExpression> getComplexASubsumers(OWLClassExpression ce) {
		return this.complexASubsumers.get(ce);
	}
	public Set<OWLClassExpression> getComplexCSubsumers(OWLClassExpression ce) {
		return this.complexCSubsumers.get(ce);
	}
	public Set<OWLClassExpression> getComplexNSubsumers(OWLClassExpression ce) {
		return this.complexNSubsumers.get(ce);
	}

	public Set<OWLClassExpression> getAllDisjunctions() {
		SetMultimap<OWLClassExpression, OWLClassExpression> subsumers = HashMultimap.create();
		subsumers.putAll(conceptSubsumers);
		subsumers.putAll(nominalSubsumers);
		subsumers.putAll(simpleASubsumers);
		Set<OWLClassExpression> disjunctions = new HashSet<>();
		for(OWLClassExpression C : subsumers.asMap().keySet()) {
			for(OWLClassExpression D : subsumers.asMap().get(C)) {
				if(D instanceof OWLObjectUnionOf) {
					disjunctions.add(D);
				}
			}
		}
		return disjunctions;
	}
	public ILPSolution callILP() throws IloException {

		SetMultimap<OWLClassExpression, OWLClassExpression> subsumers = HashMultimap.create();
		SetMultimap<OWLClassExpression, OWLClassExpression> disjoints = HashMultimap.create();
		subsumers.putAll(conceptSubsumers);
		subsumers.putAll(nominalSubsumers);
		subsumers.putAll(simpleASubsumers);
	//	System.err.println(conceptSubsumers);
		//System.err.println("simpleASubsumers "+ simpleASubsumers);
		disjoints.putAll(conceptDisjoints);
		disjoints.putAll(nominalDisjoints);
		//this.sRMap = (Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>>) (Map<?, ?>) sR.asMap();
		CplexModelGenerator cmg = null;//new CplexModelGenerator(this, (Map<OWLClassExpression, Set<OWLClassExpression>>) (Map<?, ?>)subsumers.asMap(), this.binarySubsumers, disjoints, disjointGroups, this.sRMap, this.forAllMap, this.tempRoleH, this.topMinMap, this.topMaxMap);
		ILPSolution sol = cmg.getILPSolution();
		System.out.println("Solved: "+sol.isSolved());
		System.out.println("edges: "+sol.getEdgeInformation().size());
		for(EdgeInformation ei : sol.getEdgeInformation()) {
			/*Set<OWLClassExpression> temp = new HashSet<>();
			temp.addAll(ei.getFillers());
			for(OWLClassExpression ce : temp) {
				if(this.auxiliaryConcepts.contains(ce))
					ei.getFillers().addAll(this.complexASubsumers.get(ce));
			}
			ei.getFillers().removeAll(auxiliaryConcepts);*/
			System.out.println("Roles: " + ei.getEdges() +" Qualifications: " + ei.getFillers() +" cardinality : "+ ei.getCardinality());
		}
		return sol;
	}
	
}
