package reasoner.ilp;

import java.util.*;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.util.DefaultPrefixManager;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;

import ilog.concert.IloException;
import reasoner.Ontology;
import reasoner.Dependencies.DependencySet;
import reasoner.graph.CompletionGraph;
import reasoner.graph.Edge;
import reasoner.graph.Node;
import reasoner.preprocessing.Internalization;
import reasoner.todolist.ToDoEntry;

public class ILPPreprocessor {
	
	List<OWLObjectCardinalityRestriction> cardRes = new ArrayList<>();
	Set<OWLObjectSomeValuesFrom> exists = new HashSet<>();
	Set<OWLObjectHasValue> hasValue = new HashSet<>();
	Set<OWLSubClassOfAxiom> auxiliarySubAx = new HashSet<>();
	Set<OWLClassExpression> auxiliaryConcepts = new HashSet<>();
	Set<OWLObjectPropertyExpression> auxiliaryRoles = new HashSet<>();
	Set<OWLClassExpression> subsumptionConcepts = new HashSet<>();
	Set<OWLObjectOneOf> tempNom = new HashSet<>();
	Set<OWLObjectOneOf> tempSimple = new HashSet<>();
	SetMultimap<OWLClassExpression, OWLClassExpression> conceptSubsumers = HashMultimap.create();
	Map<OWLClassExpression, Set<OWLClassExpression>> binarySubsumers = new HashMap<>();
	SetMultimap<OWLClassExpression, OWLClassExpression> conceptDisjoints = HashMultimap.create();
	SetMultimap<OWLClassExpression, OWLClassExpression> nominalSubsumers = HashMultimap.create();
	SetMultimap<OWLClassExpression, OWLClassExpression> nominalDisjoints = HashMultimap.create();
	SetMultimap<OWLClassExpression, OWLClassExpression> simpleASubsumers = HashMultimap.create();
	SetMultimap<OWLClassExpression, OWLClassExpression> complexASubsumers = HashMultimap.create();
	SetMultimap<OWLClassExpression, OWLClassExpression> extraSubsumers = HashMultimap.create();
	SetMultimap<OWLObjectPropertyExpression, OWLObjectPropertyExpression> auxRoleH = HashMultimap.create();

	Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> auxRoleHMap = new HashMap<>();
	SetMultimap<OWLClassExpression, DependencySet> conceptDs = HashMultimap.create();
	SetMultimap<OWLObjectOneOf, DependencySet> nominalDs = HashMultimap.create();
	SetMultimap<OWLSubClassOfAxiom, DependencySet> auxiliarySubAxDs = HashMultimap.create();
	SetMultimap<OWLObjectCardinalityRestriction, DependencySet> cardResDs = HashMultimap.create();
	SetMultimap<OWLObjectSomeValuesFrom, DependencySet> existsDs = HashMultimap.create();
	SetMultimap<OWLObjectHasValue, DependencySet> hasValueDs = HashMultimap.create();
	
	Set<Set<OWLClassExpression>> disjointGroups = new HashSet<>();
	Set<QCR> qcrs = new HashSet<>();
	Map<Integer, OWLObjectCardinalityRestriction> crMap = new HashMap<Integer, OWLObjectCardinalityRestriction>();
	Map<Integer, QCR> qcrMap = new HashMap<Integer, QCR>();
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
	
	Set<OWLObjectAllValuesFrom> forAllRes = new HashSet<>();

	Set<OWLSubObjectPropertyOfAxiom> subRoleAxioms = new HashSet<>();
	
	DefaultPrefixManager prefixManager;
	Ontology ontology;
	String base = null;
	Node currNode;
	Set<Edge> outgoingEdges;
	
/*	public ILPPreprocessor() {
		df = man.getOWLDataFactory();
		OWLObjectProperty r = df.getOWLObjectProperty(IRI.create(base+"#R"));
		OWLObjectProperty t = df.getOWLObjectProperty(IRI.create(base+"#T"));
		OWLObjectProperty u = df.getOWLObjectProperty(IRI.create(base+"#U"));
		OWLObjectProperty s = df.getOWLObjectProperty(IRI.create(base+"#S"));
		OWLObjectProperty w = df.getOWLObjectProperty(IRI.create(base+"#W"));
		OWLClassExpression c1 = df.getOWLClass(IRI.create(base+"#C1"));
		OWLClassExpression c2 = df.getOWLClass(IRI.create(base+"#C2"));
		OWLClassExpression c3 = df.getOWLClass(IRI.create(base+"#C3"));
		OWLClassExpression c4 = df.getOWLClass(IRI.create(base+"#C4"));
		OWLClassExpression c5 = df.getOWLClass(IRI.create(base+"#C5"));
		OWLClassExpression c6 = df.getOWLClass(IRI.create(base+"#C6"));
		OWLClassExpression c7 = df.getOWLClass(IRI.create(base+"#C7"));
		OWLObjectOneOf o1 = df.getOWLObjectOneOf(df.getOWLNamedIndividual(IRI.create(base+"#o")));
		
		OWLObjectAllValuesFrom forAll = df.getOWLObjectAllValuesFrom(r, c7);
		OWLObjectAllValuesFrom forAll2 = df.getOWLObjectAllValuesFrom(s, c6);
		OWLObjectAllValuesFrom forAll3 = df.getOWLObjectAllValuesFrom(t, c5);
		OWLSubObjectPropertyOfAxiom subRoleAx = df.getOWLSubObjectPropertyOfAxiom(r, t);
		OWLSubObjectPropertyOfAxiom subRoleAx1 = df.getOWLSubObjectPropertyOfAxiom(t, s);
		
		OWLSubObjectPropertyOfAxiom subRoleAx2 = df.getOWLSubObjectPropertyOfAxiom(t, w);
		
		forAllRes.add(forAll);
		forAllRes.add(forAll2);

		forAllRes.add(forAll3);
		subRoleAxioms.add(subRoleAx);
		subRoleAxioms.add(subRoleAx1);
		OWLObjectCardinalityRestriction cr1 = df.getOWLObjectMinCardinality(1, r, c1);
		OWLObjectCardinalityRestriction cr2 = df.getOWLObjectMinCardinality(1, r, c2);
		OWLObjectCardinalityRestriction cr3 = df.getOWLObjectMinCardinality(1, t, c3);
		OWLObjectCardinalityRestriction cr4 = df.getOWLObjectMinCardinality(1, t, c4);
		OWLObjectCardinalityRestriction cr5 = df.getOWLObjectMinCardinality(1, r, c5);
		OWLObjectCardinalityRestriction cr6 = df.getOWLObjectMinCardinality(1, r, c6);
		OWLObjectCardinalityRestriction cr7 = df.getOWLObjectMaxCardinality(6, r, c7);
		
		OWLObjectCardinalityRestriction cr8 = df.getOWLObjectMinCardinality(1, r, df.getOWLClass(IRI.create(base+"#H")));
		OWLObjectIntersectionOf in = df.getOWLObjectIntersectionOf(cr1,forAll3);
		
		//OWLObjectCardinalityRestriction cr9 = df.getOWLObjectMinCardinality(1, df.getOWLObjectProperty(IRI.create(base+"#R")), df.getOWLClass(IRI.create(base+"#I")));
		//OWLObjectCardinalityRestriction cr10 = df.getOWLObjectMinCardinality(1, df.getOWLObjectProperty(IRI.create(base+"#R")), df.getOWLClass(IRI.create(base+"#J")));
		
		cardRes.add(cr1);
		cardRes.add(cr2);
		cardRes.add(cr3);
		cardRes.add(cr4);
//		cardRes.add(cr5);
//		cardRes.add(cr6);
//		cardRes.add(cr7);
	//	cardRes.add(cr8);
		//nominals.add(o1);
	//	cardRes.add(cr9);
	//	cardRes.add(cr10);
		
		
		
		createMaps();
		/*
		 * add all qcrs in cardRes
		 * add all nominals in nominals
		 * if(c instanceof OWLObjectHasValue) // nominal 
		 * if(c instanceof OWLObjectSomeValuesFrom)--- filler instanceof OWLObjectOneOf || instanceof OWLObjectUnionOf && 
		    							((OWLObjectUnionOf)((OWLObjectSomeValuesFrom)(sax).getSubClass()).getFiller()).disjunctSet().anyMatch(dj -> dj instanceof OWLObjectOneOf))))
		 * if(c instanceof OWLObjectAllValuesFrom)---filler instanceof OWLObjectOneOf || above
		 *
	}*/
	
	public ILPPreprocessor(ToDoEntry entry, Internalization intl, OWLDataFactory df, Node n) {
		counter = 0;
		this.df = df;
		this.currNode = n;
		this.prefixManager = intl.getPrefixManager();
		this.ontology = intl.getOntology();
		this.base = this.prefixManager.getDefaultPrefix();
		//this.superRoles = ontology.getSuperRoles();
		this.superRolesMap = ontology.getSuperRolesMap();
		processEntry(entry);
		generateQCR();
		processConcepts();
		createMaps();
	}
	public ILPPreprocessor(List<ToDoEntry> entries, Internalization intl, OWLDataFactory df, Node n, Set<Edge> outgoingEdges) {
		counter = 0;
		this.df = df;
		this.currNode = n;
		this.outgoingEdges= outgoingEdges;
		this.prefixManager = intl.getPrefixManager();
		this.ontology = intl.getOntology();
		this.base = this.prefixManager.getDefaultPrefix();
		//this.superRoles = ontology.getSuperRoles();
		this.superRolesMap = ontology.getSuperRolesMap();
		for(ToDoEntry entry : entries)
			processEntry(entry);
		generateQCR();
		createForAllMap();
		
		processConcepts();
		
		createMaps();
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
						//System.out.println(" disjunct "+ c);
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
			else if(sb.getSuperClass() instanceof OWLObjectAllValuesFrom) {
				this.complexASubsumers.put(sb.getSubClass(), sb.getSuperClass());
			}
			else if(sb.getSuperClass() instanceof OWLObjectHasValue) {
				this.complexASubsumers.put(sb.getSubClass(), sb.getSuperClass());
			}
		}
	
	}

	private void processConcepts2() {
		for(OWLSubClassOfAxiom sb : this.auxiliarySubAx) {
			if(sb.getSuperClass() instanceof OWLObjectOneOf) {
				this.simpleASubsumers.put(sb.getSubClass(), sb.getSuperClass());
				nominals.add((OWLObjectOneOf)sb.getSuperClass());
			}
			else if(sb.getSuperClass() instanceof OWLClass) {
				this.simpleASubsumers.put(sb.getSubClass(), sb.getSuperClass());
				simpleConcepts.add(sb.getSuperClass());
			}
			else if(sb.getSuperClass() instanceof OWLObjectIntersectionOf) {
				addIntersectionConcepts(sb.getSubClass(), sb.getSuperClass(), null);
			}
			else if(sb.getSuperClass() instanceof OWLObjectUnionOf) {
				if(sb.getSuperClass().asDisjunctSet().stream().allMatch(dj -> (dj instanceof OWLObjectOneOf) || (dj instanceof OWLClass) || (dj instanceof OWLObjectComplementOf))) {
					this.simpleASubsumers.put(sb.getSubClass(), sb.getSuperClass());
					for(OWLClassExpression c : sb.getSuperClass().asDisjunctSet()) {
						if(c instanceof OWLObjectOneOf) {
							nominals.add((OWLObjectOneOf)c);
						}
						else if((c instanceof OWLClass) || (c instanceof OWLObjectComplementOf)) {
							simpleConcepts.add(c);
						}
					}
				}
				else
					this.complexASubsumers.put(sb.getSubClass(), sb.getSuperClass());
			}
			else if(sb.getSuperClass() instanceof OWLObjectSomeValuesFrom) {
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

	private void processEntry(ToDoEntry entry) {
		
		OWLClassExpression ce = entry.getClassExpression();
		DependencySet ds = entry.getDs();
		/*if(ce instanceof OWLObjectIntersectionOf) {
			processIntersection(ce);
			
		}
		else*/
		if(ce instanceof OWLObjectSomeValuesFrom) {
			//exists.add((OWLObjectSomeValuesFrom)ce);
			existsDs.put((OWLObjectSomeValuesFrom)ce, ds);
		}
		else if(ce instanceof OWLObjectHasValue) {
			//hasValue.add((OWLObjectHasValue)ce);
			hasValueDs.put((OWLObjectHasValue)ce, ds);
		}
		else if(ce instanceof OWLObjectAllValuesFrom) {
			processForAll((OWLObjectAllValuesFrom)ce, ds);
		}
	
	}

/*	private void processIntersection(OWLClassExpression ce) {
		for(OWLClassExpression c : ce.asConjunctSet()) {
			if(c instanceof OWLObjectUnionOf) {
				processDisjunction(c);
			}
			else if(c instanceof OWLObjectSomeValuesFrom) {
				exists.add((OWLObjectSomeValuesFrom)c);
			}
			else if(c instanceof OWLObjectHasValue) {
				hasValue.add((OWLObjectHasValue)ce);
			}
			else if(c instanceof OWLObjectAllValuesFrom) {
				processForAll((OWLObjectAllValuesFrom)c);
			}
			else if(c instanceof OWLObjectIntersectionOf) {
				processIntersection(c);
			}
		}
		
	}*/


	private void processForAll(OWLObjectAllValuesFrom c, DependencySet ds) {
		//this.forAllRes.add((OWLObjectAllValuesFrom)c);
		OWLClassExpression filler = c.getFiller();
		if(filler instanceof OWLObjectOneOf) {
			nominals.add((OWLObjectOneOf)filler);
			nominalDs.put((OWLObjectOneOf)filler, ds);
			conceptDs.put(filler, ds);
			this.forAllRes.add(c);
		}
		else if(filler instanceof OWLClass) {
			simpleConcepts.add(c.getFiller());
			conceptDs.put(filler, ds);
			this.forAllRes.add(c);
		}

		else if(filler instanceof OWLObjectComplementOf) {
			simpleConcepts.add(c.getFiller());
			conceptDs.put(filler, ds);
			this.forAllRes.add(c);
		}
		else if(filler instanceof OWLObjectIntersectionOf) {
			OWLClassExpression qualifier = df.getOWLClass("#aux_" + ++counter, prefixManager);
			auxiliaryConcepts.add(qualifier);
			for(OWLClassExpression cj : filler.asConjunctSet()) {
				this.auxiliarySubAx.add(df.getOWLSubClassOfAxiom(qualifier, cj));
				auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, cj), ds);
				conceptDs.put(cj, ds);
			}
			this.forAllRes.add(df.getOWLObjectAllValuesFrom(c.getProperty(), qualifier));
		}
		else if(filler instanceof OWLObjectUnionOf) {
			OWLClassExpression qualifier = df.getOWLClass("#aux_" + ++counter, prefixManager);
			auxiliaryConcepts.add(qualifier);
			for(OWLClassExpression dj : filler.asDisjunctSet()) {
				conceptDs.put(dj, ds);
			}
			this.auxiliarySubAx.add(df.getOWLSubClassOfAxiom(qualifier, filler));
			auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
			this.forAllRes.add(df.getOWLObjectAllValuesFrom(c.getProperty(), qualifier));
		}
		else if(filler instanceof OWLObjectAllValuesFrom) {
			OWLClassExpression qualifier = df.getOWLClass("#aux_" + ++counter, prefixManager);
			auxiliaryConcepts.add(qualifier);
			conceptDs.put(filler, ds);
			this.auxiliarySubAx.add(df.getOWLSubClassOfAxiom(qualifier, filler));
			auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
			this.forAllRes.add(df.getOWLObjectAllValuesFrom(c.getProperty(), qualifier));
		}
		else if(filler instanceof OWLObjectSomeValuesFrom) {
			OWLClassExpression qualifier = df.getOWLClass("#aux_" + ++counter, prefixManager);
			auxiliaryConcepts.add(qualifier);
			conceptDs.put(filler, ds);
			this.auxiliarySubAx.add(df.getOWLSubClassOfAxiom(qualifier, filler));
			auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
			this.forAllRes.add(df.getOWLObjectAllValuesFrom(c.getProperty(), qualifier));
		}
		
	}

/*	private void processDisjunction(OWLClassExpression c) {
		// TODO Auto-generated method stub
		
	}*/

	private void generateQCR() {
		for(OWLObjectSomeValuesFrom ex : this.existsDs.keySet()) {
			DependencySet ds = DependencySet.create();
			for(DependencySet d : this.existsDs.get(ex))
				ds.add(d);
			OWLClassExpression filler = ex.getFiller();
			OWLObjectPropertyExpression role = ex.getProperty();
			if(filler instanceof OWLObjectOneOf) {
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(1, role, filler);
				this.cardRes.add(cr);
				roles.add(role);
				cardResDs.put(cr, ds);
				nominals.add((OWLObjectOneOf)filler);
				nominalDs.put((OWLObjectOneOf)filler, ds);
				conceptDs.put(filler, ds);
			}
			else if(filler instanceof OWLClass) {
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(1, role, filler);
				this.cardRes.add(cr);
				cardResDs.put(cr, ds);
				roles.add(role);
				//this.cardRes.add(df.getOWLObjectMinCardinality(1, role, filler));
				simpleConcepts.add(filler);
				conceptDs.put(filler, ds);
			}
			else if(filler instanceof OWLObjectComplementOf) {
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(1, role, filler);
				this.cardRes.add(cr);
				cardResDs.put(cr, ds);
				roles.add(role);
				//this.cardRes.add(df.getOWLObjectMinCardinality(1, role, filler));
				simpleConcepts.add(filler);
				conceptDs.put(filler, ds);
			}
			else if(filler instanceof OWLObjectIntersectionOf) {
				OWLClassExpression qualifier = df.getOWLClass("#aux_" + ++counter, prefixManager);
				auxiliaryConcepts.add(qualifier);
				for(OWLClassExpression cj : filler.asConjunctSet()) {
					this.auxiliarySubAx.add(df.getOWLSubClassOfAxiom(qualifier, cj));
					auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, cj), ds);
					conceptDs.put(cj, ds);
				}
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(1, role, qualifier);
				this.cardRes.add(cr);
				cardResDs.put(cr, ds);
				roles.add(role);
				//filler.asConjunctSet().stream().forEach(cj -> this.auxiliarySubAx.add(df.getOWLSubClassOfAxiom(qualifier, cj)));
				//this.cardRes.add(df.getOWLObjectMinCardinality(1, role, qualifier));
			}
			else if(filler instanceof OWLObjectUnionOf) {
				OWLClassExpression qualifier = df.getOWLClass("#aux_" + ++counter, prefixManager);
				auxiliaryConcepts.add(qualifier);
				for(OWLClassExpression dj : filler.asDisjunctSet()) {
					conceptDs.put(dj, ds);
				}
				this.auxiliarySubAx.add(df.getOWLSubClassOfAxiom(qualifier, filler));
				auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(1, role, qualifier);
				this.cardRes.add(cr);
				cardResDs.put(cr, ds);
				roles.add(role);
				//this.cardRes.add(df.getOWLObjectMinCardinality(1, role, qualifier));
			}
			else if(filler instanceof OWLObjectAllValuesFrom) {
				OWLClassExpression qualifier = df.getOWLClass("#aux_" + ++counter, prefixManager);
				auxiliaryConcepts.add(qualifier);
				conceptDs.put(filler, ds);
				this.auxiliarySubAx.add(df.getOWLSubClassOfAxiom(qualifier, filler));
				auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(1, role, qualifier);
				this.cardRes.add(cr);
				cardResDs.put(cr, ds);
				roles.add(role);
				//this.cardRes.add(df.getOWLObjectMinCardinality(1, role, qualifier));
			}
			else if(filler instanceof OWLObjectSomeValuesFrom) {
				OWLClassExpression qualifier = df.getOWLClass("#aux_" + ++counter, prefixManager);
				auxiliaryConcepts.add(qualifier);
				conceptDs.put(filler, ds);
				this.auxiliarySubAx.add(df.getOWLSubClassOfAxiom(qualifier, filler));
				auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, filler), ds);
				OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(1, role, qualifier);
				this.cardRes.add(cr);
				cardResDs.put(cr, ds);
				roles.add(role);
				//this.cardRes.add(df.getOWLObjectMinCardinality(1, role, qualifier));
			}
		}
		for(OWLObjectHasValue hv : hasValueDs.keySet()) {
			DependencySet ds = DependencySet.create();
			for(DependencySet d : this.hasValueDs.get(hv))
				ds.add(d);
			OWLObjectPropertyExpression role = hv.getProperty();
			OWLIndividual ind = hv.getFiller();
			OWLObjectOneOf o = df.getOWLObjectOneOf(ind);
			nominals.add(o);
			nominalDs.put(o, ds);
			conceptDs.put(o, ds);
			OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(1, role, o);
			this.cardRes.add(cr);
			cardResDs.put(cr, ds);
			roles.add(role);
			//this.cardRes.add(df.getOWLObjectMinCardinality(1, role, o));
		}
		for(Edge e : outgoingEdges) {
			DependencySet ds = e.getDepSet();
			Set<OWLObjectPropertyExpression> eRoles = e.getLabel();
			Set<OWLClassExpression> fillers = e.getToNode().getLabel();
			OWLClassExpression qualifier = df.getOWLClass("#aux_" + ++counter, prefixManager);
			OWLObjectPropertyExpression role = df.getOWLObjectProperty("#auxRole_" + ++counter, prefixManager);
			auxiliaryConcepts.add(qualifier);
			auxiliaryRoles.add(role);
			for(OWLClassExpression c : fillers) {
				if((c instanceof OWLClass) || (c instanceof OWLObjectOneOf) || (c instanceof OWLObjectComplementOf)) {
					this.auxiliarySubAx.add(df.getOWLSubClassOfAxiom(qualifier, c));
					auxiliarySubAxDs.put(df.getOWLSubClassOfAxiom(qualifier, c), ds);
				}
				else {
					this.complexASubsumers.put(qualifier, c);
				}
			}
			for(OWLObjectPropertyExpression r : eRoles) {
				this.auxRoleH.put(role, r);
			}
			OWLObjectCardinalityRestriction cr = df.getOWLObjectMinCardinality(1, role, qualifier);
			this.cardRes.add(cr);
			cardResDs.put(cr, ds);
			roles.add(role);
		}
		this.auxRoleHMap = (Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>>) (Map<?, ?>) auxRoleH.asMap();
	}
	
	public void createForAllMap() {
		// add range restrictions
				/*for(OWLObjectPropertyExpression obj : roles) {
					if(!(ontology.getRoleRange(obj).isEmpty()))
						ontology.getRoleRange(obj).forEach(rr -> processForAll(rr, DependencySet.create()));
					
					if(superRolesMap.containsKey(obj)) { 
						for(OWLObjectPropertyExpression r : superRolesMap.get(obj)) {
							if(!(ontology.getRoleRange(r).isEmpty()))
								ontology.getRoleRange(r).forEach(rr -> processForAll(rr, DependencySet.create()));
						}
					}
				}*/
				
				// process forAll restrictions 
				//System.out.println("forAll pre "+getForAllRes().size());

		Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> tempSuperRolesMap = new HashMap<>(superRolesMap);
		tempSuperRolesMap.putAll(auxRoleHMap);
				int k=1;
				for(OWLObjectAllValuesFrom forAll : getForAllRes()) {
					boolean addForAll = false;
					OWLObjectPropertyExpression role = forAll.getProperty();
					if(roles.contains(role)){
						addForAll = true;
						if(!tempRoleH.containsKey(role)) {
							OWLObjectPropertyExpression rh = df.getOWLObjectProperty(IRI.create(base+"#H"+k));// create Helper Role
							tempRoleH.put(role, rh);
							k++;
							//System.out.println("1) role "+ role +"H role : "+rh);
							//addForAll = true;
							
							for(OWLObjectPropertyExpression r : tempSuperRolesMap.keySet()) {
								if(roles.contains(r)) {
									if(tempSuperRolesMap.get(r).contains(role)) {
										if(!tempRoleH.containsKey(r)) {
											OWLObjectPropertyExpression rh1 = df.getOWLObjectProperty(IRI.create(base+"#H"+k));
											tempRoleH.put(r, rh1);
											k++;
											//System.out.println("2) role "+ r +"H role : "+rh1);
											
										}
				
										sR.put(r, role);
										//addForAll = true;
									}
								}
							}
						}
					}
					
					else{
						for(OWLObjectPropertyExpression r : tempSuperRolesMap.keySet()) {
							if(roles.contains(r)) {
								if(tempSuperRolesMap.get(r).contains(role)) {
									if(!tempRoleH.containsKey(r)) {
										OWLObjectPropertyExpression rh = df.getOWLObjectProperty(IRI.create(base+"#H"+k));
										tempRoleH.put(r, rh);
										k++;
										//System.out.println("3) role "+ r +"H role : "+rh);
										
									}
									sR.put(r, role);
									addForAll = true;
								}
							}
						}
					}
					if(addForAll)	
						this.forAllMap.put(forAll.getProperty(), forAll.getFiller());
				}
				this.sRMap = (Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>>) (Map<?, ?>) sR.asMap();
	}
	
	
	
	private Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> getSuperRolesMap() {
		return superRolesMap;
	}
	private void setSuperRolesMap(Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> superRolesMap) {
		this.superRolesMap = superRolesMap;
	}
	public Set<OWLObjectPropertyExpression> getAuxiliaryRoles() {
		return auxiliaryRoles;
	}
	public Set<OWLObjectPropertyExpression> getAuxRoleHMap(OWLObjectPropertyExpression r) {
		return auxRoleHMap.get(r);
	}
	public void createMaps() {
		
		// add range restrictions
		/*for(OWLObjectPropertyExpression obj : roles) {
			if(!(ontology.getRoleRange(obj).isEmpty()))
				ontology.getRoleRange(obj).forEach(rr -> processForAll(rr, DependencySet.create()));
			
			if(superRolesMap.containsKey(obj)) { 
				for(OWLObjectPropertyExpression r : superRolesMap.get(obj)) {
					if(!(ontology.getRoleRange(r).isEmpty()))
						ontology.getRoleRange(r).forEach(rr -> processForAll(rr, DependencySet.create()));
				}
			}
		}*/
		
		// process forAll restrictions 
		//System.out.println("forAll pre "+getForAllRes().size());

		/*int k=1;
		for(OWLObjectAllValuesFrom forAll : getForAllRes()) {
			boolean addForAll = false;
			OWLObjectPropertyExpression role = forAll.getProperty();
			if(roles.contains(role)){
				if(!tempRoleH.containsKey(role)) {
					OWLObjectPropertyExpression rh = df.getOWLObjectProperty(IRI.create(base+"#H"+k));// create Helper Role
					tempRoleH.put(role, rh);
					k++;
					System.out.println("role "+ role +"H role : "+rh);
					addForAll = true;
					
					for(OWLObjectPropertyExpression r : superRolesMap.keySet()) {
						if(roles.contains(r)) {
							if(superRolesMap.get(r).contains(role)) {
								if(!tempRoleH.containsKey(r)) {
									OWLObjectPropertyExpression rh1 = df.getOWLObjectProperty(IRI.create(base+"#H"+k));
									tempRoleH.put(r, rh1);
									k++;
									//System.out.println("role "+ r +"H role : "+rh1);
									
								}
		
								sR.put(r, role);
								addForAll = true;
							}
						}
					}
				}
			}
			
			else{
				for(OWLObjectPropertyExpression r : superRolesMap.keySet()) {
					if(roles.contains(r)) {
						if(superRolesMap.get(r).contains(role)) {
							if(!tempRoleH.containsKey(r)) {
								OWLObjectPropertyExpression rh = df.getOWLObjectProperty(IRI.create(base+"#H"+k));
								tempRoleH.put(r, rh);
								k++;
								//System.out.println("role "+ r +"H role : "+rh);
								
							}
							sR.put(r, role);
							addForAll = true;
						}
					}
				}
			}
			if(addForAll)	
				this.forAllMap.put(forAll.getProperty(), forAll.getFiller());
		}
		this.sRMap = (Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>>) (Map<?, ?>) sR.asMap();
		*/
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
		for(OWLClassExpression ce : simpleConcepts) 
			addSubsumption(ce);
		for(OWLObjectOneOf o : nominals)
			addSubsumption(o);
		/*
		// subsumption- concepts
		
		for(OWLClassExpression ce : simpleConcepts) {
			System.out.println("concept "+ce);
			if(ontology.getAllSubsumers2(ce) != null) {
				for(OWLClassExpression sp : ontology.getAllSubsumers2(ce)) {
					System.out.println("subsumer "+sp);
					if(sp instanceof OWLObjectOneOf) {
						subsumptionConcepts.add(sp);
						nominals.add((OWLObjectOneOf)sp);
						nominalDs.put((OWLObjectOneOf)sp, DependencySet.create());
						conceptSubsumers.put(ce, sp);
					}
					else if(sp instanceof OWLClass) {
						subsumptionConcepts.add(sp);
						conceptSubsumers.put(ce, sp);
					}
					else if(sp instanceof OWLObjectUnionOf) {
						if(sp.asDisjunctSet().stream().allMatch(dj -> (dj instanceof OWLObjectOneOf) || (dj instanceof OWLClass) || (dj instanceof OWLObjectComplementOf))) {
							conceptSubsumers.put(ce, sp);
							for(OWLClassExpression c : sp.asDisjunctSet()) {
								subsumptionConcepts.add(c);
								if(c instanceof OWLObjectOneOf) {
									System.out.println("nominal added "+c);
									nominals.add((OWLObjectOneOf)c);
									nominalDs.put((OWLObjectOneOf)c, DependencySet.create());
								}
							}
						}
					}
					else if(sp instanceof OWLObjectIntersectionOf)
						checkIntersection(ce, sp);
				} 
			}
		}
		
		////
		// subsumption - nominals
		
		for(OWLObjectOneOf o : nominals) {
			System.out.println("concept "+o);
			if(!ontology.getAllSubsumers2(o).isEmpty()) {
				for(OWLClassExpression sp : ontology.getAllSubsumers2(o)) {
					System.out.println("subsumer "+sp);
					if(sp instanceof OWLObjectOneOf) {
						tempNom.add((OWLObjectOneOf)sp);
						nominalDs.put((OWLObjectOneOf)sp, DependencySet.create());
						subsumptionConcepts.add(sp);
						nominalSubsumers.put(o, sp);
					}
					else if(sp instanceof OWLClass) {
						subsumptionConcepts.add(sp);
						nominalSubsumers.put(o, sp);
					}
					else if(sp instanceof OWLObjectUnionOf) {
						if(sp.asDisjunctSet().stream().allMatch(dj -> (dj instanceof OWLObjectOneOf) || (dj instanceof OWLClass) || (dj instanceof OWLObjectComplementOf))) {
							nominalSubsumers.put(o, sp);
							for(OWLClassExpression c : sp.asDisjunctSet()) {
								if(c instanceof OWLObjectOneOf) {
									tempNom.add((OWLObjectOneOf)c);
									nominalDs.put((OWLObjectOneOf)c, DependencySet.create());
								}
							}
						}
					}
					else if(sp instanceof OWLObjectIntersectionOf)
						checkIntersection(o, sp);
				} 
			}
		}*/
		nominals.addAll(tempNom);
		
		Set<OWLClassExpression> concepts = new  HashSet<>(simpleConcepts);
		concepts.addAll(nominals);
		concepts.addAll(subsumptionConcepts);
		//concepts.stream().forEach(c -> System.out.println("concept "+c));
		this.disjointGroups = ontology.getDisjointGroups(concepts);
		this.binarySubsumers = ontology.getBinarySubsumption(concepts);
		int i = 0;
		for(OWLObjectCardinalityRestriction q : getCardResDs().keySet()) {
			//System.out.println("cardRes "+q);
			DependencySet ds = DependencySet.create();
			for(DependencySet d : getCardResDs().get(q))
				ds.add(d);
			crMap.put(i, q);
			//roles.add(q.getProperty());
			QCR qcr = new QCR(q,ds);
			qcrMap.put(i, qcr);
			qcrs.add(qcr);
			++i;
		}
		for(OWLObjectOneOf o : getNominalDs().keySet()) {
			//System.out.println("nominal "+o);
			DependencySet ds = DependencySet.create();
			for(DependencySet d : getNominalDs().get(o))
				ds.add(d);
			QCR qcr = new QCR(o,ds);
			qcrMap.put(i, qcr);
			qcrs.add(qcr);
			++i;
		}
		
	}
	

	private void addSubsumption(OWLClassExpression ce) {
		// subsumption- concepts
		if(ce instanceof OWLClass) {
			//System.out.println("concept "+ce);
			if(ontology.getAllSubsumers(ce) != null) {
				for(OWLClassExpression sp : ontology.getAllSubsumers(ce)) {
				  if(!sp.isOWLThing()) {
					//System.out.println("subsumer "+sp);
					if(sp instanceof OWLObjectOneOf) {
						//subsumptionConcepts.add(sp);
						nominals.add((OWLObjectOneOf)sp);
						nominalDs.put((OWLObjectOneOf)sp, DependencySet.create());
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
								else if(c instanceof OWLClass) {
									if(!subsumptionConcepts.contains(c)) {
										subsumptionConcepts.add(c);
										addSubsumption(c);
									}
								}
								else
									subsumptionConcepts.add(c);
							}
						}
					}
					else if(sp instanceof OWLObjectIntersectionOf)
						checkIntersection(ce, sp);
				} 
			  }
			}
		}
				////
				// subsumption - nominals
		if(ce instanceof OWLObjectOneOf) {	
			//System.out.println("concept "+ce);
					if(!ontology.getAllSubsumers((OWLObjectOneOf)ce).isEmpty()) {
						for(OWLClassExpression sp : ontology.getAllSubsumers((OWLObjectOneOf)ce)) {
							//System.out.println("subsumer "+sp);
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
										else if(c instanceof OWLClass) {
											if(!subsumptionConcepts.contains(c)) {
												subsumptionConcepts.add(c);
												addSubsumption(c);
											}
										}
										else
											subsumptionConcepts.add(c);
									}
								}
							}
							else if(sp instanceof OWLObjectIntersectionOf)
								checkIntersection(ce, sp);
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
				}
				else if(cj instanceof OWLObjectIntersectionOf)
					checkIntersection(ce, cj);
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
				}
				else if(cj instanceof OWLObjectIntersectionOf)
					checkIntersection(ce, cj);
			}
		}
	}

	public ILPSolution callILP() throws IloException {

		SetMultimap<OWLClassExpression, OWLClassExpression> subsumers = HashMultimap.create();
		SetMultimap<OWLClassExpression, OWLClassExpression> disjoints = HashMultimap.create();
		subsumers.putAll(conceptSubsumers);
		subsumers.putAll(nominalSubsumers);
		subsumers.putAll(simpleASubsumers);
		//System.out.println("simpleASubsumers "+ simpleASubsumers);
		disjoints.putAll(conceptDisjoints);
		disjoints.putAll(nominalDisjoints);
		CplexModelGenerator6 cmg = new CplexModelGenerator6(this, (Map<OWLClassExpression, Set<OWLClassExpression>>) (Map<?, ?>)subsumers.asMap(), this.binarySubsumers, disjoints, disjointGroups, this.sRMap, this.forAllMap, this.tempRoleH);
		ILPSolution sol = cmg.getILPSolution();
		System.out.println("Solved: "+sol.isSolved());
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
	
	public Set<OWLClassExpression> getAuxiliaryConcepts() {
		return auxiliaryConcepts;
	}

	public SetMultimap<OWLClassExpression, OWLClassExpression> getComplexASubsumers() {
		return complexASubsumers;
	}

	public void getSubsumers() {
		
	}
	public void getDisjoints() {
		
	}
	public void getDisjointGroups() {
		
	}
	public void getSuperRoles() {
		
	}
	
	/*public void createMaps() {
		int i = 0;
		for(OWLObjectCardinalityRestriction q : getCardRes()) {
			crMap.put(i, q);
			roles.add(q.getProperty());
			QCR qcr = new QCR(q);
			qcrMap.put(i, qcr);
			//System.out.println(i +"  "+ qcr.qualifier);
			qcrs.add(qcr);
			++i;
		}
		/*int k=1;
		for(OWLObjectProperty r : roles) {
			OWLObjectProperty rh = df.getOWLObjectProperty(IRI.create(base+"#H"+k));
			System.out.println("role "+ r +"H role : "+rh);
			tempRoleH.put(r, rh);
			k++;
		}*
		for(OWLObjectOneOf o : getNominals()) {
			QCR qcr = new QCR(o);
			qcrMap.put(i, qcr);
			qcrs.add(qcr);
			++i;
		}
		for(OWLSubObjectPropertyOfAxiom srAx : getSubRoleAxioms()) {
			this.superRoles.put(srAx.getSubProperty().getNamedProperty(), srAx.getSuperProperty().getNamedProperty());
		
		}
		this.superRolesMap = (Map<OWLObjectProperty, Set<OWLObjectProperty>>) (Map<?, ?>) superRoles.asMap();
		for(OWLSubObjectPropertyOfAxiom srAx : getSubRoleAxioms()) {
			for(OWLObjectProperty r : superRolesMap.keySet()) {
				if(superRolesMap.get(r).contains(srAx.getSubProperty().getNamedProperty())) {
					superRolesMap.get(r).add(srAx.getSuperProperty().getNamedProperty());
				}
			}
		}
		
		// process forAll restrictions 
		
		int k=1;
		for(OWLObjectAllValuesFrom forAll : getForAllRes()) {
			
			OWLObjectProperty role = forAll.getProperty().getNamedProperty();
			if(roles.contains(role)){
				if(!tempRoleH.containsKey(role)) {
					OWLObjectProperty rh = df.getOWLObjectProperty(IRI.create(base+"#H"+k));// create Helper Role
					tempRoleH.put(role, rh);
					k++;
					System.out.println("role "+ role +"H role : "+rh);
					
					for(OWLObjectProperty r : superRolesMap.keySet()) {
						if(superRolesMap.get(r).contains(role)) {
							if(!tempRoleH.containsKey(r)) {
								OWLObjectProperty rh1 = df.getOWLObjectProperty(IRI.create(base+"#H"+k));
								tempRoleH.put(r, rh1);
								k++;
								System.out.println("role "+ r +"H role : "+rh1);
								
							}

							sR.put(r, role);
						}
					}
				}
			}
			
			else{
				for(OWLObjectProperty r : superRolesMap.keySet()) {
					if(superRolesMap.get(r).contains(role)) {
						if(!tempRoleH.containsKey(r)) {
							OWLObjectProperty rh = df.getOWLObjectProperty(IRI.create(base+"#H"+k));
							tempRoleH.put(r, rh);
							k++;
							System.out.println("role "+ r +"H role : "+rh);
							
						}
						sR.put(r, role);
					}
				}
			}
				
			this.forAllMap.put(forAll.getProperty().getNamedProperty(), forAll.getFiller());
		}
		this.sRMap = (Map<OWLObjectProperty, Set<OWLObjectProperty>>) (Map<?, ?>) sR.asMap();
		
	}*/
	
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
	
	public List<OWLObjectCardinalityRestriction> getCardRes() {
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

	
	
	
}
