package reasoner; 

import java.io.File;
import java.io.FileNotFoundException;
import java.util.HashSet;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;
import java.util.stream.Collector;
import java.util.stream.Collectors;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.util.DefaultPrefixManager;


import reasoner.preprocessing.Internalization;
import reasoner.todolist.ToDoList;

public class TestReasoner{
	private static long startTime;
	ToDoList todo; 
	Internalization intr;
	OWLOntology ont;
	RuleEngine re;
	OWLDataFactory df;
	ReasonerFactory reasonerFactory;
	Reasoner reasoner ;
	OWLOntologyManager man ;
	DefaultPrefixManager prefixManager = new DefaultPrefixManager();
	Ontology ontology;
	Configuration config;
	// public TestReasoner(File file) {
	public TestReasoner() {
		 man = OWLManager.createOWLOntologyManager();
		// File file = new File("/Users/temp/Documents/PhD/PhD Research/OWL-API/SHOIQ-tests/newtests/ILP-Clash-con.owl");
		 File file = new File("/Users/temp/Documents/PhD/PhD Research/OWL-API/SHOIQ-tests/proxy-nodes-1.fowl.owl");
		 try {
			ont = man.loadOntologyFromOntologyDocument(file);
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		prefixManager.setDefaultPrefix(((IRI)ont.getOntologyID().getOntologyIRI().get()).toString());
		df = man.getOWLDataFactory();
	    reasonerFactory = new ReasonerFactory();
		todo = new ToDoList();
		intr = new Internalization(df);
		intr.setPrefixManager(prefixManager);
		reasoner = reasonerFactory.createReasoner(ont);
	    config = this.reasoner.getConfiguration();
	    ontology =  intr.internalize(ont);
		re = new RuleEngine(intr, todo, df, config);
	}
	 public static void getExecutionTime() {
			long endTime = System.currentTimeMillis();
	        System.out.println("It took " + (endTime - startTime) + " milliseconds");
		}
	public void useReasoner() throws OWLOntologyCreationException {
	     startTime = System.currentTimeMillis();
	       // intr.test(ont);
	     checkExpressivity();
	     
	     
	     Set<OWLObjectPropertyExpression> trans = getTransitiveRoles();
	      
	     
	     OWLClassExpression tgAxiom = intr.getTgAxiom();
	 //    for (OWLSubClassOfAxiom sbg : intr.getTg()) 
	   //  	 	System.out.println("TG: Subclass"+sbg.getSubClass() + " , SuperClass" + sbg.getSuperClass());
	 	    	 	
//	     for (OWLSubClassOfAxiom sbg : intr.getTui()) 
//	     	 	System.out.println("Tui: Subclass"+sbg.getSubClass() + " , SuperClass" + sbg.getSuperClass());
	 	  
	 	    
//	 	  for (OWLSubClassOfAxiom sbg : intr.getTu()) 
//	 	   	 	System.out.println("Tu: Subclass"+sbg.getSubClass() + " , SuperClass" + sbg.getSuperClass());
	     	 	
	 	  // System.out.println( tgAxiom);
	 	   re.setTransitiveRoles(trans);
	   if(tgAxiom !=null) {
	    		re.checkConsistency(tgAxiom);
		 	re.checkAboxConsistency(intr.getAboxClassAss(),tgAxiom);
	    }
	    else {
	    		re.checkAboxConsistency(intr.getAboxClassAss(),tgAxiom);
	    }
	    needAboxCheckAgain(tgAxiom);
	    System.out.println("Ontology is Consistent");
	    getExecutionTime();
	        man.removeOntology(ont);
	}
	public void needAboxCheckAgain( OWLClassExpression tgAxiom) {
		if(re.indLeft(intr.getAboxClassAss())) {
			re.checkAboxConsistency(intr.getAboxClassAss(),tgAxiom);
			needAboxCheckAgain(tgAxiom);
		}
		else
			return;
	}
	
	private Set<OWLObjectPropertyExpression> getTransitiveRoles() {
		Set<OWLObjectPropertyExpression> trans = new HashSet<>();
		for(OWLAxiom axiom : ont.axioms().filter(ax -> ax instanceof OWLTransitiveObjectPropertyAxiom).collect(Collectors.toSet()))
			trans.add(((OWLTransitiveObjectPropertyAxiom)axiom).getProperty());
		return trans;
	}
	public Ontology getOntology() {
		return ontology;
	}
	/**
	 * return (int)
	 *  0 -> unhandled ontology
	 * 
	 */
	private void checkExpressivity() {
		/*Set<OWLSubClassOfAxiom> sb = ont.axioms().filter(ax -> ax instanceof OWLSubClassOfAxiom).map(ax -> (OWLSubClassOfAxiom)ax).collect(Collectors.toSet());
		Set<OWLSubClassOfAxiom> eq = ont.axioms().filter(ax -> ax instanceof OWLEquivalentClassesAxiom).map(ax -> (OWLEquivalentClassesAxiom)ax).flatMap(ax -> ax.asOWLSubClassOfAxioms().stream()).collect(Collectors.toSet());
		Set<OWLSubClassOfAxiom> dj = ont.axioms().filter(ax -> ax instanceof OWLDisjointClassesAxiom).map(ax -> (OWLDisjointClassesAxiom)ax).flatMap(ax -> ax.asOWLSubClassOfAxioms().stream()).collect(Collectors.toSet());
		Set<OWLSubClassOfAxiom> dju = ont.axioms().filter(ax -> ax instanceof OWLDisjointUnionAxiom).map(ax -> (OWLDisjointUnionAxiom)ax).flatMap(ax -> ax.getOWLDisjointClassesAxiom().asOWLSubClassOfAxioms().stream()).collect(Collectors.toSet());
		sb.addAll(eq);
		sb.addAll(dj);
		sb.addAll(dju);
		if(sb.stream().anyMatch(s -> s.nestedClassExpressions().anyMatch(c -> c instanceof OWLObjectMaxCardinality || c instanceof OWLObjectMinCardinality))) {
			System.err.println("Reasoner cannot Proccess your Ontology. It contains Cardinatilty Restriction.");
			System.exit(0);
		}*/
		if(ont.axioms().anyMatch(ax -> ax instanceof OWLFunctionalObjectPropertyAxiom)) {
			System.err.println("Reasoner cannot Proccess your Ontology. It contains unhandled object property axioms.");
			getExecutionTime();
			System.exit(0);
		}
		boolean hasNominal = false;
		boolean hasQCRs = false;
		boolean hasInverseRoles = false;
		
		if(ont.axioms().anyMatch(ax -> ax.nestedClassExpressions().anyMatch(c -> c instanceof OWLObjectOneOf || c instanceof OWLObjectHasValue))) {
			hasNominal = true;
		}
			
		if(ont.axioms().anyMatch(ax -> ax.nestedClassExpressions().anyMatch(c -> c instanceof OWLObjectMaxCardinality || c instanceof OWLObjectMinCardinality))) {
			hasQCRs = true;
		}
				
		if(ont.axioms().anyMatch(ax -> ax instanceof OWLInverseObjectPropertiesAxiom) ) {
			hasInverseRoles = true;
		}
		else {
			Set<Set<OWLClassExpression>> sExp = new HashSet<>(); 
			ont.axioms().forEach(ax -> sExp.add(ax.nestedClassExpressions().
					filter(c -> c instanceof OWLObjectSomeValuesFrom || c instanceof OWLObjectAllValuesFrom || 
							c instanceof OWLObjectMinCardinality || c instanceof OWLObjectMaxCardinality || c instanceof OWLObjectHasValue).collect(Collectors.toSet())));
			
			if(!sExp.isEmpty()) {
				for(Set<OWLClassExpression> exp : sExp) {
					if(hasInverseRoles)
						break;
					for(OWLClassExpression e : exp) {
						
						if(e instanceof OWLObjectSomeValuesFrom) {
							if(((OWLObjectSomeValuesFrom)e).getProperty() instanceof OWLObjectInverseOf) {
								hasInverseRoles = true;
								break;
							}
						}
						else if(e instanceof OWLObjectAllValuesFrom) {
							if(((OWLObjectAllValuesFrom)e).getProperty() instanceof OWLObjectInverseOf) {
								hasInverseRoles = true;
								break;
							}
						}
						else if(e instanceof OWLObjectMinCardinality) {
							if(((OWLObjectMinCardinality)e).getProperty() instanceof OWLObjectInverseOf) {
								hasInverseRoles = true;
								break;
							}
						}
						else if(e instanceof OWLObjectMaxCardinality) {
							if(((OWLObjectMaxCardinality)e).getProperty() instanceof OWLObjectInverseOf) {
								hasInverseRoles = true;
								break;
							}
						}
						else if(e instanceof OWLObjectHasValue) {
							if(((OWLObjectHasValue)e).getProperty() instanceof OWLObjectInverseOf) {
								hasInverseRoles = true;
								break;
							}
						}
					}
				}
					
			}
		}
		
		if(hasNominal && hasQCRs && hasInverseRoles) {
			//System.err.println("SHOIQ");
			config.setSHOIQ(true);
			config.setUsePairwiseBlocking(true);
		}
		else if(hasNominal && hasQCRs && !hasInverseRoles) {
			//System.err.println("SHOQ");
			config.setSHOQ(true);
			config.setUseSubsetBlocking(true);
		}
		else if(hasNominal && !hasQCRs && hasInverseRoles) {
			//System.err.println("SHOI");
			config.setSHOI(true);
			config.setUseEqualityBlocking(true);
		}
		else if(!hasNominal && hasQCRs && hasInverseRoles) {
			//System.err.println("SHIQ");
			config.setSHIQ(true);
			config.setUsePairwiseBlocking(true);
		}
		else if(!hasNominal && !hasQCRs && hasInverseRoles) {
			//System.err.println("SHI");
			config.setSHI(true);
			config.setUseEqualityBlocking(true);
		}
		else if(hasNominal && !hasQCRs && !hasInverseRoles) {
			//System.err.println("SHO");
			config.setSHO(true);
			config.setUseSubsetBlocking(true);
		}
		else if(!hasNominal && hasQCRs && !hasInverseRoles) {
			//System.err.println("SHQ");
			config.setSHQ(true);
			config.setUseSubsetBlocking(true);
		}
		else if(!hasNominal && !hasQCRs && !hasInverseRoles){
			//System.err.println("ALC");
			config.setALC(true);
			config.setUseSubsetBlocking(true);
		}
		
	}
	

}

