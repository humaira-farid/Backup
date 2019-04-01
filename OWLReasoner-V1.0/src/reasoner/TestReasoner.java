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
	// public TestReasoner(File file) {
	 public TestReasoner() {
		 man = OWLManager.createOWLOntologyManager();
		 File file = new File("/Users/temp/Documents/PhD/PhD Research/OWL-API/integer-only-1-nom-unsat.fowl.owl");
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
		re = new RuleEngine(intr, todo, df);
	}
	 public static void getExecutionTime() {
			long endTime = System.currentTimeMillis();
	        System.out.println("It took " + (endTime - startTime) + " milliseconds");
		}
	public void useReasoner() throws OWLOntologyCreationException {
		 
	     
		    
	     reasoner = reasonerFactory.createReasoner(ont);
	     startTime = System.currentTimeMillis();
	       // intr.test(ont);
	      checkExpressivity();
	      Set<OWLObjectPropertyExpression> trans = getTransitiveRoles();
	      
	     ontology =  intr.internalize(ont);
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
		if(re.indLeft(intr.getAboxClassAss())!=0) {
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
		if(ont.axioms().anyMatch(ax -> ax.nestedClassExpressions().anyMatch(c -> c instanceof OWLObjectMaxCardinality || c instanceof OWLObjectMinCardinality))) {
			System.err.println("Reasoner cannot Proccess your Ontology. It contains Cardinatilty Restriction.");
			getExecutionTime();
			System.exit(0);
		}
		if(ont.axioms().anyMatch(ax -> ax instanceof OWLFunctionalObjectPropertyAxiom)) {
			System.err.println("Reasoner cannot Proccess your Ontology. It contains unhandled object property axioms.");
			getExecutionTime();
			System.exit(0);
		}
	}
	

}

