package reasoner; 

import java.io.File;
import java.io.FileNotFoundException;
import java.util.HashSet;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;
import java.util.stream.Collectors;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.util.DefaultPrefixManager;


import reasoner.preprocessing.Internalization;
import reasoner.todolist.ToDoList;

public class TestReasoner{
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
	 public TestReasoner(/*File file*/) {
		 man = OWLManager.createOWLOntologyManager();
		 File file = new File("/Users/temp/Desktop/PhD/PhD Research/OWL-API/testOnt7_O_fun.owl");
		 try {
			ont = man.loadOntologyFromOntologyDocument(file);
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		prefixManager.setDefaultPrefix(((IRI)ont.getOntologyID().getOntologyIRI().get()).toString());
		df = man.getOWLDataFactory();
	    reasonerFactory = new ReasonerFactory();
		todo = new ToDoList();
		intr = new Internalization();
		intr.setPrefixManager(prefixManager);
		re = new RuleEngine(intr, todo, df);
	}
	
	public void useReasoner() throws OWLOntologyCreationException {
		 
	     
		    
	     reasoner = reasonerFactory.createReasoner(ont);
	       // intr.test(ont);
	      checkExpressivity();
	     ontology =  intr.internalize(ont, df);
	     OWLClassExpression tgAxiom = intr.getTgAxiom(df);
	    // for (OWLSubClassOfAxiom sbg : intr.getTg()) 
	    // 	 	System.out.println("TG: Subclass"+sbg.getSubClass() + " , SuperClass" + sbg.getSuperClass());
	 	    	 	
	  //   for (OWLSubClassOfAxiom sbg : intr.getTui()) 
	    // 	 	System.out.println("Tui: Subclass"+sbg.getSubClass() + " , SuperClass" + sbg.getSuperClass());
	 	  
	 	    
	 	  //for (OWLSubClassOfAxiom sbg : intr.getTu()) 
	 	//   	 	System.out.println("Tu: Subclass"+sbg.getSubClass() + " , SuperClass" + sbg.getSuperClass());
	     	 	
	 	//   System.out.println( tgAxiom);
	 	   
		re.checkAboxConsistency(intr.getAboxClassAss());
	 	re.checkConsistency(tgAxiom);
	    System.out.println("Ontology is Consistent");
	        
	        man.removeOntology(ont);
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
			Main.getExecutionTime();
			System.exit(0);
		}
		if(ont.axioms().anyMatch(ax -> ax instanceof OWLTransitiveObjectPropertyAxiom || ax instanceof OWLFunctionalObjectPropertyAxiom)) {
			System.err.println("Reasoner cannot Proccess your Ontology. It contains unhandled object property axioms.");
			Main.getExecutionTime();
			System.exit(0);
		}
		
	}

}

