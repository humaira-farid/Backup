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
import org.semanticweb.owlapi.reasoner.Node;


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
	 public TestReasoner(File file) {
		 man = OWLManager.createOWLOntologyManager();
		// File file = new File("/Users/temp/Desktop/PhD/PhD Research/OWL-API/testOnt5.owl");
		 try {
			ont = man.loadOntologyFromOntologyDocument(file);
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}
		 
		df = man.getOWLDataFactory();
	    reasonerFactory = new ReasonerFactory();
		todo = new ToDoList();
		intr = new Internalization();
		re = new RuleEngine(intr, todo, df);
	}
	
	public void useReasoner() throws OWLOntologyCreationException {
		 
	     
		    
	     reasoner = reasonerFactory.createReasoner(ont);
	     //reasoner.preprocess();
	     // Ask the reasoner to do all the necessary work now
	      reasoner.precomputeInferences();
	   //  Extractor ex = new Extractor();
	    
	    // String s = "ObjectIntersectionOf";
	     //intr.parseClassExpression(ont, s);
	    // intr.test(ont);
	      checkExpressivity();
	      intr.internalize(ont, df);
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
		if(ont.axioms().anyMatch(ax -> ax instanceof OWLTransitiveObjectPropertyAxiom || ax instanceof OWLSubObjectPropertyOfAxiom || ax instanceof OWLFunctionalObjectPropertyAxiom)) {
			System.err.println("Reasoner cannot Proccess your Ontology. It contains unhandled object property axioms.");
			Main.getExecutionTime();
			System.exit(0);
		}
		
}

/*	public void applyRules(ToDoEntry entry) {
		
		reasoner.graph.Node n = entry.getNode();
		NodeTag nt = entry.getType();
		switch(nt) {
		case AND:
			re.applyAndRule(n, (OWLObjectIntersectionOf)entry.getClassExpression(), entry.getDs());
			break;
		case OR:
			re.applyOrRule(n, (OWLObjectUnionOf)entry.getClassExpression(), entry.getDs());
			break;
		case EXISTS:
			re.applyExistentialRule(n, (OWLObjectSomeValuesFrom)entry.getClassExpression(), entry.getDs());
			break;
		case FORALL:
			re.applyForAllRule(n, (OWLObjectAllValuesFrom)entry.getClassExpression(), entry.getDs());
			break;
		default:
			break;
		}
		
	}*/
	 public void printSuperClasses(Map<OWLClassExpression,Set<OWLClassExpression>> sup) {
		 
		 for(OWLClassExpression c : sup.keySet()) {
			 System.out.println("Class " + c.toString() + " has superclasses :" + sup.get(c).toString());
		 }
	 }
	 public void printSubClasses(Map<OWLClassExpression,Set<OWLClassExpression>> sub) {
		 
		 for(OWLClassExpression c : sub.keySet()) {
			 System.out.println("Class " + c + " has subclasses :" + sub.get(c));
		 }
	 }
	 public void printEquivalentClasses(Map<OWLClassExpression,Set<OWLClassExpression>> eq) {
		 
		 for(OWLClassExpression c : eq.keySet()) {
			 System.out.println("Class " + c + " has Equivalent classes :" + eq.get(c));
		 }
	 }
	 public void printDisjointClasses(Map<OWLClassExpression,Set<OWLClassExpression>> dj) {
		 
		 for(OWLClassExpression c : dj.keySet()) {
			 System.out.println("Class " + c + " has Disjoint classes :" + dj.get(c));
		 }
	 }
	 public static Set<IRI> getIRIs(File file, String prefix) throws FileNotFoundException {
		    Set<IRI> iris = new HashSet<IRI>();
		    Scanner scanner = new Scanner(file);
		    while (scanner.hasNextLine()) {
		      String line = scanner.nextLine().trim();
		      if(!line.startsWith(prefix + "http")) { continue; }
		      String suffix = line.substring(prefix.length());
		      String iri = suffix.substring(0, Math.min(suffix.length(), suffix.indexOf(" ")));
		      System.out.println("<"+ iri +">");
		      iris.add(IRI.create(iri));
		    }
		    return iris;
		  }
	 
	 public void existential(OWLSubClassOfAxiom subAx) {
		 
		 if((subAx.getSuperClass() instanceof OWLObjectSomeValuesFrom)) {
			 System.out.println(((OWLObjectSomeValuesFrom)subAx.getSuperClass()).getProperty()+" . " +((OWLObjectSomeValuesFrom)subAx.getSuperClass()).getFiller());
		 }
		 if((subAx.getSuperClass() instanceof OWLClass)) {
			 System.out.println(((OWLObjectSomeValuesFrom)subAx.getSuperClass()).getComplementNNF()+" . " +((OWLObjectSomeValuesFrom)subAx.getSuperClass()).getFiller());
		 } 
	 }
	 public Set<Disjunct> createDisjuncts(Map<OWLClassExpression ,Set<OWLClassExpression>> sp, Map<OWLClassExpression,Set<OWLClassExpression>> eq, Map<OWLClassExpression,Set<OWLClassExpression>> dj) {
			Set<Disjunct> disjuncts = new HashSet<Disjunct>();
			for(OWLClassExpression l : sp.keySet()) {
				for(OWLClassExpression r : sp.get(l)) {
					Disjunct disj = new Disjunct(l.getComplementNNF(),r);
					disjuncts.add(disj);
				}
			 }
			for(OWLClassExpression l : eq.keySet()) {
				for(OWLClassExpression r : eq.get(l)) {
					Disjunct disj = new Disjunct(l.getComplementNNF(),r);
					Disjunct disj2 = new Disjunct(r.getComplementNNF(),l);
					disjuncts.add(disj);
					disjuncts.add(disj2);
				}
			 }
			for(OWLClassExpression l : dj.keySet()) {
				for(OWLClassExpression r : dj.get(l)) {
					Disjunct disj = new Disjunct(l.getComplementNNF(),r.getComplementNNF());
					disjuncts.add(disj);
				}
			 }
			return disjuncts;
		}
}

