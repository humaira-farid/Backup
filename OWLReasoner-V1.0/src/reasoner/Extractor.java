package reasoner;

import java.util.*;
import java.util.stream.Stream;

import org.semanticweb.owlapi.model.*;

public class Extractor {
 
	public Map<OWLClassExpression,Set<OWLClassExpression>> getSuperclasses(OWLOntology ont){
		Map<OWLClassExpression,Set<OWLClassExpression>> superClasses = new HashMap<OWLClassExpression,Set<OWLClassExpression>>();
		for (OWLClass c : (Iterable<OWLClass>)ont.classesInSignature()::iterator) {
	    	 	Set<OWLClassExpression> sup = new HashSet<OWLClassExpression>();
	    	 	for (OWLSubClassOfAxiom subAx : (Iterable<OWLSubClassOfAxiom>)ont.subClassAxiomsForSubClass(c)::iterator) 
		    	 	sup.add(subAx.getSuperClass());
	    	 	superClasses.put(c, sup);
	     }
	     return superClasses;
	}
	public Map<OWLClassExpression,Set<OWLClassExpression>> getSubclasses(OWLOntology ont){
		 Map<OWLClassExpression,Set<OWLClassExpression>> subClasses = new HashMap<OWLClassExpression,Set<OWLClassExpression>>();
	     for (OWLClass c : (Iterable<OWLClass>)ont.classesInSignature()::iterator) {
	    	 	Set<OWLClassExpression> sub = new HashSet<OWLClassExpression>();
	    	 	for (OWLSubClassOfAxiom subAx : (Iterable<OWLSubClassOfAxiom>)ont.subClassAxiomsForSuperClass(c)::iterator) 
		    	 	sub.add(subAx.getSubClass());
	    	 	subClasses.put(c, sub);
	     }
	     return subClasses;
	}
	public Set<OWLClassExpression> getSuperclasses(OWLClass cls, OWLOntology ont){
		Set<OWLClassExpression> sup = new HashSet<OWLClassExpression>();
	    	for (OWLSubClassOfAxiom subAx : (Iterable<OWLSubClassOfAxiom>)ont.subClassAxiomsForSubClass(cls)::iterator) 
		    	sup.add(subAx.getSuperClass());
	    	 	
	     return sup;
	}
	public Set<OWLClassExpression> getSubclasses(OWLClass cls, OWLOntology ont){
		Set<OWLClassExpression> sub = new HashSet<OWLClassExpression>();
	    	for (OWLSubClassOfAxiom subAx : (Iterable<OWLSubClassOfAxiom>)ont.subClassAxiomsForSuperClass(cls)::iterator) 
		    	sub.add(subAx.getSubClass());
	    	 	
	     return sub;
	}
	
	
	///// get superclasses for every class expression: not allowed  
	public Map<OWLClassExpression,Set<OWLClassExpression>> getSuperclassesEx(OWLOntology ont){
		Stream<OWLSubClassOfAxiom> sp;
		Stream<OWLClassExpression> classes = ont.nestedClassExpressions();
	     Map<OWLClassExpression,Set<OWLClassExpression>> superClasses = new HashMap<OWLClassExpression,Set<OWLClassExpression>>();
	     for (OWLClassExpression c : (Iterable<OWLClassExpression>)classes::iterator) {
	    	 	sp = ont.subClassAxiomsForSubClass((OWLClass) c);// I cannot cast in this way: java.lang.ClassCastException
	    	 	Set<OWLClassExpression> sup = new HashSet<OWLClassExpression>();
	    	 	for (OWLSubClassOfAxiom subAx : (Iterable<OWLSubClassOfAxiom>)sp::iterator) 
		    	 	sup.add(subAx.getSuperClass());
	    	 	superClasses.put(c, sup);
	     }
	     return superClasses;
	}
	public Map<OWLClassExpression,Set<OWLClassExpression>> getEquivalentclasses(OWLOntology ont){
		Map<OWLClassExpression,Set<OWLClassExpression>> equiClasses = new HashMap<OWLClassExpression,Set<OWLClassExpression>>();
	     for (OWLClass c : (Iterable<OWLClass>)ont.classesInSignature()::iterator) {
	    	 	Set<OWLClassExpression> eq = new HashSet<OWLClassExpression>();
	    	 	for (OWLEquivalentClassesAxiom eqAx : (Iterable<OWLEquivalentClassesAxiom>)ont.equivalentClassesAxioms(c)::iterator) 
		    	 	eq.addAll(eqAx.getClassExpressions());
	
	    	 	eq.remove(c);
	    	 	equiClasses.put(c, eq);
	     }
	     return equiClasses;
	}
	public Map<OWLClassExpression,Set<OWLClassExpression>> getDisjointclasses(OWLOntology ont){
		Map<OWLClassExpression,Set<OWLClassExpression>> disjointClasses = new HashMap<OWLClassExpression,Set<OWLClassExpression>>();
	     for (OWLClass c : (Iterable<OWLClass>)ont.classesInSignature()::iterator) {
	    	 	Set<OWLClassExpression> dj = new HashSet<OWLClassExpression>();
	    	 	for (OWLDisjointClassesAxiom djAx : (Iterable<OWLDisjointClassesAxiom>)ont.disjointClassesAxioms(c)::iterator) 
		    	 	dj.addAll(djAx.getClassExpressions());
	    	 	dj.remove(c); // A is disjoint to B, then only add B in set, remove A from set
	    	 	disjointClasses.put(c, dj);
	     }
	     return disjointClasses;
	}
	
	
}
