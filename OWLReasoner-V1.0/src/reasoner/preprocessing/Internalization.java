package reasoner.preprocessing;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.util.DefaultPrefixManager;

import reasoner.Ontology;

public class Internalization {
	boolean prefixSet = false;
	private Set<OWLSubClassOfAxiom> Tu;
	private Set<OWLSubClassOfAxiom> Tui;
	private Set<OWLClassExpression> tuConcepts;
	private Set<OWLSubClassOfAxiom> Tg;
    Set<OWLSubClassOfAxiom> oneOfSubAx;
	private Set<OWLEquivalentClassesAxiom> Eq;
	private Set<OWLSubClassOfAxiom> oneOf;
	private Set<OWLSubClassOfAxiom> oneOfIn;
	//private Set<OWLSubClassOfAxiom> oneOfAll;
	private Set<OWLSubClassOfAxiom> hasValue;
	private Set<OWLSubClassOfAxiom> diffInd; 
	private Set<OWLSubClassOfAxiom> aboxClassAss;
	private Set<OWLSubClassOfAxiom> aboxObjProAss;
	private Set<OWLDisjointClassesAxiom> djAx;
	private Set<OWLDisjointUnionAxiom> djuAx;
    Set<OWLObjectPropertyRangeAxiom> objrAx = new HashSet<>();
    DefaultPrefixManager prefixManager = new DefaultPrefixManager();
	 
    Ontology ontology;
    OWLDataFactory df;
	Set<OWLObjectPropertyExpression> symmRoles = new HashSet<>();
    
	public Internalization(OWLDataFactory df){
		this.Tu = new HashSet<OWLSubClassOfAxiom>();
		this.Tui = new HashSet<OWLSubClassOfAxiom>();
		this.Tg = new HashSet<OWLSubClassOfAxiom>();
		this.tuConcepts = new HashSet<>();
		this.oneOfSubAx = new HashSet<>();
		this.Eq = new HashSet<OWLEquivalentClassesAxiom>();
		this.setOneOf(new HashSet<OWLSubClassOfAxiom>());
		this.setOneOfIn(new HashSet<OWLSubClassOfAxiom>());
		//this.setOneOfAll(new HashSet<OWLSubClassOfAxiom>());
		this.setHasValue(new HashSet<OWLSubClassOfAxiom>());
		diffInd = new HashSet<>();
		aboxClassAss = new HashSet<>();
		aboxObjProAss = new HashSet<>();
		djAx = new HashSet<>();
		djuAx = new HashSet<>();
		this.df = df;
		
	}
	public void test(OWLOntology ont) {
		for (OWLAxiom ax : (Iterable<OWLAxiom>)ont.axioms()::iterator) {
		    	ax = ax.getNNF();
		    if(ax instanceof OWLSubClassOfAxiom) {
		    		OWLSubClassOfAxiom sax = (OWLSubClassOfAxiom)ax;
		
				if((sax).getSubClass() instanceof OWLObjectIntersectionOf && ((OWLObjectIntersectionOf)(sax).getSubClass()).asConjunctSet().stream().allMatch(cj -> cj instanceof OWLClass)) {
					System.out.println(sax.getSubClass());
				}
		    }
	    }
	}
	
	public boolean handleQualifiedRangeRestriction(OWLClassExpression sub, OWLClassExpression sup) {
		OWLClassExpression filler = ((OWLObjectSomeValuesFrom)sub).getFiller();
		// --> R some A SubClassOf B -- OR -- R some A SubClassOf (B and C) 
		if(sup instanceof OWLClass || sup instanceof OWLObjectOneOf || (sup instanceof OWLObjectIntersectionOf && 
					((OWLObjectIntersectionOf)sup).conjunctSet().allMatch(cj -> (cj instanceof OWLClass) || (cj instanceof OWLObjectOneOf)))) {
			// --> if A is an instance of OWLClass
			if(filler instanceof OWLClass || filler.isOWLThing()) {
				OWLObjectPropertyExpression role = ((OWLObjectSomeValuesFrom)sub).getProperty();
				tuConcepts.add(filler);
				if(sup instanceof OWLClass || sup instanceof OWLObjectOneOf) {
					OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), sup);
	    				this.Tu.add(df.getOWLSubClassOfAxiom(filler, sp));
				}
				else if(sup instanceof OWLObjectIntersectionOf) {
					sup.asConjunctSet().forEach(cj -> this.Tu.add(df.getOWLSubClassOfAxiom(filler, 
							df.getOWLObjectAllValuesFrom(role.getInverseProperty(), cj))));
				}
				return true;
			}
			// --> if A is a nominal
			else if(filler instanceof OWLObjectOneOf) {
				OWLObjectPropertyExpression role = ((OWLObjectSomeValuesFrom)sub).getProperty();
				if(sup instanceof OWLClass || sup instanceof OWLObjectOneOf) {
					OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), sup);
				    	this.oneOfSubAx.add(df.getOWLSubClassOfAxiom(filler, sp));
				}
				else if(sup instanceof OWLObjectIntersectionOf) {
					sup.asConjunctSet().forEach(cj -> this.oneOfSubAx.add(df.getOWLSubClassOfAxiom(filler, 
							df.getOWLObjectAllValuesFrom(role.getInverseProperty(), cj))));
				}
				return true;
			}
			// --> if A is an instance of OWLObjectUnionOf 
			else if(filler instanceof OWLObjectUnionOf && filler.disjunctSet().allMatch(dj -> (dj instanceof OWLClass) || (dj instanceof OWLObjectOneOf))) {
				OWLObjectPropertyExpression role = ((OWLObjectSomeValuesFrom)sub).getProperty();
				if(sup instanceof OWLClass || sup instanceof OWLObjectOneOf) {
					OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), sup);
	    				for(OWLClassExpression ce : ((OWLObjectUnionOf)sub).asDisjunctSet()) {
	    					if(ce instanceof OWLClass) {
	    						tuConcepts.add(ce);
	    						this.Tu.add(df.getOWLSubClassOfAxiom(ce, sp));
	    					}
	    					else if(ce instanceof OWLObjectOneOf) {
	    						this.oneOfSubAx.add(df.getOWLSubClassOfAxiom(ce, sp));
	    					}
	    				}	
				}
				else if(sup instanceof OWLObjectIntersectionOf) {
					for(OWLClassExpression ce : ((OWLObjectIntersectionOf)sup).asConjunctSet()) {
	    					OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), ce);
	    					for(OWLClassExpression ce2 : ((OWLObjectUnionOf)sub).asDisjunctSet()) {
	    						if(ce2 instanceof OWLClass) {
		    						tuConcepts.add(ce2);
		    						this.Tu.add(df.getOWLSubClassOfAxiom(ce2, sp));
		    					}
		    					else if(ce2 instanceof OWLObjectOneOf) {
		    						this.oneOfSubAx.add(df.getOWLSubClassOfAxiom(ce2, sp));
		    					}
	    					}
					}
				}
				return true;
			}
			// --> if A is an instance of OWLObjectIntersectionOf 
			else if(filler instanceof OWLObjectIntersectionOf && filler.conjunctSet().allMatch(cj -> (cj instanceof OWLClass) || (cj instanceof OWLObjectOneOf))){
				OWLObjectPropertyExpression role = ((OWLObjectSomeValuesFrom)sub).getProperty();
				if(sup instanceof OWLClass || sup instanceof OWLObjectOneOf) {
					OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), sup);
					this.Tui.add(df.getOWLSubClassOfAxiom(filler, sp));
				}
				else if(sup instanceof OWLObjectIntersectionOf) {
					for(OWLClassExpression ce : ((OWLObjectIntersectionOf)sup).asConjunctSet()) {
	    					OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), ce);
	    					this.Tui.add(df.getOWLSubClassOfAxiom(filler, sp));
					}
				}
			}
			return true;
		}
				
		
		return false;
	}
	
	public boolean handleNominal(OWLClassExpression sub, OWLClassExpression sup) {
		if(sup instanceof OWLClass || sup instanceof OWLObjectOneOf || (sup instanceof OWLObjectIntersectionOf && 
				((OWLObjectIntersectionOf)sup).conjunctSet().allMatch(cj -> (cj instanceof OWLClass) || (cj instanceof OWLObjectOneOf)))) {					
			OWLIndividual ind = ((OWLObjectHasValue)sub).getFiller();
			OWLObjectPropertyExpression role = ((OWLObjectHasValue)sub).getProperty();
			OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), sup);
			OWLClassExpression sb = df.getOWLObjectOneOf(ind);
			oneOfSubAx.add(df.getOWLSubClassOfAxiom(sb, sp));
			return true;
		}
		return false;
	}
	public void processDisjunction(OWLClassExpression sub, OWLClassExpression sup) {
		for(OWLClassExpression ce : ((OWLObjectUnionOf)sub).asDisjunctSet()) {
			if(ce instanceof OWLObjectOneOf)
				oneOfSubAx.add(df.getOWLSubClassOfAxiom(ce, sup));
			else if(ce instanceof OWLClass) {
				tuConcepts.add(ce);
				if(sup instanceof OWLObjectIntersectionOf) {
					sup.asConjunctSet().forEach(cj -> this.Tu.add(df.getOWLSubClassOfAxiom(ce, cj)));
				}
				else
					this.Tu.add(df.getOWLSubClassOfAxiom(ce, sup));
			}
			else if(ce instanceof OWLObjectIntersectionOf && 
					ce.conjunctSet().allMatch(cj -> (cj instanceof OWLClass) || (cj instanceof OWLObjectOneOf))) {
				if(sup instanceof OWLObjectIntersectionOf) {
						sup.asConjunctSet().forEach(cj -> this.Tui.add(df.getOWLSubClassOfAxiom(ce, cj)));
					}
				else
					this.Tui.add(df.getOWLSubClassOfAxiom(ce, sup));
			}
			else if(ce instanceof OWLObjectSomeValuesFrom) {
				if(!handleQualifiedRangeRestriction(ce, sup)) {
					this.Tg.add(df.getOWLSubClassOfAxiom(ce, sup)); 
				}
			}	
			else if(ce instanceof OWLObjectHasValue) {
				if(!handleNominal(ce, sup)) {
					this.Tg.add(df.getOWLSubClassOfAxiom(ce, sup)); 
				}
			}	
			else
				this.Tg.add(df.getOWLSubClassOfAxiom(ce, sup)); 
		}
	}
	public Ontology internalize(OWLOntology ont) {
		
		Set<OWLSubClassOfAxiom> subAx = new HashSet<>();
		 Set<OWLEquivalentClassesAxiom> eqAx = new HashSet<>();
	    Set<OWLObjectPropertyDomainAxiom> objdAx = new HashSet<>();
	    Set<OWLEquivalentClassesAxiom> oneOfEqAx = new HashSet<>();
	    Set<OWLSubObjectPropertyOfAxiom> subObjProAx = new HashSet<>();
	    Set<OWLInverseObjectPropertiesAxiom> invObjProAx = new HashSet<>();
	    //Set<OWLSubClassOfAxiom> newSbAx = new HashSet<OWLSubClassOfAxiom>();
	    Set<OWLIndividual> individuals = new HashSet<>();
	    
	    for (OWLAxiom ax : (Iterable<OWLAxiom>)ont.axioms()::iterator) {
		   ax = ax.getNNF();
		  // System.err.println("ax"+ax);
		   if(!this.prefixSet) {
			   if(this.getPrefixManager().getDefaultPrefix().equals("")) {
				   try {
				   this.getPrefixManager().setDefaultPrefix(ax.toString().substring(ax.toString().indexOf("<")+1, ax.toString().indexOf("#")));
				  // System.err.println("ax added"+ ""+ ax.toString().substring(ax.toString().indexOf("<")+1, ax.toString().indexOf("#")) );
				   prefixSet = true;
				   }
				   catch(StringIndexOutOfBoundsException e) {
					   this.getPrefixManager().setDefaultPrefix("");
				   }
			   }
		   }
		//   System.err.println("ax "+ this.getPrefixManager().getDefaultPrefix());
			
			    // --> SubClassOf Axiom
		   if(ax instanceof OWLSubClassOfAxiom) {
			   OWLSubClassOfAxiom sax = (OWLSubClassOfAxiom)ax;
			   subAx.add(sax);
			   OWLClassExpression sub = sax.getSubClass();
			   OWLClassExpression sup = sax.getSuperClass();
			   
			   // --> A SubClassOf (ClassExpression)
			   if(sub instanceof OWLClass) {
				   tuConcepts.add(sub);
				   if(sup instanceof OWLObjectIntersectionOf)
					   sup.asConjunctSet().forEach(cj -> this.Tu.add(df.getOWLSubClassOfAxiom(sub, cj)));
				   else
					   this.Tu.add(sax);
				}
				// --> o SubClassOf (ClassExpression) -- OR -- (o1 or o2) SubClassOf (ClassExpression)
		    		else if((sub instanceof OWLObjectOneOf) || (sub instanceof OWLObjectUnionOf && 
			    			((OWLObjectUnionOf)sub).disjunctSet().allMatch(dj -> dj instanceof OWLObjectOneOf))) {
			    		oneOfSubAx.add(sax);
			    		//this.oneOfAll.add(sax);
		    		}
			   
				// --> (A or B) SubClassOf C
		    		else if(sub instanceof OWLObjectUnionOf) {
		    			processDisjunction(sub, sup);
		    		}
		    		
			// --> R some A SubClassOf C 
			    	else if(sub instanceof OWLObjectSomeValuesFrom) {
			    	//	System.out.println(handleQualifiedRangeRestriction(sub, sup));
			    		if(!handleQualifiedRangeRestriction(sub, sup)) {
    						this.Tg.add(df.getOWLSubClassOfAxiom(sub, sup)); 
    					}
			    	}
			// --> R hasValue o SubClassOf C
		    		else if(sub instanceof OWLObjectHasValue) {
		    			if(!handleNominal(sub, sup)) {
    						this.Tg.add(df.getOWLSubClassOfAxiom(sub, sup)); 
    					}
		    		}
			   
			// --> (A and B) SubClassOf C -- OR -- (o1 and o2) SubClassOf C -- OR -- (A and o1) SubClassOf C
		    		else if((sub instanceof OWLObjectIntersectionOf && 
		    				((OWLObjectIntersectionOf)sub).conjunctSet().allMatch(cj -> (cj instanceof OWLObjectOneOf) || (cj instanceof OWLClass)))) {
		    			if(sup instanceof OWLObjectIntersectionOf)
							sup.asConjunctSet().forEach(cj -> this.Tui.add(df.getOWLSubClassOfAxiom(sub, cj)));
		    		/*	else if(sup.isOWLNothing()) {
		    				
		    			}*/
		    			else
		    				this.Tui.add(sax);
		    		}
		    		else {
		    			// --> (ClassExpression) SubClassOf (ClassExpression)
		    			this.Tg.add(sax);
		    		}
		   }																										
		   // -->  EquivalentClasses Axiom
		    	else if(ax instanceof OWLEquivalentClassesAxiom) {
		    		OWLEquivalentClassesAxiom eax = (OWLEquivalentClassesAxiom)ax;
		    		if(eax.operands().anyMatch(eq -> (eq instanceof OWLObjectOneOf) || ((eq instanceof OWLObjectUnionOf) && 
		    				(((OWLObjectUnionOf)eq).disjunctSet().allMatch(dj -> dj instanceof OWLObjectOneOf))))) {
		    			oneOfEqAx.add(eax);
		    			for(OWLSubClassOfAxiom eqsb : eax.asOWLSubClassOfAxioms()) {
		    				if((eqsb.getSubClass() instanceof OWLObjectOneOf) || (eqsb.getSubClass() instanceof OWLObjectUnionOf && 
				    				((OWLObjectUnionOf)eqsb.getSubClass()).disjunctSet().allMatch(dj -> dj instanceof OWLObjectOneOf)))
		    					oneOfSubAx.add(eqsb);
		    				else if(eqsb.getSubClass() instanceof OWLClass) {
		    					tuConcepts.add(eqsb.getSubClass());
		    					this.Tu.add(eqsb);
		    				}
		    				else if(eqsb.getSubClass() instanceof OWLObjectIntersectionOf 
		    						&& eqsb.getSubClass().conjunctSet().allMatch(cj -> (cj instanceof OWLObjectOneOf) || (cj instanceof OWLClass))) {
		    					
		    					this.Tui.add(eqsb);
		    				}
		    				else if(eqsb.getSubClass() instanceof OWLObjectUnionOf) {
		    					processDisjunction(eqsb.getSubClass(), eqsb.getSuperClass());
		    				}
		    				else if(eqsb.getSubClass() instanceof OWLObjectSomeValuesFrom) {
					    		if(!handleQualifiedRangeRestriction(eqsb.getSubClass(), eqsb.getSuperClass())) {
		    						this.Tg.add(eqsb); 
		    					}
		    				}
		    				else
		    					Tg.add(eqsb);
		    			}
		    		}
		    		else
		    			eqAx.add((OWLEquivalentClassesAxiom) ax);
		    	}
		   
		   // --> DisjointClasses Axiom
		    	else if(ax instanceof OWLDisjointClassesAxiom) {
		    		djAx.add((OWLDisjointClassesAxiom) ax);
		    		//((OWLDisjointClassesAxiom) ax).operands().forEach(o -> System.out.println("operand "+o));
		    		for(OWLSubClassOfAxiom djsb : ((OWLDisjointClassesAxiom) ax).asOWLSubClassOfAxioms()) {
		    			
		    			if(djsb.getSubClass() instanceof OWLClass) {
		    				tuConcepts.add(djsb.getSubClass());
				    		this.Tu.add(djsb);
		    			}
				    	else
				    		this.Tg.add(djsb);
		    			}
		    		}
		   // --> DisjointUnion Axiom
		    	else if(ax instanceof OWLDisjointUnionAxiom) {
		    		djuAx.add((OWLDisjointUnionAxiom) ax);
		    		eqAx.add(((OWLDisjointUnionAxiom) ax).getOWLEquivalentClassesAxiom());
		    		for(OWLSubClassOfAxiom djusb : ((OWLDisjointUnionAxiom) ax).getOWLDisjointClassesAxiom().asOWLSubClassOfAxioms()) {
		    			if(djusb.getSubClass() instanceof OWLClass) {
		    				tuConcepts.add(djusb.getSubClass());
				    		this.Tu.add(djusb);
		    			}
				    	else
				    		this.Tg.add(djusb);
		    		}
		    	}
		   // --> Domain Axiom
		    	else if(ax instanceof OWLObjectPropertyDomainAxiom) {
		    		objdAx.add((OWLObjectPropertyDomainAxiom) ax);
			    	this.Tg.add(((OWLObjectPropertyDomainAxiom) ax).asOWLSubClassOfAxiom());
		    	}
		   // --> Range Axiom
		    	else if(ax instanceof OWLObjectPropertyRangeAxiom) {
		    		objrAx.add((OWLObjectPropertyRangeAxiom) ax);
		    		this.Tg.add(((OWLObjectPropertyRangeAxiom) ax).asOWLSubClassOfAxiom());
		    	}
		   // --> DifferentIndividuals Axiom
		    	else if(ax instanceof OWLDifferentIndividualsAxiom) {
			 	((OWLDifferentIndividualsAxiom)ax).asOWLSubClassOfAxioms().forEach(s -> diffInd.add(s));
			 	subAx.addAll(((OWLDifferentIndividualsAxiom)ax).asOWLSubClassOfAxioms());
	    		
			 }
		   // --> Class Assertion Axiom
		   
		   
		    	else if(ax instanceof OWLClassAssertionAxiom) {
		    		individuals.add(((OWLClassAssertionAxiom)ax).getIndividual());
		    		aboxClassAss.add(((OWLClassAssertionAxiom)ax).asOWLSubClassOfAxiom());
		    		oneOfSubAx.add(((OWLClassAssertionAxiom)ax).asOWLSubClassOfAxiom());
		    		subAx.add(((OWLClassAssertionAxiom)ax).asOWLSubClassOfAxiom());
		    }
		     
		   // --> role Assertion Axiom
		    else if(ax instanceof OWLObjectPropertyAssertionAxiom) {
	    			aboxObjProAss.add(((OWLObjectPropertyAssertionAxiom)ax).asOWLSubClassOfAxiom());
	    			oneOfSubAx.add(((OWLObjectPropertyAssertionAxiom)ax).asOWLSubClassOfAxiom());
	    			subAx.add(((OWLObjectPropertyAssertionAxiom)ax).asOWLSubClassOfAxiom());
		    }
	    		
	    }
	    // --> remaining Equivalent class axioms
	    Set<OWLClassExpression>  eqConcepts = new HashSet<>();
	   // eqAx.forEach(eq -> eqConcepts.addAll(eq.operands().collect(Collectors.toList())));
	    
	    for(OWLEquivalentClassesAxiom eq : eqAx) {
	    		eqConcepts.addAll(eq.operands().collect(Collectors.toSet()));
	    		for(OWLSubClassOfAxiom eqsb : eq.asOWLSubClassOfAxioms()) {
	    			if(eqsb.getSubClass() instanceof OWLObjectUnionOf) {
	    				eqConcepts.addAll(((OWLObjectUnionOf)eqsb.getSubClass()).asDisjunctSet());
	    			}
	    			if(eqsb.getSuperClass() instanceof OWLObjectIntersectionOf) {
	    				eqConcepts.addAll(((OWLObjectIntersectionOf)eqsb.getSuperClass()).asConjunctSet());
	    			}
	    		}
	    }
	    
	    for(OWLEquivalentClassesAxiom eq : eqAx) {
	    		Set<OWLClassExpression> operands = new HashSet<>();
	    		operands.addAll(eq.operands().collect(Collectors.toSet()));
	    		for(OWLClassExpression op : eq.operands().collect(Collectors.toSet())) {
	    			if(op instanceof OWLObjectUnionOf) {
	    				operands.addAll(((OWLObjectUnionOf)op).asDisjunctSet());
	    			}
	    			if(op instanceof OWLObjectIntersectionOf){
	    				operands.addAll(((OWLObjectIntersectionOf)op).asConjunctSet());
	    			}
	    		}
		    	boolean eqTag = false;
		    	for(OWLClassExpression op : operands) {
	    			if(tuConcepts.contains(op) || Collections.frequency(eqConcepts, op)>1) {
	    				eqTag = true;
	    				for(OWLSubClassOfAxiom eqsb : eq.asOWLSubClassOfAxioms()) {
	    				 //	System.err.println(eqsb);
	    					if(eqsb.getSubClass() instanceof OWLClass) {
	    						if(eqsb.getSuperClass() instanceof OWLObjectIntersectionOf)
	    							eqsb.getSuperClass().asConjunctSet().forEach(cj -> this.Tu.add(df.getOWLSubClassOfAxiom(eqsb.getSubClass(), cj)));
							else
	    							Tu.add(eqsb);
	    					}
	    					else if(eqsb.getSubClass() instanceof OWLObjectUnionOf) {
		    					processDisjunction(eqsb.getSubClass(), eqsb.getSuperClass());
		    				}
	    					else if((eqsb.getSubClass() instanceof OWLObjectIntersectionOf && 
	    		    				((OWLObjectIntersectionOf)eqsb.getSubClass()).conjunctSet().allMatch(cj -> (cj instanceof OWLObjectOneOf) || (cj instanceof OWLClass)))) {
	    		    				if(eqsb.getSuperClass() instanceof OWLObjectIntersectionOf)
	    		    					eqsb.getSuperClass().asConjunctSet().forEach(cj -> this.Tui.add(df.getOWLSubClassOfAxiom(eqsb.getSuperClass(), cj)));
	    		    				else
	    		    					this.Tui.add(eqsb);
	    					}
	    					else
	    						this.Tg.add(eqsb);
	    				}
	    				break;
	    			}
	    		}
		    	if(!eqTag) {
	    			if(eq.asOWLSubClassOfAxioms().stream().filter(esb -> (esb.getSubClass() instanceof OWLClass) || (esb.getSuperClass() instanceof OWLClass)).findAny().isPresent())
	    				this.Eq.add(eq);
	    			else
	    				eq.asOWLSubClassOfAxioms().stream().forEach(esb -> this.Tg.add(esb)); 
	    				
	    		}
	    }
	    	processOneOfAx(oneOfSubAx);
	  ont.individualsInSignature().forEach(ind ->
			  {
				  if(!individuals.contains(ind)) {
				  	aboxClassAss.add(df.getOWLSubClassOfAxiom(df.getOWLObjectOneOf(ind), df.getOWLThing()));
				  }
			  }
			  );
	    	ont.axioms().filter(ax -> ax instanceof OWLSubObjectPropertyOfAxiom).forEach(ax -> subObjProAx.add((OWLSubObjectPropertyOfAxiom) ax));
	    ont.axioms().filter(ax -> ax instanceof OWLInverseObjectPropertiesAxiom).forEach(ax -> invObjProAx.add((OWLInverseObjectPropertiesAxiom) ax));
	    ontology = new Ontology(subAx, Eq, objdAx, objrAx, oneOfSubAx, oneOfEqAx, oneOf, djAx, djuAx, diffInd, aboxClassAss, aboxObjProAss, subObjProAx, invObjProAx, this.Tu, this.Tui, this.symmRoles);
	    	return ontology;
	}
	
	public DefaultPrefixManager getPrefixManager() {
		return prefixManager;
	}
	public void setPrefixManager(DefaultPrefixManager prefixManager) {
		this.prefixManager = prefixManager;
	}
	public void setOntology(Ontology ontology) {
		this.ontology = ontology;
	}
	public Ontology getOntology() {
		return ontology;
	}
	private void processOneOfAx(Set<OWLSubClassOfAxiom> oneOfSubAx) {
		for(OWLSubClassOfAxiom sb : oneOfSubAx) {
			if((sb.getSubClass() instanceof OWLObjectOneOf) && (sb.getSuperClass() instanceof OWLObjectIntersectionOf)) {
				sb.getSuperClass().asConjunctSet().forEach(cj -> this.oneOf.add(df.getOWLSubClassOfAxiom(sb.getSubClass(), cj)));
			}
			else if((sb.getSubClass() instanceof OWLObjectOneOf))
				this.oneOf.add(sb);
			else if((sb.getSubClass() instanceof OWLObjectUnionOf) && (sb.getSuperClass() instanceof OWLObjectIntersectionOf)){
				//OWLClassExpression sp = sb.getSuperClass();
				((OWLObjectUnionOf)(sb).getSubClass()).disjunctSet().forEach(dj -> {
					sb.getSuperClass().asConjunctSet().forEach(cj -> {
						this.oneOf.add(df.getOWLSubClassOfAxiom(dj, cj));
					});
				});
			}
			else if((sb.getSubClass() instanceof OWLObjectUnionOf)){
				OWLClassExpression sp = sb.getSuperClass();
				((OWLObjectUnionOf)(sb).getSubClass()).disjunctSet().forEach(dj -> this.oneOf.add(df.getOWLSubClassOfAxiom(dj, sp)));
			}
				
		}
		
	}
	public boolean isSimpleObjectIntersectionOf(Set<OWLClassExpression> ceSet) {
		for(OWLClassExpression ce : ceSet) {
			if(!(ce instanceof OWLClass))
				return false;
		}
		return true;
	}
		
	public Set<OWLSubClassOfAxiom>  getTu() {
		return this.Tu;
	}
	public Set<OWLSubClassOfAxiom>  getTui() {
		return this.Tui;
	}
	public Set<OWLSubClassOfAxiom>  getTg() {
		return this.Tg;
	}
	//returns set of super-concepts
	public Set<OWLClassExpression> findConcept(OWLClassExpression c){
		Set<OWLClassExpression> ce = new HashSet<OWLClassExpression>();
		this.Tu.stream().filter(sb -> sb.getSubClass().equals(c)).forEach(sb -> ce.add(sb.getSuperClass()));
		for(OWLEquivalentClassesAxiom eq : this.Eq) {
			if(eq.contains(c)) {
				for(OWLSubClassOfAxiom eqsb : eq.asOWLSubClassOfAxioms()) {
					if(eqsb.getSubClass().equals(c)) {
						ce.add(eqsb.getSuperClass()); break;
					}
					else {
						ce.add(eqsb.getSubClass()); break;
					}		
				}
			}
		}
		return ce;
	}
	public void addDiffInd(OWLDifferentIndividualsAxiom ax) {
	 	ax.asOWLSubClassOfAxioms().forEach(s -> diffInd.add(s));
	}
	public Set<OWLClassExpression> findIndividual(OWLClassExpression c){
		Set<OWLClassExpression> ce = new HashSet<OWLClassExpression>();
		this.oneOf.stream().filter(sb -> sb.getSubClass().equals(c)).forEach(sb -> ce.add(sb.getSuperClass()));
		this.diffInd.stream().filter(sb -> sb.getSubClass().equals(c)).forEach(sb -> ce.add(sb.getSuperClass()));
		//this.aboxClassAss.stream().filter(sb -> sb.getSubClass().equals(c)).forEach(sb -> ce.add(sb.getSuperClass()));
		//this.aboxObjProAss.stream().filter(sb -> sb.getSubClass().equals(c)).forEach(sb -> ce.add(sb.getSuperClass()));
		return ce;
	}
	public Set<OWLClassExpression> getDisjoints(OWLClassExpression c){
		Set<OWLClassExpression> ce = new HashSet<OWLClassExpression>();
		this.djAx.stream().filter(dj -> dj.contains(c)).forEach(dj -> ce.addAll(dj.getClassExpressionsMinus(c)));
		return ce;
	}
	public Set<OWLClassExpression> getDisjointUnion(OWLClassExpression c){
		Set<OWLClassExpression> ce = new HashSet<OWLClassExpression>();
		this.djuAx.stream().filter(dj -> dj.getOWLDisjointClassesAxiom().contains(c)).forEach(dj -> ce.addAll(dj.getOWLDisjointClassesAxiom().getClassExpressionsMinus(c)));
		return ce;
	}
	public OWLClassExpression getTgAxiom() {
		if(this.getTg().isEmpty()) {
			return null;
		}
		else {
			OWLClassExpression union = null;
		 	Set<OWLClassExpression> unionSet = new HashSet<>();
		 	
		 	if(this.getTg().size()==1) {
		 		for (OWLSubClassOfAxiom sb : this.getTg()) {
		 			if(sb.getSubClass().isOWLThing()) {
		 				union = df.getOWLObjectUnionOf(df.getOWLNothing(), sb.getSuperClass());
		 			}
		 			else {
		 				union = df.getOWLObjectUnionOf(sb.getSubClass().getComplementNNF(), sb.getSuperClass());	
		 			}
		 		}
		 		if(union.asDisjunctSet().size()==1) {
		 			return union.asDisjunctSet().iterator().next();
		 		}
		 		return union;
		 	}
			for (OWLSubClassOfAxiom sb : this.getTg()) {
				if(sb.getSubClass().isOWLThing()) {
		    			union = df.getOWLObjectUnionOf(df.getOWLNothing(), sb.getSuperClass());
				}
				else {
					union = df.getOWLObjectUnionOf(sb.getSubClass().getComplementNNF(), sb.getSuperClass());
				}
		    		unionSet.add(union);
			}
			OWLClassExpression intersection = df.getOWLObjectIntersectionOf(unionSet);
			return intersection;
		}
	}
	public Set<OWLObjectAllValuesFrom> getRoleRange(OWLObjectPropertyExpression r) {
		Set<OWLObjectAllValuesFrom> ranges = new HashSet<OWLObjectAllValuesFrom>();
		for(OWLObjectPropertyRangeAxiom range: this.objrAx) {
			if(range.getProperty().equals(r))
				ranges.add((OWLObjectAllValuesFrom)range.asOWLSubClassOfAxiom().getSuperClass());
		}
		return ranges;
		
	}
	public void addInTu(OWLSubClassOfAxiom eqsb) {
		this.Tu.add(eqsb);
	}
	public void addInTg(OWLSubClassOfAxiom eqsb) {
		this.Tg.add(eqsb);
	}
	public Set<OWLSubClassOfAxiom> getOneOf() {
		return oneOf;
	}
	public void setOneOf(Set<OWLSubClassOfAxiom> oneOf) {
		this.oneOf = oneOf;
	}
	public Set<OWLSubClassOfAxiom> getHasValue() {
		return hasValue;
	}
	public void setHasValue(Set<OWLSubClassOfAxiom> hasValue) {
		this.hasValue = hasValue;
	}
	public Set<OWLSubClassOfAxiom> getDiffInd() {
		return diffInd;
	}
	public void setDiffInd(Set<OWLSubClassOfAxiom> diffInd) {
		this.diffInd = diffInd;
	}
	public Set<OWLSubClassOfAxiom> getAboxClassAss() {
		return aboxClassAss;
	}
	public void setAboxClassAss(Set<OWLSubClassOfAxiom> aboxClassAss) {
		this.aboxClassAss = aboxClassAss;
	}
	public Set<OWLSubClassOfAxiom> getAboxObjProAss() {
		return aboxObjProAss;
	}
	public void setAboxObjProAss(Set<OWLSubClassOfAxiom> aboxObjProAss) {
		this.aboxObjProAss = aboxObjProAss;
	}
	public Set<OWLSubClassOfAxiom> getOneOfIn() {
		return oneOfIn;
	}
	public void setOneOfIn(Set<OWLSubClassOfAxiom> oneOfIn) {
		this.oneOfIn = oneOfIn;
	}
	public boolean isPrefixSet() {
		return prefixSet;
	}
	public void setPrefixSet(boolean prefixSet) {
		this.prefixSet = prefixSet;
	}
	public void addFunctionalRoleAxiom(Set<OWLObjectPropertyExpression> functionalRoles) {
		for(OWLObjectPropertyExpression fr : functionalRoles) {
			Tu.add(df.getOWLSubClassOfAxiom(df.getOWLThing(), df.getOWLObjectMaxCardinality(1, fr, df.getOWLThing())));
		}
		
	}
	public void addInverseFunctionalRoleAxiom(Set<OWLObjectPropertyExpression> inverseFunctionalRoles) {
		for(OWLObjectPropertyExpression invfr : inverseFunctionalRoles) {
			Tu.add(df.getOWLSubClassOfAxiom(df.getOWLThing(), df.getOWLObjectMaxCardinality(1, invfr, df.getOWLThing())));
		}
		
	}
	
	public void setSymmetricRoles(Set<OWLObjectPropertyExpression> symm) {
		this.symmRoles = symm;
		
	}
	/*
	 * 
	 *if((((OWLSubClassOfAxiom) ax).getSubClass() instanceof OWLObjectOneOf)) {// || (((OWLSubClassOfAxiom) ax).getSuperClass() instanceof OWLObjectOneOf)) {
		    			oneOfSubAx.add((OWLSubClassOfAxiom) ax);
		    		}
		    		else if(((OWLSubClassOfAxiom) ax).getSubClass() instanceof OWLObjectHasValue) {
		    			OWLIndividual ind = ((OWLObjectHasValue)((OWLSubClassOfAxiom) ax).getSubClass()).getFiller();
		    			OWLObjectPropertyExpression role = ((OWLObjectHasValue)((OWLSubClassOfAxiom) ax).getSubClass()).getProperty();
		    			OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), ((OWLSubClassOfAxiom) ax).getSuperClass());
		    			OWLClassExpression sb = df.getOWLObjectOneOf(ind);
		    			oneOfSubAx.add(df.getOWLSubClassOfAxiom(sb, sp));
		    		}
		    		else if(((OWLSubClassOfAxiom) ax).getSuperClass() instanceof OWLObjectHasValue) {
		    			OWLIndividual ind = ((OWLObjectHasValue)((OWLSubClassOfAxiom) ax).getSuperClass()).getFiller();
		    			OWLObjectPropertyExpression role = ((OWLObjectHasValue)((OWLSubClassOfAxiom) ax).getSuperClass()).getProperty();
		    			OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), ((OWLSubClassOfAxiom) ax).getSubClass());
		    			OWLClassExpression sb = df.getOWLObjectOneOf(ind);
		    			oneOfSubAx.add(df.getOWLSubClassOfAxiom(sb, sp));
		    		}
		    		else if(ax.nestedClassExpressions().anyMatch(sbx -> sbx instanceof OWLObjectOneOf || sbx instanceof OWLObjectHasValue)) {
		    			this.Tg.add((OWLSubClassOfAxiom) ax);
		    		}
	 */
}

