package reasoner.preprocessing;

import java.util.HashSet;
import java.util.Set;

import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.util.DefaultPrefixManager;

import reasoner.Ontology;

public class Internalization {

	private Set<OWLSubClassOfAxiom> Tu;
	private Set<OWLSubClassOfAxiom> Tui;
	private Set<OWLSubClassOfAxiom> Tg;
	private Set<OWLEquivalentClassesAxiom> Eq;
	private Set<OWLSubClassOfAxiom> oneOf;
	private Set<OWLSubClassOfAxiom> oneOfIn;
	private Set<OWLSubClassOfAxiom> oneOfAll;
	private Set<OWLSubClassOfAxiom> hasValue;
	private Set<OWLSubClassOfAxiom> diffInd; 
	private Set<OWLSubClassOfAxiom> aboxClassAss;
	private Set<OWLSubClassOfAxiom> aboxObjProAss;
	private Set<OWLDisjointClassesAxiom> djAx;
	private Set<OWLDisjointUnionAxiom> djuAx;
    Set<OWLObjectPropertyRangeAxiom> objrAx = new HashSet<>();
    DefaultPrefixManager prefixManager = new DefaultPrefixManager();
	 
    Ontology ontology;
	
	public Internalization(){
		this.Tu = new HashSet<OWLSubClassOfAxiom>();
		this.Tui = new HashSet<OWLSubClassOfAxiom>();
		this.Tg = new HashSet<OWLSubClassOfAxiom>();
		this.Eq = new HashSet<OWLEquivalentClassesAxiom>();
		this.setOneOf(new HashSet<OWLSubClassOfAxiom>());
		this.setOneOfIn(new HashSet<OWLSubClassOfAxiom>());
		this.setOneOfAll(new HashSet<OWLSubClassOfAxiom>());
		this.setHasValue(new HashSet<OWLSubClassOfAxiom>());
		diffInd = new HashSet<>();
		aboxClassAss = new HashSet<>();
		aboxObjProAss = new HashSet<>();
		djAx = new HashSet<>();
		djuAx = new HashSet<>();
		
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
		
	public Ontology internalize(OWLOntology ont, OWLDataFactory df) {
		
		Set<OWLSubClassOfAxiom> subAx = new HashSet<>();
	    Set<OWLEquivalentClassesAxiom> eqAx = new HashSet<>();
	    Set<OWLObjectPropertyDomainAxiom> objdAx = new HashSet<>();
	    Set<OWLSubClassOfAxiom> oneOfSubAx = new HashSet<>();
	    Set<OWLEquivalentClassesAxiom> oneOfEqAx = new HashSet<>();
	    Set<OWLSubObjectPropertyOfAxiom> subObjProAx = new HashSet<>();
	    Set<OWLInverseObjectPropertiesAxiom> invObjProAx = new HashSet<>();
	    Set<OWLSubClassOfAxiom> newSbAx = new HashSet<OWLSubClassOfAxiom>();
		   
	    for (OWLAxiom ax : (Iterable<OWLAxiom>)ont.axioms()::iterator) {
		   // 	System.out.println("ax: "+ax);
	    		ax = ax.getNNF();
	    	//	System.out.println("nnf ax:  "+ax);
		    if(ax instanceof OWLSubClassOfAxiom) {
		    		OWLSubClassOfAxiom sax = (OWLSubClassOfAxiom)ax;
		    		subAx.add(sax);
		    		if(((sax).getSubClass() instanceof OWLObjectOneOf) || ((sax).getSubClass() instanceof OWLObjectUnionOf && 
		    				((OWLObjectUnionOf)(sax).getSubClass()).disjunctSet().allMatch(dj -> dj instanceof OWLObjectOneOf))) {
			    		oneOfSubAx.add(sax);
			    		this.oneOfAll.add(sax);
		    		}
		    		else if((sax).getSubClass() instanceof OWLObjectSomeValuesFrom && 
		    				((((OWLObjectSomeValuesFrom)(sax).getSubClass()).getFiller() instanceof OWLObjectOneOf) ||
		    					(((OWLObjectSomeValuesFrom)(sax).getSubClass()).getFiller() instanceof OWLObjectUnionOf && 
		    							((OWLObjectUnionOf)((OWLObjectSomeValuesFrom)(sax).getSubClass()).getFiller()).disjunctSet().allMatch(dj -> dj instanceof OWLObjectOneOf)))) {
		    			OWLClassExpression sb = ((OWLObjectSomeValuesFrom)(sax).getSubClass()).getFiller();
		    			OWLObjectPropertyExpression role = ((OWLObjectSomeValuesFrom)(sax).getSubClass()).getProperty();
		    			OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), (sax).getSuperClass());
		    			oneOfSubAx.add(df.getOWLSubClassOfAxiom(sb, sp));
		    			this.oneOfAll.add(df.getOWLSubClassOfAxiom(sb, sp));
		    		}

		    		else if((sax).getSuperClass() instanceof OWLObjectSomeValuesFrom && 
		    				((((OWLObjectSomeValuesFrom)(sax).getSuperClass()).getFiller() instanceof OWLObjectOneOf) ||
		    					(((OWLObjectSomeValuesFrom)(sax).getSuperClass()).getFiller() instanceof OWLObjectUnionOf && 
		    							((OWLObjectUnionOf)((OWLObjectSomeValuesFrom)(sax).getSuperClass()).getFiller()).disjunctSet().allMatch(dj -> dj instanceof OWLObjectOneOf)))) {
		    			OWLClassExpression sb = ((OWLObjectSomeValuesFrom)(sax).getSuperClass()).getFiller();
		    			OWLObjectPropertyExpression role = ((OWLObjectSomeValuesFrom)(sax).getSuperClass()).getProperty();
		    			OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), (sax).getSubClass());
		    			oneOfSubAx.add(df.getOWLSubClassOfAxiom(sb, sp));
		    			//this.oneOfAll.add(df.getOWLSubClassOfAxiom(sb, sp));
		    		}
		    		else if(sax.getSubClass() instanceof OWLObjectHasValue) {
		    			OWLIndividual ind = ((OWLObjectHasValue)(sax).getSubClass()).getFiller();
		    			OWLObjectPropertyExpression role = ((OWLObjectHasValue)(sax).getSubClass()).getProperty();
		    			OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), (sax).getSuperClass());
		    			OWLClassExpression sb = df.getOWLObjectOneOf(ind);
		    			oneOfSubAx.add(df.getOWLSubClassOfAxiom(sb, sp));
		    			//this.oneOfAll.add(df.getOWLSubClassOfAxiom(sb, sp));
		    		}
		    		else if((sax).getSuperClass() instanceof OWLObjectHasValue) {
		    			OWLIndividual ind = ((OWLObjectHasValue)(sax).getSuperClass()).getFiller();
		    			OWLObjectPropertyExpression role = ((OWLObjectHasValue)(sax).getSuperClass()).getProperty();
		    			OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), (sax).getSubClass());
		    			OWLClassExpression sb = df.getOWLObjectOneOf(ind);
		    			oneOfSubAx.add(df.getOWLSubClassOfAxiom(sb, sp));
		    			//this.oneOfAll.add(df.getOWLSubClassOfAxiom(sb, sp));
		    		}
		    		else if(((sax).getSubClass() instanceof OWLObjectUnionOf && 
		    				((OWLObjectUnionOf)(sax).getSubClass()).disjunctSet().anyMatch(dj -> dj instanceof OWLObjectOneOf))) {
		    			for(OWLClassExpression ce : ((OWLObjectUnionOf)(sax).getSubClass()).asDisjunctSet()) {
		    				if(ce instanceof OWLObjectOneOf)
		    					this.oneOfAll.add(df.getOWLSubClassOfAxiom(ce, (sax).getSuperClass()));//FIXME might be we need to add it in oneOfSubAx
		    				else if(ce instanceof OWLClass)
	    						this.Tu.add(df.getOWLSubClassOfAxiom(ce, (sax).getSuperClass()));
	    					else
	    						this.Tg.add(df.getOWLSubClassOfAxiom(ce, (sax).getSuperClass())); 
		    			}
		    		}
		    		else if(((sax).getSubClass() instanceof OWLObjectIntersectionOf && 
		    				((OWLObjectIntersectionOf)(sax).getSubClass()).conjunctSet().allMatch(cj -> (cj instanceof OWLObjectOneOf) || (cj instanceof OWLClass)))) {
			    		this.Tui.add(sax);
		    		}
		    	/*	else if(ax.nestedClassExpressions().anyMatch(sbx -> sbx instanceof OWLObjectOneOf || sbx instanceof OWLObjectHasValue)) {
		    			this.Tg.add(sax);
		    		}*/
		    		else {
		    			if((sax).getSubClass() instanceof OWLClass)
			    			this.Tu.add(sax);
		    			else if((sax).getSubClass() instanceof OWLObjectIntersectionOf && ((OWLObjectIntersectionOf)(sax).getSubClass()).conjunctSet().allMatch(cj -> cj instanceof OWLClass)) {
		    				//if(isSimpleObjectIntersectionOf(((OWLObjectIntersectionOf)(sax).getSubClass()).asConjunctSet()))
		    				this.Tui.add(sax);
		    			}//FIXME what if we have class and nominals
		    			else if((sax).getSubClass() instanceof OWLObjectIntersectionOf && ((OWLObjectIntersectionOf)(sax).getSubClass()).conjunctSet().allMatch(cj -> cj instanceof OWLObjectOneOf)) {
		    				this.Tui.add(sax);
		    				this.oneOfIn.add(sax);
		    				this.oneOfAll.add(sax);
		    			}
		    			else if((sax).getSubClass() instanceof OWLObjectUnionOf && ((OWLObjectUnionOf)(sax).getSubClass()).disjunctSet().anyMatch(cj -> cj instanceof OWLClass)) {
		    				for(OWLClassExpression ce : ((OWLObjectUnionOf)(sax).getSubClass()).asDisjunctSet()) {
		    					if(ce instanceof OWLClass)
		    						this.Tu.add(df.getOWLSubClassOfAxiom(ce, (sax).getSuperClass()));
		    					else
		    						this.Tg.add(df.getOWLSubClassOfAxiom(ce, (sax).getSuperClass())); 
		    						
		    				}
		    			}//FIXME what if we have class and nominals
		    			else
			    			this.Tg.add(sax);
		    		}
		    }
		    	else if(ax instanceof OWLEquivalentClassesAxiom) {
		    		OWLEquivalentClassesAxiom eax = (OWLEquivalentClassesAxiom)ax;
		    		if((eax).operands().anyMatch(eq -> (eq instanceof OWLObjectOneOf) || ((eq instanceof OWLObjectUnionOf) && 
		    				(((OWLObjectUnionOf)(eq)).disjunctSet().allMatch(dj -> dj instanceof OWLObjectOneOf))))) {
		    			oneOfEqAx.add(eax);
		    			for(OWLSubClassOfAxiom eqsb : eax.asOWLSubClassOfAxioms()) {
		    				if(((eqsb).getSubClass() instanceof OWLObjectOneOf) || ((eqsb).getSubClass() instanceof OWLObjectUnionOf && 
				    				((OWLObjectUnionOf)(eqsb).getSubClass()).disjunctSet().allMatch(dj -> dj instanceof OWLObjectOneOf)))
		    					oneOfSubAx.add(eqsb);
		    				else if((eqsb).getSubClass() instanceof OWLClass) {
		    					boolean eqTag = false;
			    		    		for(OWLSubClassOfAxiom sb : this.Tu) {
			    		    			if((eqsb).getSubClass().equals(sb.getSubClass())) {
			    		    				eqTag = true;
			    		    				newSbAx.add(eqsb);
			    		    				break;
			    		    			}
			    		    		}
			    		    		if(!eqTag) {
			    		    			if(eax.asOWLSubClassOfAxioms().stream().filter(esb -> (esb.getSubClass() instanceof OWLClass) || (esb.getSuperClass() instanceof OWLClass)).iterator().hasNext())
			    		    				this.Eq.add(eax);
			    		    			else
			    		    				eax.asOWLSubClassOfAxioms().stream().forEach(esb -> this.Tg.add(esb)); 
			    		    		}
		    				}
		    				else
		    					Tg.add(eqsb);
		    			}
		    		}
		    		/*else if(eax.nestedClassExpressions().anyMatch(sbx -> sbx instanceof OWLObjectOneOf || sbx instanceof OWLObjectHasValue)) {
		    			for(OWLSubClassOfAxiom eqsb : eax.asOWLSubClassOfAxioms()) {
		    				this.Tg.add(eqsb);
		    			}
		    		}*/
		    		else
		    			eqAx.add((OWLEquivalentClassesAxiom) ax);
		    	}	
		    	else if(ax instanceof OWLDisjointClassesAxiom) {
		    		djAx.add((OWLDisjointClassesAxiom) ax);
		    		//((OWLDisjointClassesAxiom) ax).operands().forEach(o -> System.out.println("operand "+o));
		    		for(OWLSubClassOfAxiom djsb : ((OWLDisjointClassesAxiom) ax).asOWLSubClassOfAxioms()) {
		    			
		    			if(djsb.getSubClass() instanceof OWLClass)
				    		this.Tu.add(djsb);
				    	else
				    		this.Tg.add(djsb);
		    			}
		    		}
		    	else if(ax instanceof OWLDisjointUnionAxiom) {
		    		djuAx.add((OWLDisjointUnionAxiom) ax);
		    		for(OWLSubClassOfAxiom djusb : ((OWLDisjointUnionAxiom) ax).getOWLDisjointClassesAxiom().asOWLSubClassOfAxioms()) {
		    			if(djusb.getSubClass() instanceof OWLClass)
				    		this.Tu.add(djusb);
				    	else
				    		this.Tg.add(djusb);
		    		}
		    	}
		    	else if(ax instanceof OWLObjectPropertyDomainAxiom) {
		    		objdAx.add((OWLObjectPropertyDomainAxiom) ax);
			    	this.Tg.add(((OWLObjectPropertyDomainAxiom) ax).asOWLSubClassOfAxiom());
		    	}
		    	else if(ax instanceof OWLObjectPropertyRangeAxiom) {
		    		objrAx.add((OWLObjectPropertyRangeAxiom) ax);
		    		this.Tg.add(((OWLObjectPropertyRangeAxiom) ax).asOWLSubClassOfAxiom());
		    	}
		    
		    	else if(ax instanceof OWLDifferentIndividualsAxiom) {
			 	((OWLDifferentIndividualsAxiom)ax).asOWLSubClassOfAxioms().forEach(s -> diffInd.add(s));
	    		
			 }
		    	else if(ax instanceof OWLClassAssertionAxiom) {
		    		aboxClassAss.add(((OWLClassAssertionAxiom)ax).asOWLSubClassOfAxiom());
		    }
		    else if(ax instanceof OWLObjectPropertyAssertionAxiom) {
	    			aboxObjProAss.add(((OWLObjectPropertyAssertionAxiom)ax).asOWLSubClassOfAxiom());
		    }
	    		
	    }
	    
	    
	    
	    for(OWLEquivalentClassesAxiom eq : eqAx) {
	    		boolean eqTag = false;
	    		for(OWLSubClassOfAxiom sb : this.Tu) {
	    			if(eq.contains(sb.getSubClass())) {
	    				eqTag = true;
	    				for(OWLSubClassOfAxiom eqsb : eq.asOWLSubClassOfAxioms()) {
	    					if(eqsb.getSubClass() instanceof OWLClass) {
	    						newSbAx.add(eqsb);
	    					}
	    					else
	    						this.Tg.add(eqsb);
	    				}
	    				break;
	    			}
	    		}
	    		if(!eqTag) {
	    			if(eq.asOWLSubClassOfAxioms().stream().filter(esb -> (esb.getSubClass() instanceof OWLClass) || (esb.getSuperClass() instanceof OWLClass)).iterator().hasNext())
	    				this.Eq.add(eq);
	    			else
	    				eq.asOWLSubClassOfAxioms().stream().forEach(esb -> this.Tg.add(esb)); 
	    				
	    		}
	    }

		//System.out.println("tg size:  "+ Tg.size());
	  /*  for(OWLSubClassOfAxiom nsb : newSbAx)
	    		this.Tu.add(nsb);*/
	    this.Tu.addAll(newSbAx);
	    	processOneOfAx(oneOfSubAx, df);
	    
	 //   ont.axioms().filter(ax -> ax instanceof OWLSubClassOfAxiom).forEach(ax -> subAx.add((OWLSubClassOfAxiom) ax));
	 //   ont.axioms().filter(ax -> ax instanceof OWLEquivalentClassesAxiom).forEach(ax -> eqAx.add((OWLEquivalentClassesAxiom) ax));
	 //   ont.axioms().filter(ax -> ax instanceof OWLDisjointClassesAxiom).forEach(ax -> djAx.add((OWLDisjointClassesAxiom) ax));
	    ont.axioms().filter(ax -> ax instanceof OWLSubObjectPropertyOfAxiom).forEach(ax -> subObjProAx.add((OWLSubObjectPropertyOfAxiom) ax));
	    ont.axioms().filter(ax -> ax instanceof OWLInverseObjectPropertiesAxiom).forEach(ax -> invObjProAx.add((OWLInverseObjectPropertiesAxiom) ax));
	    ontology = new Ontology(subAx, Eq, objdAx, objrAx, oneOfSubAx, oneOfEqAx, djAx, djuAx, diffInd, aboxClassAss, aboxObjProAss, subObjProAx, invObjProAx, this.Tu, this.Tui);
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
	private void processOneOfAx(Set<OWLSubClassOfAxiom> oneOfSubAx, OWLDataFactory df ) {
		for(OWLSubClassOfAxiom sb : oneOfSubAx) {
			if(((sb).getSubClass() instanceof OWLObjectOneOf))
				this.oneOf.add(sb);
			else if(((sb).getSubClass() instanceof OWLObjectUnionOf)){
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
	public Set<OWLClassExpression> findIndividual(OWLClassExpression c){
		Set<OWLClassExpression> ce = new HashSet<OWLClassExpression>();
		this.oneOf.stream().filter(sb -> sb.getSubClass().equals(c)).forEach(sb -> ce.add(sb.getSuperClass()));
		this.diffInd.stream().filter(sb -> sb.getSubClass().equals(c)).forEach(sb -> ce.add(sb.getSuperClass()));
		this.aboxClassAss.stream().filter(sb -> sb.getSubClass().equals(c)).forEach(sb -> ce.add(sb.getSuperClass()));
		this.aboxObjProAss.stream().filter(sb -> sb.getSubClass().equals(c)).forEach(sb -> ce.add(sb.getSuperClass()));
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
	public OWLClassExpression getTgAxiom(OWLDataFactory df) {
		OWLClassExpression union;
	 	Set<OWLClassExpression> unionSet = new HashSet<>();
		for (OWLSubClassOfAxiom sb : this.getTg()) {
	    		union = df.getOWLObjectUnionOf(sb.getSubClass().getComplementNNF(), sb.getSuperClass());
	    		unionSet.add(union);
		}
		OWLClassExpression intersection = df.getOWLObjectIntersectionOf(unionSet);
		return intersection;
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
	public Set<OWLSubClassOfAxiom> getOneOfAll() {
		return oneOfAll;
	}
	public void setOneOfAll(Set<OWLSubClassOfAxiom> oneOfAll) {
		this.oneOfAll = oneOfAll;
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

