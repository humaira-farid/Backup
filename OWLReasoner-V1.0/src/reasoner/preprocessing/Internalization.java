package reasoner.preprocessing;

import java.util.HashSet;
import java.util.Set;

import org.semanticweb.owlapi.model.*;

public class Internalization {

	private Set<OWLSubClassOfAxiom> Tu;
	private Set<OWLSubClassOfAxiom> Tui;
	private Set<OWLSubClassOfAxiom> Tg;
	private Set<OWLEquivalentClassesAxiom> Eq;
	private Set<OWLSubClassOfAxiom> oneOf;
	private Set<OWLSubClassOfAxiom> hasValue;
	private Set<OWLSubClassOfAxiom> diffInd; 
	private Set<OWLSubClassOfAxiom> aboxClassAss;
	private Set<OWLSubClassOfAxiom> aboxObjProAss;
	
	
	public Internalization(){
		this.Tu = new HashSet<OWLSubClassOfAxiom>();
		this.Tui = new HashSet<OWLSubClassOfAxiom>();
		this.Tg = new HashSet<OWLSubClassOfAxiom>();
		this.Eq = new HashSet<OWLEquivalentClassesAxiom>();
		this.setOneOf(new HashSet<OWLSubClassOfAxiom>());
		this.setHasValue(new HashSet<OWLSubClassOfAxiom>());
		diffInd = new HashSet<>();
		aboxClassAss = new HashSet<>();
		aboxObjProAss = new HashSet<>();
	}
	public void test(OWLOntology ont) {
		for (OWLAxiom ax : (Iterable<OWLAxiom>)ont.axioms()::iterator) {
	    	ax = ax.getNNF();
	    if(ax instanceof OWLSubClassOfAxiom) {
	    		OWLSubClassOfAxiom sax = (OWLSubClassOfAxiom)ax;
	
		if((sax).getSubClass() instanceof OWLObjectIntersectionOf && ((OWLObjectIntersectionOf)(sax).getSubClass()).asConjunctSet().stream().allMatch(cj -> cj instanceof OWLClass)) {
		System.out.println(sax.getSubClass());
		}
	    }}
	}
		
	public void internalize(OWLOntology ont, OWLDataFactory df) {
		
		Set<OWLSubClassOfAxiom> subAx = new HashSet<>();
	    Set<OWLEquivalentClassesAxiom> eqAx = new HashSet<>();
	    Set<OWLDisjointClassesAxiom> djAx = new HashSet<>();
	    Set<OWLDisjointUnionAxiom> djuAx = new HashSet<>();
	    Set<OWLObjectPropertyDomainAxiom> objdAx = new HashSet<>();
	    Set<OWLObjectPropertyRangeAxiom> objrAx = new HashSet<>();
	    Set<OWLSubClassOfAxiom> oneOfSubAx = new HashSet<>();
	    Set<OWLEquivalentClassesAxiom> oneOfEqAx = new HashSet<>();
	    for (OWLAxiom ax : (Iterable<OWLAxiom>)ont.axioms()::iterator) {
		    	ax = ax.getNNF();
		    if(ax instanceof OWLSubClassOfAxiom) {
		    		OWLSubClassOfAxiom sax = (OWLSubClassOfAxiom)ax;
		    		subAx.add(sax);
		    		if(((sax).getSubClass() instanceof OWLObjectOneOf) || ((sax).getSubClass() instanceof OWLObjectUnionOf && 
		    				((OWLObjectUnionOf)(sax).getSubClass()).disjunctSet().allMatch(dj -> dj instanceof OWLObjectOneOf))) {
			    		oneOfSubAx.add(sax);
		    		}
		    		else if((sax).getSubClass() instanceof OWLObjectSomeValuesFrom && 
		    				((((OWLObjectSomeValuesFrom)(sax).getSubClass()).getFiller() instanceof OWLObjectOneOf) ||
		    					(((OWLObjectSomeValuesFrom)(sax).getSubClass()).getFiller() instanceof OWLObjectUnionOf && 
		    							((OWLObjectUnionOf)((OWLObjectSomeValuesFrom)(sax).getSubClass()).getFiller()).disjunctSet().allMatch(dj -> dj instanceof OWLObjectOneOf)))) {
		    			OWLClassExpression sb = ((OWLObjectSomeValuesFrom)(sax).getSubClass()).getFiller();
		    			OWLObjectPropertyExpression role = ((OWLObjectSomeValuesFrom)(sax).getSubClass()).getProperty();
		    			OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), (sax).getSuperClass());
		    			oneOfSubAx.add(df.getOWLSubClassOfAxiom(sb, sp));
		    		}
		    		else if((sax).getSuperClass() instanceof OWLObjectSomeValuesFrom && 
		    				((((OWLObjectSomeValuesFrom)(sax).getSuperClass()).getFiller() instanceof OWLObjectOneOf) ||
		    					(((OWLObjectSomeValuesFrom)(sax).getSuperClass()).getFiller() instanceof OWLObjectUnionOf && 
		    							((OWLObjectUnionOf)((OWLObjectSomeValuesFrom)(sax).getSuperClass()).getFiller()).disjunctSet().allMatch(dj -> dj instanceof OWLObjectOneOf)))) {
		    			OWLClassExpression sb = ((OWLObjectSomeValuesFrom)(sax).getSuperClass()).getFiller();
		    			OWLObjectPropertyExpression role = ((OWLObjectSomeValuesFrom)(sax).getSuperClass()).getProperty();
		    			OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), (sax).getSubClass());
		    			oneOfSubAx.add(df.getOWLSubClassOfAxiom(sb, sp));
		    		}
		    	/*	else if(ax.nestedClassExpressions().anyMatch(sbx -> sbx instanceof OWLObjectOneOf || sbx instanceof OWLObjectHasValue)) {
		    			this.Tg.add(sax);
		    		}*/
		    		else {
		    			if((sax).getSubClass() instanceof OWLClass)
			    			this.Tu.add(sax);
		    			else if((sax).getSubClass() instanceof OWLObjectIntersectionOf && ((OWLObjectIntersectionOf)(sax).getSubClass()).asConjunctSet().stream().allMatch(cj -> cj instanceof OWLClass)) {
		    				//if(isSimpleObjectIntersectionOf(((OWLObjectIntersectionOf)(sax).getSubClass()).asConjunctSet()))
		    					this.Tui.add(sax);
		    			}
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
	    Set<OWLSubClassOfAxiom> newSbAx = new HashSet<OWLSubClassOfAxiom>();
	   
	    
	    
	    for(OWLEquivalentClassesAxiom eq : eqAx) {
	    		boolean eqTag = false;
	    		for(OWLSubClassOfAxiom sb : this.Tu) {
	    			if(eq.contains(sb.getSubClass())) {
	    				eqTag = true;
	    				for(OWLSubClassOfAxiom eqsb : eq.asOWLSubClassOfAxioms()) {
	    					if(eqsb.getSubClass() instanceof OWLClass) 
	    						newSbAx.add(eqsb);
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
	    for(OWLSubClassOfAxiom nsb : newSbAx)
	    		this.Tu.add(nsb);
	    	processOneOfAx(oneOfSubAx, df);
	    
	 //   ont.axioms().filter(ax -> ax instanceof OWLSubClassOfAxiom).forEach(ax -> subAx.add((OWLSubClassOfAxiom) ax));
	 //   ont.axioms().filter(ax -> ax instanceof OWLEquivalentClassesAxiom).forEach(ax -> eqAx.add((OWLEquivalentClassesAxiom) ax));
	 //   ont.axioms().filter(ax -> ax instanceof OWLDisjointClassesAxiom).forEach(ax -> djAx.add((OWLDisjointClassesAxiom) ax));
	 //   ont.axioms().filter(ax -> ax instanceof OWLDisjointUnionAxiom).forEach(ax -> djuAx.add((OWLDisjointUnionAxiom) ax));
	     
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

