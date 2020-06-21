package reasoner;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.semanticweb.owlapi.model.*;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import com.google.common.collect.SetMultimap;

public class Ontology {
	Set<OWLSubClassOfAxiom> Tu = new HashSet<>();
	Set<OWLSubClassOfAxiom> Tui = new HashSet<>();
	Set<OWLSubClassOfAxiom> subAx = new HashSet<>(); 

	Set<OWLSubClassOfAxiom> allSubAx = new HashSet<>(); 
	Set<OWLEquivalentClassesAxiom> Eq = new HashSet<>();
	private Set<OWLSubClassOfAxiom> oneOf = new HashSet<>();
	Set<OWLEquivalentClassesAxiom> allEqAx = new HashSet<>();
	Set<OWLObjectPropertyDomainAxiom> objdAx = new HashSet<>(); 
	Set<OWLObjectPropertyRangeAxiom> objrAx = new HashSet<>();
	Set<OWLSubClassOfAxiom> oneOfSubAx = new HashSet<>(); 
	Set<OWLSubClassOfAxiom> eqSubAx = new HashSet<>(); 
	Set<OWLEquivalentClassesAxiom> oneOfEqAx = new HashSet<>();
	Set<OWLDisjointClassesAxiom> djAx = new HashSet<>(); 
	Set<OWLDisjointUnionAxiom> djuAx = new HashSet<>(); 
	Set<OWLSubClassOfAxiom> diffIndSubAx = new HashSet<>();
	Set<OWLSubClassOfAxiom> aboxClassAss = new HashSet<>(); 
	Set<OWLSubClassOfAxiom> aboxObjProAss = new HashSet<>();
	Set<OWLInverseObjectPropertiesAxiom> invObjProAx = new HashSet<>();
    Set<OWLSubObjectPropertyOfAxiom> subObjProAx = new HashSet<>();
    SetMultimap<OWLObjectPropertyExpression, OWLObjectPropertyExpression> superRoles = HashMultimap.create();
    Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> superRolesMap = new HashMap<>();
    Map<OWLClassExpression, Set<OWLClassExpression>> conceptSubsumersMap = new HashMap<>();
    Map<OWLObjectOneOf, Set<OWLClassExpression>> nominalSubsumersMap = new HashMap<>();
    SetMultimap<OWLObjectOneOf, OWLClassExpression> nominalSubsumers = HashMultimap.create();
    SetMultimap<OWLClassExpression, OWLClassExpression> subsumers = HashMultimap.create();
    SetMultimap<OWLClassExpression, OWLClassExpression> allSubsumers = HashMultimap.create();

    Map<OWLClassExpression, Set<OWLClassExpression>> allSubsumersMap = new HashMap<>();
    SetMultimap<OWLClassExpression, OWLClassExpression> conceptEq = HashMultimap.create();
    SetMultimap<OWLClassExpression, OWLClassExpression> oneOfEq = HashMultimap.create();
    Map<OWLClassExpression, Set<OWLClassExpression>> conceptEqMap = new HashMap<>();
    Map<OWLClassExpression, Set<OWLClassExpression>> oneOfEqMap = new HashMap<>();
    SetMultimap<OWLClassExpression, OWLClassExpression> tuSubsumers = HashMultimap.create();
    SetMultimap<OWLObjectOneOf, OWLClassExpression> nomSubsumers = HashMultimap.create();
    SetMultimap<OWLClassExpression, OWLClassExpression> binarySubsumers = HashMultimap.create();
    SetMultimap<OWLClassExpression, OWLClassExpression> disjointConcepts = HashMultimap.create();
    Set<Set<OWLClassExpression>> disjointGroups = new HashSet<>();
    Set<Set<OWLClassExpression>> disjointNomGroups = new HashSet<>();
    SetMultimap<OWLClassExpression, OWLClassExpression> diffIndividuals = HashMultimap.create();
    Set<OWLObjectPropertyExpression> symmRoles = new HashSet<>();
	public Ontology(Set<OWLSubClassOfAxiom> subAx, 
			Set<OWLEquivalentClassesAxiom> eqAx,
			Set<OWLObjectPropertyDomainAxiom> objdAx, 
			Set<OWLObjectPropertyRangeAxiom> objrAx,
			Set<OWLSubClassOfAxiom> oneOfSubAx, 
			Set<OWLEquivalentClassesAxiom> oneOfEqAx,
			Set<OWLSubClassOfAxiom> oneOf, 
			Set<OWLDisjointClassesAxiom> djAx, 
			Set<OWLDisjointUnionAxiom> djuAx, 
			Set<OWLSubClassOfAxiom> diffIndSubAx,
			Set<OWLSubClassOfAxiom> aboxClassAss, 
			Set<OWLSubClassOfAxiom> aboxObjProAss, 
			Set<OWLSubObjectPropertyOfAxiom> subObjProAx, 
			Set<OWLInverseObjectPropertiesAxiom> invObjProAx, 
			Set<OWLSubClassOfAxiom> tu, Set<OWLSubClassOfAxiom> tui, Set<OWLObjectPropertyExpression> symmRoles) {
		this.subAx = subAx;
		this.Eq = eqAx;
		this.objdAx = objdAx;
		this.objrAx = objrAx;
		this.oneOfSubAx = oneOfSubAx;
		this.oneOfEqAx = oneOfEqAx;
		this.oneOf = oneOf;
		this.djAx = djAx;
		this.djuAx = djuAx;
		this.diffIndSubAx = diffIndSubAx;
		this.aboxClassAss = aboxClassAss;
		this.aboxObjProAss = aboxObjProAss;
		this.allEqAx.addAll(eqAx);
		this.allEqAx.addAll(oneOfEqAx);
		this.subObjProAx = subObjProAx;
		this.invObjProAx = invObjProAx;
		this.Tu = tu;
		this.Tui = tui;
		this.symmRoles = symmRoles;
		createSuperRolesMap();
		createMaps();
	}
	public Set<OWLObjectPropertyExpression> getSuperRoles(OWLObjectPropertyExpression r){
		Set<OWLObjectPropertyExpression> supRoles = new HashSet<>();
		if(this.getSuperRolesMap().get(r) != null)
			supRoles.addAll(this.getSuperRolesMap().get(r));
		return supRoles;
	}
	public Set<OWLObjectPropertyExpression> getInvOfInvSuperRoles(OWLObjectPropertyExpression r){
		Set<OWLObjectPropertyExpression> supRoles = new HashSet<>();
		if(this.getSuperRolesMap().get(r.getInverseProperty()) != null) {
			this.getSuperRolesMap().get(r.getInverseProperty()).stream().forEach(ir -> supRoles.add(ir.getInverseProperty()));
		}
		return supRoles;
	}
	public Set<OWLObjectPropertyExpression> getInverseProperty(OWLObjectPropertyExpression r){
		Set<OWLObjectPropertyExpression> invRoles = new HashSet<>();
		for(OWLInverseObjectPropertiesAxiom inv : getInvObjProAx()) {
			if(inv.properties().anyMatch(ir -> ir.equals(r))) {
				if(inv.getFirstProperty().equals(r))
					invRoles.add(inv.getSecondProperty());
				else
					invRoles.add(inv.getFirstProperty());
			}
		}
		return invRoles;
	}
	public Set<OWLObjectPropertyExpression> getInverseOfInverseProperty(OWLObjectPropertyExpression r){
		Set<OWLObjectPropertyExpression> invRoles = new HashSet<>();
		for(OWLInverseObjectPropertiesAxiom inv : getInvObjProAx()) {
			if(inv.properties().anyMatch(ir -> ir.equals(r))) {
				if(inv.getFirstProperty().equals(r))
					invRoles.add(inv.getSecondProperty().getInverseProperty());
				else
					invRoles.add(inv.getFirstProperty().getInverseProperty());
			}

			else if(inv.properties().anyMatch(ir -> ir.equals(r.getInverseProperty()))) {
				if(inv.getFirstProperty().equals(r.getInverseProperty()))
					invRoles.add(inv.getSecondProperty());
				else
					invRoles.add(inv.getFirstProperty());
			}
		}
		return invRoles;
	}
	public Set<OWLClassExpression> findIndividual(OWLClassExpression c){
		Set<OWLClassExpression> ce = new HashSet<OWLClassExpression>();
		this.oneOf.stream().filter(sb -> sb.getSubClass().equals(c)).forEach(sb -> ce.add(sb.getSuperClass()));
		this.diffIndSubAx.stream().filter(sb -> sb.getSubClass().equals(c)).forEach(sb -> ce.add(sb.getSuperClass()));
		this.aboxClassAss.stream().filter(sb -> sb.getSubClass().equals(c)).forEach(sb -> ce.add(sb.getSuperClass()));
		this.aboxObjProAss.stream().filter(sb -> sb.getSubClass().equals(c)).forEach(sb -> ce.add(sb.getSuperClass()));
		return ce;
	}
	@SuppressWarnings("unchecked")
	private void createMaps() {
		//SetMultimap<OWLObjectOneOf, OWLClassExpression> nomSubAx = HashMultimap.create();
		for(OWLSubClassOfAxiom sb : this.Tu) {
			tuSubsumers.put(sb.getSubClass(), sb.getSuperClass());
		}
		conceptSubsumersMap = (Map<OWLClassExpression, Set<OWLClassExpression>>) (Map<?, ?>) tuSubsumers.asMap();
	
		/*for(OWLSubClassOfAxiom sb : this.aboxClassAss) {
		//	nomSubAx.put((OWLObjectOneOf)sb.getSubClass(), sb.getSuperClass());
			nominalSubsumers.put((OWLObjectOneOf)sb.getSubClass(), sb.getSuperClass());
		}*/
		for(OWLSubClassOfAxiom sb : this.oneOf) {
		//	nomSubAx.put((OWLObjectOneOf)sb.getSubClass(), sb.getSuperClass());
			nominalSubsumers.put((OWLObjectOneOf)sb.getSubClass(), sb.getSuperClass());
		}
		for(OWLSubClassOfAxiom sb : this.diffIndSubAx) {
			//	nomSubAx.put((OWLObjectOneOf)sb.getSubClass(), sb.getSuperClass());
				nominalSubsumers.put((OWLObjectOneOf)sb.getSubClass(), sb.getSuperClass());
			}
		this.nominalSubsumersMap = (Map<OWLObjectOneOf, Set<OWLClassExpression>>) (Map<?, ?>) nominalSubsumers.asMap();
		for(OWLObjectOneOf sb : nominalSubsumers.keySet()) {
			for(OWLObjectOneOf c : nominalSubsumersMap.keySet()) {
				if(nominalSubsumersMap.get(c).contains(sb)) {
					nominalSubsumersMap.get(c).addAll(nominalSubsumers.get(sb));
				}
			}
		}
		for(OWLObjectOneOf sb : nominalSubsumersMap.keySet()) {
			for(OWLClassExpression c : conceptSubsumersMap.keySet()) {
				if(conceptSubsumersMap.get(c).contains(sb)) {
					conceptSubsumersMap.get(c).addAll(nominalSubsumersMap.get(sb));
				}
			}
		}
		for(OWLClassExpression sb : conceptSubsumersMap.keySet()) {
			for(OWLClassExpression c : conceptSubsumersMap.keySet()) {
				if(conceptSubsumersMap.get(c).contains(sb)) {
					conceptSubsumersMap.get(c).addAll(conceptSubsumersMap.get(sb));
				}
			}
		}
		for(OWLClassExpression sb : conceptSubsumersMap.keySet()) {
			for(OWLObjectOneOf c : nominalSubsumersMap.keySet()) {
				if(nominalSubsumersMap.get(c).contains(sb)) {
					nominalSubsumersMap.get(c).addAll(conceptSubsumersMap.get(sb));
				}
			}
		}
		/*for(OWLClassExpression sb : nominalSubsumersMap.keySet()) {
			System.out.println("concept: "+sb +" subsumers : "+nominalSubsumersMap.get(sb));
		}
		for(OWLClassExpression sb : conceptSubsumersMap.keySet()) {
			System.out.println("concept: "+sb +" subsumers : "+conceptSubsumersMap.get(sb));
		}*/
		
		for(OWLSubClassOfAxiom sb : this.Tui) {
			binarySubsumers.put(sb.getSubClass(), sb.getSuperClass());
		}
		for(OWLDisjointClassesAxiom dj : this.djAx) {
			dj.asOWLSubClassOfAxioms().forEach(sb -> disjointConcepts.put(sb.getSubClass(), sb.getSuperClass().getComplementNNF()));
		}
		for(OWLDisjointUnionAxiom dj : this.djuAx) {
			((OWLDisjointUnionAxiom) dj).getOWLDisjointClassesAxiom().asOWLSubClassOfAxioms().forEach(sb -> disjointConcepts.put(sb.getSubClass(), sb.getSuperClass().getComplementNNF()));
		}
		for(OWLSubClassOfAxiom sb : this.Tu) {
			if(!(sb.getSubClass() instanceof OWLObjectComplementOf) && (sb.getSuperClass() instanceof OWLObjectComplementOf) )
				disjointConcepts.put(sb.getSubClass(), sb.getSuperClass().getComplementNNF());
		}
		//System.out.println("tui size "+Tui.size());
		for(OWLSubClassOfAxiom sb : this.Tui) {
			if(sb.getSuperClass() instanceof OWLObjectComplementOf) {
				Set<OWLClassExpression> dg = new HashSet<>(sb.getSubClass().asConjunctSet());
				dg.add(sb.getSuperClass().getComplementNNF());
				disjointGroups.add(dg);
			}
			else if(sb.getSuperClass().isOWLNothing())
				disjointGroups.add(sb.getSubClass().asConjunctSet());
		}
		for(OWLSubClassOfAxiom sb : this.diffIndSubAx) {
			//System.out.println("diff "+sb.getSubClass()+" - "+sb.getSuperClass().getComplementNNF());
			diffIndividuals.put(sb.getSubClass(), sb.getSuperClass().getComplementNNF());
		}
		for(OWLEquivalentClassesAxiom eq : Eq) {
			for(OWLSubClassOfAxiom sb : eq.asOWLSubClassOfAxioms()) {
				eqSubAx.add(sb);
				conceptEq.put(sb.getSubClass(), sb.getSuperClass());
			}
		}
		
		/*for(OWLEquivalentClassesAxiom eq : oneOfEqAx) {
			for(OWLSubClassOfAxiom sb : eq.asOWLSubClassOfAxioms()){
				eqSubAx.add(sb);
				conceptEq.put(sb.getSubClass(), sb.getSuperClass());
			}
		}*/
		conceptEqMap = (Map<OWLClassExpression, Set<OWLClassExpression>>) (Map<?, ?>) conceptEq.asMap();
		for(OWLClassExpression sb :  conceptEq.keySet()) {
			for(OWLClassExpression c : conceptEqMap.keySet()) {
				if(conceptEqMap.get(c).contains(sb)) {
					conceptEqMap.get(c).addAll(conceptEq.get(sb));
				}
			}
		}
		
	}
	private void createSuperRolesMap() {
		for(OWLSubObjectPropertyOfAxiom obj : getSubObjProAx()) {
			superRoles.put(obj.getSubProperty(), obj.getSuperProperty());
		}
		for(OWLObjectPropertyExpression sr : symmRoles) {
			superRoles.put(sr, sr.getInverseProperty());
			superRoles.put(sr.getInverseProperty(), sr);
		}
		this.superRolesMap = (Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>>) (Map<?, ?>) superRoles.asMap();
		
		for(OWLObjectPropertyExpression sr : superRoles.keySet()) {
			for(OWLObjectPropertyExpression r : superRolesMap.keySet()) {
				if(superRolesMap.get(r).contains(sr)) {
					superRolesMap.get(r).addAll(superRoles.get(sr));
				}
			}
		}
	}
	/*private void createMaps() {
		for(OWLSubObjectPropertyOfAxiom obj : getSubObjProAx()) {
			superRoles.put(obj.getSubProperty(), obj.getSuperProperty());
		}
		this.superRolesMap = (Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>>) (Map<?, ?>) superRoles.asMap();
		
		for(OWLSubObjectPropertyOfAxiom srAx : getSubObjProAx()) {
			for(OWLObjectPropertyExpression r : superRolesMap.keySet()) {
				if(superRolesMap.get(r).contains(srAx.getSubProperty())) {
					superRolesMap.get(r).add(srAx.getSuperProperty());
				}
			}
		}
		
		////
		allSubAx.addAll(Tu);
		allSubAx.addAll(aboxClassAss);
		allSubAx.addAll(aboxObjProAss);
		allSubAx.addAll(oneOf);
		for(OWLSubClassOfAxiom sb : this.Tu) {
			allSubsumers.put(sb.getSubClass(), sb.getSuperClass());
		}
		for(OWLSubClassOfAxiom sb : this.aboxClassAss) {
			allSubsumers.put(sb.getSubClass(), sb.getSuperClass());
		}
		for(OWLSubClassOfAxiom sb : this.aboxObjProAss) {
			allSubsumers.put(sb.getSubClass(), sb.getSuperClass());
		}
		for(OWLSubClassOfAxiom sb : this.oneOf) {
			allSubsumers.put(sb.getSubClass(), sb.getSuperClass());
		}
		this.allSubsumersMap = (Map<OWLClassExpression, Set<OWLClassExpression>>) (Map<?, ?>) allSubsumers.asMap();
		
		for(OWLSubClassOfAxiom sbAx : allSubAx) {
			for(OWLClassExpression c : allSubsumersMap.keySet()) {
				if(allSubsumersMap.get(c).contains(sbAx.getSubClass())) {
					allSubsumersMap.get(c).add(sbAx.getSuperClass());
				}
			}
		}
		
		////
		for(OWLSubClassOfAxiom sb : this.Tu) {
			tuSubsumers.put(sb.getSubClass(), sb.getSuperClass());
		}
		
		for(OWLSubClassOfAxiom sb : this.subAx) {
			subsumers.put(sb.getSubClass(), sb.getSuperClass());
			if(sb.getSubClass() instanceof OWLObjectOneOf) {
				nominalSubsumers.put((OWLObjectOneOf)sb.getSubClass(), sb.getSuperClass());
				//nominalSubsumers.putAll((OWLObjectOneOf)sb.getSubClass(), this.findIndividual((OWLObjectOneOf)sb.getSubClass()));
			}
		}
		nominalSubsumersMap = (Map<OWLObjectOneOf, Set<OWLClassExpression>>) (Map<?, ?>) nominalSubsumers.asMap();
		for(OWLSubClassOfAxiom sb : this.subAx) {
			for(OWLObjectOneOf c : nominalSubsumersMap.keySet()) {
				if(nominalSubsumersMap.get(c).contains(sb.getSubClass())) {
					nominalSubsumersMap.get(c).add(sb.getSuperClass());
				}
			}
		}
		
		
		
		conceptSubsumersMap = (Map<OWLClassExpression, Set<OWLClassExpression>>) (Map<?, ?>) tuSubsumers.asMap();
		
		for(OWLSubClassOfAxiom sb : this.Tu) {
			for(OWLClassExpression c : conceptSubsumersMap.keySet()) {
				if(conceptSubsumersMap.get(c).contains(sb.getSubClass())) {
					conceptSubsumersMap.get(c).add(sb.getSuperClass());
				}
			}
		}
	/*	for(OWLSubClassOfAxiom sb : this.Tu) {
			for(OWLClassExpression c : conceptSubsumersMap.keySet()) {
				if(conceptSubsumersMap.get(c).contains(sb.getSubClass())) {
					conceptSubsumersMap.get(c).add(sb.getSuperClass());
					if(tuSubsumers.containsKey(sb.getSuperClass()))
						conceptSubsumersMap.get(c).addAll(tuSubsumers.get(sb.getSuperClass()));
					else if((sb.getSuperClass() instanceof OWLObjectUnionOf) 
							&& (sb.getSuperClass().asDisjunctSet().stream().allMatch(dj -> (dj instanceof OWLClass)||(dj instanceof OWLObjectOneOf)))) {
						for(OWLClassExpression cdj : sb.getSuperClass().asDisjunctSet()) {
							if(cdj instanceof OWLClass) {
								if(tuSubsumers.containsKey(cdj))
									conceptSubsumersMap.get(c).addAll(tuSubsumers.get(cdj));
							}
							else if(cdj instanceof OWLObjectOneOf) {
								if(nominalSubsumersMap.containsKey(cdj)){
									System.out.println("cdj "+ cdj+" sup "+nominalSubsumersMap.get(cdj));
									conceptSubsumersMap.get(c).addAll(nominalSubsumersMap.get(cdj));
								}
							}
						}
					}
				}
				
			}
		}
		*/
		/*for(OWLSubClassOfAxiom sb : this.Tui) {
			binarySubsumers.put(sb.getSubClass(), sb.getSuperClass());
		}
		for(OWLDisjointClassesAxiom dj : this.djAx) {
			dj.asOWLSubClassOfAxioms().forEach(sb -> disjointConcepts.put(sb.getSubClass(), sb.getSuperClass().getComplementNNF()));
		}
		for(OWLSubClassOfAxiom sb : this.Tu) {
			if(!(sb.getSubClass() instanceof OWLObjectComplementOf) && (sb.getSuperClass() instanceof OWLObjectComplementOf) )
				disjointConcepts.put(sb.getSubClass(), sb.getSuperClass().getComplementNNF());
		}
		//System.out.println("tui size "+Tui.size());
		for(OWLSubClassOfAxiom sb : this.Tui) {
			if(sb.getSuperClass() instanceof OWLObjectComplementOf) {
				Set<OWLClassExpression> dg = new HashSet<>(sb.getSubClass().asConjunctSet());
				dg.add(sb.getSuperClass().getComplementNNF());
				disjointGroups.add(dg);
			}
			else if(sb.getSuperClass().isOWLNothing())
				disjointGroups.add(sb.getSubClass().asConjunctSet());
		}
		for(OWLSubClassOfAxiom sb : this.diffIndSubAx) {
			//System.out.println("diff "+sb.getSubClass()+" - "+sb.getSuperClass().getComplementNNF());
			diffIndividuals.put(sb.getSubClass(), sb.getSuperClass().getComplementNNF());
		}
		for(OWLEquivalentClassesAxiom eq : Eq) {
			for(OWLSubClassOfAxiom sb : eq.asOWLSubClassOfAxioms()) {
				eqSubAx.add(sb);
				conceptEq.put(sb.getSubClass(), sb.getSuperClass());
			}
		}
		
		for(OWLEquivalentClassesAxiom eq : oneOfEqAx) {
			for(OWLSubClassOfAxiom sb : eq.asOWLSubClassOfAxioms()){
				eqSubAx.add(sb);
				conceptEq.put(sb.getSubClass(), sb.getSuperClass());
			}
		}
		conceptEqMap = (Map<OWLClassExpression, Set<OWLClassExpression>>) (Map<?, ?>) conceptEq.asMap();
		for(OWLSubClassOfAxiom sb : eqSubAx) {
			for(OWLClassExpression c : conceptEqMap.keySet()) {
				if(conceptEqMap.get(c).contains(sb.getSubClass())) {
					conceptEqMap.get(c).add(sb.getSuperClass());
				}
			}
		}
		
		
	}*/
	private Map<OWLClassExpression, Set<OWLClassExpression>> getConceptSubsumersMap() {
		return conceptSubsumersMap;
	}
	public boolean hasNominal(OWLClassExpression ce) {
		if(getAllSubsumers(ce)!=null) {
			if(getAllSubsumers(ce).stream().anyMatch(c -> c instanceof OWLObjectOneOf))
				return true;
			else if(getAllSubsumers(ce).stream().anyMatch(c -> c instanceof OWLObjectUnionOf)){
				//getAllSubsumers(ce).stream().filter(c -> c instanceof OWLObjectUnionOf).map(c -> (OWLObjectUnionOf)c).collect(Collectors.toSet());
				for(OWLClassExpression sp : getAllSubsumers(ce).stream().filter(c -> c instanceof OWLObjectUnionOf).collect(Collectors.toSet())) {
					if(sp.asDisjunctSet().stream().anyMatch(dj -> dj instanceof OWLObjectOneOf))
							return true;
				}
			}
			else if(getAllSubsumers(ce).stream().anyMatch(c -> c instanceof OWLObjectIntersectionOf)) {
				for(OWLClassExpression sp : getAllSubsumers(ce).stream().filter(c -> c instanceof OWLObjectIntersectionOf).collect(Collectors.toSet())) {
					if(sp.asConjunctSet().stream().anyMatch(cj -> cj instanceof OWLObjectOneOf))
							return true;
				}
			}
		}
		return false;
	}

	private Map<OWLObjectOneOf, Set<OWLClassExpression>> getNominalSubsumersMap() {
		return nominalSubsumersMap;
	}


	public Set<OWLClassExpression> getSubsumers(OWLObjectOneOf o){
		Set<OWLClassExpression> sup = new HashSet<OWLClassExpression>();
		this.subAx.stream().filter(sb -> sb.getSubClass().equals(o)).forEach(sb -> sup.add(sb.getSuperClass()));
		for(OWLEquivalentClassesAxiom eq : this.oneOfEqAx) {
			if(eq.contains(o)) {
				for(OWLSubClassOfAxiom eqsb : eq.asOWLSubClassOfAxioms()) {
					if(eqsb.getSubClass().equals(o)) {
						sup.add(eqsb.getSuperClass()); break;
					}
					else {
						sup.add(eqsb.getSubClass()); break;
					}		
				}
			}
		}
		return sup;
	}
	public Set<OWLClassExpression> getSubsumers(OWLClassExpression c){
		if(c instanceof OWLClass)
			return getSubsumers(c);
		else if(c instanceof OWLObjectOneOf)
			return getSubsumers((OWLObjectOneOf)c);
		return new HashSet<OWLClassExpression>();
	}
	
	public Set<OWLClassExpression> getSubsumers(OWLClass c){
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
	/*public Set<OWLClassExpression> getAllSubsumers2(OWLClassExpression c){
		Set<OWLClassExpression> ce = new HashSet<OWLClassExpression>();
		if(this.allSubsumersMap.get(c) != null)
			ce.addAll(allSubsumersMap.get(c));
		if(this.conceptEqMap.get(c) != null)
			ce.addAll(conceptEqMap.get(c));
		Set<OWLClassExpression> ce2 = new HashSet<OWLClassExpression>();
		for(OWLClassExpression sp : ce) {
			if(this.conceptEqMap.get(sp) != null)
				ce2.addAll(conceptEqMap.get(sp));
		}
		ce.addAll(ce2);
		return ce;
	}*/
	public Set<OWLClassExpression> getAllSubsumers(OWLClassExpression c){
		Set<OWLClassExpression> ce = new HashSet<OWLClassExpression>();
		if(this.conceptSubsumersMap.get(c) != null)
			ce.addAll(conceptSubsumersMap.get(c));
		if(this.conceptEqMap.get(c) != null)
			ce.addAll(conceptEqMap.get(c));
		Set<OWLClassExpression> ce2 = new HashSet<OWLClassExpression>();
		for(OWLClassExpression sp : ce) {
			if(this.conceptEqMap.get(sp) != null)
				ce2.addAll(conceptEqMap.get(sp));
		}
		ce.addAll(ce2);
		//System.err.println("c "+ c+" subsumers "+ce.size());
		return ce;
	}
	public Set<OWLClassExpression> getAllComplementEq(OWLClassExpression c){
		Set<OWLClassExpression> ce = new HashSet<OWLClassExpression>();
		if(this.conceptEqMap.get(c) != null) {
			for(OWLClassExpression ceq : conceptEqMap.get(c)) {
				OWLClassExpression ceqNNF = ceq.getComplementNNF();
				ce.add(ceqNNF);
				if(ceqNNF instanceof OWLClass) {
					if(this.conceptSubsumersMap.get(ceqNNF) != null)
						ce.addAll(conceptSubsumersMap.get(ceqNNF));
				}
				else if(ceqNNF instanceof OWLObjectOneOf) {
					if(this.nominalSubsumersMap.get(ceqNNF) != null)
						ce.addAll(nominalSubsumersMap.get(ceqNNF));
				}
			}
		}
			//conceptEqMap.get(c).stream().forEach(ceq -> ce.add(ceq.getComplementNNF()));
		return ce;
	}
	public Set<OWLClassExpression> getAllSubsumers(OWLObjectOneOf o){
		Set<OWLClassExpression> ce = new HashSet<OWLClassExpression>();
		if(this.nominalSubsumersMap.get(o) != null)
			ce.addAll(nominalSubsumersMap.get(o));
		if(this.conceptEqMap.get(o) != null)
			ce.addAll(conceptEqMap.get(o));
		Set<OWLClassExpression> ce2 = new HashSet<OWLClassExpression>();
		for(OWLClassExpression sp : ce) {
			if(this.conceptEqMap.get(sp) != null)
				ce2.addAll(conceptEqMap.get(sp));
		}
		ce.addAll(ce2);
		return ce;
	}
	public Set<OWLClassExpression> getDisjointConcepts(OWLClassExpression ce){
		Set<OWLClassExpression> disjoints = new HashSet<OWLClassExpression>();
		this.disjointConcepts.keySet().stream().filter(c -> c.equals(ce)).forEach(c -> disjoints.addAll(disjointConcepts.get(c)));
		for(OWLEquivalentClassesAxiom eq : this.Eq) {
			if(eq.contains(ce)) {
				for(OWLSubClassOfAxiom eqsb : eq.asOWLSubClassOfAxioms()) {
					if(eqsb.getSubClass().equals(ce) && eqsb.getSuperClass() instanceof OWLObjectComplementOf) {
						disjoints.add(eqsb.getSuperClass()); break;
					}		
				}
			}
		}
		return disjoints;
	}
	public Set<OWLClassExpression> getDisjointConcepts(OWLObjectOneOf o){
		Set<OWLClassExpression> disjoints = new HashSet<OWLClassExpression>();
		this.disjointConcepts.keySet().stream().filter(c -> c.equals(o)).forEach(c -> disjoints.addAll(disjointConcepts.get(c)));
		this.diffIndividuals.keySet().stream().filter(c -> c.equals(o)).forEach(c -> disjoints.addAll(diffIndividuals.get(c)));
		for(OWLEquivalentClassesAxiom eq : this.oneOfEqAx) {
			if(eq.contains(o)) {
				for(OWLSubClassOfAxiom eqsb : eq.asOWLSubClassOfAxioms()) {
					if(eqsb.getSubClass().equals(o) && eqsb.getSuperClass() instanceof OWLObjectComplementOf) {
						disjoints.add(eqsb.getSuperClass()); break;
					}		
				}
			}
		}
		return disjoints;
	}
	
	public Set<Set<OWLClassExpression>> getDisjointGroups(Set<OWLClassExpression> setCe){
		Set<Set<OWLClassExpression>> disjoints = new HashSet<>();
		for(Set<OWLClassExpression> dg : this.disjointGroups) {
			 if(setCe.containsAll(dg))
				disjoints.add(dg);
		}
		return disjoints;
	}
	public Map<OWLClassExpression, Set<OWLClassExpression>> getBinarySubsumption(Set<OWLClassExpression> setCe){
		Map<OWLClassExpression, Set<OWLClassExpression>> binarySub = new HashMap<>();
		for(OWLClassExpression bs : this.binarySubsumers.keySet()) {
			 if(setCe.containsAll(bs.asConjunctSet()))
				binarySub.put(bs, binarySubsumers.get(bs));
		}
		return binarySub;
	}
	
	public Set<OWLObjectAllValuesFrom> getRoleRange(OWLObjectPropertyExpression r) {
		Set<OWLObjectAllValuesFrom> ranges = new HashSet<OWLObjectAllValuesFrom>();
		for(OWLObjectPropertyRangeAxiom range: this.objrAx) {
			if(range.getProperty().equals(r))
				ranges.add((OWLObjectAllValuesFrom)range.asOWLSubClassOfAxiom().getSuperClass());
		}
		return ranges;
		
	}


	public Set<OWLSubClassOfAxiom> getTu() {
		return Tu;
	}


	public Set<OWLSubClassOfAxiom> getTui() {
		return Tui;
	}


	public Set<OWLSubClassOfAxiom> getSubAx() {
		return subAx;
	}


	public Set<OWLEquivalentClassesAxiom> getEq() {
		return Eq;
	}


	public Set<OWLEquivalentClassesAxiom> getAllEqAx() {
		return allEqAx;
	}


	public Set<OWLObjectPropertyDomainAxiom> getObjdAx() {
		return objdAx;
	}


	public Set<OWLObjectPropertyRangeAxiom> getObjrAx() {
		return objrAx;
	}


	public Set<OWLSubClassOfAxiom> getOneOfSubAx() {
		return oneOfSubAx;
	}


	public Set<OWLEquivalentClassesAxiom> getOneOfEqAx() {
		return oneOfEqAx;
	}


	public Set<OWLSubClassOfAxiom> getDiffIndSubAx() {
		return diffIndSubAx;
	}


	public Set<OWLSubClassOfAxiom> getAboxClassAss() {
		return aboxClassAss;
	}


	private Set<OWLInverseObjectPropertiesAxiom> getInvObjProAx() {
		return invObjProAx;
	}

	public Set<OWLSubClassOfAxiom> getAboxObjProAss() {
		return aboxObjProAss;
	}


	public Set<OWLSubObjectPropertyOfAxiom> getSubObjProAx() {
		return subObjProAx;
	}


	public SetMultimap<OWLObjectPropertyExpression, OWLObjectPropertyExpression> getSuperRoles() {
		return superRoles;
	}


	public SetMultimap<OWLClassExpression, OWLClassExpression> getSubsumers() {
		return subsumers;
	}


	public SetMultimap<OWLClassExpression, OWLClassExpression> getTuSubsumers() {
		return tuSubsumers;
	}


	public SetMultimap<OWLClassExpression, OWLClassExpression> getBinarySubsumers() {
		return binarySubsumers;
	}


	public SetMultimap<OWLClassExpression, OWLClassExpression> getDisjointConcepts() {
		return disjointConcepts;
	}
	public void addDisjointConcepts(OWLClassExpression c1, OWLClassExpression c2) {
		disjointConcepts.put(c1, c2);
	}

	public Set<Set<OWLClassExpression>> getDisjointGroups() {
		return disjointGroups;
	}


	public SetMultimap<OWLClassExpression, OWLClassExpression> getDiffIndividuals() {
		return diffIndividuals;
	}
	public void addDiffIndividuals(OWLClassExpression o1, OWLClassExpression o2) {
		diffIndividuals.put(o1, o2);
	}

	public Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> getSuperRolesMap() {
		return superRolesMap;
	}
	
	
}
