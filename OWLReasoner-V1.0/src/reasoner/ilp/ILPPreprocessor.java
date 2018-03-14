package reasoner.ilp;

import java.util.*;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;

import ilog.concert.IloException;

public class ILPPreprocessor {
	
	List<OWLObjectCardinalityRestriction> cardRes = new ArrayList<>();
	
	
	Set<QCR> qcrs = new HashSet<>();
	Map<Integer, OWLObjectCardinalityRestriction> crMap = new HashMap<Integer, OWLObjectCardinalityRestriction>();
	Map<Integer, QCR> qcrMap = new HashMap<Integer, QCR>();
	Set<OWLObjectOneOf> nominals = new HashSet<>();
	OWLDataFactory df;
	OWLOntologyManager man = OWLManager.createOWLOntologyManager();
	Set<OWLObjectProperty> roles = new HashSet<>();
	Map<OWLObjectProperty, OWLObjectProperty> tempRoleH = new HashMap<>();
	SetMultimap<OWLObjectProperty, OWLObjectProperty> superRoles = HashMultimap.create();
	SetMultimap<OWLObjectProperty, OWLObjectProperty> sR = HashMultimap.create();
	
	Map<OWLObjectProperty, Set<OWLObjectProperty>> superRolesMap = new HashMap<>();
	Map<OWLObjectProperty, Set<OWLObjectProperty>> sRMap = new HashMap<>();
	
	SetMultimap<OWLObjectProperty, OWLClassExpression> forAllMap = HashMultimap.create();
	
	Set<OWLObjectAllValuesFrom> forAllRes = new HashSet<>();

	Set<OWLSubObjectPropertyOfAxiom> subRoleAxioms = new HashSet<>();
	String base = "http://www.semanticweb.org/ontologies/individualsexample";
	
	public ILPPreprocessor(/*axiom*/) {
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
		 */
	}
	
	public void callILP() throws IloException {
		CplexModelGenerator cmg = new CplexModelGenerator(this, this.sRMap, this.forAllMap, this.tempRoleH);
		ILPSolution sol = cmg.getILPSolution();
		
		//CplexModelGenerator2 cmg = new CplexModelGenerator2(this);
		//ILPSolution sol = cmg.solve();
		System.out.println("Solved: "+sol.isSolved());
		for(EdgeInformation ei : sol.getEdgeInformation()) {
			System.out.println("edge info: " + ei.getEdges() +" filler: " + ei.getFillers() +" cardinality : "+ ei.getCardinality());
		}
	}
	
	public void getSubsumers() {
		
	}
	public void getDisjoints() {
		
	}
	public void getDisjointGroups() {
		
	}
	public void getSuperRoles() {
		
	}
	
	public void createMaps() {
		int i = 0;
		for(OWLObjectCardinalityRestriction q : getCardRes()) {
			crMap.put(i, q);
			roles.add(q.getProperty().getNamedProperty());
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
		}*/
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
		
	}
	
	public SetMultimap<OWLObjectProperty, OWLClassExpression> getForAllMap() {
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

	
	
	
}
