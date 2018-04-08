package reasoner.ilp;

import java.util.*;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;

import ilog.concert.IloException;

public class ILPPreprocessor2 {
	
	List<OWLObjectCardinalityRestriction> cardRes = new ArrayList<>();
	
	
	Set<QCR> qcrs = new HashSet<>();
	Set<Nominal> noms = new HashSet<>();
	Map<Integer, OWLObjectCardinalityRestriction> crMap = new HashMap<Integer, OWLObjectCardinalityRestriction>();
	Map<Integer, QCR> qcrMap = new HashMap<Integer, QCR>();
	Map<Integer, Nominal> nomMap = new HashMap<Integer, Nominal>();
	Set<OWLObjectOneOf> nominals = new HashSet<>();
	OWLDataFactory df;
	OWLOntologyManager man = OWLManager.createOWLOntologyManager();
	
	public ILPPreprocessor2(/*axiom*/) {
		df = man.getOWLDataFactory();
		String base = "http://www.semanticweb.org/ontologies/individualsexample";
		OWLObjectCardinalityRestriction cr1 = df.getOWLObjectMinCardinality(1, df.getOWLObjectProperty(IRI.create(base+"#R")), df.getOWLClass(IRI.create(base+"#A")));
		OWLObjectCardinalityRestriction cr2 = df.getOWLObjectMaxCardinality(1, df.getOWLObjectProperty(IRI.create(base+"#R")), df.getOWLClass(IRI.create(base+"#B")));
		OWLObjectCardinalityRestriction cr3 = df.getOWLObjectMinCardinality(1, df.getOWLObjectProperty(IRI.create(base+"#R")), df.getOWLClass(IRI.create(base+"#C")));
		OWLObjectCardinalityRestriction cr4 = df.getOWLObjectMinCardinality(1, df.getOWLObjectProperty(IRI.create(base+"#R")), df.getOWLClass(IRI.create(base+"#D")));
		OWLObjectCardinalityRestriction cr5 = df.getOWLObjectMinCardinality(1, df.getOWLObjectProperty(IRI.create(base+"#R")), df.getOWLClass(IRI.create(base+"#E")));
		OWLObjectCardinalityRestriction cr6 = df.getOWLObjectMinCardinality(1, df.getOWLObjectProperty(IRI.create(base+"#R")), df.getOWLClass(IRI.create(base+"#F")));
		OWLObjectCardinalityRestriction cr7 = df.getOWLObjectMinCardinality(1, df.getOWLObjectProperty(IRI.create(base+"#R")), df.getOWLClass(IRI.create(base+"#G")));
		OWLObjectCardinalityRestriction cr8 = df.getOWLObjectMinCardinality(1, df.getOWLObjectProperty(IRI.create(base+"#R")), df.getOWLClass(IRI.create(base+"#H")));
		OWLObjectOneOf o1 = df.getOWLObjectOneOf(df.getOWLNamedIndividual(IRI.create(base+"#o")));
		//OWLObjectCardinalityRestriction cr9 = df.getOWLObjectMinCardinality(1, df.getOWLObjectProperty(IRI.create(base+"#R")), df.getOWLClass(IRI.create(base+"#I")));
		//OWLObjectCardinalityRestriction cr10 = df.getOWLObjectMinCardinality(1, df.getOWLObjectProperty(IRI.create(base+"#R")), df.getOWLClass(IRI.create(base+"#J")));
		
		cardRes.add(cr1);
		cardRes.add(cr2);
		cardRes.add(cr3);
		cardRes.add(cr4);
	//	cardRes.add(cr5);
	//	cardRes.add(cr6);
	//	cardRes.add(cr7);
	//	cardRes.add(cr8);
		nominals.add(o1);
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
		CplexModelGenerator3 cmg = new CplexModelGenerator3(this);
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
			QCR qcr = new QCR(q, null);
			qcrMap.put(i, qcr);
			//System.out.println(i +"  "+ qcr.qualifier);
			qcrs.add(qcr);
			++i;
		}
		for(OWLObjectOneOf o : getNominals()) {
			Nominal nom = new Nominal(o);
			noms.add(nom);
			nomMap.put(i, nom);
			++i;
		}
		
	}
	public Set<Nominal> getNoms() {
		return noms;
	}

	public void setNoms(Set<Nominal> noms) {
		this.noms = noms;
	}

	public Map<Integer, Nominal> getNomMap() {
		return nomMap;
	}

	public void setNomMap(Map<Integer, Nominal> nomMap) {
		this.nomMap = nomMap;
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
