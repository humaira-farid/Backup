package reasoner.ilp;

import java.util.*;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;

public class ILPPreprocessor {
	Set<OWLObjectCardinalityRestriction> cardRes = new HashSet<>();
	
	Set<QCR> qcrs = new HashSet<>();
	Map<Integer, OWLObjectCardinalityRestriction> crMap = new HashMap<Integer, OWLObjectCardinalityRestriction>();
	Map<Integer, QCR> qcrMap = new HashMap<Integer, QCR>();
	Set<OWLObjectOneOf> nominals = new HashSet<>();
	OWLDataFactory df;
	OWLOntologyManager man = OWLManager.createOWLOntologyManager();
	
	public ILPPreprocessor() {
		df = man.getOWLDataFactory();
		String base = "http://www.semanticweb.org/ontologies/individualsexample";
		OWLObjectCardinalityRestriction cr1 = df.getOWLObjectMinCardinality(1, df.getOWLObjectProperty(IRI.create(base+"#R")), df.getOWLClass(IRI.create(base+"#A")));
		OWLObjectCardinalityRestriction cr2 = df.getOWLObjectMinCardinality(1, df.getOWLObjectProperty(IRI.create(base+"#R")), df.getOWLClass(IRI.create(base+"#B")));
		OWLObjectCardinalityRestriction cr3 = df.getOWLObjectMinCardinality(1, df.getOWLObjectProperty(IRI.create(base+"#R")), df.getOWLClass(IRI.create(base+"#c")));
		cardRes.add(cr1);
		cardRes.add(cr2);
		cardRes.add(cr3);
	}
	
	public void callILP() {
		CplexModelGenerator cmg = new CplexModelGenerator(this);
		cmg.generateCplexModel();
	}
	public void createMaps() {
		int i = 0;
		for(OWLObjectCardinalityRestriction q : getCardRes()) {
			crMap.put(i, q);
			qcrMap.put(i, new QCR(q));
			++i;
		}
	}
	public Map<Integer, OWLObjectCardinalityRestriction> getCRMap() {
		return crMap;
	}
	public Map<Integer, QCR> getQCRMap() {
		return qcrMap;
	}
	
	public Set<OWLObjectCardinalityRestriction> getCardRes() {
		return cardRes;
	}

	public void setCardRes(Set<OWLObjectCardinalityRestriction> cardRes) {
		this.cardRes = cardRes;
	}

	public Set<QCR> getQcrs() {
		for(OWLObjectCardinalityRestriction q : getCardRes())
			qcrs.add(new QCR(q));
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
