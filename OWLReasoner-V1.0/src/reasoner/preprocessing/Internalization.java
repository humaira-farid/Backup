package reasoner.preprocessing;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.util.DefaultPrefixManager;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;

import reasoner.Configuration;
import reasoner.Ontology;

public class Internalization {
	boolean prefixSet = false;
	Set<OWLIndividual> individuals = new HashSet<>();
	Set<OWLSubClassOfAxiom> subAx = new HashSet<>();
	private Set<OWLSubClassOfAxiom> Tu;
	private Set<OWLSubClassOfAxiom> Tui;
	private Set<OWLClassExpression> tuConcepts;
	private Set<OWLSubClassOfAxiom> Tg;
	Set<OWLSubClassOfAxiom> oneOfSubAx;
	private Set<OWLEquivalentClassesAxiom> Eq;
	private Set<OWLSubClassOfAxiom> oneOf;
	private Set<OWLSubClassOfAxiom> oneOfIn;
	// private Set<OWLSubClassOfAxiom> oneOfAll;
	private Set<OWLSubClassOfAxiom> hasValue;
	private Set<OWLSubClassOfAxiom> diffInd;
	private Set<OWLSubClassOfAxiom> aboxClassAss;
	private Set<OWLSubClassOfAxiom> aboxObjProAss;
	private Set<OWLDisjointClassesAxiom> djAx;
	private Set<OWLDisjointUnionAxiom> djuAx;
	Set<OWLObjectPropertyRangeAxiom> objrAx = new HashSet<>();
	SetMultimap<OWLObjectPropertyExpression, OWLClassExpression> rangeRestrictions = HashMultimap.create();
	SetMultimap<OWLObjectPropertyExpression, OWLClassExpression> domainRestrictions = HashMultimap.create();
	SetMultimap<OWLObjectPropertyExpression, OWLObjectUnionOf> extendedDomainRestrictions = HashMultimap.create();
	SetMultimap<OWLClassExpression, OWLClassExpression> atomicSupClassGCIs = HashMultimap.create();
	Set<OWLSubClassOfAxiom> atomicGCIs = new HashSet<>();
	Set<OWLSubClassOfAxiom> tgAx = new HashSet<>();
	DefaultPrefixManager prefixManager = new DefaultPrefixManager();
	Configuration config;

	Ontology ontology;
	OWLDataFactory df;
	Set<OWLObjectPropertyExpression> symmRoles = new HashSet<>();

	public Internalization(OWLDataFactory df, Configuration config) {
		this.Tu = new HashSet<OWLSubClassOfAxiom>();
		this.Tui = new HashSet<OWLSubClassOfAxiom>();
		this.Tg = new HashSet<OWLSubClassOfAxiom>();
		this.tuConcepts = new HashSet<>();
		this.oneOfSubAx = new HashSet<>();
		this.Eq = new HashSet<OWLEquivalentClassesAxiom>();
		this.setOneOf(new HashSet<OWLSubClassOfAxiom>());
		this.setOneOfIn(new HashSet<OWLSubClassOfAxiom>());
		// this.setOneOfAll(new HashSet<OWLSubClassOfAxiom>());
		this.setHasValue(new HashSet<OWLSubClassOfAxiom>());
		diffInd = new HashSet<>();
		aboxClassAss = new HashSet<>();
		aboxObjProAss = new HashSet<>();
		djAx = new HashSet<>();
		djuAx = new HashSet<>();
		this.df = df;
		this.config = config;

	}

	public void test(OWLOntology ont) {
		for (OWLAxiom ax : (Iterable<OWLAxiom>) ont.axioms()::iterator) {
			ax = ax.getNNF();
			if (ax instanceof OWLSubClassOfAxiom) {
				OWLSubClassOfAxiom sax = (OWLSubClassOfAxiom) ax;

				if ((sax).getSubClass() instanceof OWLObjectIntersectionOf
						&& ((OWLObjectIntersectionOf) (sax).getSubClass()).asConjunctSet().stream()
								.allMatch(cj -> cj instanceof OWLClass)) {
					System.out.println(sax.getSubClass());
				}
			}
		}
	}

	public boolean handleQualifiedRangeRestriction(OWLClassExpression sub, OWLClassExpression sup) {
		OWLClassExpression filler = ((OWLObjectSomeValuesFrom) sub).getFiller();
		// --> R some A SubClassOf B -- OR -- R some A SubClassOf (B and C)
		if (sup instanceof OWLClass || sup instanceof OWLObjectOneOf
				|| (sup instanceof OWLObjectIntersectionOf && ((OWLObjectIntersectionOf) sup).conjunctSet()
						.allMatch(cj -> (cj instanceof OWLClass) || (cj instanceof OWLObjectOneOf)))) {
			// --> if A is an OWLClass
			if (filler instanceof OWLClass || filler.isOWLThing()) {
				OWLObjectPropertyExpression role = ((OWLObjectSomeValuesFrom) sub).getProperty();
				tuConcepts.add(filler);
				if (sup instanceof OWLClass || sup instanceof OWLObjectOneOf) {
					OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), sup);
					this.Tu.add(df.getOWLSubClassOfAxiom(filler, sp));
				} else if (sup instanceof OWLObjectIntersectionOf) {
					sup.asConjunctSet().forEach(cj -> this.Tu.add(df.getOWLSubClassOfAxiom(filler,
							df.getOWLObjectAllValuesFrom(role.getInverseProperty(), cj))));
				}
				return true;
			}
			// --> if A is a nominal
			else if (filler instanceof OWLObjectOneOf) {
				OWLObjectPropertyExpression role = ((OWLObjectSomeValuesFrom) sub).getProperty();
				if (sup instanceof OWLClass || sup instanceof OWLObjectOneOf) {
					OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), sup);
					this.oneOfSubAx.add(df.getOWLSubClassOfAxiom(filler, sp));
				} else if (sup instanceof OWLObjectIntersectionOf) {
					sup.asConjunctSet().forEach(cj -> this.oneOfSubAx.add(df.getOWLSubClassOfAxiom(filler,
							df.getOWLObjectAllValuesFrom(role.getInverseProperty(), cj))));
				}
				return true;
			}
			// --> if A is OWLObjectUnionOf
			else if (filler instanceof OWLObjectUnionOf && filler.disjunctSet()
					.allMatch(dj -> (dj instanceof OWLClass) || (dj instanceof OWLObjectOneOf))) {
				OWLObjectPropertyExpression role = ((OWLObjectSomeValuesFrom) sub).getProperty();
				if (sup instanceof OWLClass || sup instanceof OWLObjectOneOf) {
					OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), sup);
					for (OWLClassExpression ce : ((OWLObjectUnionOf) sub).asDisjunctSet()) {
						if (ce instanceof OWLClass) {
							tuConcepts.add(ce);
							this.Tu.add(df.getOWLSubClassOfAxiom(ce, sp));
						} else if (ce instanceof OWLObjectOneOf) {
							this.oneOfSubAx.add(df.getOWLSubClassOfAxiom(ce, sp));
						}
					}
				} else if (sup instanceof OWLObjectIntersectionOf) {
					for (OWLClassExpression ce : ((OWLObjectIntersectionOf) sup).asConjunctSet()) {
						OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), ce);
						for (OWLClassExpression ce2 : ((OWLObjectUnionOf) sub).asDisjunctSet()) {
							if (ce2 instanceof OWLClass) {
								tuConcepts.add(ce2);
								this.Tu.add(df.getOWLSubClassOfAxiom(ce2, sp));
							} else if (ce2 instanceof OWLObjectOneOf) {
								this.oneOfSubAx.add(df.getOWLSubClassOfAxiom(ce2, sp));
							}
						}
					}
				}
				return true;
			}
			// --> if A is OWLObjectIntersectionOf
			else if (filler instanceof OWLObjectIntersectionOf && filler.conjunctSet()
					.allMatch(cj -> (cj instanceof OWLClass) || (cj instanceof OWLObjectOneOf))) {
				OWLObjectPropertyExpression role = ((OWLObjectSomeValuesFrom) sub).getProperty();
				if (sup instanceof OWLClass || sup instanceof OWLObjectOneOf) {
					OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), sup);
					this.Tui.add(df.getOWLSubClassOfAxiom(/*filler*/df.getOWLObjectIntersectionOf(filler.asConjunctSet()), sp));
				} else if (sup instanceof OWLObjectIntersectionOf) {
					for (OWLClassExpression ce : ((OWLObjectIntersectionOf) sup).asConjunctSet()) {
						OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), ce);
						this.Tui.add(df.getOWLSubClassOfAxiom(/*filler*/df.getOWLObjectIntersectionOf(filler.asConjunctSet()), sp));
					}
				}
			}
			return true;
		}

		return false;
	}

	public boolean handleNominal(OWLClassExpression sub, OWLClassExpression sup) {
		if(sub instanceof OWLObjectHasValue){
			if (sup instanceof OWLClass || sup instanceof OWLObjectOneOf
					|| (sup instanceof OWLObjectIntersectionOf && ((OWLObjectIntersectionOf) sup).conjunctSet()
							.allMatch(cj -> (cj instanceof OWLClass) || (cj instanceof OWLObjectOneOf)))) {
				OWLIndividual ind = ((OWLObjectHasValue) sub).getFiller();
				OWLObjectPropertyExpression role = ((OWLObjectHasValue) sub).getProperty();
				OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), sup);
				OWLClassExpression sb = df.getOWLObjectOneOf(ind);
				oneOfSubAx.add(df.getOWLSubClassOfAxiom(sb, sp));
				return true;
			}
		}
		if(sub instanceof OWLObjectSomeValuesFrom){
			if (sup instanceof OWLClass || sup instanceof OWLObjectOneOf
					|| (sup instanceof OWLObjectIntersectionOf && ((OWLObjectIntersectionOf) sup).conjunctSet()
							.allMatch(cj -> (cj instanceof OWLClass) || (cj instanceof OWLObjectOneOf)))) {
				OWLObjectPropertyExpression role = ((OWLObjectSomeValuesFrom) sub).getProperty();
				OWLClassExpression sp = df.getOWLObjectAllValuesFrom(role.getInverseProperty(), sup);
				OWLClassExpression sb = ((OWLObjectSomeValuesFrom) sub).getFiller();
				oneOfSubAx.add(df.getOWLSubClassOfAxiom(sb, sp));
				return true;
			}
		}
		
		return false;
	}

	public void processDisjunction(OWLClassExpression sub, OWLClassExpression sup) {
		for (OWLClassExpression ce : ((OWLObjectUnionOf) sub).asDisjunctSet()) {
			if (ce instanceof OWLObjectOneOf)
				oneOfSubAx.add(df.getOWLSubClassOfAxiom(ce, sup));
			else if (ce instanceof OWLClass) {
				tuConcepts.add(ce);
				if (sup instanceof OWLObjectIntersectionOf) {
					sup.asConjunctSet().forEach(cj -> this.Tu.add(df.getOWLSubClassOfAxiom(ce, cj)));
				} else
					this.Tu.add(df.getOWLSubClassOfAxiom(ce, sup));
			} else if (ce instanceof OWLObjectIntersectionOf
					&& ce.conjunctSet().allMatch(cj -> (cj instanceof OWLClass) || (cj instanceof OWLObjectOneOf))) {
				if (sup instanceof OWLObjectIntersectionOf) {
					sup.asConjunctSet().forEach(cj -> this.Tui.add(df.getOWLSubClassOfAxiom(/*ce*/df.getOWLObjectIntersectionOf(ce.asConjunctSet()), cj)));
				} else
					this.Tui.add(df.getOWLSubClassOfAxiom(/*ce*/df.getOWLObjectIntersectionOf(ce.asConjunctSet()), sup));
			} else if (ce instanceof OWLObjectSomeValuesFrom) {
				if (!handleQualifiedRangeRestriction(ce, sup)) {
					this.Tg.add(df.getOWLSubClassOfAxiom(ce, sup));
				}
			} else if (ce instanceof OWLObjectHasValue) {
				if (config.isSHI() || config.isSHOI() || config.isSHOIQ() || config.isSHIQ()) {
					if (!handleNominal(ce, sup)) {
						this.Tg.add(df.getOWLSubClassOfAxiom(ce, sup));
					}
				} else
					this.Tg.add(df.getOWLSubClassOfAxiom(ce, sup));
			} else
				this.Tg.add(df.getOWLSubClassOfAxiom(ce, sup));
		}
	}

	public Ontology internalize(OWLOntology ont) {

		Set<OWLEquivalentClassesAxiom> eqAx = new HashSet<>();
		Set<OWLObjectPropertyDomainAxiom> objdAx = new HashSet<>();
		Set<OWLEquivalentClassesAxiom> oneOfEqAx = new HashSet<>();
		Set<OWLSubObjectPropertyOfAxiom> subObjProAx = new HashSet<>();
		Set<OWLInverseObjectPropertiesAxiom> invObjProAx = new HashSet<>();
		// Set<OWLSubClassOfAxiom> newSbAx = new HashSet<OWLSubClassOfAxiom>();

		for (OWLAxiom ax : (Iterable<OWLAxiom>) ont.axioms()::iterator) {
			ax = ax.getNNF();
		//	 System.err.println("ax :  "+ax);
			if (!this.prefixSet) {
				if (this.getPrefixManager().getDefaultPrefix().equals("")) {
					try {
						this.getPrefixManager().setDefaultPrefix(
								ax.toString().substring(ax.toString().indexOf("<") + 1, ax.toString().indexOf("#")));
						// System.err.println("ax added"+ ""+
						// ax.toString().substring(ax.toString().indexOf("<")+1,
						// ax.toString().indexOf("#")) );
						prefixSet = true;
					} catch (StringIndexOutOfBoundsException e) {
						this.getPrefixManager().setDefaultPrefix("");
					}
				}
			}
			// System.err.println("ax "+ this.getPrefixManager().getDefaultPrefix());

			// --> SubClassOf Axiom
			if (ax instanceof OWLSubClassOfAxiom) {
				OWLSubClassOfAxiom sax = (OWLSubClassOfAxiom) ax;
				subAx.add(sax);
				
				// --> A SubClassOf (B or (C or D)) --> A SubClassOf (B or C or D)
				if(sax.getSuperClass() instanceof OWLObjectUnionOf) {
					sax = df.getOWLSubClassOfAxiom(sax.getSubClass(), df.getOWLObjectUnionOf(sax.getSuperClass().asDisjunctSet()));
				}
				// --> (A and (B and C) SubClassOf D --> (A and B and C) SubClassOf D
				if(sax.getSubClass() instanceof OWLObjectIntersectionOf) {
					sax = df.getOWLSubClassOfAxiom(df.getOWLObjectIntersectionOf(sax.getSubClass().asConjunctSet()), sax.getSuperClass());
				}

				OWLClassExpression sub = sax.getSubClass();
				OWLClassExpression sup = sax.getSuperClass();
				
				
				// --> TOP SubClassOf (ClassExpression)
				if(sub.isOWLThing()) {
					if (sup instanceof OWLObjectIntersectionOf)
						sup.asConjunctSet().forEach(cj -> this.Tg.add(df.getOWLSubClassOfAxiom(sub, cj)));
					else
						Tg.add(sax);
					System.out.println("TOP SubClassOf (ClassExpression) " + sax);
				}
				
				// --> A SubClassOf (ClassExpression)
				else if (sub instanceof OWLClass) {
					tuConcepts.add(sub);
					if (sup instanceof OWLObjectIntersectionOf)
						sup.asConjunctSet().forEach(cj -> this.Tu.add(df.getOWLSubClassOfAxiom(sub, cj)));
					else
						this.Tu.add(sax);
				}
				// --> o SubClassOf (ClassExpression) -- OR -- (o1 or o2) SubClassOf
				// (ClassExpression)
				else if ((sub instanceof OWLObjectOneOf) || (sub instanceof OWLObjectUnionOf
						&& ((OWLObjectUnionOf) sub).disjunctSet().allMatch(dj -> dj instanceof OWLObjectOneOf))) {
					oneOfSubAx.add(sax);
					// this.oneOfAll.add(sax);
				}

				// --> (A or B) SubClassOf C
				else if (sub instanceof OWLObjectUnionOf) {
					processDisjunction(sub, sup);
				}
				// --> R some o SubClassOf C
				else if (sub instanceof OWLObjectSomeValuesFrom && ((OWLObjectSomeValuesFrom)sub).getFiller() instanceof OWLObjectOneOf) {
					if (config.isSHI() || config.isSHOI() || config.isSHOIQ() || config.isSHIQ()) {
						if (!handleNominal(sub, sup)) {
							this.Tg.add(df.getOWLSubClassOfAxiom(sub, sup));
						}
					} else
						this.Tg.add(df.getOWLSubClassOfAxiom(sub, sup));
				}
				// --> R some A SubClassOf C
				else if (sub instanceof OWLObjectSomeValuesFrom) {
					// System.out.println(handleQualifiedRangeRestriction(sub, sup));
					if (config.isSHI() || config.isSHOI() || config.isSHOIQ() || config.isSHIQ()) {
						if (!handleQualifiedRangeRestriction(sub, sup)) {
							this.Tg.add(df.getOWLSubClassOfAxiom(sub, sup));
						}
					} else
						this.Tg.add(df.getOWLSubClassOfAxiom(sub, sup));
				}
				// --> R hasValue o SubClassOf C
				else if (sub instanceof OWLObjectHasValue) {
					if (config.isSHI() || config.isSHOI() || config.isSHOIQ() || config.isSHIQ()) {
						if (!handleNominal(sub, sup)) {
							this.Tg.add(df.getOWLSubClassOfAxiom(sub, sup));
						}
					} else
						this.Tg.add(df.getOWLSubClassOfAxiom(sub, sup));
				}

				// --> (A and B) SubClassOf C -- OR -- (o1 and o2) SubClassOf C -- OR -- (A and
				// o1) SubClassOf C
				else if (sub instanceof OWLObjectIntersectionOf) {
						proccessIntersection(sax);
				}else {
					// --> (ClassExpression) SubClassOf (ClassExpression)
					this.Tg.add(sax);
				}
			}
			// --> EquivalentClasses Axiom
			else if (ax instanceof OWLEquivalentClassesAxiom) {
				OWLEquivalentClassesAxiom eax = (OWLEquivalentClassesAxiom) ax;
				if (eax.operands().anyMatch(eq -> (eq instanceof OWLObjectOneOf) || ((eq instanceof OWLObjectUnionOf)
						&& (((OWLObjectUnionOf) eq).disjunctSet().allMatch(dj -> dj instanceof OWLObjectOneOf))))) {
					oneOfEqAx.add(eax);
					for (OWLSubClassOfAxiom eqsb : eax.asOWLSubClassOfAxioms()) {
						// --> A SubClassOf (B or (C or D)) --> A SubClassOf (B or C or D)
						if(eqsb.getSuperClass() instanceof OWLObjectUnionOf) {
							eqsb = df.getOWLSubClassOfAxiom(eqsb.getSubClass(), df.getOWLObjectUnionOf(eqsb.getSuperClass().asDisjunctSet()));
						}
						// --> (A and (B and C) SubClassOf D --> (A and B and C) SubClassOf D
						if(eqsb.getSubClass() instanceof OWLObjectIntersectionOf) {
							eqsb = df.getOWLSubClassOfAxiom(df.getOWLObjectIntersectionOf(eqsb.getSubClass().asConjunctSet()), eqsb.getSuperClass());
						}

						OWLClassExpression sub = eqsb.getSubClass();
						OWLClassExpression sup = eqsb.getSuperClass();
						if(sub.isOWLThing()) {
							Tg.add(eqsb);
							System.out.println("TOP EquivalentOf (ClassExpression) " + eqsb);
						}
						else if ((sub instanceof OWLObjectOneOf)
								|| (sub instanceof OWLObjectUnionOf
										&& ((OWLObjectUnionOf) sub).disjunctSet()
												.allMatch(dj -> dj instanceof OWLObjectOneOf)))
							oneOfSubAx.add(eqsb);
						else if (sub instanceof OWLClass) {
							tuConcepts.add(sub);
							this.Tu.add(eqsb);
						} else if (sub instanceof OWLObjectIntersectionOf) {
							proccessIntersection(eqsb);
						} else if (sub instanceof OWLObjectUnionOf) {
							processDisjunction(sub, sup);
						} else if (sub instanceof OWLObjectSomeValuesFrom) {
							if (config.isSHI() || config.isSHOI() || config.isSHOIQ() || config.isSHIQ()) {
								if (!handleQualifiedRangeRestriction(sub, sup)) {
									this.Tg.add(eqsb);
								}
							} else
								this.Tg.add(eqsb);
						} else
							Tg.add(eqsb);
					}
				} else
					eqAx.add((OWLEquivalentClassesAxiom) ax);
			}

			// --> DisjointClasses Axiom
			else if (ax instanceof OWLDisjointClassesAxiom) {
				djAx.add((OWLDisjointClassesAxiom) ax);
				// ((OWLDisjointClassesAxiom) ax).operands().forEach(o ->
				// System.out.println("operand "+o));
				for (OWLSubClassOfAxiom djsb : ((OWLDisjointClassesAxiom) ax).asOWLSubClassOfAxioms()) {

					if (djsb.getSubClass() instanceof OWLClass) {
						tuConcepts.add(djsb.getSubClass());
						this.Tu.add(djsb);
					} else
						this.Tg.add(djsb);
				}
			}
			// --> DisjointUnion Axiom
			else if (ax instanceof OWLDisjointUnionAxiom) {
				djuAx.add((OWLDisjointUnionAxiom) ax);
				eqAx.add(((OWLDisjointUnionAxiom) ax).getOWLEquivalentClassesAxiom());
				for (OWLSubClassOfAxiom djusb : ((OWLDisjointUnionAxiom) ax).getOWLDisjointClassesAxiom()
						.asOWLSubClassOfAxioms()) {
					System.out.println("djusb "+djusb);
					if (djusb.getSubClass() instanceof OWLClass) {
						tuConcepts.add(djusb.getSubClass());
						this.Tu.add(djusb);
					} else
						this.Tg.add(djusb);
				}
			}
			/*
			 * // --> Domain Axiom else if(ax instanceof OWLObjectPropertyDomainAxiom) {
			 * objdAx.add((OWLObjectPropertyDomainAxiom) ax);
			 * this.Tg.add(((OWLObjectPropertyDomainAxiom) ax).asOWLSubClassOfAxiom()); } //
			 * --> Range Axiom else if(ax instanceof OWLObjectPropertyRangeAxiom) {
			 * objrAx.add((OWLObjectPropertyRangeAxiom) ax);
			 * this.Tg.add(((OWLObjectPropertyRangeAxiom) ax).asOWLSubClassOfAxiom()); }
			 */

			// --> Domain Axiom
			else if (ax instanceof OWLObjectPropertyDomainAxiom) {
				objdAx.add((OWLObjectPropertyDomainAxiom) ax);
				this.domainRestrictions.put(((OWLObjectPropertyDomainAxiom) ax).getProperty(),
						((OWLObjectPropertyDomainAxiom) ax).asOWLSubClassOfAxiom().getSuperClass());
				// System.out.println("domain Role "+ ((OWLObjectPropertyDomainAxiom)
				// ax).getProperty() + " domain: "+ ((OWLObjectPropertyDomainAxiom)
				// ax).asOWLSubClassOfAxiom().getSuperClass());
			}
			// --> Range Axiom
			else if (ax instanceof OWLObjectPropertyRangeAxiom) {
				objrAx.add((OWLObjectPropertyRangeAxiom) ax);
				// OWLClassExpression ce = ((OWLObjectPropertyRangeAxiom)
				// ax).asOWLSubClassOfAxiom().getSuperClass();
				this.rangeRestrictions.put(((OWLObjectPropertyRangeAxiom) ax).getProperty(),
						((OWLObjectAllValuesFrom) ((OWLObjectPropertyRangeAxiom) ax).asOWLSubClassOfAxiom()
								.getSuperClass()).getFiller());
				// System.out.println("Range Role "+ ((OWLObjectPropertyRangeAxiom)
				// ax).getProperty() + " range: "+
				// ((OWLObjectAllValuesFrom)((OWLObjectPropertyRangeAxiom)
				// ax).asOWLSubClassOfAxiom().getSuperClass()).getFiller());
			}

			// --> DifferentIndividuals Axiom
			else if (ax instanceof OWLDifferentIndividualsAxiom) {
				((OWLDifferentIndividualsAxiom) ax).asOWLSubClassOfAxioms().forEach(s -> diffInd.add(s));
				subAx.addAll(((OWLDifferentIndividualsAxiom) ax).asOWLSubClassOfAxioms());

			}
			// --> Class Assertion Axiom

			else if (ax instanceof OWLClassAssertionAxiom) {
				individuals.add(((OWLClassAssertionAxiom) ax).getIndividual());
				aboxClassAss.add(((OWLClassAssertionAxiom) ax).asOWLSubClassOfAxiom());
				oneOfSubAx.add(((OWLClassAssertionAxiom) ax).asOWLSubClassOfAxiom());
				subAx.add(((OWLClassAssertionAxiom) ax).asOWLSubClassOfAxiom());
			}

			// --> role Assertion Axiom
			else if (ax instanceof OWLObjectPropertyAssertionAxiom) {
				aboxObjProAss.add(((OWLObjectPropertyAssertionAxiom) ax).asOWLSubClassOfAxiom());
				oneOfSubAx.add(((OWLObjectPropertyAssertionAxiom) ax).asOWLSubClassOfAxiom());
				subAx.add(((OWLObjectPropertyAssertionAxiom) ax).asOWLSubClassOfAxiom());
			}

		}
		// --> remaining Equivalent class axioms
		Set<OWLClassExpression> eqConcepts = new HashSet<>();
		// eqAx.forEach(eq ->
		// eqConcepts.addAll(eq.operands().collect(Collectors.toList())));

		for (OWLEquivalentClassesAxiom eq : eqAx) {
			eqConcepts.addAll(eq.operands().collect(Collectors.toSet()));
			for (OWLSubClassOfAxiom eqsb : eq.asOWLSubClassOfAxioms()) {
				if (eqsb.getSubClass() instanceof OWLObjectUnionOf) {
					eqConcepts.addAll(((OWLObjectUnionOf) eqsb.getSubClass()).asDisjunctSet());
				}
				if (eqsb.getSuperClass() instanceof OWLObjectIntersectionOf) {
					eqConcepts.addAll(((OWLObjectIntersectionOf) eqsb.getSuperClass()).asConjunctSet());
				}
			}
		}

		for (OWLEquivalentClassesAxiom eq : eqAx) {
			Set<OWLClassExpression> operands = new HashSet<>();
			operands.addAll(eq.operands().collect(Collectors.toSet()));
			for (OWLClassExpression op : eq.operands().collect(Collectors.toSet())) {
				if (op instanceof OWLObjectUnionOf) {
					operands.addAll(((OWLObjectUnionOf) op).asDisjunctSet());
				}
				if (op instanceof OWLObjectIntersectionOf) {
					operands.addAll(((OWLObjectIntersectionOf) op).asConjunctSet());
				}
			}
			boolean eqTag = false;
			for (OWLClassExpression op : operands) {
				if (tuConcepts.contains(op) || Collections.frequency(eqConcepts, op) > 1) {
					eqTag = true;
					for (OWLSubClassOfAxiom eqsb : eq.asOWLSubClassOfAxioms()) {
						// --> A SubClassOf (B or (C or D)) --> A SubClassOf (B or C or D)
						if(eqsb.getSuperClass() instanceof OWLObjectUnionOf) {
							eqsb = df.getOWLSubClassOfAxiom(eqsb.getSubClass(), df.getOWLObjectUnionOf(eqsb.getSuperClass().asDisjunctSet()));
						}
						// --> (A and (B and C) SubClassOf D --> (A and B and C) SubClassOf D
						if(eqsb.getSubClass() instanceof OWLObjectIntersectionOf) {
							eqsb = df.getOWLSubClassOfAxiom(df.getOWLObjectIntersectionOf(eqsb.getSubClass().asConjunctSet()), eqsb.getSuperClass());
						}
						final OWLSubClassOfAxiom NewEqsb = eqsb;
						// System.err.println(eqsb);
						if (eqsb.getSubClass() instanceof OWLClass) {
							if (eqsb.getSuperClass() instanceof OWLObjectIntersectionOf)
								eqsb.getSuperClass().asConjunctSet()
										.forEach(cj -> this.Tu.add(df.getOWLSubClassOfAxiom(NewEqsb.getSubClass(), cj)));
							else
								Tu.add(eqsb);
						} else if (eqsb.getSubClass() instanceof OWLObjectUnionOf) {
							processDisjunction(eqsb.getSubClass(), eqsb.getSuperClass());
						} else if ((eqsb.getSubClass() instanceof OWLObjectIntersectionOf)) {
							proccessIntersection(NewEqsb);
						} else
							this.Tg.add(eqsb);
					}
					break;
				}
			}
			if (!eqTag) {
				if (eq.asOWLSubClassOfAxioms().stream().filter(
						esb -> (esb.getSubClass() instanceof OWLClass) || (esb.getSuperClass() instanceof OWLClass))
						.findAny().isPresent())
					this.Eq.add(eq);
				else
					eq.asOWLSubClassOfAxioms().stream().forEach(esb -> this.Tg.add(esb));

			}
		}
		processExtendedRoleAbsorption();
		for(OWLSubClassOfAxiom sb : this.getTu()){
			if (sb.getSubClass().isOWLThing()) {
				this.Tg.add(sb);
				//this.Tu.remove(sb);
			}
		}
		processTg();
		optimizeTg(); //creating Class assertions.
		
		/*for (OWLSubClassOfAxiom sbAx : this.Tg) {
			OWLClassExpression sup = sbAx.getSuperClass();
			if(sup instanceof OWLObjectUnionOf) {
				
					if((sup.disjunctSet().collect(Collectors.toSet()).size() == 2) && (sup.disjunctSet().anyMatch(ds -> ds instanceof OWLClass) && sup.disjunctSet().anyMatch(ds -> ds instanceof OWLObjectComplementOf))) {
						OWLClassExpression supC = sup.disjunctSet().filter(dj -> dj instanceof OWLClass).iterator().next();
						OWLClassExpression ind = sup.disjunctSet().filter(dj -> dj instanceof OWLObjectComplementOf).iterator().next().getComplementNNF();
						System.out.println("ind " + ind +" superclass "+ supC);
						if(ind instanceof OWLObjectOneOf) {
							OWLSubClassOfAxiom subClassAx = df.getOWLSubClassOfAxiom(ind, supC);
							individuals.add(ind.individualsInSignature().iterator().next());
							aboxClassAss.add(subClassAx);
							oneOfSubAx.add(subClassAx);
							subAx.add(subClassAx);
							System.out.println("subClassAx "+ subClassAx);
							this.Tg.remove(sbAx);
						}
					}
				
			}
		}*/
		
		////optimizeTG();
		
		processOneOfAx(oneOfSubAx);
		
		ont.individualsInSignature().forEach(ind -> {
			if (!individuals.contains(ind)) {
				aboxClassAss.add(df.getOWLSubClassOfAxiom(df.getOWLObjectOneOf(ind), df.getOWLThing()));
			}
		});
		
		ont.axioms().filter(ax -> ax instanceof OWLSubObjectPropertyOfAxiom)
				.forEach(ax -> subObjProAx.add((OWLSubObjectPropertyOfAxiom) ax));
		ont.axioms().filter(ax -> ax instanceof OWLInverseObjectPropertiesAxiom)
				.forEach(ax -> invObjProAx.add((OWLInverseObjectPropertiesAxiom) ax));
		

		ontology = new Ontology(subAx, Eq, objdAx, objrAx, oneOfSubAx, oneOfEqAx, oneOf, djAx, djuAx, diffInd,
				aboxClassAss, aboxObjProAss, subObjProAx, invObjProAx, this.Tu, this.Tui, this.symmRoles);
		
		System.out.println("tg size internalize method "+ this.getTgAx().size());
		return ontology;
	}
	

	private void optimizeTg() {
		Set<OWLSubClassOfAxiom> removeTg = new HashSet<>();
		for (OWLSubClassOfAxiom sbAx : this.tgAx) {
			OWLClassExpression sup = sbAx.getSuperClass();
			if(sup instanceof OWLObjectUnionOf) {
				
				/// // OWLThing SubClassOf A or (not {i})
				if(sup.disjunctSet().anyMatch(ds -> ds.getComplementNNF() instanceof OWLObjectOneOf)) {
					for(OWLClassExpression dj : sup.disjunctSet().filter(d -> d instanceof OWLObjectComplementOf).collect(Collectors.toSet())) {
						if(dj.getComplementNNF() instanceof OWLObjectOneOf) {
							Set<OWLClassExpression> supSet = new HashSet<>();
							for(OWLClassExpression dj2 : sup.disjunctSet().collect(Collectors.toSet())) {
								if(!dj2.equals(dj)) {
									supSet.add(dj2);
								}
							}
							OWLClassExpression supC;
							if(supSet.size() == 1)
								supC = supSet.iterator().next();
							else	
								supC = df.getOWLObjectUnionOf(supSet);
							OWLSubClassOfAxiom subClassAx = df.getOWLSubClassOfAxiom(dj.getComplementNNF(), supC);
							individuals.add(dj.getComplementNNF().individualsInSignature().iterator().next());
							aboxClassAss.add(subClassAx);
							oneOfSubAx.add(subClassAx);
							subAx.add(subClassAx);
							System.out.println("subClassAx "+ subClassAx);
							removeTg.add(sbAx);
							break;
						}
					}
				}
				// OWLThing SubClassOf A or (not {a,b,c})
				else if(sup.disjunctSet().anyMatch(ds -> ds instanceof OWLObjectIntersectionOf)) {
					boolean flag = false;
					for(OWLClassExpression in : sup.disjunctSet().filter(d -> d instanceof OWLObjectIntersectionOf).collect(Collectors.toSet())) {
						if(in.conjunctSet().allMatch(cj -> cj.getComplementNNF() instanceof OWLObjectOneOf)) {
							Set<OWLClassExpression> supSet = new HashSet<>();
							for(OWLClassExpression dj2 : sup.disjunctSet().collect(Collectors.toSet())) {
								if(!dj2.equals(in)) {
									supSet.add(dj2);
								}
							}
							OWLClassExpression supC;
							if(supSet.size() == 1)
								supC = supSet.iterator().next();
							else	
								supC = df.getOWLObjectUnionOf(supSet);
							for(OWLClassExpression sb : in.conjunctSet().collect(Collectors.toSet())) {
								OWLSubClassOfAxiom subClassAx = df.getOWLSubClassOfAxiom(sb.getComplementNNF(), supC);
								individuals.add(sb.getComplementNNF().individualsInSignature().iterator().next());
								aboxClassAss.add(subClassAx);
								oneOfSubAx.add(subClassAx);
								subAx.add(subClassAx);
								System.out.println("subClassAx "+ subClassAx);
							}
							removeTg.add(sbAx);
							flag = true;
							break;
						}
					}
					if(!flag) {
						// OWLThing SubClassOf A or (not (B or {i})) or (not (B or C))
						for(OWLClassExpression in : sup.disjunctSet().filter(d -> d instanceof OWLObjectIntersectionOf).collect(Collectors.toSet())) {
							if(in.conjunctSet().allMatch(cj -> (cj.getComplementNNF() instanceof OWLObjectOneOf) ||  (cj.getComplementNNF() instanceof OWLClass))) {
								Set<OWLClassExpression> supSet = new HashSet<>();
								for(OWLClassExpression dj2 : sup.disjunctSet().collect(Collectors.toSet())) {
									if(!dj2.equals(in)) {
										supSet.add(dj2);
									}
								}
								OWLClassExpression supC;
								if(supSet.size() == 1)
									supC = supSet.iterator().next();
								else	
									supC = df.getOWLObjectUnionOf(supSet);
								for(OWLClassExpression sb : in.conjunctSet().collect(Collectors.toSet())) {
									if(sb.getComplementNNF() instanceof OWLObjectOneOf) {
										OWLSubClassOfAxiom subClassAx = df.getOWLSubClassOfAxiom(sb.getComplementNNF(), supC);
										individuals.add(sb.getComplementNNF().individualsInSignature().iterator().next());
										aboxClassAss.add(subClassAx);
										oneOfSubAx.add(subClassAx);
										subAx.add(subClassAx);
										System.out.println("subClassAx "+ subClassAx);
									}
									else if(sb.getComplementNNF() instanceof OWLClass) {
										OWLSubClassOfAxiom subClassAx = df.getOWLSubClassOfAxiom(sb.getComplementNNF(), supC);
										this.Tu.add(subClassAx);
										subAx.add(subClassAx);
										System.out.println("subClassAx "+ subClassAx);
									}
								}
								removeTg.add(sbAx);
								flag = true;
								break;
							}
						}
					}
				}
				// OWLThing SubClassOf A or (not (B))
				else if(sup.disjunctSet().anyMatch(ds -> ds.getComplementNNF() instanceof OWLClass)) {
					for(OWLClassExpression dj : sup.disjunctSet().filter(d -> d instanceof OWLObjectComplementOf).collect(Collectors.toSet())) {
						if(dj.getComplementNNF() instanceof OWLClass) {
							Set<OWLClassExpression> supSet = new HashSet<>();
							for(OWLClassExpression dj2 : sup.disjunctSet().collect(Collectors.toSet())) {
								if(!dj2.equals(dj)) {
									supSet.add(dj2);
								}
							}
							OWLClassExpression supC;
							if(supSet.size() == 1)
								supC = supSet.iterator().next();
							else	
								supC = df.getOWLObjectUnionOf(supSet);
							OWLSubClassOfAxiom subClassAx = df.getOWLSubClassOfAxiom(dj.getComplementNNF(), supC);
							this.Tu.add(subClassAx);
							subAx.add(subClassAx);
							System.out.println("subClassAx "+ subClassAx);
							removeTg.add(sbAx);
							break;
						}
					}
				}
			}
			
		}
		this.tgAx.removeAll(removeTg);
	}

	private void processExtendedRoleAbsorption() {
	//	System.out.println("tg before:" + Tg);
		Set<OWLSubClassOfAxiom> remove = new HashSet<>();
		for (OWLSubClassOfAxiom sbAx : this.Tg) {
			
			if(sbAx.getSuperClass() instanceof OWLClass) {
				this.atomicSupClassGCIs.put(sbAx.getSuperClass(), sbAx.getSubClass());
			}
			if (sbAx.getSubClass() instanceof OWLObjectSomeValuesFrom) {
				OWLObjectUnionOf newEntry;
				if(sbAx.getSuperClass().isOWLNothing()) 
					 newEntry =df.getOWLObjectUnionOf(sbAx.getSubClass().getComplementNNF());
				else
					newEntry = df.getOWLObjectUnionOf(sbAx.getSuperClass(),sbAx.getSubClass().getComplementNNF());
				
				extendedDomainRestrictions.put(((OWLObjectSomeValuesFrom) sbAx.getSubClass()).getProperty(), newEntry);
				remove.add(sbAx);
			}
			else if (sbAx.getSubClass() instanceof OWLObjectMinCardinality) {
				OWLObjectUnionOf newEntry;
				if(sbAx.getSuperClass().isOWLNothing()) 
					 newEntry =df.getOWLObjectUnionOf(sbAx.getSubClass().getComplementNNF());
				else
					newEntry = df.getOWLObjectUnionOf(sbAx.getSuperClass(),sbAx.getSubClass().getComplementNNF());
			
				extendedDomainRestrictions.put(((OWLObjectMinCardinality) sbAx.getSubClass()).getProperty(), newEntry);
				remove.add(sbAx);
			}
			else if (sbAx.getSubClass() instanceof OWLObjectMaxCardinality) {
				OWLObjectUnionOf newEntry;
				if(sbAx.getSuperClass().isOWLNothing()) 
					 newEntry =df.getOWLObjectUnionOf(sbAx.getSubClass().getComplementNNF());
				else
					newEntry = df.getOWLObjectUnionOf(sbAx.getSuperClass(),sbAx.getSubClass().getComplementNNF());
			
				extendedDomainRestrictions.put(((OWLObjectMaxCardinality) sbAx.getSubClass()).getProperty(), newEntry);
				remove.add(sbAx);
			}
			else if (sbAx.getSubClass() instanceof OWLObjectAllValuesFrom) {
				OWLObjectUnionOf newEntry;
				if(sbAx.getSuperClass().isOWLNothing()) 
					 newEntry =df.getOWLObjectUnionOf(sbAx.getSubClass().getComplementNNF());
				else
					newEntry = df.getOWLObjectUnionOf(sbAx.getSuperClass(),sbAx.getSubClass().getComplementNNF());
			
				extendedDomainRestrictions.put(((OWLObjectAllValuesFrom) sbAx.getSubClass()).getProperty(), newEntry);
				remove.add(sbAx);
			}
			else if (sbAx.getSubClass() instanceof OWLObjectHasValue) {
				OWLObjectUnionOf newEntry;
				if(sbAx.getSuperClass().isOWLNothing()) 
					 newEntry =df.getOWLObjectUnionOf(sbAx.getSubClass().getComplementNNF());
				else
					newEntry = df.getOWLObjectUnionOf(sbAx.getSuperClass(),sbAx.getSubClass().getComplementNNF());
			
				extendedDomainRestrictions.put(((OWLObjectHasValue) sbAx.getSubClass()).getProperty(), newEntry);
				remove.add(sbAx);
			}
			//////
			else if (sbAx.getSubClass() instanceof OWLObjectIntersectionOf) {
				if(sbAx.getSubClass().asConjunctSet().stream().anyMatch(cj -> cj instanceof OWLObjectSomeValuesFrom || 
						cj instanceof OWLObjectMinCardinality || cj instanceof OWLObjectMaxCardinality ||
						cj instanceof OWLObjectAllValuesFrom || cj instanceof OWLObjectHasValue)) {
					for(OWLClassExpression ce : sbAx.getSubClass().asConjunctSet()) {
						if (ce instanceof OWLObjectSomeValuesFrom) {
							OWLObjectUnionOf newEntry;
							if(sbAx.getSuperClass().isOWLNothing()) 
								 newEntry =df.getOWLObjectUnionOf(sbAx.getSubClass().getComplementNNF());
							else
								newEntry = df.getOWLObjectUnionOf(sbAx.getSuperClass(),sbAx.getSubClass().getComplementNNF());
						
							extendedDomainRestrictions.put(((OWLObjectSomeValuesFrom) ce).getProperty(), newEntry);
							remove.add(sbAx);
							break;
						}
						else if (ce instanceof OWLObjectMinCardinality) {
							OWLObjectUnionOf newEntry;
							if(sbAx.getSuperClass().isOWLNothing()) 
								 newEntry =df.getOWLObjectUnionOf(sbAx.getSubClass().getComplementNNF());
							else
								newEntry = df.getOWLObjectUnionOf(sbAx.getSuperClass(),sbAx.getSubClass().getComplementNNF());
						
							extendedDomainRestrictions.put(((OWLObjectMinCardinality) ce).getProperty(), newEntry);
							remove.add(sbAx);
							break;
						}
						else if (ce instanceof OWLObjectMaxCardinality) {
							OWLObjectUnionOf newEntry;
							if(sbAx.getSuperClass().isOWLNothing()) 
								 newEntry =df.getOWLObjectUnionOf(sbAx.getSubClass().getComplementNNF());
							else
								newEntry = df.getOWLObjectUnionOf(sbAx.getSuperClass(),sbAx.getSubClass().getComplementNNF());
						
							extendedDomainRestrictions.put(((OWLObjectMaxCardinality) ce).getProperty(), newEntry);
							remove.add(sbAx);
							break;
						}
						else if (ce instanceof OWLObjectAllValuesFrom) {
							OWLObjectUnionOf newEntry;
							if(sbAx.getSuperClass().isOWLNothing()) 
								 newEntry =df.getOWLObjectUnionOf(sbAx.getSubClass().getComplementNNF());
							else
								newEntry = df.getOWLObjectUnionOf(sbAx.getSuperClass(),sbAx.getSubClass().getComplementNNF());
						
							extendedDomainRestrictions.put(((OWLObjectAllValuesFrom) ce).getProperty(), newEntry);
							remove.add(sbAx);
							break;
						}
						else if (ce instanceof OWLObjectHasValue) {
							OWLObjectUnionOf newEntry;
							if(sbAx.getSuperClass().isOWLNothing()) 
								 newEntry =df.getOWLObjectUnionOf(sbAx.getSubClass().getComplementNNF());
							else
								newEntry = df.getOWLObjectUnionOf(sbAx.getSuperClass(),sbAx.getSubClass().getComplementNNF());
						
							extendedDomainRestrictions.put(((OWLObjectHasValue) ce).getProperty(), newEntry);
							remove.add(sbAx);
							break;
						}
					}
				}
				
			}
		}
		this.Tg.removeAll(remove);
		//System.out.println("tg after:" + Tg);
		//System.out.println("extendedDomainRestrictions " + extendedDomainRestrictions.size());
		for (OWLSubClassOfAxiom sbAx : this.Tu) {
			if(sbAx.getSuperClass() instanceof OWLClass) {
				this.atomicSupClassGCIs.put(sbAx.getSuperClass(), sbAx.getSubClass());
			}
		}
		for (OWLSubClassOfAxiom sbAx : this.Tui) {
			if(sbAx.getSuperClass() instanceof OWLClass) {
				this.atomicSupClassGCIs.put(sbAx.getSuperClass(), sbAx.getSubClass());
			}
		}
	}
	public Set<OWLClassExpression> getApplicableGCIs(OWLClassExpression ce){
		return this.atomicSupClassGCIs.get(ce);
	}
	
	public Set<OWLObjectUnionOf> getApplicableGCIs(OWLObjectPropertyExpression role){
		return extendedDomainRestrictions.get(role);
	}
	private void proccessIntersection(OWLSubClassOfAxiom sbAx) {
		OWLClassExpression sub = sbAx.getSubClass();
		OWLClassExpression sup = sbAx.getSuperClass();
		// --> (A and B) SubClassOf C   or (A and {o}) SubClassOf C
		if ((sub.conjunctSet().allMatch(cj -> (cj instanceof OWLObjectOneOf) || (cj instanceof OWLClass)))) {
			//System.out.println("here"+sub);
			if (sup instanceof OWLObjectIntersectionOf)
				sup.asConjunctSet().forEach(cj -> this.Tui.add(df.getOWLSubClassOfAxiom(sub, cj)));
			else
				this.Tui.add(sbAx);
		}

		// --> (A and (ClassExpression)) SubClassOf C ----- GCI Absorption
		else if ((sub instanceof OWLObjectIntersectionOf && ((OWLObjectIntersectionOf) sub).conjunctSet()
				.anyMatch(cj -> (cj instanceof OWLObjectOneOf) || (cj instanceof OWLClass)))) {
			OWLClassExpression subC = null;
			Set<OWLClassExpression> supC = new HashSet<OWLClassExpression>();
			supC.add(sup);
			for (OWLClassExpression ce : ((OWLObjectIntersectionOf) sub).conjunctSet()
					.collect(Collectors.toSet())) {
				if (ce instanceof OWLClass || ce instanceof OWLObjectOneOf) {
					subC = ce;
					break;
				}
			}
			for (OWLClassExpression ce : ((OWLObjectIntersectionOf) sub).conjunctSet()
					.collect(Collectors.toSet())) {
				if (!ce.equals(subC)) {
					supC.add(ce.getComplementNNF());
				}
			}
			OWLSubClassOfAxiom newSubAx = df.getOWLSubClassOfAxiom(subC, df.getOWLObjectUnionOf(supC));
			this.Tu.add(newSubAx);
		} 
		else if ((sub instanceof OWLObjectIntersectionOf) && 
				(!sub.asConjunctSet().stream().anyMatch(cj -> cj instanceof OWLObjectSomeValuesFrom || 
				cj instanceof OWLObjectMinCardinality || cj instanceof OWLObjectMaxCardinality ||
				cj instanceof OWLObjectAllValuesFrom || cj instanceof OWLObjectHasValue))) {
			boolean flag = false;
			for(OWLClassExpression ce : sub.asConjunctSet()) {
				//---> (A or B) and (classExpression or C) subClassOf D 
				if(ce instanceof OWLObjectUnionOf && 
						ce.asDisjunctSet().stream().allMatch(dj -> dj instanceof OWLClass || dj instanceof OWLObjectOneOf)) {
					Set<OWLClassExpression> supClassSet = new HashSet<>();
					supClassSet.add(sbAx.getSuperClass());
					for(OWLClassExpression ce2 : sbAx.getSubClass().asConjunctSet()) {
						if(!ce2.equals(ce)) {
							supClassSet.add(ce2.getComplementNNF());
						}
					}
					OWLObjectUnionOf superClass = df.getOWLObjectUnionOf(supClassSet);
					for(OWLClassExpression dj : ce.asDisjunctSet()) {
						this.Tu.add(df.getOWLSubClassOfAxiom(dj, superClass)) ;
					}
					flag = true;
					break;
				}
			}
				
			/*if(!flag) {
				for(OWLClassExpression ce : sbAx.getSubClass().asConjunctSet()) {
					if(ce instanceof OWLObjectUnionOf && 
							ce.asDisjunctSet().stream().anyMatch(dj -> dj instanceof OWLClass || dj instanceof OWLObjectOneOf)) {
						Set<OWLClassExpression> supClassSet = new HashSet<>();
						supClassSet.add(sbAx.getSuperClass());
						for(OWLClassExpression ce2 : sbAx.getSubClass().asConjunctSet()) {
							if(!ce2.equals(ce)) {
								supClassSet.add(ce2.getComplementNNF());
							}
						}
						OWLObjectUnionOf superClass = df.getOWLObjectUnionOf(supClassSet);
						for(OWLClassExpression dj : ce.asDisjunctSet()) {
							if(dj instanceof OWLClass || dj instanceof OWLObjectOneOf)
								this.Tu.add(df.getOWLSubClassOfAxiom(dj, superClass)) ;
							else if(dj instanceof OWLObjectIntersectionOf)
								proccessIntersection(df.getOWLSubClassOfAxiom(dj, superClass));
							//else if(dj instanceof OWLObjectIntersectionOf && 
							//		dj.asConjunctSet().stream().allMatch(cj -> cj instanceof OWLClass || cj instanceof OWLObjectOneOf))
							//	this.Tui.add(df.getOWLSubClassOfAxiom(dj, superClass)) ;
							else
								this.Tg.add(df.getOWLSubClassOfAxiom(dj, superClass)) ;
						}
						flag = true;
						break;
					}
				}
			}*/
			if(!flag) {
				for(OWLClassExpression ce : sbAx.getSubClass().asConjunctSet()) {
					if(ce instanceof OWLObjectUnionOf) {
						Set<OWLClassExpression> supClassSet = new HashSet<>();
						supClassSet.add(sbAx.getSuperClass());
						for(OWLClassExpression ce2 : sbAx.getSubClass().asConjunctSet()) {
							if(!ce2.equals(ce)) {
								supClassSet.add(ce2.getComplementNNF());
							}
						}
						OWLObjectUnionOf superClass = df.getOWLObjectUnionOf(supClassSet);
						for(OWLClassExpression dj : ce.asDisjunctSet()) {
							if(dj instanceof OWLClass || dj instanceof OWLObjectOneOf)
								this.Tu.add(df.getOWLSubClassOfAxiom(dj, superClass)) ;
							else if(dj instanceof OWLObjectIntersectionOf)
								proccessIntersection(df.getOWLSubClassOfAxiom(dj, superClass));
							else
								this.Tg.add(df.getOWLSubClassOfAxiom(dj, superClass)) ;
						}
						flag = true;
						break;
					}
				}
			}
			if(!flag)
				this.Tg.add(sbAx);
		}
		else 
			this.Tg.add(sbAx);
	}

	public Set<OWLObjectUnionOf> getExtendedDomainRestrictions(OWLObjectPropertyExpression role) {
		return extendedDomainRestrictions.get(role);
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
		for (OWLSubClassOfAxiom sb : oneOfSubAx) {
			if ((sb.getSubClass() instanceof OWLObjectOneOf)
					&& (sb.getSuperClass() instanceof OWLObjectIntersectionOf)) {
				sb.getSuperClass().asConjunctSet()
						.forEach(cj -> this.oneOf.add(df.getOWLSubClassOfAxiom(sb.getSubClass(), cj)));
			} else if ((sb.getSubClass() instanceof OWLObjectOneOf))
				this.oneOf.add(sb);
			else if ((sb.getSubClass() instanceof OWLObjectUnionOf)
					&& (sb.getSuperClass() instanceof OWLObjectIntersectionOf)) {
				// OWLClassExpression sp = sb.getSuperClass();
				((OWLObjectUnionOf) (sb).getSubClass()).disjunctSet().forEach(dj -> {
					sb.getSuperClass().asConjunctSet().forEach(cj -> {
						this.oneOf.add(df.getOWLSubClassOfAxiom(dj, cj));
					});
				});
			} else if ((sb.getSubClass() instanceof OWLObjectUnionOf)) {
				OWLClassExpression sp = sb.getSuperClass();
				((OWLObjectUnionOf) (sb).getSubClass()).disjunctSet()
						.forEach(dj -> this.oneOf.add(df.getOWLSubClassOfAxiom(dj, sp)));
			}

		}

	}

	public boolean isSimpleObjectIntersectionOf(Set<OWLClassExpression> ceSet) {
		for (OWLClassExpression ce : ceSet) {
			if (!(ce instanceof OWLClass))
				return false;
		}
		return true;
	}

	public Set<OWLSubClassOfAxiom> getTu() {
		return this.Tu;
	}

	public Set<OWLSubClassOfAxiom> getTui() {
		return this.Tui;
	}

	private Set<OWLSubClassOfAxiom> getTg() {
		return this.Tg;
	}

	// returns set of super-concepts
	public Set<OWLClassExpression> findConcept(OWLClassExpression c) {
		Set<OWLClassExpression> ce = new HashSet<OWLClassExpression>();
		this.Tu.stream().filter(sb -> sb.getSubClass().equals(c)).forEach(sb -> ce.add(sb.getSuperClass()));
		for (OWLEquivalentClassesAxiom eq : this.Eq) {
			if (eq.contains(c)) {
				for (OWLSubClassOfAxiom eqsb : eq.asOWLSubClassOfAxioms()) {
					if (eqsb.getSubClass().equals(c)) {
						ce.add(eqsb.getSuperClass());
						break;
					} else {
						ce.add(eqsb.getSubClass());
						break;
					}
				}
			}
		}
		return ce;
	}

	public Set<OWLClassExpression> findConceptEq(OWLClassExpression c) {
		Set<OWLClassExpression> ce = new HashSet<OWLClassExpression>();
		for (OWLEquivalentClassesAxiom eq : this.Eq) {
			if (eq.contains(c)) {
				for (OWLSubClassOfAxiom eqsb : eq.asOWLSubClassOfAxioms()) {
					if (eqsb.getSubClass().equals(c)) {
						ce.add(eqsb.getSuperClass());
						break;
					} else {
						ce.add(eqsb.getSubClass());
						break;
					}
				}
			}
		}
		return ce;
	}

	public void addDiffInd(OWLDifferentIndividualsAxiom ax) {
		ax.asOWLSubClassOfAxioms().forEach(s -> diffInd.add(s));
	}

	public Set<OWLClassExpression> findIndividual(OWLClassExpression c) {
		Set<OWLClassExpression> ce = new HashSet<OWLClassExpression>();
		this.oneOf.stream().filter(sb -> sb.getSubClass().equals(c)).forEach(sb -> ce.add(sb.getSuperClass()));
		this.diffInd.stream().filter(sb -> sb.getSubClass().equals(c)).forEach(sb -> ce.add(sb.getSuperClass()));
		// this.aboxClassAss.stream().filter(sb ->
		// sb.getSubClass().equals(c)).forEach(sb -> ce.add(sb.getSuperClass()));
		// this.aboxObjProAss.stream().filter(sb ->
		// sb.getSubClass().equals(c)).forEach(sb -> ce.add(sb.getSuperClass()));
		return ce;
	}

	public Set<OWLClassExpression> getDisjoints(OWLClassExpression c) {
		Set<OWLClassExpression> ce = new HashSet<OWLClassExpression>();
		this.djAx.stream().filter(dj -> dj.contains(c)).forEach(dj -> ce.addAll(dj.getClassExpressionsMinus(c)));
		return ce;
	}

	public Set<OWLClassExpression> getDisjointUnion(OWLClassExpression c) {
		Set<OWLClassExpression> ce = new HashSet<OWLClassExpression>();
		this.djuAx.stream().filter(dj -> dj.getOWLDisjointClassesAxiom().contains(c))
				.forEach(dj -> ce.addAll(dj.getOWLDisjointClassesAxiom().getClassExpressionsMinus(c)));
		return ce;
	}
	
	public void processTg() {
		if (!this.getTg().isEmpty()) {
			for (OWLSubClassOfAxiom sb : this.getTg()) {
				if (sb.getSubClass().isOWLThing()) {
					this.tgAx.add(sb);
				} else if(sb.getSuperClass().isOWLNothing()) {
					this.tgAx.add(df.getOWLSubClassOfAxiom(df.getOWLThing(), sb.getSubClass().getComplementNNF()));
				}else {
					OWLClassExpression union = df.getOWLObjectUnionOf(sb.getSubClass().getComplementNNF(), sb.getSuperClass());
					this.tgAx.add(df.getOWLSubClassOfAxiom(df.getOWLThing(), union));
				}
			}
		}
	}
	public Set<OWLSubClassOfAxiom> getTgAx() {
		return this.tgAx;
	}
	public OWLClassExpression getTgAxiom() {
		if (this.tgAx.isEmpty()) {
			return null;
		} else {
			OWLClassExpression union = null;
			Set<OWLClassExpression> unionSet = new HashSet<>();

			if (this.tgAx.size() == 1) {
				for (OWLSubClassOfAxiom sb : this.tgAx) {
					union = sb.getSuperClass();
					if(union.asDisjunctSet().stream().allMatch(dj -> dj instanceof OWLClass || dj instanceof OWLObjectOneOf || dj.getComplementNNF() instanceof OWLClass || dj.getComplementNNF() instanceof OWLObjectOneOf)) {
						this.atomicGCIs.add(sb);
					}
				}
				System.out.println("union.asDisjunctSet().size() size "+ union.asDisjunctSet().size());
				
				
				if (union.asDisjunctSet().size() == 1) {
					return union.asDisjunctSet().iterator().next();
				}
				return union;
			}
			for (OWLSubClassOfAxiom sb : this.tgAx) {
				union = sb.getSuperClass();
				if(union.asDisjunctSet().stream().allMatch(dj -> dj instanceof OWLClass || dj instanceof OWLObjectOneOf || dj.getComplementNNF() instanceof OWLClass || dj.getComplementNNF() instanceof OWLObjectOneOf)) {
					this.atomicGCIs.add(sb);
				}
				unionSet.add(union);
			}
			OWLClassExpression intersection = df.getOWLObjectIntersectionOf(unionSet);
			return intersection;
		}
	}

	
	/*public OWLClassExpression getTgAxiom() {
		if (this.getTg().isEmpty()) {
			return null;
		} else {
			OWLClassExpression union = null;
			Set<OWLClassExpression> unionSet = new HashSet<>();

			if (this.getTg().size() == 1) {
				for (OWLSubClassOfAxiom sb : this.getTg()) {
					if (sb.getSubClass().isOWLThing()) {
						//union = df.getOWLObjectUnionOf(df.getOWLNothing(), sb.getSuperClass());
					//	union = df.getOWLObjectUnionOf(sb.getSuperClass());
						union = sb.getSuperClass();
					} else {
						union = df.getOWLObjectUnionOf(sb.getSubClass().getComplementNNF(), sb.getSuperClass());
					}
				}
				System.out.println("union.asDisjunctSet().size() size "+ union.asDisjunctSet().size());
				
				
				if(union.asDisjunctSet().stream().allMatch(dj -> dj instanceof OWLClass)) {
					this.atomicGCIs.add(union);
				}
				if (union.asDisjunctSet().size() == 1) {
					return union.asDisjunctSet().iterator().next();
				}
				return union;
			}
			for (OWLSubClassOfAxiom sb : this.getTg()) {
				if (sb.getSubClass().isOWLThing()) {
					//union = df.getOWLObjectUnionOf(df.getOWLNothing(), sb.getSuperClass());
					//union = df.getOWLObjectUnionOf(sb.getSuperClass());
					union = sb.getSuperClass();
				} else {
					union = df.getOWLObjectUnionOf(sb.getSubClass().getComplementNNF(), sb.getSuperClass());
				}
				
				if(union.asDisjunctSet().stream().allMatch(dj -> dj instanceof OWLClass)) {
					this.atomicGCIs.add(union);
				}
				unionSet.add(union);
			}
			OWLClassExpression intersection = df.getOWLObjectIntersectionOf(unionSet);
			return intersection;
		}
	}
*/

	public Set<OWLSubClassOfAxiom> getAtomicGCIs() {
		return atomicGCIs;
	}

	public Set<OWLObjectAllValuesFrom> getRoleRange(OWLObjectPropertyExpression r) {
		Set<OWLObjectAllValuesFrom> ranges = new HashSet<OWLObjectAllValuesFrom>();
		for (OWLObjectPropertyRangeAxiom range : this.objrAx) {
			if (range.getProperty().equals(r))
				ranges.add((OWLObjectAllValuesFrom) range.asOWLSubClassOfAxiom().getSuperClass());
		}
		return ranges;

	}

	public Set<OWLClassExpression> getDomainRestriction(OWLObjectPropertyExpression r) {
		return this.domainRestrictions.get(r);
	}

	public Set<OWLClassExpression> getRangeRestriction(OWLObjectPropertyExpression r) {
		return this.rangeRestrictions.get(r);
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
		for (OWLObjectPropertyExpression fr : functionalRoles) {
			Tu.add(df.getOWLSubClassOfAxiom(df.getOWLThing(), df.getOWLObjectMaxCardinality(1, fr, df.getOWLThing())));
		}

	}

	public void addInverseFunctionalRoleAxiom(Set<OWLObjectPropertyExpression> inverseFunctionalRoles) {
		for (OWLObjectPropertyExpression invfr : inverseFunctionalRoles) {
			Tu.add(df.getOWLSubClassOfAxiom(df.getOWLThing(),
					df.getOWLObjectMaxCardinality(1, invfr, df.getOWLThing())));
		}

	}

	public void setSymmetricRoles(Set<OWLObjectPropertyExpression> symm) {
		this.symmRoles = symm;

	}
	/*
	 * 
	 * if((((OWLSubClassOfAxiom) ax).getSubClass() instanceof OWLObjectOneOf)) {//
	 * || (((OWLSubClassOfAxiom) ax).getSuperClass() instanceof OWLObjectOneOf)) {
	 * oneOfSubAx.add((OWLSubClassOfAxiom) ax); } else if(((OWLSubClassOfAxiom)
	 * ax).getSubClass() instanceof OWLObjectHasValue) { OWLIndividual ind =
	 * ((OWLObjectHasValue)((OWLSubClassOfAxiom) ax).getSubClass()).getFiller();
	 * OWLObjectPropertyExpression role = ((OWLObjectHasValue)((OWLSubClassOfAxiom)
	 * ax).getSubClass()).getProperty(); OWLClassExpression sp =
	 * df.getOWLObjectAllValuesFrom(role.getInverseProperty(), ((OWLSubClassOfAxiom)
	 * ax).getSuperClass()); OWLClassExpression sb = df.getOWLObjectOneOf(ind);
	 * oneOfSubAx.add(df.getOWLSubClassOfAxiom(sb, sp)); } else
	 * if(((OWLSubClassOfAxiom) ax).getSuperClass() instanceof OWLObjectHasValue) {
	 * OWLIndividual ind = ((OWLObjectHasValue)((OWLSubClassOfAxiom)
	 * ax).getSuperClass()).getFiller(); OWLObjectPropertyExpression role =
	 * ((OWLObjectHasValue)((OWLSubClassOfAxiom) ax).getSuperClass()).getProperty();
	 * OWLClassExpression sp =
	 * df.getOWLObjectAllValuesFrom(role.getInverseProperty(), ((OWLSubClassOfAxiom)
	 * ax).getSubClass()); OWLClassExpression sb = df.getOWLObjectOneOf(ind);
	 * oneOfSubAx.add(df.getOWLSubClassOfAxiom(sb, sp)); } else
	 * if(ax.nestedClassExpressions().anyMatch(sbx -> sbx instanceof OWLObjectOneOf
	 * || sbx instanceof OWLObjectHasValue)) { this.Tg.add((OWLSubClassOfAxiom) ax);
	 * }
	 */
}
