package reasoner.ilp;

import java.io.IOException;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import org.semanticweb.owlapi.apibinding.OWLFunctionalSyntaxFactory;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLObjectCardinalityRestriction;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectOneOf;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import com.google.common.collect.SetMultimap;

import ilog.concert.*;
import ilog.cplex.*;


public class CplexModelGenerator2 {
	static double RC_EPS = 1.0e-6;
	
	List<OWLObjectCardinalityRestriction> qcr_list;
	Map<Integer , OWLObjectCardinalityRestriction> qcr_map;
	Map<Integer , QCR> subroles; 
	Set<OWLClassExpression> all_qcr_qualifiers;
	Set<OWLClassExpression> all_qualifiers;
	Set<OWLClassExpression> max_qcr_qualifiers; 
	SetMultimap<OWLClassExpression, OWLClassExpression> concept_subsumers; 
	SetMultimap<OWLClassExpression, OWLClassExpression> concept_disjoints;
	SetMultimap<ConceptPair, OWLClassExpression> together_concepts;
	Set<Set<OWLClassExpression>> disjoint_groups;
	boolean initiallySolved;
	Set<OWLObjectCardinalityRestriction> infeasibilities;
	int M;

	Logger logger = LoggerFactory.getLogger(CplexModelGenerator2.class);

	@SuppressWarnings({ "deprecation", "unused" })
	public CplexModelGenerator2(ILPPreprocessor ilpPr) {

		this.qcr_list = ilpPr.getCardRes();
		int subrolenum = 0;
		Map<Integer, QCR> subroles = null;
		Map<Integer, OWLObjectCardinalityRestriction> qcr_map = null;
		Set<OWLClassExpression> max_qcr_qualifiers = null;
		Set<OWLClassExpression> all_qcr_qualifiers = null;
		infeasibilities = new HashSet<>();
		if(qcr_list != null) {
			subroles  = new HashMap<Integer, QCR>();
			qcr_map = new HashMap<Integer, OWLObjectCardinalityRestriction>();
			for(OWLObjectCardinalityRestriction qcr : qcr_list){
				subroles.put(subrolenum, new QCR(qcr));
				qcr_map.put(subrolenum, qcr);
				++subrolenum;
			}

			max_qcr_qualifiers = subroles.values().stream()
					.filter(qcr -> qcr.type.equals("MAX"))
					.map(qcr -> qcr.qualifier)
					.collect(Collectors.toSet());

			all_qcr_qualifiers = subroles.values().stream()
					.map(qcr -> qcr.qualifier)
					.collect(Collectors.toSet());
		}

		this.subroles = subroles;
		this.qcr_map = qcr_map;
		this.all_qcr_qualifiers = all_qcr_qualifiers;
		this.max_qcr_qualifiers = max_qcr_qualifiers;

		IloCplex initSolver;
		try {
			initSolver = new IloCplex();
			initSolver.setOut(new NullOutputStream());
// TODO i changed max to min
			IloObjective initObj = initSolver.addMinimize();

			Map<OWLClassExpression , IloNumVar> check_var = new HashMap<>();
			for(OWLClassExpression C : all_qcr_qualifiers){
				if(!check_var.containsKey(C))
					check_var.put(C , initSolver.numVar(0., Double.MAX_VALUE));
			}


			// Setting objective function
			IloLinearNumExpr initobjExpr = initSolver.linearNumExpr();
			initobjExpr.addTerm(0 , initSolver.numVar(0., Double.MAX_VALUE));
			initObj.setExpr(initobjExpr);
			Map<IloRange , Set<OWLObjectCardinalityRestriction>> rang_qcr_map = new HashMap<>();

			for(OWLClassExpression C : check_var.keySet()){
				HashMap<Double , OWLObjectCardinalityRestriction> LBs = new HashMap<>();
				HashMap<Double , OWLObjectCardinalityRestriction> UBs = new HashMap<>();
				for(Integer val : subroles.keySet()){
					QCR qcr = subroles.get(val);
					if(qcr.qualifier.equals(C)){
						if(qcr.type.equals("MIN"))
							LBs.put((double) qcr.cardinality , qcr_map.get(val));
						else if(qcr.type.equals("MAX"))
							UBs.put((double) qcr.cardinality , qcr_map.get(val));
						else {
							LBs.put((double) qcr.cardinality , qcr_map.get(val));
							UBs.put((double) qcr.cardinality , qcr_map.get(val));
						}
					}
				}
				double lb = 0;
				double ub = 10000;
				Set<OWLObjectCardinalityRestriction> LB_map = new HashSet<>();
				Set<OWLObjectCardinalityRestriction> UB_map = new HashSet<>();
				if(!LBs.isEmpty()){
					lb = Collections.max(LBs.keySet());
					LB_map.add(LBs.get(lb));
				}
				if(!UBs.isEmpty()){
					ub = Collections.min(UBs.keySet());
					UB_map.add(UBs.get(ub));
				}
				if(lb < 0)
					lb = 0;
				if(ub < 0)
					ub = 0;
				if(!LBs.isEmpty() && UBs.isEmpty()){
					ub = lb + 1;
				}

				rang_qcr_map.put(initSolver.addLe(check_var.get(C) , ub) , UB_map);
				rang_qcr_map.put(initSolver.addGe(check_var.get(C) , lb) , LB_map);
			}

			if(initSolver.solve()){
				initiallySolved = true;
				this.concept_subsumers = HashMultimap.create();
				for(Entry<OWLClassExpression, OWLClassExpression> e : concept_subsumers.entries()){
					this.concept_subsumers.put(e.getKey(), e.getValue());
				}

				this.concept_disjoints = HashMultimap.create();
				for(Entry<OWLClassExpression, OWLClassExpression> e : concept_disjoints.entries()){
					this.concept_disjoints.put(e.getKey(), e.getValue());
				}

				this.together_concepts = HashMultimap.create();
				for(Entry<ConceptPair, OWLClassExpression> e : together_concepts.entries()){
					ArrayList<OWLClassExpression> AandB = new ArrayList<>();
					AandB.addAll(((OWLClassExpression) e.getKey()).asConjunctSet());
					this.together_concepts.put(new ConceptPair(AandB.get(0), AandB.get(1)), e.getValue());
				}

				this.disjoint_groups = new HashSet<>();
				for(Set<OWLClassExpression> e : disjoint_groups){
					this.disjoint_groups.add(e);
				}

				if(all_qcr_qualifiers != null)
					this.all_qualifiers = new HashSet<OWLClassExpression>(all_qcr_qualifiers);
				else
					this.all_qualifiers = new HashSet<OWLClassExpression>();

			//	OWLClassExpression Thing = (OWLClassExpression)OWLFunctionalSyntaxFactory.OWLThing();
			//	this.all_qualifiers.add(Thing);

				if(concept_subsumers.keySet() != null){
					this.all_qualifiers.addAll(concept_subsumers.keySet());
					for(OWLClassExpression C : concept_subsumers.keySet()){
						this.all_qualifiers.addAll(concept_subsumers.get(C));
					}
				}

				if(concept_disjoints.keySet() != null){
					this.all_qualifiers.addAll(concept_disjoints.keySet());
					for(OWLClassExpression C : concept_disjoints.keySet()){
						this.all_qualifiers.addAll(concept_disjoints.get(C));
					}
				}

				if(together_concepts != null){
					if(together_concepts.keySet() != null){
						for(ConceptPair AB : together_concepts.keySet()){
							this.all_qualifiers.addAll(((OWLClassExpression) AB).asConjunctSet());
							this.all_qualifiers.addAll(together_concepts.get(AB));
						}
					}
				}

				if(disjoint_groups != null){
					//this.all_qualifiers.add(OWLFunctionalSyntaxFactory.OWLNothing());
					for(Set<OWLClassExpression> entry : disjoint_groups){
						this.all_qualifiers.addAll(entry);
					}
				}

				Set<OWLClassExpression> temp_complement = new HashSet<>();
				for(OWLClassExpression C : this.all_qualifiers){
					if(C instanceof OWLObjectComplementOf){
						OWLClassExpression NotC = ((OWLObjectComplementOf)C).getOperand();
						temp_complement.add(NotC);
						this.concept_disjoints.put(C, NotC);
					}
				}
				this.all_qualifiers.addAll(temp_complement); 

				for(QCR qcr : this.subroles.values()){
					OWLClassExpression C = qcr.qualifier;
					if(!(C instanceof OWLObjectComplementOf) && qcr.type.equals("MAX") && qcr.cardinality == 0){
						OWLClassExpression NotC = C.getObjectComplementOf();
						this.concept_disjoints.put(C, NotC);
						this.all_qualifiers.add(NotC);
					}
				}
			}
			else{
				initiallySolved = false;
				Set<IloRange> temp_rng_set = rang_qcr_map.keySet();
				IloRange[] rng = temp_rng_set.toArray(new IloRange[temp_rng_set.size()]);
				double[] lb_pref = new double[rng.length];
				double[] ub_pref = new double[rng.length];
				for (int c1 = 0; c1 < rng.length; c1++)
				{
					lb_pref[c1] = 1.0;//change it per your requirements
					ub_pref[c1] = 1.0;//change it per your requirements
				}
				if (initSolver.feasOpt(rng, lb_pref, ub_pref))
				{
					double[] infeas = initSolver.getInfeasibilities(rng);
					//Print bound changes					
					for (int c3 = 0; c3 < infeas.length; c3++)
						if(infeas[c3]!=0)
							infeasibilities.addAll(rang_qcr_map.get(rng[c3]));
				}
				else
				{
					System.out.println("FeasOpt failed- Could not repair infeasibilities");
				}
				
				initSolver.end();
			}
		} catch (IloException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
			
		}

		// the following statement is used to log any messages  
		logger.trace("Request for solving the system of inequalities:");
		if(subroles != null){
			for(QCR qcr : subroles.values()){
				String type;
				if(qcr.type.equals("MIN"))
					type = ">=";
				else if(qcr.type.equals("MAX"))
					type = "<=";
				else
					type = "=";

				if((qcr.qualifier instanceof OWLObjectComplementOf))
					logger.trace(type + " " + qcr.cardinality + " R.~" + ((OWLEntity)((OWLObjectComplementOf)qcr.qualifier).getOperand()).getIRI().getFragment());
				else
					logger.trace(type + " " + qcr.cardinality + " R." + ((OWLEntity)qcr.qualifier).getIRI().getFragment());
			}
		}
		logger.trace("-----------------------------------");
		
		

	}   

	static class SubSet {
		double[] rolesIndexSet;
		double[] conceptIndexSet;
		int cost;

		SubSet(double[] rolesIndexSet, double[] conceptIndexSet){
			this.rolesIndexSet = rolesIndexSet;
			this.conceptIndexSet = conceptIndexSet;
			cost = 0;
			for(int j = 0 ; j < conceptIndexSet.length ; j++)
				cost += conceptIndexSet[j];
		}

		public double[] getRolesIndexSet() {
			return rolesIndexSet;
		}
		public void setRolesIndexSet(double[] rolesIndexSet) {
			this.rolesIndexSet = rolesIndexSet;
		}
		public double[] getConceptIndexSet() {
			return conceptIndexSet;
		}
		public void setConceptIndexSet(double[] conceptIndexSet) {
			this.conceptIndexSet = conceptIndexSet;
		}
		public void setCost(int cost){
			this.cost = cost;
		}
		public int getCost(){
			return cost;
		}
	}

	static class IloNumVarArray {
		int _num           = 0;
		IloNumVar[] _array = new IloNumVar[32];

		void add(IloNumVar ivar) {
			if ( _num >= _array.length ) {
				IloNumVar[] array = new IloNumVar[2 * _array.length];
				System.arraycopy(_array, 0, array, 0, _num);
				_array = array;
			}
			_array[_num++] = ivar;
		}

		IloNumVar getElement(int i) { return _array[i]; }
		int       getSize()         { return _num; }
	}

	private class NullOutputStream extends OutputStream {    
		@Override
		public void write(int b) throws IOException {
		}
	}

	private class ConceptPair{

		OWLClassExpression A;
		OWLClassExpression B;

		ConceptPair(OWLClassExpression A , OWLClassExpression B){
			this.A = A;
			this.B = B;
		}

		public OWLClassExpression getA() {
			return A;
		}

		public OWLClassExpression getB() {
			return B;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + getOuterType().hashCode();
			result = prime * result + ((A == null) ? 0 : A.hashCode());
			result = prime * result + ((B == null) ? 0 : B.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			ConceptPair other = (ConceptPair) obj;
			if (!getOuterType().equals(other.getOuterType()))
				return false;
			if (A == null) {
				if (other.A != null)
					return false;
			} else if (!A.equals(other.A))
				return false;
			if (B == null) {
				if (other.B != null)
					return false;
			} else if (!B.equals(other.B))
				return false;
			return true;
		}

		@Override
		public String toString() {
			return "< " + A + ", " + B + " >";
		}

		private CplexModelGenerator2 getOuterType() {
			return CplexModelGenerator2.this;
		}

	}


	@SuppressWarnings("deprecation")
	public ILPSolution solve() throws IloException{

		ILPSolution return_information = new ILPSolution();

		if(!initiallySolved){
			return_information.setInfeasible_set(infeasibilities);
			return_information.setSolved(false);
			logger.trace("Infeasible ILP");
			logger.trace("Trivially infeasible inequality system.");
			logger.trace("Infeasibilities:");
			logger.trace(infeasibilities.toString());
			return return_information;
		}

		OWLClassExpression Thing = (OWLClassExpression)OWLFunctionalSyntaxFactory.OWLThing();

		for(OWLClassExpression C : all_qualifiers){
			if((!C.equals(Thing)) && !concept_subsumers.containsEntry(C, Thing)){
				concept_subsumers.put(C, Thing);
			}
		}

		int M = 10000;
		int subroles_num;
		if(subroles != null) {
			subroles_num = subroles.keySet().size(); 
		} else {
			subroles_num = 0;
		}
		int qualifier_num = all_qualifiers.size();
		System.out.println("all qualifiers: "+ all_qualifiers.size());

		@SuppressWarnings("unchecked") // Safe because SetMultimap guarantees this.
		final Map<OWLClassExpression, Set<OWLClassExpression>> concept_subsumers_map = 
		(Map<OWLClassExpression, Set<OWLClassExpression>>) (Map<?, ?>) concept_subsumers.asMap();

		logger.trace("Concept Subsumers Received:");
		for(OWLClassExpression C : concept_subsumers_map.keySet()){
			for(OWLClassExpression D : concept_subsumers_map.get(C)){
				if(C instanceof OWLObjectComplementOf && D instanceof OWLObjectComplementOf)
					logger.trace("~" + ((OWLEntity)((OWLObjectComplementOf)C).getOperand()).getIRI().getFragment() + " � ~" + ((OWLEntity)((OWLObjectComplementOf)D).getOperand()).getIRI().getFragment());
				else if(C instanceof OWLObjectComplementOf && !(D instanceof OWLObjectComplementOf))
					logger.trace("~" + ((OWLEntity)((OWLObjectComplementOf)C).getOperand()).getIRI().getFragment() + " � " + ((OWLEntity)D).getIRI().getFragment());
				else if(!(C instanceof OWLObjectComplementOf) && D instanceof OWLObjectComplementOf)
					logger.trace(((OWLEntity)C).getIRI().getFragment() + " � ~" + ((OWLEntity)((OWLObjectComplementOf)D).getOperand()).getIRI().getFragment());
				else
					logger.trace(((OWLEntity)C).getIRI().getFragment() + " � " + ((OWLEntity)D).getIRI().getFragment());
			}
		}
		logger.trace("-----------------------------------");

		@SuppressWarnings("unchecked") // Safe because SetMultimap guarantees this.
		final Map<OWLClassExpression, Set<OWLClassExpression>> concept_disjoints_map = 
		(Map<OWLClassExpression, Set<OWLClassExpression>>) (Map<?, ?>) concept_disjoints.asMap();

		logger.trace("Concept Disjoints Received:");
		for(OWLClassExpression C : concept_disjoints_map.keySet()){
			for(OWLClassExpression D : concept_disjoints_map.get(C)){
				if(C instanceof OWLObjectComplementOf && D instanceof OWLObjectComplementOf)
					logger.trace("~" + ((OWLEntity)((OWLObjectComplementOf)C).getOperand()).getIRI().getFragment() + " ^ ~" + ((OWLEntity)((OWLObjectComplementOf)D).getOperand()).getIRI().getFragment()+ " = Nothing");
				else if(C instanceof OWLObjectComplementOf && !(D instanceof OWLObjectComplementOf))
					logger.trace("~" + ((OWLEntity)((OWLObjectComplementOf)C).getOperand()).getIRI().getFragment() + " ^ " + ((OWLEntity)D).getIRI().getFragment()+ " = Nothing");
				else if(!(C instanceof OWLObjectComplementOf) && D instanceof OWLObjectComplementOf)
					logger.trace(((OWLEntity)C).getIRI().getFragment() + " ^ ~" + ((OWLEntity)((OWLObjectComplementOf)D).getOperand()).getIRI().getFragment()+ " = Nothing");
				else
					logger.trace(((OWLEntity)C).getIRI().getFragment() + " ^ " + ((OWLEntity)D).getIRI().getFragment()+ " = Nothing");
			}
		}
		logger.trace("-----------------------------------");

		logger.trace("Disjoint Groups Received:");
		for(Set<OWLClassExpression> e : disjoint_groups){
			logger.trace(e.toString());
		}
		logger.trace("-----------------------------------");

		int temp_qualifier_num = 0;
		BiMap<OWLClassExpression, Integer> qualifiers = HashBiMap.create();
		for(OWLClassExpression C : all_qualifiers){
			qualifiers.put(C, temp_qualifier_num);
			++temp_qualifier_num;
		}

		/// MASTER PROBLEM ///

		IloCplex qcrSolver = new IloCplex();
		qcrSolver.setOut(new NullOutputStream());

		IloObjective Obj = qcrSolver.addMinimize();
		IloRange[]   Constraint = new IloRange[subroles_num];
		IloLinearNumExpr[] expr = new IloLinearNumExpr[subroles_num];

		// //System.out.println("Done! 3");
		for (int i = 0; i < subroles_num; i++) {
			if(subroles.get(i).type.equals("MIN")){
				Constraint[i] = qcrSolver.addGe(expr[i], subroles.get(i).cardinality);
			}
			else{
				Constraint[i] = qcrSolver.addLe(expr[i], subroles.get(i).cardinality);	
			}
		}

		IloNumVarArray h = new IloNumVarArray();
		IloNumVarArray x = new IloNumVarArray();
		ArrayList<SubSet> subsets = new ArrayList<SubSet>();
		//System.out.println("sub num " + subroles_num);
		for (int i = 0; i < subroles_num; i++) {
			System.out.println("sub num " + i);
			h.add(qcrSolver.numVar(qcrSolver.column(Obj, M).and(
					qcrSolver.column(Constraint[i],1)),
					0.0, Double.MAX_VALUE));
		}
		qcrSolver.setParam(IloCplex.Param.RootAlgorithm, IloCplex.Algorithm.Primal);

		/// PATTERN-GENERATION PROBLEM ///

		IloCplex colSolver = new IloCplex();
		colSolver.setOut(new NullOutputStream());

		IloObjective ReducedCost = colSolver.addMinimize();
		IloNumVar[] a = colSolver.numVarArray(subroles_num, 0., 1, 
				IloNumVarType.Int);
		IloNumVar[] b = colSolver.numVarArray(qualifier_num, 0., 1, 
				IloNumVarType.Int);

		// In at-least restrictions: if a[i]==1 --> b[i.qualifier]=1
		// In at-most restrictions: if b[i.qualifier]==1 --> a[i]=1
		for (int i = 0; i < subroles_num; i++ ) {
			if(subroles.get(i).type.equals("MIN"))
				colSolver.addLe(a[i] , b[qualifiers.get(subroles.get(i).qualifier)]);
			else
				colSolver.addLe(b[qualifiers.get(subroles.get(i).qualifier)] , a[i]);	 
		}


		
		colSolver.addLe(colSolver.sum(colSolver.prod(1.0, b[qualifiers.get(subroles.get(0).qualifier)]),
				colSolver.prod(1.0, b[qualifiers.get(subroles.get(1).qualifier)])), 1);
		// Checking disjoints
		for (OWLClassExpression C : all_qualifiers){
			if(concept_disjoints_map.get(C) != null){
				for(OWLClassExpression D : concept_disjoints_map.get(C)){
					if(C instanceof OWLObjectComplementOf){
						if(((OWLObjectComplementOf)C).getOperand().equals(D))
							colSolver.addEq(colSolver.sum(colSolver.prod(1.0, b[qualifiers.get(C)]),
									colSolver.prod(1.0, b[qualifiers.get(D)])), 1);
						else 
							colSolver.addLe(colSolver.sum(colSolver.prod(1.0, b[qualifiers.get(C)]),
									colSolver.prod(1.0, b[qualifiers.get(D)])), 1);
					}
					else if(D instanceof OWLObjectComplementOf){
						if(((OWLObjectComplementOf)D).getOperand().equals(C))
							colSolver.addEq(colSolver.sum(colSolver.prod(1.0, b[qualifiers.get(C)]),
									colSolver.prod(1.0, b[qualifiers.get(D)])), 1);
						else 
							colSolver.addLe(colSolver.sum(colSolver.prod(1.0, b[qualifiers.get(C)]),
									colSolver.prod(1.0, b[qualifiers.get(D)])), 1);
					}
					else
						colSolver.addLe(colSolver.sum(colSolver.prod(1.0, b[qualifiers.get(C)]),
								colSolver.prod(1.0, b[qualifiers.get(D)])), 1);
				}
			}
		}

		// Checking multikeys          
		if(together_concepts != null){
			@SuppressWarnings("unchecked") // Safe because SetMultimap guarantees this.
			final Map<ConceptPair, Set<OWLClassExpression>> together_concepts_map = 
			(Map<ConceptPair, Set<OWLClassExpression>>) (Map<?, ?>) together_concepts.asMap();

			logger.trace("Binary Subsumptions Received:");
			for(ConceptPair AB : together_concepts_map.keySet()){
				OWLClassExpression A = AB.getA();
				OWLClassExpression B = AB.getB();
				for(OWLClassExpression D : together_concepts_map.get(AB)){
					if(A instanceof OWLObjectComplementOf && B instanceof OWLObjectComplementOf && D instanceof OWLObjectComplementOf)
						logger.trace("<~" + ((OWLEntity)((OWLObjectComplementOf)A).getOperand()).getIRI().getFragment() +  " , ~" +  ((OWLEntity)((OWLObjectComplementOf)B).getOperand()).getIRI().getFragment() + "> � ~" + ((OWLEntity)((OWLObjectComplementOf)D).getOperand()).getIRI().getFragment());
					else if(A instanceof OWLObjectComplementOf && B instanceof OWLObjectComplementOf && !(D instanceof OWLObjectComplementOf))
						logger.trace("<~" + ((OWLEntity)((OWLObjectComplementOf)A).getOperand()).getIRI().getFragment() +  " , ~" +  ((OWLEntity)((OWLObjectComplementOf)B).getOperand()).getIRI().getFragment() + "> � " + ((OWLEntity)D).getIRI().getFragment());
					else if(A instanceof OWLObjectComplementOf && !(B instanceof OWLObjectComplementOf) && D instanceof OWLObjectComplementOf)
						logger.trace("<~" + ((OWLEntity)((OWLObjectComplementOf)A).getOperand()).getIRI().getFragment() +  " , " +  ((OWLEntity)B).getIRI().getFragment() + "> � ~" + ((OWLEntity)((OWLObjectComplementOf)D).getOperand()).getIRI().getFragment());
					else if(!(A instanceof OWLObjectComplementOf) && B instanceof OWLObjectComplementOf && D instanceof OWLObjectComplementOf)
						logger.trace("<" + ((OWLEntity)A).getIRI().getFragment() +  " , ~" +  ((OWLEntity)((OWLObjectComplementOf)B).getOperand()).getIRI().getFragment() + "> � ~ " + ((OWLEntity)((OWLObjectComplementOf)D).getOperand()).getIRI().getFragment());
					else if(A instanceof OWLObjectComplementOf && !(B instanceof OWLObjectComplementOf) && !(D instanceof OWLObjectComplementOf))
						logger.trace("<~" + ((OWLEntity)((OWLObjectComplementOf)A).getOperand()).getIRI().getFragment() +  " , " +  ((OWLEntity)B).getIRI().getFragment() + "> � " + ((OWLEntity)D).getIRI().getFragment());
					else if(!(A instanceof OWLObjectComplementOf) && B instanceof OWLObjectComplementOf && !(D instanceof OWLObjectComplementOf))
						logger.trace("<" + ((OWLEntity)A).getIRI().getFragment() +  " , ~" +  ((OWLEntity)((OWLObjectComplementOf)B).getOperand()).getIRI().getFragment() + "> � " + ((OWLEntity)D).getIRI().getFragment());
					else if(!(A instanceof OWLObjectComplementOf) && !(B instanceof OWLObjectComplementOf) && D instanceof OWLObjectComplementOf)
						logger.trace("<" + ((OWLEntity)A).getIRI().getFragment() +  " , " +  ((OWLEntity)B).getIRI().getFragment() + "> � ~ " + ((OWLEntity)((OWLObjectComplementOf)D).getOperand()).getIRI().getFragment());
					else
						logger.trace("<" + ((OWLEntity)A).getIRI().getFragment() + " , " + ((OWLEntity)B).getIRI().getFragment() + "> � " + ((OWLEntity)D).getIRI().getFragment());
				}
			}

			for (ConceptPair AB : together_concepts_map.keySet()){
				for(OWLClassExpression X : together_concepts_map.get(AB)){
					colSolver.addLe(colSolver.sum(colSolver.prod(1.0, b[qualifiers.get(AB.getA())]),
							colSolver.prod(1.0, b[qualifiers.get(AB.getB())]),
							colSolver.prod(-1.0, b[qualifiers.get(X)])), 1);
				}
			}
			logger.trace("-----------------------------------");
		}
		
		// Checking disjoint groups          
		if(disjoint_groups != null){
			OWLClassExpression Nothing = OWLFunctionalSyntaxFactory.OWLNothing();
			for (Set<OWLClassExpression> disjoints : disjoint_groups){
				IloLinearNumExpr exprDisjoints = colSolver.linearNumExpr();
				for(OWLClassExpression X : disjoints){
					exprDisjoints.addTerm(1 , b[qualifiers.get(X)]);
				}
				exprDisjoints.addTerm(-1, b[qualifiers.get(Nothing)]);
				colSolver.addLe(exprDisjoints, disjoints.size() - 1);
			}
			logger.trace("-----------------------------------");
		}

		// Check Nothing
		for (OWLClassExpression C : all_qualifiers){
			if(C.isOWLNothing()){
				colSolver.addLe(b[qualifiers.get(C)], 0);
				colSolver.addGe(b[qualifiers.get(C)], 0);
			}
		}

		logger.trace("Qualifiers:");
		for(OWLClassExpression C : qualifiers.keySet()){
			if(C instanceof OWLObjectComplementOf)
				logger.trace("~" + ((OWLEntity)((OWLObjectComplementOf)C).getOperand()).getIRI().getFragment() + " : " + qualifiers.get(C));
			else
				logger.trace(((OWLEntity)C).getIRI().getFragment() + " : " + qualifiers.get(C));
		}
		/// COLUMN-GENERATION PROCEDURE ///

		double[] newCol = new double[subroles_num];

		/// COLUMN-GENERATION PROCEDURE ///

		double relaxed_opt;
		for (;;) {
			logger.trace("*****************************"); 
			/// OPTIMIZE OVER CURRENT COLUMNS ///

			boolean is_master_feasible = false;
			if(qcrSolver.solve()){


				is_master_feasible = true;

				relaxed_opt = qcrSolver.getObjValue();



				logger.trace("RMP Obj: " + relaxed_opt);
				ArrayList<Double> tempx = new ArrayList<Double>();
				for(int i = 0 ; i < x.getSize(); i++){
					tempx.add(qcrSolver.getValue(x.getElement(i)));
				}
				ArrayList<Double> temph = new ArrayList<Double>();
				for(int i = 0 ; i < h.getSize(); i++){
					temph.add(qcrSolver.getValue(h.getElement(i)));
				}
				if(x.getSize() != 0)
					logger.trace("x: " + tempx);
				logger.trace("h: " + temph);
				System.out.println("RMP obj  "+qcrSolver.getObjValue());
				//if(qcrSolver.getObjValue() < M){
			//		break;
			//	}
				/// FIND AND ADD A NEW COLUMN ///

				double[] price = qcrSolver.getDuals(Constraint);
				IloLinearNumExpr objExpr = colSolver.linearNumExpr();
				System.out.println("b length " + b.length );
				for(int j = 0 ; j < b.length ; j++)
					objExpr.addTerm(1 , b[j]);
				ReducedCost.setExpr(colSolver.diff(objExpr,
						colSolver.scalProd(a, price)));
				
				if(colSolver.solve()){
					System.out.println("Pricing Obj: " + colSolver.getObjValue());
					logger.trace("Pricing Obj: " + colSolver.getObjValue());

					if ( colSolver.getObjValue() > -RC_EPS ){
						logger.trace("Relaxed solved! Obj: " + relaxed_opt);
						break;
					}

					newCol = colSolver.getValues(a);

					logger.trace("a: " + Arrays.toString(colSolver.getValues(a)));
					logger.trace("b: " + Arrays.toString(colSolver.getValues(b)));

					double[] bVal = colSolver.getValues(b);
					int cost = 0;
					for(int j = 0 ; j < bVal.length ; j++)
						cost += bVal[j];

					IloColumn column = qcrSolver.column(Obj, cost);
					for ( int i = 0; i < subroles_num; i++ )
						column = column.and(qcrSolver.column(Constraint[i], newCol[i]));

					x.add( qcrSolver.numVar(column, 0., Double.MAX_VALUE) );
					subsets.add(new SubSet(colSolver.getValues(a) , colSolver.getValues(b)));
				}
				else
					break;
			}
			else 
			{	
				logger.trace("Infeasible RMP");
				logger.trace("Infeasible inequality system.");
				return_information.setSolved(is_master_feasible);
				return return_information;
			}
		}

		if( relaxed_opt < M ){
			System.out.println("Feasible Relaxation: " + relaxed_opt);
			logger.trace("Feasible Relaxation");
			for ( int i = 0; i < x.getSize(); i++ ) {
				qcrSolver.add(qcrSolver.conversion(x.getElement(i),
						IloNumVarType.Int));
			}
			for ( int i = 0; i < h.getSize(); i++ ) {
				qcrSolver.add(qcrSolver.conversion(h.getElement(i),
						IloNumVarType.Int));
			}

			boolean result = false;     
			if(qcrSolver.solve()){
				result = true;
				Set<EdgeInformation> edgeInformationSet = new HashSet<EdgeInformation>();
				if( qcrSolver.getObjValue() < M){
					logger.trace("Feasible ILP");
					logger.trace("ILP obj: " + qcrSolver.getObjValue());
					logger.trace("Feasible inequality system.");
					BiMap<Integer, OWLClassExpression> reverse_qualifiers_map = qualifiers.inverse();
					for(int i = 0; i < x.getSize(); i++){
						int cardinality = (int) qcrSolver.getValue(x.getElement(i));
						if(cardinality > 0.5){
							SubSet tempSubSet = subsets.get(i);
							Set<OWLObjectPropertyExpression> tempObjectSet = new HashSet<>();
							Set<OWLClassExpression> tempClassSet = new HashSet<>();
							boolean addIt = false;
							for(int j = 0 ; j < tempSubSet.getConceptIndexSet().length ; j++){
								if(tempSubSet.getConceptIndexSet()[j] > 0.5){
									tempClassSet.add(reverse_qualifiers_map.get(j));
									if(!addIt)
										addIt = true;
								}
							}
							if(addIt){
								for(int j = 0 ; j < tempSubSet.getRolesIndexSet().length ; j++){
									if(tempSubSet.getRolesIndexSet()[j] > 0.5)
										tempObjectSet.add(subroles.get(j).role);
								}
								////System.out.println("Heeeeeeeeeeey! " + tempClassSet);
								
								////System.out.println("Heeeeeeeeeeey! " + tempClassSet);
								EdgeInformation tempEdgeInformation = new EdgeInformation(tempObjectSet , tempClassSet , cardinality);
								edgeInformationSet.add(tempEdgeInformation);
							}
						}
					}

					Set<QCR> temp_max_qcrs = subroles.values().stream()
							.filter(qcr -> qcr.type.equals("MAX"))
							.collect(Collectors.toSet());
					Map<QCR , Integer> check_complement = new HashMap<>();
					for(QCR q : temp_max_qcrs){
						check_complement.put(q, q.cardinality);
					}

					int check_node_num = 0;
					for(EdgeInformation e : edgeInformationSet)
						check_node_num += e.getCardinality();

					for(QCR q : temp_max_qcrs){
						int remained_nodes = check_node_num;
						Set<EdgeInformation> addedEdgeInformations = new HashSet<EdgeInformation>();
						Set<EdgeInformation> reserveEdgeInformations = new HashSet<EdgeInformation>();
						for(EdgeInformation e : edgeInformationSet){
							if(e.getFillers().contains(q.qualifier)){
								reserveEdgeInformations.add(e);
								check_complement.put(q, check_complement.get(q) - e.getCardinality());
								remained_nodes -= e.getCardinality();
							}
						}
						if(check_complement.get(q) > 0 && remained_nodes > 0){
							////System.out.println(q.qualifier);
							for(EdgeInformation e : edgeInformationSet){
								if(check_complement.get(q) == 0)
									break;
								Set<OWLObjectPropertyExpression> tempObj = e.getEdges();
								Set<OWLClassExpression> tempSet = e.getFillers();
								int card = e.getCardinality();
								if(!e.getFillers().contains(q.qualifier)){
									if(e.getCardinality() > check_complement.get(q)){
										EdgeInformation tempEdgeInformation = new EdgeInformation(tempObj , tempSet , card - check_complement.get(q));
										addedEdgeInformations.add(tempEdgeInformation);
										e.modifyCardinality(check_complement.get(q));
										reserveEdgeInformations.add(e);
										check_complement.put(q, 0);
									}
									else{
										reserveEdgeInformations.add(e);
										check_complement.put(q, check_complement.get(q) - card);
									}
								}
							}
						}
						edgeInformationSet.addAll(addedEdgeInformations);
						for(EdgeInformation e : edgeInformationSet){
							if(!reserveEdgeInformations.contains(e))
								e.addFiller(q.qualifier.getComplementNNF());
						}
					}

					Map<EdgeInformation , Integer> edge_map = new HashMap<>();
					for(EdgeInformation e : edgeInformationSet){
						EdgeInformation indic = this.containsEdge(edge_map.keySet(), e);
						if(indic == null)
							edge_map.put(e, e.getCardinality());
						else {
							edge_map.put(indic, edge_map.get(indic) + e.getCardinality());
						}
					}

					Set<EdgeInformation> finalEdgeInformations = new HashSet<EdgeInformation>();
					for(EdgeInformation e : edge_map.keySet()){
						Set<OWLClassExpression> fillers = e.getFillers();
						////System.out.println("Heeeeeeeeeeey! " + fillers);
						////System.out.println(auxs);
						
						////System.out.println("Hoooooooooooy! " + fillers);
						EdgeInformation tempEdgeInformation = new EdgeInformation(e.getEdges(), fillers, edge_map.get(e));
						finalEdgeInformations.add(tempEdgeInformation);
					}

					//System.out.println(this.all_qualifiers);

					return_information.setEdgeInformation(finalEdgeInformations);
				}
				else {
					result = false;
					Set<OWLObjectCardinalityRestriction> infeasible_set  = new HashSet<>();
					for(int i = 0; i < subroles_num; i++){
						if(qcrSolver.getValue(h.getElement(i)) > 0.1){
							infeasible_set.add(qcr_map.get(i));
						}
					}
					return_information.setInfeasible_set(infeasible_set);
				}
			}
			else{
				logger.trace("Infeasible ILP");
				logger.trace("Infeasible inequality system.");
			}
			qcrSolver.end();
			colSolver.end();
			return_information.setSolved(result);
			
			return return_information;
		}
		else{
			logger.trace("Infeasible Relaxation");
			logger.trace("Infeasible inequality system.");
			Set<OWLObjectCardinalityRestriction> infeasible_set  = new HashSet<>();
			for(int i = 0; i < subroles_num; i++){
				if(qcrSolver.getValue(h.getElement(i)) > 0.1){
					infeasible_set.add(qcr_map.get(i));
				}
			}
			qcrSolver.end();
			colSolver.end();
			return_information.setSolved(false);
			return_information.setInfeasible_set(infeasible_set);
			return return_information;
		}
	}

	private EdgeInformation containsEdge(Set<EdgeInformation> aSet , EdgeInformation a){
		Set<OWLClassExpression> tempSet = a.getFillers();
		Set<OWLObjectPropertyExpression> tempObj = a.getEdges();
		for(EdgeInformation e : aSet){
			if(e.getFillers().equals(tempSet) && e.getEdges().equals(tempObj))
				return e;
		}
		return null;	
	}
}