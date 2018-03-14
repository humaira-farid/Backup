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
import org.semanticweb.owlapi.model.OWLObjectCardinalityRestriction;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectOneOf;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;

import ilog.concert.*;
import ilog.cplex.*;
import reasoner.ilp.CplexModelGenerator2.SubSet;


public class CplexModelGenerator4 {
	IloCplex cplexModel;
	ILPPreprocessor ilpPro;
	List<OWLObjectCardinalityRestriction> qcrList;
	Set<QCR> qcrs;
	Set<OWLObjectOneOf> nominals;
	Set<OWLClassExpression> qcrQualifiers = null;
	Set<OWLClassExpression> allQualifiers;
	Map<Integer, QCR> qcrMap;
	Map<Integer, OWLObjectCardinalityRestriction> crMap;
	BiMap<OWLClassExpression, Integer> qualifiers = HashBiMap.create();
	Set<OWLObjectCardinalityRestriction> infeasibilities = new HashSet<>();
	boolean initiallySolved;
	int M;
	int totalQCR = 0;
	int totalNominals = 0;
	int totalVar = 0;
	static double RC_EPS = 1.0e-6;
	
	public CplexModelGenerator4(ILPPreprocessor ilpPr) {
		//System.out.println(Math.abs(2.5 % 1) <= RC_EPS);
		ilpPro = ilpPr;
		qcrs = ilpPro.getQcrs();
		qcrQualifiers = qcrs.stream().map(qcr -> qcr.qualifier).collect(Collectors.toSet());
		nominals = new HashSet<OWLObjectOneOf>(ilpPro.getNominals());
		allQualifiers = new HashSet<OWLClassExpression>(qcrQualifiers);
		allQualifiers.addAll(nominals);
		qcrMap  = ilpPro.getQCRMap();
		crMap = ilpPro.getCRMap();
		qcrList = ilpPro.cardRes;
		M = 100;
		int tempQN = 0;
		for(OWLClassExpression C : allQualifiers){
			qualifiers.put(C, tempQN);
			++tempQN;
		}
		
		totalQCR = qcrs.size();
		totalNominals = nominals.size();
		totalVar = totalQCR+totalNominals;
		
		try {
			cplexModel= new IloCplex();
		} catch (IloException e) {
			e.printStackTrace();
		}
	}
	
	public ILPSolution getILPSolution() throws IloException {
		
		generateCplexModel();
		 return solve(new RMPModel().generateRmpModel(), new PPModel().GeneratePpModel());
	}
	public void generateCplexModel(/*OWLObjectMinCardinality minCard*/) {
		
		IloCplex initSolver;
		try {
			initSolver = new IloCplex();
			initSolver.setOut(new NullOutputStream());

			IloObjective initObj = initSolver.addMinimize();

			Map<OWLClassExpression , IloNumVar> check_var = new HashMap<>();
			for(OWLClassExpression C : qcrQualifiers){
				if(!check_var.containsKey(C))
					check_var.put(C , initSolver.numVar(0., Double.MAX_VALUE));
			}


			// Setting objective function
			IloLinearNumExpr initobjExpr = initSolver.linearNumExpr();
			initobjExpr.addTerm(0 , initSolver.numVar(0., Double.MAX_VALUE));
			//void addTerm(double coef,IloNumVar var)throws IloException
					//  Adds the new term coef * var to a scalar product.
			initObj.setExpr(initobjExpr);
			Map<IloRange , Set<OWLObjectCardinalityRestriction>> rang_qcr_map = new HashMap<>();

			for(OWLClassExpression C : check_var.keySet()){
				HashMap<Double , OWLObjectCardinalityRestriction> LBs = new HashMap<>();
				HashMap<Double , OWLObjectCardinalityRestriction> UBs = new HashMap<>();
				for(Integer val : qcrMap.keySet()){
					QCR qcr = qcrMap.get(val);
					if(qcr.qualifier.equals(C)){
						if(qcr.type.equals("MIN"))
							LBs.put((double) qcr.cardinality , crMap.get(val));
						else if(qcr.type.equals("MAX"))
							UBs.put((double) qcr.cardinality , crMap.get(val));
						else {
							LBs.put((double) qcr.cardinality , crMap.get(val));
							UBs.put((double) qcr.cardinality , crMap.get(val));
						}
					}
				}
				double lb = 0;
				double ub = 10000;
				Set<OWLObjectCardinalityRestriction> LB_map = new HashSet<>();
				Set<OWLObjectCardinalityRestriction> UB_map = new HashSet<>();
				if(!LBs.isEmpty()){
					lb = Collections.max(LBs.keySet());// so if we have >=1A and >=2A then it will consider >=2A only
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
				if(qcrQualifiers != null)
					this.allQualifiers = new HashSet<OWLClassExpression>(qcrQualifiers);
				else
					this.allQualifiers = new HashSet<OWLClassExpression>();

			//	OWLClassExpression Thing = (OWLClassExpression)OWLFunctionalSyntaxFactory.OWLThing();
			//	this.allQualifiers.add(Thing);

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
					//This method computes a minimum-cost relaxation in order to make the active model feasible by relaxing the bounds of the range constraints specified in the array rngs.
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

		
		
		/*try {
			
			double lb = 0.0;
			double ub = Double.MAX_VALUE;
			
			//IloObjective Obj = cplexModel.addMinimize();
			IloRange[]   Constraint = new IloRange[totalVar];
			IloLinearNumExpr[] expr = new IloLinearNumExpr[totalVar];

			int i = 0;
			int M = 10;
			IloNumVar[] h = cplexModel.numVarArray(totalVar, lb, ub);
			IloNumVar[] x = cplexModel.numVarArray(totalVar, lb, ub);
			for (QCR qcr : qcrs) {
				if(qcr.type.equals("MIN")){
				//	Constraint[i] = cplexModel.addGe(expr[i], qcr.cardinality);
					Constraint[i] = cplexModel.addGe(h[i], qcr.cardinality);
					i++;
				}
				else if(qcr.type.equals("MAX")){
				//	Constraint[i] = cplexModel.addLe(expr[i], qcr.cardinality);	
					Constraint[i] = cplexModel.addLe(h[i], qcr.cardinality);
					i++;
				}
				///exact cardinality???? 
			}
			for (int j = i; j < totalVar; j++ )
				Constraint[j] = cplexModel.addEq(h[j], 1);
				
				//Constraint[j] = cplexModel.addEq(expr[j], 1);
				
			IloLinearNumExpr objective = cplexModel.linearNumExpr();
			for (int j = 0; j < totalVar; j++ ) 
				objective.addTerm(M, h[j]);
			cplexModel.addMinimize(objective);
			
			//variables
			//IloNumVar h1 = cplexModel.numVar(0, Double.MAX_VALUE, "h1");
			//IloNumVar h2 = cplexModel.numVar(0, Double.MAX_VALUE, "h2");
		
			//expressions -- min 10h1 + 10 h2
			//IloLinearNumExpr objective = cplexModel.linearNumExpr();
			//objective.addTerm(10, h1);
			//objective.addTerm(10, h2);
			
			//define objective
			//cplexModel.addMinimize(objective);
			
			//define constraints -- h1  >=1 
			//cplex.addGe(h1, minCard.getCardinality());
			//cplexModel.addGe(h1, 1);
			//cplexModel.addGe(h2, 1);
			//define constraints --  (60h1 + 60h2 >= 8)
			//cplex.addGe(cplex.sum(cplex.prod(60, h1), cplex.prod(60, h2)), 20);
			//define constraints --  (2h1 + 4h2 <= 20)
			//cplex.addLe(cplex.sum(cplex.prod(2, h1), cplex.prod(4, h2)), 20);
			//cplex.solve();
			
			if(cplexModel.solve()) {
				System.out.println("obj = "+cplexModel.getObjValue());
				for (int j = 0; j < totalVar; j++ ) 
					System.out.println("h"+ j +" = "+cplexModel.getValue(h[j]));
				for (int j = 0; j < totalVar; j++ ) 
					System.out.println("c"+ j +" = "+cplexModel.getDual(Constraint[j]));
				
			}
			
			
			IloCplex ppSolver = new IloCplex();
			IloObjective ReducedCost = ppSolver.addMinimize();
			IloNumVar[] r = ppSolver.numVarArray(totalVar, 0., 1, 
					IloNumVarType.Int);
			IloNumVar[] b = ppSolver.numVarArray(this.qcrQualifiers.size(), 0., 1, 
					IloNumVarType.Int);

			// In at-least restrictions: if a[i]==1 --> b[i.qualifier]=1
			// In at-most restrictions: if b[i.qualifier]==1 --> a[i]=1
			int k = 0;
			for (QCR qcr : qcrs) {
				if(qcr.type.equals("MIN")){
					ppSolver.addLe(r[k], b[qualifiers.get(qcrMap.get(i).qualifier)]);
					k++;
				}
				else{
					ppSolver.addLe(b[qualifiers.get(qcrMap.get(i).qualifier)], r[k]);
					k++;
				}
			}
			
			
		}
		catch(IloException e) {
			e.printStackTrace();
		}*/
	}
	
	
	public IloCplex getCplexModel() {
		return this.cplexModel;
	}
	
	public ILPSolution solve(RMPModel rmpModel, PPModel ppModel) throws IloException{
		//int M = 100;
		ILPSolution return_information = new ILPSolution();
		
		if(!initiallySolved){
			return_information.setInfeasible_set(infeasibilities);
			return_information.setSolved(false);
			return return_information;
		}
		
		IloCplex rmpCplex = rmpModel.getRmpCplex();
		IloObjective obj = rmpCplex.getObjective();
		IloCplex ppCplex = ppModel.getPpCplex();
		
		IloObjective reducedCost = ppCplex.getObjective();
		
		IloRange[]   Constraint = rmpModel.getConstraint() ;
		IloLinearNumExpr[] expr = rmpModel.getExpr();
		IloNumVarArray h = rmpModel.getH();
		IloNumVarArray x = rmpModel.getX();
		ArrayList<SubSet> subsets = rmpModel.getSubsets();
		
		IloNumVar[] r = ppModel.getR();
		IloNumVar[] b = ppModel.getB();
		
		

		/// COLUMN-GENERATION PROCEDURE ///

				double[] newCol = new double[totalVar];

				/// COLUMN-GENERATION PROCEDURE ///

				double relaxed_opt;
				for (;;) {
					
					boolean is_master_feasible = false;
					if(rmpCplex.solve()){
						is_master_feasible = true;

						relaxed_opt = rmpCplex.getObjValue();
					ArrayList<Double> tempx = new ArrayList<Double>();
					for(int i = 0 ; i < x.getSize(); i++){
						tempx.add(rmpCplex.getValue(x.getElement(i)));
					}
					ArrayList<Double> temph = new ArrayList<Double>();
					for(int i = 0 ; i < h.getSize(); i++){
						temph.add(rmpCplex.getValue(h.getElement(i)));
						System.out.println("card " + rmpCplex.getValue(h.getElement(i)));
					}
				/*	if(rmpCplex.getObjValue() < M){
						break;
					}
					-*/
					/// FIND AND ADD A NEW COLUMN ///

					double[] price = rmpCplex.getDuals(Constraint);
					IloLinearNumExpr objExpr = ppCplex.linearNumExpr();
					for(int j = 0 ; j < b.length ; j++)
						objExpr.addTerm(1 , b[j]);
					reducedCost.setExpr(ppCplex.diff(objExpr,
							ppCplex.scalProd(r, price)));

					if(ppCplex.solve()){
						
						if ( ppCplex.getObjValue() > -RC_EPS ){
							
							break;
						}

						newCol = ppCplex.getValues(r);

						
						double[] bVal = ppCplex.getValues(b);
						//System.out.println("bVal " + bVal.length);
						int cost = 0;
						for(int j = 0 ; j < bVal.length ; j++) {
							//System.out.println("bVal " + bVal[j]);
							cost += bVal[j];
						}
						//System.out.println("cost " + cost);
						IloColumn column = rmpCplex.column(obj, cost);//Creates and returns a column from the specified objective and value.
						for ( int i = 0; i < totalVar; i++ )
							column = column.and(rmpCplex.column(Constraint[i], newCol[i]));//Creates and returns a column from the specified range and value.

						x.add( rmpCplex.numVar(column, 0., Double.MAX_VALUE) );
						subsets.add(new SubSet(ppCplex.getValues(r) , ppCplex.getValues(b)));
					}
					else
						break;
				}
				else 
				{	
					
					return_information.setSolved(is_master_feasible);
					return return_information;
				}
			}
				System.out.println("relaxed_opt " + relaxed_opt);
			if( relaxed_opt < M ){
				for ( int i = 0; i < x.getSize(); i++ ) {
					rmpCplex.add(rmpCplex.conversion(x.getElement(i),IloNumVarType.Int));//Adds object to the invoking model.
											//Converts a numeric variable to a specified type.
				}
				for ( int i = 0; i < h.getSize(); i++ ) {
					rmpCplex.add(rmpCplex.conversion(h.getElement(i),IloNumVarType.Int));
				}

				boolean result = false;     
				if(rmpCplex.solve()){
					result = true;
					Set<EdgeInformation> edgeInformationSet = new HashSet<EdgeInformation>();
					if( rmpCplex.getObjValue() < M){
						for(int i = 0; i < h.getSize(); i++){
							int cardinality = (int) rmpCplex.getValue(h.getElement(i));
							//System.out.println("cardinality " + cardinality);
							if(cardinality > 0){
								System.out.println("cardinality " + cardinality);
							}
						}
						BiMap<Integer, OWLClassExpression> reverse_qualifiers_map = qualifiers.inverse();
						for(int i = 0; i < x.getSize(); i++){
							int cardinality = (int) rmpCplex.getValue(x.getElement(i));
							//System.out.println("cardinality " + rmpCplex.getValue(x.getElement(i)));
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
											tempObjectSet.add(qcrMap.get(j).role);
									}
									////System.out.println("Heeeeeeeeeeey! " + tempClassSet);
									EdgeInformation tempEdgeInformation = new EdgeInformation(tempObjectSet , tempClassSet , cardinality);
									edgeInformationSet.add(tempEdgeInformation);
								}
							}
						}

						Set<QCR> temp_max_qcrs = qcrMap.values().stream()
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
						for(int i = 0; i < totalVar; i++){
							if(rmpCplex.getValue(h.getElement(i)) > 0.1){
								infeasible_set.add(crMap.get(i));
							}
						}
						return_information.setInfeasible_set(infeasible_set);
					}
				}
				else{
					System.out.println("Infeasible inequality system.");
				}
				rmpCplex.end();
				ppCplex.end();
				return_information.setSolved(result);
				
				return return_information;
			}
			else{
				Set<OWLObjectCardinalityRestriction> infeasible_set  = new HashSet<>();
				for(int i = 0; i < totalVar; i++){
					if(rmpCplex.getValue(h.getElement(i)) > 0.1){
						infeasible_set.add(crMap.get(i));
					}
				}
				rmpCplex.end();
				ppCplex.end();
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
	private class NullOutputStream extends OutputStream {    
		@Override
		public void write(int b) throws IOException {
		}
	}
	
	
	private class RMPModel{
		IloCplex rmpCplex;
		IloObjective obj;
		IloRange[]   Constraint;
		IloLinearNumExpr[] expr;
		IloNumVarArray h;
		private IloNumVarArray x;
		ArrayList<SubSet> subsets;
		
		private RMPModel() throws IloException {
			rmpCplex = new IloCplex();
			rmpCplex.setOut(new NullOutputStream());
			obj = rmpCplex.addMinimize();
			Constraint = new IloRange[totalVar];
			expr = new IloLinearNumExpr[totalVar];


			h = new IloNumVarArray();
			setX(new IloNumVarArray());
			subsets = new ArrayList<SubSet>();
		}
		
		public RMPModel generateRmpModel() throws IloException {
			
			//System.out.println("totalVar "+ totalVar + "qcrmap size " + qcrMap.size());
			for (int i = 0; i < totalVar; i++) {
				if(qcrMap.get(i).type.equals("MIN")){
					Constraint[i] = rmpCplex.addGe(expr[i], qcrMap.get(i).cardinality);
				}
				else{
					Constraint[i] = rmpCplex.addLe(expr[i], qcrMap.get(i).cardinality);	
				}
			}

			for (int i = 0; i < totalVar; i++)
				h.add(rmpCplex.numVar(rmpCplex.column(obj, M).and(
						rmpCplex.column(Constraint[i],1)),
						0.0, Double.MAX_VALUE));

			rmpCplex.setParam(IloCplex.Param.RootAlgorithm, IloCplex.Algorithm.Primal);
			return this;
		}

		public IloCplex getRmpCplex() {
			return rmpCplex;
		}

		public void setRmpCplex(IloCplex rmpCplex) {
			this.rmpCplex = rmpCplex;
		}

		public IloObjective getObj() {
			return obj;
		}

		public void setObj(IloObjective obj) {
			this.obj = obj;
		}

		public IloRange[] getConstraint() {
			return Constraint;
		}

		public void setConstraint(IloRange[] constraint) {
			Constraint = constraint;
		}

		public IloLinearNumExpr[] getExpr() {
			return expr;
		}

		public void setExpr(IloLinearNumExpr[] expr) {
			this.expr = expr;
		}

		public IloNumVarArray getH() {
			return h;
		}

		public void setH(IloNumVarArray h) {
			this.h = h;
		}

		public ArrayList<SubSet> getSubsets() {
			return subsets;
		}

		public void setSubsets(ArrayList<SubSet> subsets) {
			this.subsets = subsets;
		}

		public IloNumVarArray getX() {
			return x;
		}

		public void setX(IloNumVarArray x) {
			this.x = x;
		}
	}
	private class PPModel{
		IloCplex ppCplex;
		IloObjective reducedCost;
		IloNumVar[] r ;
		IloNumVar[] b ;
		
		public IloCplex getPpCplex() {
			return ppCplex;
		}
		public void setPpCplex(IloCplex ppCplex) {
			this.ppCplex = ppCplex;
		}
		public IloObjective getReducedCost() {
			return reducedCost;
		}
		public void setReducedCost(IloObjective reducedCost) {
			this.reducedCost = reducedCost;
		}
		public IloNumVar[] getR() {
			return r;
		}
		public void setR(IloNumVar[] r) {
			this.r = r;
		}
		public IloNumVar[] getB() {
			return b;
		}
		public void setB(IloNumVar[] b) {
			this.b = b;
		}
		
		public PPModel GeneratePpModel() throws IloException {
			ppCplex = new IloCplex();
			ppCplex.setOut(new NullOutputStream());

			reducedCost = ppCplex.addMinimize();
			r = ppCplex.numVarArray(totalVar, 0., 1, 
					IloNumVarType.Int);
			b = ppCplex.numVarArray(qcrQualifiers.size(), 0., 1, 
					IloNumVarType.Int);

			// In at-least restrictions: if r[i]==1 --> b[i.qualifier]=1
			// In at-most restrictions: if b[i.qualifier]==1 --> a[i]=1
			for (int i = 0; i < totalVar; i++ ) {
				if(qcrMap.get(i).type.equals("MIN"))
					ppCplex.addLe(r[i] , b[qualifiers.get(qcrMap.get(i).qualifier)]);
				else
					ppCplex.addLe(b[qualifiers.get(qcrMap.get(i).qualifier)] , r[i]);	 
			}
			//disjoint
			/*ppCplex.addLe(ppCplex.sum(ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(0).qualifier)]),
					ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(1).qualifier)])), 1);*/
			//subsumption

			ppCplex.addLe(b[qualifiers.get(qcrMap.get(0).qualifier)],b[qualifiers.get(qcrMap.get(1).qualifier)]);
			
			//ppCplex.addLe(ppCplex.sum(ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(1).qualifier)]),
			//		ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(2).qualifier)])), 1);
			return this;
		}
	}
}

