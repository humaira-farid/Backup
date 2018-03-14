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
import org.semanticweb.owlapi.model.*;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import com.google.common.collect.SetMultimap;

import ilog.concert.*;
import ilog.cplex.*;
import reasoner.ilp.CplexModelGenerator2.SubSet;


public class CplexModelGenerator1 {
	IloCplex cplexModel;
	ILPPreprocessor ilpPro;
	List<OWLObjectCardinalityRestriction> qcrList;
	Set<QCR> qcrs;
	Set<OWLObjectOneOf> nominals;
	Set<OWLClassExpression> qcrQualifiers = null;
	Set<OWLClassExpression> allQualifiers;
	Map<Integer, QCR> qcrMap;
	Map<Integer, OWLObjectCardinalityRestriction> crMap;
	Set<OWLObjectProperty> axiomRoles = null;
	//Set<OWLObjectProperty> otherRoles = new HashSet<>();
	Set<OWLObjectProperty> srRoles = new HashSet<>();
	
	BiMap<OWLClassExpression, Integer> qualifiers = HashBiMap.create();
	//BiMap<OWLObjectProperty, Integer> otherRolesMap = HashBiMap.create();
	BiMap<OWLObjectProperty, Integer> srRolesMap = HashBiMap.create();
	
	BiMap<OWLObjectProperty, Integer> tempRoleHMap = HashBiMap.create();
	
	Set<OWLObjectCardinalityRestriction> infeasibilities = new HashSet<>();
	Map<OWLObjectProperty, Set<OWLObjectProperty>> superRoles = new HashMap<>();;
	SetMultimap<OWLObjectProperty, OWLClassExpression> forAllMap;

	Map<OWLObjectProperty, OWLObjectProperty> tempRoleH = new HashMap<>();
	
	boolean initiallySolved;
	int M;
	int totalQCR = 0;
	int totalNominals = 0;
	int totalVar = 0;
	static double RC_EPS = 1.0e-6;
	
	public CplexModelGenerator1(ILPPreprocessor ilpPr, 
			Map<OWLObjectProperty, Set<OWLObjectProperty>> superRoles,
			SetMultimap<OWLObjectProperty, OWLClassExpression> forAllMap, Map<OWLObjectProperty, OWLObjectProperty> tempRoleH) {
		
		ilpPro = ilpPr;
		this.superRoles =  superRoles;
		this.tempRoleH = tempRoleH;
		qcrs = ilpPro.getQcrs();
		qcrQualifiers = qcrs.stream().map(qcr -> qcr.qualifier).collect(Collectors.toSet());
		nominals = new HashSet<OWLObjectOneOf>(ilpPro.getNominals());
		allQualifiers = new HashSet<OWLClassExpression>(qcrQualifiers);
		
		//allQualifiers.addAll(nominals);
		
		qcrMap  = ilpPro.getQCRMap();
		crMap = ilpPro.getCRMap();
		qcrList = ilpPro.cardRes;
		
		axiomRoles = qcrs.stream().filter(qcr -> qcr.role!=null).map(qcr -> qcr.role.getNamedProperty()).collect(Collectors.toSet());
		
		for(OWLObjectProperty role : axiomRoles) {
			if(superRoles.get(role)!=null) {
				for(OWLObjectProperty supRole : superRoles.get(role)) {
					this.srRoles.add(supRole);
				}
			}
		}
		
		this.forAllMap = HashMultimap.create();
		for(Entry<OWLObjectProperty, OWLClassExpression> e : forAllMap.entries()){
			this.forAllMap.put(e.getKey(), e.getValue());
			allQualifiers.add(e.getValue());
		}
		
		M = 100;
		int tempQN = 0;
		for(OWLClassExpression C : allQualifiers){
			qualifiers.put(C, tempQN);
			++tempQN;
		}
		int tempRN = 0;
		for(OWLObjectProperty r : srRoles){
			srRolesMap.put(r, tempRN);
			++tempRN;
		}
		int tempRHN = 0;
		for(Entry<OWLObjectProperty, OWLObjectProperty> e : tempRoleH.entrySet()){
		//for(OWLObjectProperty r : tempRoleH.){
			tempRoleHMap.put(e.getValue(), tempRHN);
			++tempRHN;
		}
		totalQCR = qcrs.size();
		totalNominals = nominals.size();
		totalVar = totalQCR;//+totalNominals;
		
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
			/*	if(qcrQualifiers != null)
					this.allQualifiers = new HashSet<OWLClassExpression>(qcrQualifiers);
				else
					this.allQualifiers = new HashSet<OWLClassExpression>();
			 */
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

		
	}
	
	
	public IloCplex getCplexModel() {
		return this.cplexModel;
	}
	
	public ILPSolution solve(RMPModel rmpModel, PPModel ppModel) throws IloException{
		//int M = 100;
		ILPSolution returnSolution = new ILPSolution();
		
		if(!initiallySolved){
			returnSolution.setInfeasible_set(infeasibilities);
			returnSolution.setSolved(false);
			return returnSolution;
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
		IloNumVar[] sr = ppModel.getSR();
	//	IloNumVar[] hr = ppModel.getHR();
		IloNumVar[] b = ppModel.getB();
		
		

		/// Generating new columns ///

				double[] newCol = new double[totalVar];

				double relaxed_opt;
				while (true) {
					
					boolean isRMPFeasible = false;
					if(rmpCplex.solve()){
						isRMPFeasible = true;
						relaxed_opt = rmpCplex.getObjValue();
						System.out.println("relaxed_opt "+relaxed_opt);
					for(int j=0; j<x.getSize(); j++)
						System.out.println("x value  "+rmpCplex.getValue(x.getElement(j)));
					
				//	if(relaxed_opt < M){
				//		break;
				//	}
					
					/// generate and add a new column in RMP

					double[] price = rmpCplex.getDuals(Constraint);
					for(int j = 0 ; j < price.length ; j++)
						System.out.println("dual value  "+price[j]);
					
					IloLinearNumExpr objExpr = ppCplex.linearNumExpr();
					for(int j = 0 ; j < b.length ; j++)
						objExpr.addTerm(1 , b[j]);
					
					reducedCost.setExpr(ppCplex.diff(objExpr,ppCplex.scalProd(r, price)));

					if(ppCplex.solve()){
						
						if ( ppCplex.getObjValue() > -RC_EPS ){
							break;
						}

						newCol = ppCplex.getValues(r);
						
						double[] bVal = ppCplex.getValues(b);
						//System.out.println("bVal " + bVal.length);
						int cost = 0;
						double[] rv = ppCplex.getValues(r);
						System.out.println("------");
						for(int j = 0 ; j < rv.length ; j++) {
							System.out.println("r v  ["+j +"]"+ rv[j]);
							
						}
						
						
						double[] srv = ppCplex.getValues(sr);
						
						for(int j = 0 ; j < srv.length ; j++) {
							System.out.println("sr v ["+j +"]"+ srv[j]);
							
						}
						for(int j = 0 ; j < bVal.length ; j++) {
							//System.out.println("bVal " + bVal[j]);
							cost += bVal[j];
						}
						//System.out.println("cost " + cost);
						IloColumn column = rmpCplex.column(obj, cost);//Creates and returns a column from the specified objective and value.
						for ( int i = 0; i < totalVar; i++ )
							column = column.and(rmpCplex.column(Constraint[i], newCol[i]));//Creates and returns a column from the specified range and value.
						
						x.add( rmpCplex.numVar(column, 0., Double.MAX_VALUE) );
						subsets.add(new SubSet(ppCplex.getValues(r) , ppCplex.getValues(b), ppCplex.getValues(sr)));
						
						//subsets.add(new SubSet(ppCplex.getValues(r) , ppCplex.getValues(b), ppCplex.getValues(sr), ppCplex.getValues(hr)));
					}
					else
						break;
				}
				else 
				{	
					
					returnSolution.setSolved(isRMPFeasible);
					return returnSolution;
				}
			}
				System.out.println("final relaxed_opt " + relaxed_opt);
			if( relaxed_opt < M ){
				System.out.println("x.getSize() " + x.getSize());
				for ( int i = 0; i < x.getSize(); i++ ) {
					/// LP relaxation 
					//System.out.println("cardinality " + rmpCplex.getValue(x.getElement(i)));
					rmpCplex.add(rmpCplex.conversion(x.getElement(i),IloNumVarType.Int));//Adds object to the invoking model.
											//Converts a numeric variable to a specified type.
					//rmpCplex.add(x.getElement(i));


				}
				for ( int i = 0; i < h.getSize(); i++ ) {
					rmpCplex.add(rmpCplex.conversion(h.getElement(i),IloNumVarType.Int));
				}

				boolean result = false;     
				if(rmpCplex.solve()){
					result = true;
					Set<EdgeInformation> edgeInformationSet = new HashSet<EdgeInformation>();
					
					if( rmpCplex.getObjValue() < M){
						System.out.println("rmpCplex.getObjValue() " + rmpCplex.getObjValue());
						for(int i = 0; i < h.getSize(); i++){
							double cardinality = rmpCplex.getValue(h.getElement(i));
							//System.out.println("cardinality " + cardinality);
							if(cardinality > 0){
								System.out.println("non zero cardinality " + cardinality);
							}
						}
						
						BiMap<Integer, OWLClassExpression> reverseQualifiers = qualifiers.inverse();
						BiMap<Integer, OWLObjectProperty> reverseRoles = srRolesMap.inverse();
						BiMap<Integer, OWLObjectProperty> reverseTempRoles = tempRoleHMap.inverse();
						Map<OWLObjectProperty, OWLObjectProperty> reverseTempRoleH = new HashMap<>();
						for(Entry<OWLObjectProperty, OWLObjectProperty> e : tempRoleH.entrySet()){
							reverseTempRoleH.put(e.getValue(), e.getKey());
						}
						//System.out.println("x.getSize() ---" + x.getSize());
						
						
						for(int i = 0; i < x.getSize(); i++){
							double cardinality = rmpCplex.getValue(x.getElement(i));
							if(!isInteger(cardinality)) {
								System.out.println("non integer cardinality " + cardinality);
							}
							else {
								System.out.println("x cardinality " + cardinality);
								if(cardinality > 0.0){
									System.out.println("i value " + i);
									
									SubSet tempSubSet = subsets.get(i);
									
									Set<OWLObjectPropertyExpression> tempRoleSet = new HashSet<>();
									Set<OWLObjectPropertyExpression> tempSupRoleSet = new HashSet<>();
									Set<OWLClassExpression> tempClassSet = new HashSet<>();
										
									boolean addIt = false;
										
									for(int j = 0 ; j < tempSubSet.getConceptIndexSet().length ; j++){
										if(tempSubSet.getConceptIndexSet()[j] > 0){ // if b value is 1
											tempClassSet.add(reverseQualifiers.get(j));
											if(!addIt)
												addIt = true;
											}
									}
									System.out.println("tempClassSet "+tempClassSet.size());
									if(addIt){
											for(int j = 0 ; j < tempSubSet.getRolesIndexSet().length ; j++){
												if(tempSubSet.getRolesIndexSet()[j] > 0) { // if r value is 1
													System.out.println(" role "+qcrMap.get(j).role);
													tempRoleSet.add(qcrMap.get(j).role);
												}
											}
											for(int j = 0 ; j < tempSubSet.getSupRolesIndexSet().length ; j++){
												if(tempSubSet.getSupRolesIndexSet()[j] > 0) { // if sr value is 1
													System.out.println("sr["+j+"]: "+tempSubSet.getSupRolesIndexSet()[j]);
													System.out.println("sup role "+reverseRoles.get(j) );
													
													tempSupRoleSet.add(reverseRoles.get(j));
												}
											}
										/*	for(int j = 0 ; j < tempSubSet.getTempSupRolesIndexSet().length ; j++){
												if(tempSubSet.getTempSupRolesIndexSet()[j] > 0) { // if hr value is 1
													System.out.println(tempSubSet.getTempSupRolesIndexSet()[j]);
													System.out.println("temp role "+reverseTempRoles.get(j) +" role "+reverseTempRoleH.get(reverseTempRoles.get(j)));
													tempSupRoleSet.add(reverseTempRoleH.get(reverseTempRoles.get(j)));
												}
											}*/
											tempRoleSet.addAll(tempSupRoleSet);
											EdgeInformation tempEdgeInformation = new EdgeInformation(tempRoleSet , tempClassSet , cardinality);
											edgeInformationSet.add(tempEdgeInformation);
										}
									
								}
							}
						}
						
						// Adding complement to ensure at most restrictions
						Set<QCR> tempMaxQcrs = qcrMap.values().stream().filter(qcr -> qcr.type.equals("MAX")).collect(Collectors.toSet());
						Map<QCR , Integer> check_complement = new HashMap<>();
						for(QCR q : tempMaxQcrs){
							check_complement.put(q, q.cardinality);
						}

						int totalNodes = 0;
						for(EdgeInformation e : edgeInformationSet)
							totalNodes += e.getCardinality();

						for(QCR q : tempMaxQcrs){
							int remained_nodes = totalNodes;
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
							EdgeInformation tempEdgeInformation = new EdgeInformation(e.getEdges(), fillers, edge_map.get(e));
							finalEdgeInformations.add(tempEdgeInformation);
						}

						returnSolution.setEdgeInformation(finalEdgeInformations);
					}
					else {
						result = false;
						Set<OWLObjectCardinalityRestriction> infeasible_set  = new HashSet<>();
						for(int i = 0; i < totalVar; i++){
							if(rmpCplex.getValue(h.getElement(i)) > 0.1){
								infeasible_set.add(crMap.get(i));
							}
						}
						returnSolution.setInfeasible_set(infeasible_set);
					}
				}
				else{
					System.out.println("Infeasible inequality system.");
				}
				rmpCplex.end();
				ppCplex.end();
				returnSolution.setSolved(result);
				
				return returnSolution;
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
				returnSolution.setSolved(false);
				returnSolution.setInfeasible_set(infeasible_set);
				return returnSolution;
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
		double[] supRolesIndexSet;
		double[] conceptIndexSet;
		//double[] tempSupRolesIndexSet;
		int cost;

		SubSet(double[] rolesIndexSet, double[] conceptIndexSet, double[] supRolesIndexSet){
			this.rolesIndexSet = rolesIndexSet;
			this.conceptIndexSet = conceptIndexSet;
			this.supRolesIndexSet = supRolesIndexSet;
			//this.tempSupRolesIndexSet = tempSupRolesIndexSet;
			cost = 0;
			for(int j = 0 ; j < conceptIndexSet.length ; j++)
				cost += conceptIndexSet[j];
		}

	/*	public double[] getTempSupRolesIndexSet() {
			return tempSupRolesIndexSet;
		}*/

		public double[] getSupRolesIndexSet() {
			return supRolesIndexSet;
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
	private boolean isInteger(double d) {
		//System.out.println(Math.abs(2.5 % 1) <= RC_EPS);
		if(Math.abs(d % 1) <= RC_EPS)
			return true;
		return false;
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
			
			/*int k=0;
			while(k<totalQCR) {
				if(qcrMap.get(k).type.equals("MIN")){
					Constraint[k] = rmpCplex.addGe(expr[k], qcrMap.get(k).cardinality);
					k++;
				}
				else if(qcrMap.get(k).type.equals("MAX")){
					Constraint[k] = rmpCplex.addLe(expr[k], qcrMap.get(k).cardinality);	
					k++;
				}
				else{
					Constraint[k] = rmpCplex.addEq(expr[k], qcrMap.get(k).cardinality);
					k++;
				}
			}
			for (int i = 0; i < totalNominals; i++) {
				Constraint[k] = rmpCplex.addGe(expr[k], 1);
				k++;
			}*/
			System.out.println("total var : "+totalVar);
			System.out.println("qcrmap size : "+qcrMap.size());
			for (int i = 0; i < totalVar; i++) {
				if(qcrMap.get(i).type.equals("MIN")){
					Constraint[i] = rmpCplex.addGe(expr[i], qcrMap.get(i).cardinality);
				}
				else if(qcrMap.get(i).type.equals("MAX")){
					Constraint[i] = rmpCplex.addLe(expr[i], qcrMap.get(i).cardinality);	
				}
				else{
					Constraint[i] = rmpCplex.addEq(expr[i], qcrMap.get(i).cardinality);	
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
		IloNumVar[] sr ;
		IloNumVar[] hr ;
		
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
		public IloNumVar[] getHR() {
			return hr;
		}
		public IloNumVar[] getSR() {
			return sr;
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
			
			Map<OWLObjectProperty, Set<OWLClassExpression>> forAllMaps = 
					(Map<OWLObjectProperty, Set<OWLClassExpression>>) (Map<?, ?>) forAllMap.asMap();
			
				
			ppCplex = new IloCplex();
			ppCplex.setOut(new NullOutputStream());

			reducedCost = ppCplex.addMinimize();
			r = ppCplex.numVarArray(totalVar, 0., 1, IloNumVarType.Int);
			b = ppCplex.numVarArray(allQualifiers.size(), 0., 1, IloNumVarType.Int);
			//if(otherRoles.size()!=0)
			sr = ppCplex.boolVarArray(srRoles.size());//numVarArray(otherRoles.size(), 0., 1, IloNumVarType.Int);
			hr = ppCplex.boolVarArray(tempRoleH.size());//numVarArray(tempRoleH.size(), 0., 1, IloNumVarType.Int);
			
			// In at-least restrictions: if r[i]==1 --> b[i.qualifier]=1
			// In at-most restrictions: if b[i.qualifier]==1 --> a[i]=1
			
			
			SetMultimap<OWLObjectProperty, Integer> axiomRolesMap = HashMultimap.create();
			
			for (int i = 0; i < totalVar; i++ ) {
				if(qcrMap.get(i).role!=null) {
					axiomRolesMap.put(qcrMap.get(i).role.getNamedProperty(), i);
					if(tempRoleH.containsKey(qcrMap.get(i).role.getNamedProperty()))
						ppCplex.addLe(r[i] , hr[tempRoleHMap.get(tempRoleH.get(qcrMap.get(i).role.getNamedProperty()))]);
					//ppCplex.addLe(ppCplex.diff(r[i], hr[tempRoleHMap.get(tempRoleH.get(qcrMap.get(i).role.getNamedProperty()))]), 0);
					//System.out.println("r["+i+"]: role "+"hr["+tempRoleHMap.get(tempRoleH.get(qcrMap.get(i).role.getNamedProperty()))+"] "+ tempRoleH.get(qcrMap.get(i).role.getNamedProperty()));
				}
				if(qcrMap.get(i).type.equals("MIN"))
					ppCplex.addLe(r[i] , b[qualifiers.get(qcrMap.get(i).qualifier)]);
				else if (qcrMap.get(i).type.equals("MAX"))
					ppCplex.addLe(b[qualifiers.get(qcrMap.get(i).qualifier)] , r[i]);
				else {
					ppCplex.addLe(r[i] , b[qualifiers.get(qcrMap.get(i).qualifier)]);
					ppCplex.addLe(b[qualifiers.get(qcrMap.get(i).qualifier)] , r[i]);
				}
			}
			//for(IloNumVar v : hr)
			//	ppCplex.add(v);
			//disjoint
			/*ppCplex.addLe(ppCplex.sum(ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(0).qualifier)]),
					ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(1).qualifier)])), 1);*/
			//subsumption

			// this can work for top
		/*	Map<OWLObjectProperty, Set<Integer>> axiomRolesMaps = 
					(Map<OWLObjectProperty, Set<Integer>>) (Map<?, ?>) axiomRolesMap.asMap();
			for (OWLObjectProperty role : superRoles.keySet()){
				if(superRoles.get(role) != null){
					OWLObjectProperty tempSupRole = tempRoleH.get(role);
					for(OWLObjectProperty supRole : superRoles.get(role)){
						if(axiomRoles.contains(supRole)) {
							for(int i : axiomRolesMaps.get(supRole))
								ppCplex.addLe(hr[tempRoleHMap.get(tempSupRole)], r[i]);
						}
						else
							ppCplex.addLe(hr[tempRoleHMap.get(tempSupRole)], sr[otherRolesMap.get(supRole)]);
					}
				}
			}*/
			
			
			
			
			// Role Hierarchy
			for (OWLObjectProperty role : superRoles.keySet()){
				if(superRoles.get(role) != null){
					OWLObjectProperty tempSupRole = tempRoleH.get(role);
					for(OWLObjectProperty supRole : superRoles.get(role)){
						System.out.println("role : "+role+" H role "+tempSupRole+" sup role " +supRole);
						System.out.println("hr["+tempRoleHMap.get(tempSupRole)+"] <= "+ "sr["+srRolesMap.get(supRole)+"]");
						if(axiomRoles.contains(supRole)) {
							System.out.println("hr["+tempRoleHMap.get(tempSupRole)+"] <= "+ "hr["+tempRoleHMap.get(tempRoleH.get(supRole))+"]");
							ppCplex.addLe(hr[tempRoleHMap.get(tempSupRole)], hr[tempRoleHMap.get(tempRoleH.get(supRole))]);
							
						}
						ppCplex.addLe(hr[tempRoleHMap.get(tempSupRole)], sr[srRolesMap.get(supRole)]);
						
					}
				}
			}
			
			/*for (OWLObjectProperty role : superRoles.keySet()){
				if(superRoles.get(role) != null){
					OWLObjectProperty tempSupRole = tempRoleH.get(role);
					for(OWLObjectProperty supRole : superRoles.get(role)){
						System.out.println("role : "+role+" H role "+tempSupRole+" sup role " +supRole);
						if(axiomRoles.contains(supRole)) {
							System.out.println("hr["+tempRoleHMap.get(tempSupRole)+"] <= "+ "hr["+tempRoleHMap.get(tempRoleH.get(supRole))+"]");
							ppCplex.addLe(hr[tempRoleHMap.get(tempSupRole)], hr[tempRoleHMap.get(tempRoleH.get(supRole))]);
							
						}
						else {
							System.out.println("hr["+tempRoleHMap.get(tempSupRole)+"] <= "+ "sr["+otherRolesMap.get(supRole)+"]");
							
							ppCplex.addLe(hr[tempRoleHMap.get(tempSupRole)], sr[otherRolesMap.get(supRole)]);
						}
					}
				}
			}*/
			
			/*
			for (OWLObjectProperty role : superRoles.keySet()){
				if(superRoles.get(role) != null){
					OWLObjectProperty tempSupRole = null;
					boolean hasHelperRole = false;
					if(tempRoleH.containsKey(role)) {
						hasHelperRole = true;
						tempSupRole = tempRoleH.get(role);
					}
					for(OWLObjectProperty supRole : superRoles.get(role)){
						//System.out.println("role : "+role+" H role "+tempSupRole+" sup role " +supRole);
						if(axiomRoles.contains(supRole)) {
							if(hasHelperRole) {
								//System.out.println("hr["+tempRoleHMap.get(tempSupRole)+"] <= "+ "hr["+tempRoleHMap.get(tempRoleH.get(supRole))+"]");
								if(tempRoleH.containsKey(supRole))
									ppCplex.addLe(hr[tempRoleHMap.get(tempSupRole)], hr[tempRoleHMap.get(tempRoleH.get(supRole))]);
								else
									ppCplex.addLe(hr[tempRoleHMap.get(tempSupRole)], hr[tempRoleHMap.get(tempRoleH.get(supRole))]);
							}
							else
								ppCplex.addLe(r[axiomRolesMap.get(role)], sr[axiomRolesMap.get(supRole)])
						}
						else {
							System.out.println("hr["+tempRoleHMap.get(tempSupRole)+"] <= "+ "sr["+otherRolesMap.get(supRole)+"]");
							
							ppCplex.addLe(hr[tempRoleHMap.get(tempSupRole)], sr[otherRolesMap.get(supRole)]);
						}
					
					}
				}
			}*/
			
			
			
			//For All Restrictions -- Semantics 
			/*for (OWLObjectProperty role : forAllMaps.keySet()){
				if(forAllMaps.get(role) != null){
					for(OWLClassExpression C : forAllMaps.get(role))
						ppCplex.addLe(sr[srRolesMap.get(role)], b[qualifiers.get(C)]);
					
				}
			}*/
			
			for (OWLObjectProperty role : forAllMaps.keySet()){
				if(forAllMaps.get(role) != null){
					if(axiomRoles.contains(role)) {
						OWLObjectProperty tempSupRole = tempRoleH.get(role);
						System.out.println("role : "+role+" H role "+tempSupRole);
						
						for(OWLClassExpression C : forAllMaps.get(role)) {
							ppCplex.addLe(hr[tempRoleHMap.get(tempSupRole)], b[qualifiers.get(C)]);
							if(srRolesMap.get(role)!=null)
								ppCplex.addLe(sr[srRolesMap.get(role)], b[qualifiers.get(C)]);
						}
					}
					else {
						System.out.println("role : "+role);
						
						for(OWLClassExpression C : forAllMaps.get(role))
							ppCplex.addLe(sr[srRolesMap.get(role)], b[qualifiers.get(C)]);
					}
				}
			}
			
			
			
		/*	for (OWLObjectProperty role : forAllMaps.keySet()){
				if(forAllMaps.get(role) != null){
					OWLObjectProperty tempSupRole = tempRoleH.get(role);
					for(OWLClassExpression C : forAllMaps.get(role)){
						if(axiomRoles.contains(role))
							ppCplex.addLe(hr[tempRoleHMap.get(tempSupRole)], b[qualifiers.get(C)]);
						else 
							ppCplex.addLe(sr[otherRolesMap.get(role)], b[qualifiers.get(C)]);
					}
				}
			}*/
			
			
			///
			//ppCplex.addLe(b[qualifiers.get(qcrMap.get(0).qualifier)],b[qualifiers.get(qcrMap.get(3).qualifier)]);
			
		/*	ppCplex.addLe(b[qualifiers.get(qcrMap.get(1).qualifier)],b[qualifiers.get(qcrMap.get(6).qualifier)]);
			ppCplex.addLe(b[qualifiers.get(qcrMap.get(2).qualifier)],b[qualifiers.get(qcrMap.get(6).qualifier)]);
			ppCplex.addLe(b[qualifiers.get(qcrMap.get(3).qualifier)],b[qualifiers.get(qcrMap.get(6).qualifier)]);
			ppCplex.addLe(b[qualifiers.get(qcrMap.get(4).qualifier)],b[qualifiers.get(qcrMap.get(6).qualifier)]);
			ppCplex.addLe(b[qualifiers.get(qcrMap.get(5).qualifier)],b[qualifiers.get(qcrMap.get(6).qualifier)]);
			
			ppCplex.addLe(ppCplex.sum(ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(0).qualifier)]),
					ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(1).qualifier)]),
					ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(3).qualifier)])), 2);
			
			ppCplex.addLe(ppCplex.sum(ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(0).qualifier)]),
					ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(2).qualifier)]),
					ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(4).qualifier)])), 2);
			
			ppCplex.addLe(ppCplex.sum(ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(3).qualifier)]),
					ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(4).qualifier)]),
					ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(5).qualifier)])), 2);
			
			ppCplex.addLe(ppCplex.sum(ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(0).qualifier)]),
					ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(5).qualifier)])), 1);
			
			ppCplex.addLe(ppCplex.sum(ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(1).qualifier)]),
					ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(4).qualifier)])), 1);*/
			
			ppCplex.addLe(ppCplex.sum(ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(1).qualifier)]),
					ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(3).qualifier)])), 1);
			
			return this;
		}
	}
}

