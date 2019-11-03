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


import org.semanticweb.owlapi.model.*;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import com.google.common.collect.SetMultimap;

import ilog.concert.*;
import ilog.cplex.*;
import reasoner.Dependencies.DependencySet;
import reasoner.ilp.CplexModelGenerator.IloNumVarArray;


public class CplexModelGenerator10 {
	//IloCplex cplexModel;
	ILPPreprocessor ilpPro;
	List<OWLObjectCardinalityRestriction> qcrList = new ArrayList<>();
	Set<QCR> qcrs = new HashSet<>();
	Set<OWLObjectOneOf> nominals = new HashSet<>();
	Set<OWLClassExpression> qcrQualifiers =  new HashSet<>();
	Set<OWLClassExpression> allQualifiers = new HashSet<>();
	Map<Integer, QCR> qcrMap = new HashMap<>();
	Map<Integer, OWLObjectCardinalityRestriction> crMap = new HashMap<>();
	Set<OWLObjectPropertyExpression> axiomRoles = new HashSet<>();
	Set<OWLObjectPropertyExpression> srRoles = new HashSet<>();
	Map<OWLClassExpression, Set<OWLClassExpression>> conceptSubsumersMap = new HashMap<>();
	Map<OWLClassExpression, Set<OWLClassExpression>> binarySubsumersMap = new HashMap<>();
	SetMultimap<OWLClassExpression, OWLClassExpression> conceptDisjoints = HashMultimap.create();
	Map<OWLClassExpression, OWLClassExpression> negations = new HashMap<>();
	BiMap<OWLClassExpression, Integer> qualifiers = HashBiMap.create();
	BiMap<OWLObjectPropertyExpression, Integer> srRolesMap = HashBiMap.create();
	Set<Set<OWLClassExpression>> disjointGroups = new HashSet<>();
	BiMap<OWLObjectPropertyExpression, Integer> tempRoleHMap = HashBiMap.create();
	Map<OWLObjectPropertyExpression, OWLClassExpression> topMinMap; 
	Map<OWLObjectPropertyExpression, OWLClassExpression> topMaxMap;
	Set<OWLObjectCardinalityRestriction> infeasibilities = new HashSet<>();
	Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> superRoles = new HashMap<>();
	SetMultimap<OWLObjectPropertyExpression, OWLClassExpression> forAllMap;

	Map<OWLObjectPropertyExpression, OWLObjectPropertyExpression> tempRoleH = new HashMap<>();
	IloRange[]   orgConstraint = null;
	IloNumVar[] orgR = null;
	
	boolean initiallySolved;
	int M;
	int totalQCR = 0;
	int totalNominals = 0;
	int totalVar = 0;
	static double RC_EPS = 1.0e-6d;
	
	public CplexModelGenerator10(ILPPreprocessor ilpPr, 
			Map<OWLClassExpression, Set<OWLClassExpression>> conceptSubsumersMap,
			Map<OWLClassExpression, Set<OWLClassExpression>> binarySubsumers, 
			SetMultimap<OWLClassExpression, OWLClassExpression> conceptDisjoints,
			Set<Set<OWLClassExpression>> disjointGroups,
			Map<OWLObjectPropertyExpression, Set<OWLObjectPropertyExpression>> sRMap,
			SetMultimap<OWLObjectPropertyExpression, OWLClassExpression> forAllMap2, 
			Map<OWLObjectPropertyExpression, OWLObjectPropertyExpression> tempRoleH2, 
			Map<OWLObjectPropertyExpression, OWLClassExpression> topMinMap, 
			Map<OWLObjectPropertyExpression, OWLClassExpression> topMaxMap) {
		
		ilpPro = ilpPr;
		qcrs = ilpPro.getQcrs();
		qcrQualifiers = qcrs.stream().map(qcr -> qcr.qualifier).collect(Collectors.toSet());
		qcrMap  = ilpPro.getQCRMap();
		crMap = ilpPro.getCRMap();
		qcrList = ilpPro.getCardRes();
		
		generateCplexModel();
		//System.out.println(" solved "+initiallySolved);
		if(initiallySolved) {
			
			this.disjointGroups = disjointGroups;
			this.conceptSubsumersMap = new HashMap<>(conceptSubsumersMap);
			this.binarySubsumersMap = new HashMap<>(binarySubsumers);
			
			this.topMinMap = new HashMap<>(topMinMap);
			this.topMaxMap = new HashMap<>(topMaxMap);
		//	System.out.println(" map "+topMaxMap);
			
			this.conceptDisjoints = HashMultimap.create();
			for(Entry<OWLClassExpression, OWLClassExpression> e : conceptDisjoints.entries()){
				//System.out.println("conceptDisjoints "+ e.getKey()+ e.getValue());
				this.conceptDisjoints.put(e.getKey(), e.getValue());
			}
			//System.out.println("conceptDisjoints "+ conceptDisjoints.size());
			this.superRoles =  sRMap;
			this.tempRoleH = tempRoleH2;
			
			nominals = new HashSet<OWLObjectOneOf>(ilpPro.getNominals());
			allQualifiers = new HashSet<OWLClassExpression>(qcrQualifiers);
			if(conceptSubsumersMap.keySet() != null){
				this.allQualifiers.addAll(conceptSubsumersMap.keySet());
				for(OWLClassExpression C : conceptSubsumersMap.keySet()){
					Set<OWLClassExpression> temp = new HashSet<>();
					conceptSubsumersMap.get(C).stream().filter(ce -> (ce instanceof OWLClass) || (ce instanceof OWLObjectOneOf) || (ce instanceof OWLObjectComplementOf)).forEach(ce -> temp.add(ce));
					conceptSubsumersMap.get(C).stream().filter(ce -> (ce instanceof OWLObjectUnionOf)).forEach(ce -> temp.addAll(ce.asDisjunctSet()));
				//	System.out.println("temp size "+temp.size()); 
					this.allQualifiers.addAll(temp);
					
				}
			}
			
			if(binarySubsumers.keySet() != null){
				for(OWLClassExpression C : binarySubsumers.keySet()){
					this.allQualifiers.addAll(binarySubsumers.get(C));
				}
			}
			
			if(conceptDisjoints.keySet() != null){
				this.allQualifiers.addAll(conceptDisjoints.keySet());
				for(OWLClassExpression C : conceptDisjoints.keySet()){
					this.allQualifiers.addAll(conceptDisjoints.get(C));
				}
			}
		
			axiomRoles = qcrs.stream().filter(qcr -> qcr.role!=null).map(qcr -> qcr.role).collect(Collectors.toSet());
			
			for(OWLObjectPropertyExpression role : axiomRoles) {
				if(sRMap.get(role)!=null) {
					for(OWLObjectPropertyExpression supRole : sRMap.get(role)) {
						this.srRoles.add(supRole);
					}
				}
			}
			
			this.forAllMap = HashMultimap.create();
			for(Entry<OWLObjectPropertyExpression, OWLClassExpression> e : forAllMap2.entries()){
				this.forAllMap.put(e.getKey(), e.getValue());
				allQualifiers.add(e.getValue());
			}
			//System.out.println("allQualifiers size "+allQualifiers.size());
			//System.out.println("allQualifiers "+allQualifiers);
			Set<OWLClassExpression> neg = new HashSet<>();
			allQualifiers.stream().filter(c -> c instanceof OWLObjectComplementOf).forEach(c -> neg.add(c));
		//	System.err.println(""+ neg.size());
			if(!neg.isEmpty()) {
				for(OWLClassExpression n : neg) {
					if(allQualifiers.contains(n.getComplementNNF())) {
						this.negations.put(n, n.getComplementNNF());
					}
				}
			}
			
			
			int tempQN = 0;
			for(OWLClassExpression C : allQualifiers){
				qualifiers.put(C, tempQN);
				++tempQN;
			}
			int tempRN = 0;
			for(OWLObjectPropertyExpression r : srRoles){
				srRolesMap.put(r, tempRN);
				++tempRN;
			}
			int tempRHN = 0;
			for(Entry<OWLObjectPropertyExpression, OWLObjectPropertyExpression> e : tempRoleH2.entrySet()){
				tempRoleHMap.put(e.getValue(), tempRHN);
				++tempRHN;
			}
			totalQCR = qcrs.size();
			totalNominals = nominals.size();
			totalVar = totalQCR;//+totalNominals;
			M = 1000*totalVar;
			//System.out.println("M value "+M);
		}
		/*try {
			cplexModel= new IloCplex();
		} catch (IloException e) {
			e.printStackTrace();
		}*/
	}
	
	public ILPSolution getILPSolution() throws IloException {
		return solve();
		/*ILPSolution sol = checkFeasibility();
		if(sol == null) {
			CplexModelSolver cms = new CplexModelSolver(new RMPModel().generateRmpModel(), new PPModel().GeneratePpModel(), this.totalVar);
			Result rs =  cms.solve();
			if (rs.subsets!=null)
			return solve(rs.rmpCplex,  rs.subsets);
			else{
					return infeasible(rs.getRmpCplex(), rs.getPpCplex());
				}
		}
		else 
			return sol;*/
		
	}
	

	/*private ILPSolution checkFeasibility() {
		ILPSolution returnSolution = new ILPSolution();
		
		if(!initiallySolved){
			returnSolution.setInfeasible_set(infeasibilities);
			returnSolution.setSolved(false);
			return returnSolution;
		}
		return null;
	}*/

	public void generateCplexModel() {
		
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
	
	
	/*public IloCplex getCplexModel() {
		return this.cplexModel;
	}*/
	
	//public ILPSolution solve(RMPModel rmpModel, PPModel ppModel) throws IloException{
	public ILPSolution solve() throws IloException{
		//int M = 100;
		ILPSolution returnSolution = new ILPSolution();
		
		if(!initiallySolved){
			returnSolution.setInfeasible_set(infeasibilities);
			returnSolution.setSolved(false);
			return returnSolution;
		}
		RMPModel rmpModel = new RMPModel().generateRmpModel();
		PPModel ppModel = new PPModel().GeneratePpModel();
		
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
		IloNumVar[] b = ppModel.getB();
		
		System.out.println("solving...");

		/// Generating new columns ///

				double[] newCol = new double[totalVar];

				double relaxed_opt;
				while (true) {
					
					boolean isRMPFeasible = false;
					if(rmpCplex.solve()){
						isRMPFeasible = true;
						relaxed_opt = rmpCplex.getObjValue();
					//	System.out.println("relaxed_opt "+relaxed_opt);
				//	for(int j=0; j<x.getSize(); j++)
				//		System.out.println("x value  "+rmpCplex.getValue(x.getElement(j)));
					
					
					/// generate and add a new column in RMP
						
					double[] price = rmpCplex.getDuals(Constraint);
					
				//	for(int j = 0 ; j < price.length ; j++)
				//		System.out.println("dual value  "+price[j]);
					
					IloLinearNumExpr objExpr = ppCplex.linearNumExpr();
					for(int j = 0 ; j < b.length ; j++)
						objExpr.addTerm(1 , b[j]);
					
					// FIXME changed Sep 23, 2019
					
				//	System.err.println(ppCplex.prod(1.0/2,ppCplex.square(ppCplex.prod(2.0, objExpr))));
				//	reducedCost.setExpr(ppCplex.diff(ppCplex.prod(1.0/2,ppCplex.square(ppCplex.prod(2.0, objExpr))),ppCplex.scalProd(r, price)));
					reducedCost.setExpr(ppCplex.diff(ppCplex.square(objExpr),ppCplex.scalProd(r, price)));
				//	reducedCost.setExpr(ppCplex.diff(ppCplex.prod(objExpr, objExpr),ppCplex.scalProd(r, price)));
				//	reducedCost.setExpr(ppCplex.diff(objExpr,ppCplex.scalProd(r, price)));

					if(ppCplex.solve()){
					//	System.err.println(ppCplex.getObjValue());
						if ( ppCplex.getObjValue() > -RC_EPS ){
							break;
						}

						newCol = ppCplex.getValues(r);
						
						double[] bVal = ppCplex.getValues(b);
						
						int cost = 0;
					/*	double[] rv = ppCplex.getValues(r);
						System.out.println("------");
						for(int j = 0 ; j < rv.length ; j++) {
							System.out.println("r v  ["+j +"]"+ rv[j]);
							
						}*/
						
						
					//	double[] srv = ppCplex.getValues(sr);
						
					//	for(int j = 0 ; j < srv.length ; j++) {
					//		System.out.println("sr v ["+j +"]"+ srv[j]);
							
					//	}
						for(int j = 0 ; j < bVal.length ; j++) {
							//System.out.println("bVal " + bVal[j]);
							cost += bVal[j];
						}
						/*if(cost>5) {
							cost += cost-1;
						}*/
							
					//	System.err.println("cost " + cost + " square "+cost*cost);
						IloColumn column = rmpCplex.column(obj, cost*cost);//Creates and returns a column from the specified objective and value.
						for ( int i = 0; i < totalVar; i++ )
							column = column.and(rmpCplex.column(Constraint[i], newCol[i]));//Creates and returns a column from the specified range and value.
						
						x.add( rmpCplex.numVar(column, 0., Double.MAX_VALUE) );
						subsets.add(new SubSet(ppCplex.getValues(r) , ppCplex.getValues(b), ppCplex.getValues(sr)));
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
		//	System.out.println("final relaxed_opt " + relaxed_opt);
			if( relaxed_opt < M ){
				
				//System.out.println("x.getSize() " + x.getSize());
				
				
				
				boolean nonInteger = false;
				for ( int i = 0; i < x.getSize(); i++ ) {
					double cardinality = rmpCplex.getValue(x.getElement(i));
				//	System.out.println("x"+i +": "+cardinality+ " rounded: " + Math.round(cardinality * 100000D) / 100000D);
					if(!isInteger(Math.round(cardinality * 100000D) / 100000D)) {
						nonInteger = true;
						break;
					}
				}
				
				 double sumh = 0.0D;
			       
				
				for(int l = 0; l < h.getSize(); l++){
					sumh +=  rmpCplex.getValue(h.getElement(l));
						
				}
				sumh =  Math.round(sumh * 100000D) / 100000D;
				//System.out.println("non zero cardinality " + sumh+ " rounded: " + Math.round(sumh * 100000D) / 100000D);
				if(nonInteger) {
					System.out.println("non integer cardinality! trying for integer solution ");
				/*	for ( int i = 0; i < x.getSize(); i++ ) {
						rmpCplex.add(rmpCplex.conversion(x.getElement(i),IloNumVarType.Int));//Adds object to the invoking model.
												//Converts a numeric variable to a specified type.
					}*/
					
					orgConstraint = Arrays.copyOf(rmpModel.Constraint, rmpModel.Constraint.length);
					orgR = ppCplex.numVarArray(r.length, 0., 1, IloNumVarType.Int);
					System.arraycopy(r, 0, orgR, 0, r.length);
				//	System.out.println("constraint size " + orgConstraint.length);
					
					returnSolution = applyBranchAndPrice(rmpModel, ppModel, rmpCplex, ppCplex, x, h,subsets, b, r, sr, rmpModel.Constraint);
					rmpCplex.end();
					ppCplex.end();
					
					return returnSolution;
					
					/////
					///
					
					/*while(true) {
						
					}*/
					
					
					////
				}
				else {
					for ( int i = 0; i < x.getSize(); i++ ) 
						rmpCplex.add(x.getElement(i));
				}
				for ( int i = 0; i < h.getSize(); i++ ) {
					rmpCplex.add(rmpCplex.conversion(h.getElement(i),IloNumVarType.Int));
				}
				
			/*	for ( int i = 0; i < x.getSize(); i++ ) {
					/// LP relaxation 
					//System.out.println("cardinality " + rmpCplex.getValue(x.getElement(i)));
					rmpCplex.add(rmpCplex.conversion(x.getElement(i),IloNumVarType.Int));//Adds object to the invoking model.
											//Converts a numeric variable to a specified type.
					


				}*/
				

				boolean result = false;     
				if(rmpCplex.solve()){
					result = true;
					Set<EdgeInformation> edgeInformationSet = new HashSet<EdgeInformation>();
					
					if( rmpCplex.getObjValue() < M){
						//System.out.println("rmpCplex.getObjValue() " + rmpCplex.getObjValue());
						for(int i = 0; i < h.getSize(); i++){
							double cardinality = rmpCplex.getValue(h.getElement(i));
							//System.out.println("cardinality " + cardinality);
							cardinality = Math.round(sumh * 100000D) / 100000D;
							if(cardinality > 0){
								System.out.println("non zero cardinality " + cardinality);
							}
						}
						
						BiMap<Integer, OWLClassExpression> reverseQualifiers = qualifiers.inverse();
						BiMap<Integer, OWLObjectPropertyExpression> reverseRoles = srRolesMap.inverse();
						BiMap<Integer, OWLObjectPropertyExpression> reverseTempRoles = tempRoleHMap.inverse();
						Map<OWLObjectPropertyExpression, OWLObjectPropertyExpression> reverseTempRoleH = new HashMap<>();
						for(Entry<OWLObjectPropertyExpression, OWLObjectPropertyExpression> e : tempRoleH.entrySet()){
							reverseTempRoleH.put(e.getValue(), e.getKey());
						}
						//System.out.println("x.getSize() ---" + x.getSize());
						
						
						for(int i = 0; i < x.getSize(); i++){
							double cardinality = rmpCplex.getValue(x.getElement(i));
							if(!isInteger(Math.round(cardinality * 100000D) / 100000D)) {
								System.out.println("non integer cardinality " + Math.round(cardinality * 100000D) / 100000D);
							}
							else {
							//	System.out.println("x cardinality " + cardinality);
								if((Math.round(cardinality * 100000D) / 100000D) > 0.0){
									//System.out.println("i value " + i);
									
									SubSet tempSubSet = subsets.get(i);
									
									Set<OWLObjectPropertyExpression> tempRoleSet = new HashSet<>();
									Set<OWLObjectPropertyExpression> tempSupRoleSet = new HashSet<>();
									Set<OWLClassExpression> tempClassSet = new HashSet<>();
									Set<Integer> nodeSet = new HashSet<>();
										
									boolean addIt = false;
										
									for(int j = 0 ; j < tempSubSet.getConceptIndexSet().length ; j++){
										if(tempSubSet.getConceptIndexSet()[j] > 0){ // if b value is 1
											tempClassSet.add(reverseQualifiers.get(j));
											if(!addIt)
												addIt = true;
											}
									}
								//	System.out.println("tempClassSet "+tempClassSet.size());
									Set<OWLClassExpression> temp = new HashSet<>();
									temp.addAll(tempClassSet);
									for(OWLClassExpression ce : temp) {
										if(ilpPro.getAuxiliaryConcepts().contains(ce))
											tempClassSet.addAll(ilpPro.getComplexASubsumers(ce));
										if(ilpPro.getNodeIdMap().containsKey(ce))
											nodeSet.add(ilpPro.getNodeIdMap().get(ce));
									}
									tempClassSet.removeAll(ilpPro.getAuxiliaryConcepts());
									if(addIt){
										DependencySet ds = DependencySet.create();
											for(int j = 0 ; j < tempSubSet.getRolesIndexSet().length ; j++){
												if(tempSubSet.getRolesIndexSet()[j] > 0) { // if r value is 1
													//System.out.println(" role "+qcrMap.get(j).role);
													if(qcrMap.get(j).role!=null) {
														tempRoleSet.add(qcrMap.get(j).role);
														ds.add(qcrMap.get(j).ds);
													}
												}
											}
											
											for(int j = 0 ; j < tempSubSet.getSupRolesIndexSet().length ; j++){
												if(tempSubSet.getSupRolesIndexSet()[j] > 0) { // if sr value is 1
													//System.out.println("sr["+j+"]: "+tempSubSet.getSupRolesIndexSet()[j]);
													//System.out.println("sup role "+reverseRoles.get(j) );
													
													tempSupRoleSet.add(reverseRoles.get(j));
												}
											}
											tempRoleSet.addAll(tempSupRoleSet);
											
											Set<OWLObjectPropertyExpression> temp2 = new HashSet<>();
											temp2.addAll(tempRoleSet);
											for(OWLObjectPropertyExpression rr : temp2) {
												if(ilpPro.getAuxiliaryRoles().contains(rr))
													tempRoleSet.addAll(ilpPro.getAuxRoleHMap(rr));
											}
											tempRoleSet.removeAll(ilpPro.getAuxiliaryRoles());
											
											if(!tempRoleSet.isEmpty()) {
												EdgeInformation tempEdgeInformation = new EdgeInformation(tempRoleSet , tempClassSet , cardinality, ds, nodeSet);
												edgeInformationSet.add(tempEdgeInformation);
											}
										}
									
								}
							}
						}
						
						// Adding complement to ensure at most restrictions
						/*Set<QCR> tempMaxQcrs = qcrMap.values().stream().filter(qcr -> qcr.type.equals("MAX")).collect(Collectors.toSet());
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
								if(e.getEdges().contains(q.role) && e.getFillers().contains(q.qualifier)){
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
									if(e.getEdges().contains(q.role) && !e.getFillers().contains(q.qualifier)){
										if(e.getCardinality() > check_complement.get(q)){
											EdgeInformation tempEdgeInformation = new EdgeInformation(tempObj , tempSet , card - check_complement.get(q), e.getDs());
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
						}*/
						///////////////////////////////////// at-most restriction end
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
							EdgeInformation tempEdgeInformation = new EdgeInformation(e.getEdges(), fillers, edge_map.get(e), e.getDs(), e.getNodeSet());
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
				List<Integer> remove = new  ArrayList<>();
				for(int i = 0; i < totalVar; i++){
					if(rmpCplex.getValue(h.getElement(i)) > 0.1){
						infeasible_set.add(crMap.get(i));
						///
						remove.add(i);
					}
				}
				for(int i = 0; i < remove.size(); i++){
					// if it is back edge inequality
					if(ilpPro.getNodeIdMap().containsKey(crMap.get(remove.get(i)).getFiller())) {
						rmpCplex.remove(Constraint[remove.get(i)]);
						if(rmpCplex.solve()) {
							return runILPAgain(crMap.get(remove.get(i)));
							
						}
					}
					
					
				}
			//	System.err.println("solved? "+ rmpCplex.solve() + rmpCplex.getObjValue() );
				
				////
				
				//// 25-oct-2k19
				/*
				double[] infeas = rmpCplex.getInfeasibilities(Constraint);
				double[] infeas2 = ppCplex.getInfeasibilities(b);
				double[] infeas3 = ppCplex.getInfeasibilities(r);
				System.err.println(infeas2.length);
				for(int  i = 0; i < infeas.length; i++) {
					System.err.println(infeas[i]);
					if(infeas[i]!=0)
					
					System.err.println(qcrMap.get(Constraint[i]).qualifier);
				}*/
				////
				rmpCplex.end();
				ppCplex.end();
				returnSolution.setSolved(false);
				returnSolution.setInfeasible_set(infeasible_set);
				return returnSolution;
			}
		}
	
	private ILPSolution runILPAgain(OWLObjectCardinalityRestriction owlObjectCardinalityRestriction) throws IloException {
		System.out.println(conceptSubsumersMap.remove(owlObjectCardinalityRestriction.getFiller()));
		return this.solve();
	}

	/**
	 * @param rmpModel
	 * @param ppModel
	 * @param rmpCplex
	 * @param ppCplex
	 * @param x1
	 * @param h1
	 * @param subsets1
	 * @param b
	 * @param r1
	 * @param sr
	 * @param Constraint1
	 * @param expr2
	 * @return
	 * @throws IloException
	 */
	private ILPSolution applyBranchAndPrice( RMPModel rmpModel, PPModel ppModel, IloCplex rmpCplex, IloCplex ppCplex, IloNumVarArray x1, IloNumVarArray h1,
			ArrayList<SubSet> subsets1, IloNumVar[] b, IloNumVar[] r1, IloNumVar[] sr, IloRange[] Constraint1) throws IloException {
		
		ILPSolution returnSolution = new ILPSolution();
		IloNumVarArray x = new IloNumVarArray(x1);
		IloNumVarArray h = new IloNumVarArray(h1);
		ArrayList<SubSet> subsets = new ArrayList<SubSet>(subsets1);
	//	int size = x.getSize();
	//	System.out.println("x size :"+ size);
	//	System.out.println("start :"+ start);
		
		
		for ( int i = 0; i < x.getSize(); i++ ) {
		//for ( int i = start+1; i < subsets.size(); i++ ) {
			
		//	System.out.println("i : "+i);
		//	System.out.println("obj : "+rmpCplex.getObjValue());
		//	rmpCplex.solve();
		//	double cardinality = rmpCplex.getValue(x.getElement(i));
			double cardinality = Math.round(rmpCplex.getValue(x.getElement(i))* 100000D) / 100000D;
			System.out.println("cardinality second :"+ cardinality);
			
			if(!isInteger(cardinality)) {
			
				
			//  System.out.println("Trying value number "+ i);			
			// subsets = new ArrayList<SubSet>(subsets1);
			
				
				double fractional = cardinality % 1;
				double part1 = cardinality - fractional;
				double part2 = part1 + 1;
			//	System.out.println("i "+i+" subset size"+subsets.size()+" x size"+ x.getSize());
				
				/*if(i>=subsets.size()) {
					System.out.println("i "+i+" subset size"+subsets.size());
					break;
				}*/
				SubSet tempSubSet = subsets.get(i);
				
				
				// try both branches
				boolean infeasible = false;
				for(int k = 0; k < 2; k++) {
					
					IloRange[] Constraint =  Arrays.copyOf(Constraint1, Constraint1.length+1);
					IloConstraint[]  ppNewCons = null;
				//	System.out.println("constraint size " + Constraint.length);
				
					
					
					IloNumVar[] r = ppCplex.numVarArray(r1.length+1, 0., 1, IloNumVarType.Int);
					
					System.arraycopy(r1, 0, r, 0, r1.length);
					
						
					IloObjective obj = rmpCplex.getObjective();
					IloObjective reducedCost = ppCplex.getObjective();
					Set<Integer> bvalues = new HashSet<>();
					infeasible = false;
					
				
					if(k == 0) {
						System.out.println("1 Trying part "+ (k+1) + " inequality "+ part2);
					//	Constraint[totalVar] =  rmpCp.addGe(expr[totalVar], part2);
						Constraint[Constraint1.length] =  rmpCplex.addGe(x.getElement(i), part2);
					//	Constraint[totalVar] =  rmpCplex.addGe(xv, part2);
						// check which b values are 1
						for(int j = 0 ; j < tempSubSet.getConceptIndexSet().length ; j++){
							if(tempSubSet.getConceptIndexSet()[j] > 0){ // if b value is 1
							//System.out.println("bvalue "+ j );
								bvalues.add(j);
							}
						}
						
						// add constraint in PP
						IloLinearNumExpr nexpr = ppCplex.linearNumExpr();
						ppNewCons = new IloConstraint[bvalues.size()+1];
						int count = 0;
						for (Integer bv : bvalues){
							//System.out.println(bv);
							nexpr.addTerm(1, b[bv]);
							ppNewCons[count] = ppCplex.addLe(r[r1.length], b[bv]);
							count++;
						}
						ppNewCons[count] = ppCplex.addLe(ppCplex.diff(nexpr, bvalues.size() - 1), r[r1.length]);
					}
					else {
						System.out.println("1 Trying part "+ (k+1) + " inequality "+ part1);
						//Constraint[totalVar] =  rmpCp.addLe(expr[totalVar], part1);
						Constraint[Constraint1.length] =  rmpCplex.addLe(x.getElement(i), part1);
					//	Constraint[totalVar] =  rmpCplex.addLe(xv, part1);
						// check which b values are 1
						for(int j = 0 ; j < tempSubSet.getConceptIndexSet().length ; j++){
							if(tempSubSet.getConceptIndexSet()[j] > 0){ // if b value is 1
								bvalues.add(j);
							}
						}
						ppNewCons = new IloConstraint[bvalues.size()+1];
						int count = 0;
						// add constraint in PP
						IloLinearNumExpr nexpr = ppCplex.linearNumExpr();
						for (Integer bv : bvalues){
							//System.out.println(bv);
							//System.out.println(r[totalVar]);
							nexpr.addTerm(1, b[bv]);
							ppNewCons[count] = ppCplex.addLe(b[bv], r[r1.length]);
							count++;
						}
						ppNewCons[count] = ppCplex.addLe(ppCplex.diff(nexpr, bvalues.size() - 1), r[r1.length]);
					}
				
					
					double[] newCol = new double[totalVar+1];
				//	System.out.println("M value "+M);
					double relaxed_opt = M;
					while (true) {
						
						infeasible = false;
						boolean isRMPFeasible = false;
						if(rmpCplex.solve()){
							//System.out.println("feasible ");
							isRMPFeasible = true;
							relaxed_opt = rmpCplex.getObjValue();
						//System.out.println("relaxed opt inside "+relaxed_opt);
						/// generate and add a new column in RMP
						/*for ( int l = 0; l < x.getSize(); l++ ) {
							double card = rmpCplex.getValue(x.getElement(l));
							System.out.println("cardinality inside!  "+ card);
						}*/
							
						double[] price = rmpCplex.getDuals(Constraint);
						//System.out.println("dual value  # "+price.length);
						//for(int j = 0 ; j < price.length ; j++)
						//	System.out.println("dual value  bNp "+price[j]);
						
					/*	double[] price2 = rmpCp.getAX(Constraint);
						for(int j = 0 ; j < price2.length ; j++)
							System.out.println("AX value  bNp "+price2[j]);*/
						
						IloLinearNumExpr objExpr = ppCplex.linearNumExpr();
						for(int j = 0 ; j < b.length ; j++)
							objExpr.addTerm(1 , b[j]);
						//System.out.println("r value  # "+r.length);
						reducedCost.setExpr(ppCplex.diff(ppCplex.square(objExpr),ppCplex.scalProd(r, price)));
						//reducedCost.setExpr(ppCplex.diff(objExpr,ppCplex.scalProd(r, price)));
						
						if(ppCplex.solve()){
							//System.out.println("pp objective "+ppCplex.getObjValue());
							if ( ppCplex.getObjValue() > -RC_EPS ){
								//System.out.println("break" + -RC_EPS);
								break;
							}
	
							newCol = ppCplex.getValues(r);
							
							double[] bVal = ppCplex.getValues(b);
							
							int cost = 0;
							double[] rv = ppCplex.getValues(r);
						//	System.out.println("------");
						//	for(int j = 0 ; j < rv.length ; j++) {
						//		System.out.println("r v  ["+j +"]"+ rv[j]);
								
						//	}
							
							
						//	double[] srv = ppCp.getValues(sr);
							
						//	for(int j = 0 ; j < srv.length ; j++) {
						//		System.out.println("sr v ["+j +"]"+ srv[j]);
								
						//	}
							for(int j = 0 ; j < bVal.length ; j++) {
								//System.out.println("bVal " + bVal[j]);
								cost += bVal[j];
							}
							/*if(cost>5) {
								cost += cost-1;
							}*/
								
							//System.out.println("cost " + cost);
							IloColumn column = rmpCplex.column(obj, cost*cost);//Creates and returns a column from the specified objective and value.
							for ( int ii = 0; ii < Constraint.length; ii++ )
								column = column.and(rmpCplex.column(Constraint[ii], newCol[ii]));//Creates and returns a column from the specified range and value.
							
							x.add( rmpCplex.numVar(column, 0., Double.MAX_VALUE) );
							subsets.add(new SubSet(ppCplex.getValues(r) , ppCplex.getValues(b), ppCplex.getValues(sr)));
						//	System.out.println("x add "+ x.getSize()+" subset add "+ subsets.size());
							
						}
						else {
							infeasible = true;
							break;
						}
					}
					else{	
						//System.out.println("infeasible 1");
						infeasible = true;
						break;
					}
				  }
				
				if(!infeasible) {
					if( relaxed_opt < M ){
						//System.out.println("relaxed opt "+relaxed_opt);
						//System.out.println("x.getSize() " + x.getSize());
						
						boolean nonInteger = false;
						for ( int l = 0; l < x.getSize(); l++ ) {
							double card = rmpCplex.getValue(x.getElement(l));
						//	System.out.println("cardinality outside!  "+ card);
				//		if(!isInteger(Math.round(card * 100000D) / 100000D)) {
							if(!isInteger(card)) {
								nonInteger = true;
								break;
							}
						}
						for(int l = 0; l < h.getSize(); l++){
							double card = rmpCplex.getValue(h.getElement(l));
							card = Math.round(card * 100000D) / 100000D;
							if(card > 0){
								//System.out.println("non zero cardinality " + card+ " rounded: " + Math.round(card * 100000D) / 100000D);
								infeasible = true;
								break;
							}
						}
						
						if(infeasible) {
							
						}
					//	if(nonInteger) {
						if(nonInteger && !infeasible) {
							System.out.println("non integer cardinality! trying for integer solution ");
							//infeasible = true;
						//	System.out.println("before call : i "+i+" subset size"+subsets.size()+" x size"+ x.getSize());
							ILPSolution sol = applyBranchAndPrice2(-1, rmpModel, ppModel, rmpCplex, ppCplex, x, h, subsets, b, r, sr, Constraint);
							if(sol.solved)	
								return sol;
							else if(k == 1) {
								return sol;
							}
							else {
								for(int j = totalVar; j<Constraint.length; j++) {
									rmpCplex.remove(Constraint[j]);
								}
								rmpCplex.solve();
								Constraint1 = new IloRange[orgConstraint.length];
								Constraint1 =	Arrays.copyOf(orgConstraint, orgConstraint.length);
								ppCplex =  	new PPModel().GeneratePpModel().getPpCplex();
								r1 = ppCplex.numVarArray(orgR.length, 0., 1, IloNumVarType.Int);
								System.arraycopy(orgR, 0, r1, 0, orgR.length);
								//ppCplex.solve();
								continue;
							}
								
							
						}
						
						else {
							for ( int l = 0; l < x.getSize(); l++ ) 
								rmpCplex.add(x.getElement(l));
							for ( int l = 0; l < h.getSize(); l++ ) {
								rmpCplex.add(h.getElement(l));
							}
						}
					
						
	
						boolean result = false;     
						if(rmpCplex.solve()){

							result = true;
							Set<EdgeInformation> edgeInformationSet = new HashSet<EdgeInformation>();
							
							if( rmpCplex.getObjValue() < M){
								System.out.println("rmp obj " + rmpCplex.getObjValue());
								for(int l = 0; l < h.getSize(); l++){
									double card = rmpCplex.getValue(h.getElement(l));
									card = Math.round(card * 100000D) / 100000D;
									if(card > 0){
										//System.out.println("non zero cardinality " + card);
										infeasible = true;
										break;
									}
								}
							/*	for(int l = 0; l < x.getSize(); l++){
									double card = rmpCplex.getValue(x.getElement(l));
									if(!isInteger(card)) {
										System.out.println("non integer cardinality " + card);
										infeasible = true;
										break;
									}
								}*/
								if(!infeasible) {
									BiMap<Integer, OWLClassExpression> reverseQualifiers = qualifiers.inverse();
									BiMap<Integer, OWLObjectPropertyExpression> reverseRoles = srRolesMap.inverse();
									BiMap<Integer, OWLObjectPropertyExpression> reverseTempRoles = tempRoleHMap.inverse();
									Map<OWLObjectPropertyExpression, OWLObjectPropertyExpression> reverseTempRoleH = new HashMap<>();
									for(Entry<OWLObjectPropertyExpression, OWLObjectPropertyExpression> e : tempRoleH.entrySet()){
										reverseTempRoleH.put(e.getValue(), e.getKey());
									}
									for(int l = 0; l < x.getSize(); l++){
									  double cardinality2 = rmpCplex.getValue(x.getElement(l));
									//  System.out.println("x cardinality2 " + cardinality2);
									  if(cardinality2 > 0.0){
												//	System.out.println("l value " + l);
										SubSet tempSubSet1 = subsets.get(l);
												
										Set<OWLObjectPropertyExpression> tempRoleSet = new HashSet<>();
										Set<OWLObjectPropertyExpression> tempSupRoleSet = new HashSet<>();
										Set<OWLClassExpression> tempClassSet = new HashSet<>();
										Set<Integer> nodeSet = new HashSet<>();
										
										boolean addIt = false;
													
										for(int j = 0 ; j < tempSubSet1.getConceptIndexSet().length ; j++){
											if(tempSubSet1.getConceptIndexSet()[j] > 0){ // if b value is 1
												tempClassSet.add(reverseQualifiers.get(j));
												if(!addIt)
													addIt = true;
											}
										}
										//	System.out.println("tempClassSet "+tempClassSet.size());
										Set<OWLClassExpression> temp = new HashSet<>();
										temp.addAll(tempClassSet);
										for(OWLClassExpression ce : temp) {
											if(ilpPro.getAuxiliaryConcepts().contains(ce))
												tempClassSet.addAll(ilpPro.getComplexASubsumers(ce));
											if(ilpPro.getNodeIdMap().containsKey(ce))
												nodeSet.add(ilpPro.getNodeIdMap().get(ce));
											}
											tempClassSet.removeAll(ilpPro.getAuxiliaryConcepts());
											if(addIt){
												DependencySet ds = DependencySet.create();
												for(int j = 0 ; j < tempSubSet1.getRolesIndexSet().length ; j++){
													if(tempSubSet1.getRolesIndexSet()[j] > 0) { // if r value is 1
														//System.out.println(" role "+qcrMap.get(j).role);
														if(qcrMap.get(j)!=null) {
														if(qcrMap.get(j).role!=null) {
															tempRoleSet.add(qcrMap.get(j).role);
															ds.add(qcrMap.get(j).ds);
														}
														}
													}
												}
												for(int j = 0 ; j < tempSubSet1.getSupRolesIndexSet().length ; j++){
													if(tempSubSet1.getSupRolesIndexSet()[j] > 0) { // if sr value is 1
														//System.out.println("sr["+j+"]: "+tempSubSet1.getSupRolesIndexSet()[j]);
														//System.out.println("sup role "+reverseRoles.get(j) );
															
														tempSupRoleSet.add(reverseRoles.get(j));
													}
												}
												tempRoleSet.addAll(tempSupRoleSet);
												Set<OWLObjectPropertyExpression> temp2 = new HashSet<>();
												temp2.addAll(tempRoleSet);
												for(OWLObjectPropertyExpression rr : temp2) {
													if(ilpPro.getAuxiliaryRoles().contains(rr))
														tempRoleSet.addAll(ilpPro.getAuxRoleHMap(rr));
													}
													tempRoleSet.removeAll(ilpPro.getAuxiliaryRoles());
													
													if(!tempRoleSet.isEmpty()) {
														EdgeInformation tempEdgeInformation = new EdgeInformation(tempRoleSet , tempClassSet , cardinality2, ds, nodeSet);
														edgeInformationSet.add(tempEdgeInformation);
													}
												}
											}
										
									}
									
									// Adding complement to ensure at most restrictions
								/*	Set<QCR> tempMaxQcrs = qcrMap.values().stream().filter(qcr -> qcr.type.equals("MAX")).collect(Collectors.toSet());
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
														EdgeInformation tempEdgeInformation = new EdgeInformation(tempObj , tempSet , card - check_complement.get(q), e.getDs());
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
									}*/
	
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
										EdgeInformation tempEdgeInformation = new EdgeInformation(e.getEdges(), fillers, edge_map.get(e), e.getDs(), e.getNodeSet());
										finalEdgeInformations.add(tempEdgeInformation);
									}
	
									returnSolution.setEdgeInformation(finalEdgeInformations);
								}
								else {
									/*result = false;
									Set<OWLObjectCardinalityRestriction> infeasible_set  = new HashSet<>();
									for(int l = 0; l < totalVar; l++){
										if(rmpCplex.getValue(h.getElement(l)) > 0.1){
											infeasible_set.add(crMap.get(l));
										}
									}
									returnSolution.setInfeasible_set(infeasible_set);*/
									System.out.println("Infeasible inequality system. Trying other option");
									for(int j = totalVar; j<Constraint.length; j++) {
										rmpCplex.remove(Constraint[j]);
									}
									rmpCplex.solve();
									Constraint1 = new IloRange[orgConstraint.length];
									Constraint1 =	Arrays.copyOf(orgConstraint, orgConstraint.length);
									ppCplex =  	new PPModel().GeneratePpModel().getPpCplex();
									r1 = ppCplex.numVarArray(orgR.length, 0., 1, IloNumVarType.Int);
									System.arraycopy(orgR, 0, r1, 0, orgR.length);
									continue;
								}
							}
							else{
								
								System.out.println("Infeasible inequality system. Trying other option");
								for(int j = totalVar; j<Constraint.length; j++) {
									rmpCplex.remove(Constraint[j]);
								}
								rmpCplex.solve();
								Constraint1 = new IloRange[orgConstraint.length];
								Constraint1 =	Arrays.copyOf(orgConstraint, orgConstraint.length);
								ppCplex =  	new PPModel().GeneratePpModel().getPpCplex();
								r1 = ppCplex.numVarArray(orgR.length, 0., 1, IloNumVarType.Int);
								System.arraycopy(orgR, 0, r1, 0, orgR.length);
								continue;
							}
						//	rmpCplex.end();
						//	ppCplex.end();
							returnSolution.setSolved(result);
							
							return returnSolution;
						}
					/*	else{
							infeasible = true;
							rmpCplex.remove(Constraint[Constraint1.length]);
							for(IloConstraint ppc : ppNewCons) {
								ppCplex.remove(ppc);
							}
							continue;
						}*/
					}
					else {
						if(k==1) {
							System.out.println("No solution k 2");
							Set<OWLObjectCardinalityRestriction> infeasible_set  = new HashSet<>();
							for(int l = 0; l < totalVar; l++){
								if(rmpCplex.getValue(h.getElement(l)) > 0.1){
									infeasible_set.add(crMap.get(l));
								}
							}
							
						//	rmpCplex.end();
						//	ppCplex.end();
							returnSolution.setSolved(false);
							returnSolution.setInfeasible_set(infeasible_set);
							return returnSolution;
						}
						//System.out.println("here");
						for(int j = totalVar; j<Constraint.length; j++) {
							rmpCplex.remove(Constraint[j]);
						}
						rmpCplex.solve();
						Constraint1 = new IloRange[orgConstraint.length];
						Constraint1 =	Arrays.copyOf(orgConstraint, orgConstraint.length);
						ppCplex =  	new PPModel().GeneratePpModel().getPpCplex();
						r1 = ppCplex.numVarArray(orgR.length, 0., 1, IloNumVarType.Int);
						System.arraycopy(orgR, 0, r1, 0, orgR.length);
						/*for(IloConstraint ppc : ppNewCons) {
							ppCplex.remove(ppc);
						}*/
						continue;
					}
				}
				else {
					if(k==1) {
						System.out.println("No solution");
						Set<OWLObjectCardinalityRestriction> infeasible_set  = new HashSet<>();
						for(int l = 0; l < totalVar; l++){
							if(rmpCplex.getValue(h.getElement(l)) > 0.1){
								infeasible_set.add(crMap.get(l));
							}
						}
						
					//	rmpCplex.end();
					//	ppCplex.end();
						returnSolution.setSolved(false);
						returnSolution.setInfeasible_set(infeasible_set);
						return returnSolution;
					}
					for(int j = totalVar; j<Constraint.length; j++) {
						rmpCplex.remove(Constraint[j]);
					}
					rmpCplex.solve();
					Constraint1 = new IloRange[orgConstraint.length];
					Constraint1 =	Arrays.copyOf(orgConstraint, orgConstraint.length);
					ppCplex =  	new PPModel().GeneratePpModel().getPpCplex();
					r1 = ppCplex.numVarArray(orgR.length, 0., 1, IloNumVarType.Int);
					System.arraycopy(orgR, 0, r1, 0, orgR.length);
				/*for(IloConstraint ppc : ppNewCons) {
						ppCplex.remove(ppc);
					}*/
					continue;
				}
			}
				if(infeasible == true) {
					System.out.println("No solution");
					Set<OWLObjectCardinalityRestriction> infeasible_set  = new HashSet<>();
					for(int l = 0; l < totalVar; l++){
						if(rmpCplex.getValue(h.getElement(l)) > 0.1){
							infeasible_set.add(crMap.get(l));
						}
					}
					
				//	rmpCplex.end();
				//	ppCplex.end();
					returnSolution.setSolved(false);
					returnSolution.setInfeasible_set(infeasible_set);
					return returnSolution;
				}
		}
			
	  }
		System.out.println("No solution");
		Set<OWLObjectCardinalityRestriction> infeasible_set  = new HashSet<>();
		for(int l = 0; l < totalVar; l++){
			if(rmpCplex.getValue(h.getElement(l)) > 0.1){
				infeasible_set.add(crMap.get(l));
			}
		}
		
	//	rmpCplex.end();
	//	ppCplex.end();
		returnSolution.setSolved(false);
		returnSolution.setInfeasible_set(infeasible_set);
		return returnSolution;
					
	}
	
	private ILPSolution applyBranchAndPrice2(int start, RMPModel rmpModel, PPModel ppModel, IloCplex rmpCplex, IloCplex ppCplex, IloNumVarArray x1, IloNumVarArray h1,
			ArrayList<SubSet> subsets1, IloNumVar[] b, IloNumVar[] r1, IloNumVar[] sr, IloRange[] Constraint1) throws IloException {
		
		ILPSolution returnSolution = new ILPSolution();
		IloNumVarArray x = new IloNumVarArray(x1);
		IloNumVarArray h = new IloNumVarArray(h1);
		ArrayList<SubSet> subsets = new ArrayList<SubSet>(subsets1);
	//	int size = x.getSize();
	//	System.out.println("x size :"+ size);
	//	System.out.println("start :"+ start);
		
		
		for ( int i = start+1; i < x.getSize(); i++ ) {
		//for ( int i = start+1; i < subsets.size(); i++ ) {
			start++;
		//	System.out.println("i : "+i);
		//	System.out.println("obj : "+rmpCplex.getObjValue());
		//	rmpCplex.solve();
		//	double cardinality = rmpCplex.getValue(x.getElement(i));
			double cardinality = Math.round(rmpCplex.getValue(x.getElement(i))* 100000D) / 100000D;
			System.out.println("cardinality second 2:"+ cardinality);
			/*for ( int ii = 0; ii < x.getSize(); ii++ ) {
				System.out.println("cardinality check :"+ Math.round(rmpCplex.getValue(x.getElement(ii))* 100000D) / 100000D);
			}*/
			if(!isInteger(cardinality)) {
			
				
			 System.out.println("Trying value number "+ i +" card " + cardinality );			
			// subsets = new ArrayList<SubSet>(subsets1);
			
			
			
				
				double fractional = cardinality % 1;
				double part1 = cardinality - fractional;
				double part2 = part1 + 1;
			//	System.out.println("i "+i+" subset size"+subsets.size()+" x size"+ x.getSize());
				
				/*if(i>=subsets.size()) {
					System.out.println("i "+i+" subset size"+subsets.size());
					break;
				}*/
				SubSet tempSubSet = subsets.get(i);
				
				
				// try both branches
				boolean infeasible = false;
				for(int k = 0; k < 2; k++) {
					
					IloRange[] Constraint =  Arrays.copyOf(Constraint1, Constraint1.length+1);
					IloConstraint[]  ppNewCons = null;
				//	System.out.println("constraint size " + Constraint.length);
				
					
					IloNumVar[] r = ppCplex.numVarArray(r1.length+1, 0., 1, IloNumVarType.Int);
					
					System.arraycopy(r1, 0, r, 0, r1.length);
					
						
					IloObjective obj = rmpCplex.getObjective();
					IloObjective reducedCost = ppCplex.getObjective();
					Set<Integer> bvalues = new HashSet<>();
					infeasible = false;
					
				
					if(k == 0) {
						System.out.println("Trying part "+ (k+1) + " inequality "+ part2);
					//	Constraint[totalVar] =  rmpCp.addGe(expr[totalVar], part2);
						Constraint[Constraint1.length] =  rmpCplex.addGe(x.getElement(i), part2);
					//	Constraint[totalVar] =  rmpCplex.addGe(xv, part2);
						// check which b values are 1
						for(int j = 0 ; j < tempSubSet.getConceptIndexSet().length ; j++){
							if(tempSubSet.getConceptIndexSet()[j] > 0){ // if b value is 1
							//System.out.println("bvalue "+ j );
								bvalues.add(j);
							}
						}
						
						// add constraint in PP
						IloLinearNumExpr nexpr = ppCplex.linearNumExpr();
						ppNewCons = new IloConstraint[bvalues.size()+1];
						int count = 0;
						for (Integer bv : bvalues){
							//System.out.println(bv);
							nexpr.addTerm(1, b[bv]);
							ppNewCons[count] = ppCplex.addLe(r[r1.length], b[bv]);
							count++;
						}
						ppNewCons[count] = ppCplex.addLe(ppCplex.diff(nexpr, bvalues.size() - 1), r[r1.length]);
					}
					else {
						System.out.println("Trying part "+ (k+1) + " inequality "+ part1);
						//Constraint[totalVar] =  rmpCp.addLe(expr[totalVar], part1);
						Constraint[Constraint1.length] =  rmpCplex.addLe(x.getElement(i), part1);
					//	Constraint[totalVar] =  rmpCplex.addLe(xv, part1);
						// check which b values are 1
						for(int j = 0 ; j < tempSubSet.getConceptIndexSet().length ; j++){
							if(tempSubSet.getConceptIndexSet()[j] > 0){ // if b value is 1
								bvalues.add(j);
							}
						}
						ppNewCons = new IloConstraint[bvalues.size()+1];
						int count = 0;
						// add constraint in PP
						IloLinearNumExpr nexpr = ppCplex.linearNumExpr();
						for (Integer bv : bvalues){
							//System.out.println(bv);
							//System.out.println(r[totalVar]);
							nexpr.addTerm(1, b[bv]);
							ppNewCons[count] = ppCplex.addLe(b[bv], r[r1.length]);
							count++;
						}
						ppNewCons[count] = ppCplex.addLe(ppCplex.diff(nexpr, bvalues.size() - 1), r[r1.length]);
					}
				
					
					double[] newCol = new double[totalVar+1];
				//	System.out.println("M value "+M);
					double relaxed_opt = M;
					while (true) {
						
						infeasible = false;
						boolean isRMPFeasible = false;
						if(rmpCplex.solve()){
							System.out.println("feasible ");
							isRMPFeasible = true;
							relaxed_opt = rmpCplex.getObjValue();
						//System.out.println("relaxed opt inside "+relaxed_opt);
						/// generate and add a new column in RMP
						/*for ( int l = 0; l < x.getSize(); l++ ) {
							double card = rmpCplex.getValue(x.getElement(l));
							System.out.println("cardinality inside!  "+ card);
						}*/
							
						double[] price = rmpCplex.getDuals(Constraint);
						//System.out.println("dual value  # "+price.length);
						//for(int j = 0 ; j < price.length ; j++)
						//	System.out.println("dual value  bNp "+price[j]);
						
					/*	double[] price2 = rmpCp.getAX(Constraint);
						for(int j = 0 ; j < price2.length ; j++)
							System.out.println("AX value  bNp "+price2[j]);*/
						
						IloLinearNumExpr objExpr = ppCplex.linearNumExpr();
						for(int j = 0 ; j < b.length ; j++)
							objExpr.addTerm(1 , b[j]);
						//System.out.println("r value  # "+r.length);
						reducedCost.setExpr(ppCplex.diff(ppCplex.square(objExpr),ppCplex.scalProd(r, price)));
						//	reducedCost.setExpr(ppCplex.diff(objExpr,ppCplex.scalProd(r, price)));
						
						if(ppCplex.solve()){
							//System.out.println("pp objective "+ppCplex.getObjValue());
							if ( ppCplex.getObjValue() > -RC_EPS ){
								//System.out.println("break" + -RC_EPS);
								break;
							}
	
							newCol = ppCplex.getValues(r);
							
							double[] bVal = ppCplex.getValues(b);
							
							int cost = 0;
							double[] rv = ppCplex.getValues(r);
						//	System.out.println("------");
						//	for(int j = 0 ; j < rv.length ; j++) {
						//		System.out.println("r v  ["+j +"]"+ rv[j]);
								
						//	}
							
							
						//	double[] srv = ppCp.getValues(sr);
							
						//	for(int j = 0 ; j < srv.length ; j++) {
						//		System.out.println("sr v ["+j +"]"+ srv[j]);
								
						//	}
							for(int j = 0 ; j < bVal.length ; j++) {
								//System.out.println("bVal " + bVal[j]);
								cost += bVal[j];
							}
							/*if(cost>5) {
								cost += cost-1;
							}*/
								
							//System.out.println("cost " + cost);
							IloColumn column = rmpCplex.column(obj, cost*cost);//Creates and returns a column from the specified objective and value.
							for ( int ii = 0; ii < Constraint.length; ii++ )
								column = column.and(rmpCplex.column(Constraint[ii], newCol[ii]));//Creates and returns a column from the specified range and value.
							
							x.add( rmpCplex.numVar(column, 0., Double.MAX_VALUE) );
							subsets.add(new SubSet(ppCplex.getValues(r) , ppCplex.getValues(b), ppCplex.getValues(sr)));
						//	System.out.println("x add "+ x.getSize()+" subset add "+ subsets.size());
							
						}
						else {
							infeasible = true;
							break;
						}
					}
					else{	
						//System.out.println("infeasible 1");
						infeasible = true;
						break;
					}
				  }
				
				if(!infeasible) {
					if( relaxed_opt < M ){
						//System.out.println("relaxed opt "+relaxed_opt);
						//System.out.println("x.getSize() " + x.getSize());
						/*for(int l = 0; l < h.getSize(); l++){
							double card = rmpCplex.getValue(h.getElement(l));
							if(card > 0){
								System.out.println("non zero cardinality " + card);
								infeasible = true;
								break;
							}
						}
						if(infeasible) {
							for(int j = totalVar; j<Constraint.length; j++) {
								rmpCplex.remove(Constraint[j]);
							}
							Constraint1 = new IloRange[orgConstraint.length];
							Constraint1 =	Arrays.copyOf(orgConstraint, orgConstraint.length);
							ppCplex =  	new PPModel().GeneratePpModel().getPpCplex();
							r1 = ppCplex.numVarArray(orgR.length, 0., 1, IloNumVarType.Int);
							System.arraycopy(orgR, 0, r1, 0, orgR.length);
							for(IloConstraint ppc : ppNewCons) {
								ppCplex.remove(ppc);
							}
							System.out.println("k value "+k);
							continue;
						}*/
						boolean nonInteger = false;
						for ( int l = 0; l < x.getSize(); l++ ) {
							double card = rmpCplex.getValue(x.getElement(l));
							card = Math.round(card * 100000D) / 100000D;
						//	System.out.println("cardinality outside!  "+ card);
				//		if(!isInteger(Math.round(card * 100000D) / 100000D)) {
							if(!isInteger(card)) {
								nonInteger = true;
								break;
							}
						}
						for(int l = 0; l < h.getSize(); l++){
							double card = rmpCplex.getValue(h.getElement(l));
							card = Math.round(card * 100000D) / 100000D;
							if(card > 0){
							//	System.out.println("non zero cardinality " + card+ " rounded: " + Math.round(card * 100000D) / 100000D);
								infeasible = true;
								break;
							}
						}
						
						
		
						if(nonInteger && !infeasible) {
							System.out.println("non integer cardinality! trying for integer solution ");
							//infeasible = true;
						//	System.out.println("before call : i "+i+" subset size"+subsets.size()+" x size"+ x.getSize());
							ILPSolution sol = applyBranchAndPrice2(start, rmpModel, ppModel, rmpCplex, ppCplex, x, h, subsets, b, r, sr, Constraint);
							if(sol.solved)	
								return sol;
							/*else if(k == 1) {
								return sol;
							}*/
							else {
								rmpCplex.remove(Constraint[Constraint1.length]);
								/*for(int j = totalVar; j<Constraint.length; j++) {
									rmpCplex.remove(Constraint[j]);
								}*/
								rmpCplex.solve(); 
								
								
								for(int j = 0; j<ppNewCons.length; j++) {
									ppCplex.remove(ppNewCons[j]);
								}
								ppCplex.solve();
							//	Constraint1 = new IloRange[orgConstraint.length];
							//	Constraint1 =	Arrays.copyOf(orgConstraint, orgConstraint.length);
							//	ppCplex =  	new PPModel().GeneratePpModel().getPpCplex();
							//	r1 = ppCplex.numVarArray(orgR.length, 0., 1, IloNumVarType.Int);
							//	System.arraycopy(orgR, 0, r1, 0, orgR.length);
								//ppCplex.solve();
								continue;
							}
								
							
						}
						else {
							for ( int l = 0; l < x.getSize(); l++ ) 
								rmpCplex.add(x.getElement(l));
						}
					
						for ( int l = 0; l < h.getSize(); l++ ) {
							rmpCplex.add(h.getElement(l));
							//rmpCp.add(rmpCp.conversion(h.getElement(l),IloNumVarType.Int));
						}
	
						boolean result = false;     
						if(rmpCplex.solve()){

							/*if(k!=1) {
								for(int j = totalVar; j<Constraint.length; j++) {
									rmpCplex.remove(Constraint[j]);
								}
								Constraint1 = new IloRange[orgConstraint.length];
								Constraint1 =	Arrays.copyOf(orgConstraint, orgConstraint.length);
								ppCplex =  	new PPModel().GeneratePpModel().getPpCplex();
								r1 = ppCplex.numVarArray(orgR.length, 0., 1, IloNumVarType.Int);
								System.arraycopy(orgR, 0, r1, 0, orgR.length);
								continue;
							}*/
							result = true;
							Set<EdgeInformation> edgeInformationSet = new HashSet<EdgeInformation>();
							
							if( rmpCplex.getObjValue() < M){
								System.out.println("rmp obj " + rmpCplex.getObjValue());
								for(int l = 0; l < h.getSize(); l++){
									double card = rmpCplex.getValue(h.getElement(l));
									card = Math.round(card * 100000D) / 100000D;
									if(card > 0){
										//System.out.println("non zero cardinality " + card);
										infeasible = true;
										break;
									}
								}
							/*	for(int l = 0; l < x.getSize(); l++){
									double card = rmpCplex.getValue(x.getElement(l));
									if(!isInteger(card)) {
										System.out.println("non integer cardinality " + card);
										infeasible = true;
										break;
									}
								}*/
								if(!infeasible) {
									BiMap<Integer, OWLClassExpression> reverseQualifiers = qualifiers.inverse();
									BiMap<Integer, OWLObjectPropertyExpression> reverseRoles = srRolesMap.inverse();
									BiMap<Integer, OWLObjectPropertyExpression> reverseTempRoles = tempRoleHMap.inverse();
									Map<OWLObjectPropertyExpression, OWLObjectPropertyExpression> reverseTempRoleH = new HashMap<>();
									for(Entry<OWLObjectPropertyExpression, OWLObjectPropertyExpression> e : tempRoleH.entrySet()){
										reverseTempRoleH.put(e.getValue(), e.getKey());
									}
									for(int l = 0; l < x.getSize(); l++){
									  double cardinality2 = rmpCplex.getValue(x.getElement(l));
									//  System.out.println("x cardinality2 " + cardinality2);
									  if(cardinality2 > 0.0){
												//	System.out.println("l value " + l);
										SubSet tempSubSet1 = subsets.get(l);
												
										Set<OWLObjectPropertyExpression> tempRoleSet = new HashSet<>();
										Set<OWLObjectPropertyExpression> tempSupRoleSet = new HashSet<>();
										Set<OWLClassExpression> tempClassSet = new HashSet<>();
										Set<Integer> nodeSet = new HashSet<>();
										
										boolean addIt = false;
													
										for(int j = 0 ; j < tempSubSet1.getConceptIndexSet().length ; j++){
											if(tempSubSet1.getConceptIndexSet()[j] > 0){ // if b value is 1
												tempClassSet.add(reverseQualifiers.get(j));
												if(!addIt)
													addIt = true;
											}
										}
										//	System.out.println("tempClassSet "+tempClassSet.size());
										Set<OWLClassExpression> temp = new HashSet<>();
										temp.addAll(tempClassSet);
										for(OWLClassExpression ce : temp) {
											if(ilpPro.getAuxiliaryConcepts().contains(ce))
												tempClassSet.addAll(ilpPro.getComplexASubsumers(ce));
											if(ilpPro.getNodeIdMap().containsKey(ce))
												nodeSet.add(ilpPro.getNodeIdMap().get(ce));
											}
											tempClassSet.removeAll(ilpPro.getAuxiliaryConcepts());
											if(addIt){
												DependencySet ds = DependencySet.create();
												for(int j = 0 ; j < tempSubSet1.getRolesIndexSet().length ; j++){
													if(tempSubSet1.getRolesIndexSet()[j] > 0) { // if r value is 1
														//System.out.println(" role "+qcrMap.get(j).role);
														if(qcrMap.get(j)!=null) {
														if(qcrMap.get(j).role!=null) {
															tempRoleSet.add(qcrMap.get(j).role);
															ds.add(qcrMap.get(j).ds);
														}
														}
													}
												}
												for(int j = 0 ; j < tempSubSet1.getSupRolesIndexSet().length ; j++){
													if(tempSubSet1.getSupRolesIndexSet()[j] > 0) { // if sr value is 1
														//System.out.println("sr["+j+"]: "+tempSubSet1.getSupRolesIndexSet()[j]);
														//System.out.println("sup role "+reverseRoles.get(j) );
															
														tempSupRoleSet.add(reverseRoles.get(j));
													}
												}
												tempRoleSet.addAll(tempSupRoleSet);
												Set<OWLObjectPropertyExpression> temp2 = new HashSet<>();
												temp2.addAll(tempRoleSet);
												for(OWLObjectPropertyExpression rr : temp2) {
													if(ilpPro.getAuxiliaryRoles().contains(rr))
														tempRoleSet.addAll(ilpPro.getAuxRoleHMap(rr));
													}
													tempRoleSet.removeAll(ilpPro.getAuxiliaryRoles());
													
													if(!tempRoleSet.isEmpty()) {
														EdgeInformation tempEdgeInformation = new EdgeInformation(tempRoleSet , tempClassSet , cardinality2, ds, nodeSet);
														edgeInformationSet.add(tempEdgeInformation);
													}
												}
											}
										
									}
									
									// Adding complement to ensure at most restrictions
								/*	Set<QCR> tempMaxQcrs = qcrMap.values().stream().filter(qcr -> qcr.type.equals("MAX")).collect(Collectors.toSet());
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
														EdgeInformation tempEdgeInformation = new EdgeInformation(tempObj , tempSet , card - check_complement.get(q), e.getDs());
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
									}*/
	
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
										EdgeInformation tempEdgeInformation = new EdgeInformation(e.getEdges(), fillers, edge_map.get(e), e.getDs(), e.getNodeSet());
										finalEdgeInformations.add(tempEdgeInformation);
									}
	
									returnSolution.setEdgeInformation(finalEdgeInformations);
								}
								else {
									/*result = false;
									Set<OWLObjectCardinalityRestriction> infeasible_set  = new HashSet<>();
									for(int l = 0; l < totalVar; l++){
										if(rmpCplex.getValue(h.getElement(l)) > 0.1){
											infeasible_set.add(crMap.get(l));
										}
									}
									returnSolution.setInfeasible_set(infeasible_set);*/
									System.out.println("Infeasible inequality system. Trying other option");
									
									
									rmpCplex.remove(Constraint[Constraint1.length]);
									rmpCplex.solve(); 
									
									
									for(int j = 0; j<ppNewCons.length; j++) {
										ppCplex.remove(ppNewCons[j]);
									}
									ppCplex.solve();
									
									/*for(int j = totalVar; j<Constraint.length; j++) {
										rmpCplex.remove(Constraint[j]);
									}
									rmpCplex.solve();
									Constraint1 = new IloRange[orgConstraint.length];
									Constraint1 =	Arrays.copyOf(orgConstraint, orgConstraint.length);
									ppCplex =  	new PPModel().GeneratePpModel().getPpCplex();
									r1 = ppCplex.numVarArray(orgR.length, 0., 1, IloNumVarType.Int);
									System.arraycopy(orgR, 0, r1, 0, orgR.length);*/
									continue;
								}
							}
							else{
								
								System.out.println("Infeasible inequality system. Trying other option");
								
								rmpCplex.remove(Constraint[Constraint1.length]);
								rmpCplex.solve(); 
								
								
								for(int j = 0; j<ppNewCons.length; j++) {
									ppCplex.remove(ppNewCons[j]);
								}
								ppCplex.solve();
								
								
								/*for(int j = totalVar; j<Constraint.length; j++) {
									rmpCplex.remove(Constraint[j]);
								}
								rmpCplex.solve();
								Constraint1 = new IloRange[orgConstraint.length];
								Constraint1 =	Arrays.copyOf(orgConstraint, orgConstraint.length);
								ppCplex =  	new PPModel().GeneratePpModel().getPpCplex();
								r1 = ppCplex.numVarArray(orgR.length, 0., 1, IloNumVarType.Int);
								System.arraycopy(orgR, 0, r1, 0, orgR.length);*/
								continue;
							}
						//	rmpCplex.end();
						//	ppCplex.end();
							returnSolution.setSolved(result);
							
							return returnSolution;
						}
					/*	else{
							infeasible = true;
							rmpCplex.remove(Constraint[Constraint1.length]);
							for(IloConstraint ppc : ppNewCons) {
								ppCplex.remove(ppc);
							}
							continue;
						}*/
					}
					else {
						//System.out.println("here");
						
						rmpCplex.remove(Constraint[Constraint1.length]);
						rmpCplex.solve(); 
						
						
						for(int j = 0; j<ppNewCons.length; j++) {
							ppCplex.remove(ppNewCons[j]);
						}
						ppCplex.solve();
						
						/*for(int j = totalVar; j<Constraint.length; j++) {
							rmpCplex.remove(Constraint[j]);
						}
						rmpCplex.solve();
						Constraint1 = new IloRange[orgConstraint.length];
						Constraint1 =	Arrays.copyOf(orgConstraint, orgConstraint.length);
						ppCplex =  	new PPModel().GeneratePpModel().getPpCplex();
						r1 = ppCplex.numVarArray(orgR.length, 0., 1, IloNumVarType.Int);
						System.arraycopy(orgR, 0, r1, 0, orgR.length);*/
						/*for(IloConstraint ppc : ppNewCons) {
							ppCplex.remove(ppc);
						}*/
						continue;
					}
				}
				else {
					
					rmpCplex.remove(Constraint[Constraint1.length]);
					rmpCplex.solve(); 
					
					
					for(int j = 0; j<ppNewCons.length; j++) {
						ppCplex.remove(ppNewCons[j]);
					}
					ppCplex.solve();
					
					/*for(int j = totalVar; j<Constraint.length; j++) {
						rmpCplex.remove(Constraint[j]);
					}
					rmpCplex.solve();
					Constraint1 = new IloRange[orgConstraint.length];
					Constraint1 =	Arrays.copyOf(orgConstraint, orgConstraint.length);
					ppCplex =  	new PPModel().GeneratePpModel().getPpCplex();
					r1 = ppCplex.numVarArray(orgR.length, 0., 1, IloNumVarType.Int);
					System.arraycopy(orgR, 0, r1, 0, orgR.length);*/
				/*for(IloConstraint ppc : ppNewCons) {
						ppCplex.remove(ppc);
					}*/
					continue;
				}
			}
				if(infeasible == true) {
					System.out.println("No solution");
					Set<OWLObjectCardinalityRestriction> infeasible_set  = new HashSet<>();
					for(int l = 0; l < totalVar; l++){
						if(rmpCplex.getValue(h.getElement(l)) > 0.1){
							infeasible_set.add(crMap.get(l));
						}
					}
					
				//	rmpCplex.end();
				//	ppCplex.end();
					returnSolution.setSolved(false);
					returnSolution.setInfeasible_set(infeasible_set);
					return returnSolution;
				}
		}
			
	  }
		System.out.println("No solution");
		Set<OWLObjectCardinalityRestriction> infeasible_set  = new HashSet<>();
		for(int l = 0; l < totalVar; l++){
			if(rmpCplex.getValue(h.getElement(l)) > 0.1){
				infeasible_set.add(crMap.get(l));
			}
		}
		
	//	rmpCplex.end();
	//	ppCplex.end();
		returnSolution.setSolved(false);
		returnSolution.setInfeasible_set(infeasible_set);
		return returnSolution;
					
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
		IloNumVar[] _array;

		public IloNumVarArray() {
			_array = new IloNumVar[32];
			
		}
		public IloNumVarArray(IloNumVarArray x1) {
			this._num = x1.get_num();
			_array = new IloNumVar[this._num];
			System.arraycopy(x1._array, 0, _array, 0, _num);
		}

		void add(IloNumVar ivar) {
			if ( _num >= _array.length ) {
				IloNumVar[] array = new IloNumVar[2 * _array.length];
				System.arraycopy(_array, 0, array, 0, _num);
				_array = array;
			}
			_array[_num++] = ivar;
		}

		public int get_num() {
			return _num;
		}
		public void set_num(int _num) {
			this._num = _num;
		}
		public IloNumVar[] get_array() {
			return _array;
		}
		public void set_array(IloNumVar[] _array) {
			this._array = _array;
		}
		IloNumVar getElement(int i) { return _array[i]; }
		void addElement(int i, IloNumVar ivar) {  _array[i] = ivar; }
		int       getSize()         { return _num; }
	}
	static class SubSet {
		double[] rolesIndexSet;
		double[] supRolesIndexSet;
		double[] conceptIndexSet;
		int cost;

		SubSet(double[] rolesIndexSet, double[] conceptIndexSet, double[] supRolesIndexSet){
			this.rolesIndexSet = rolesIndexSet;
			this.conceptIndexSet = conceptIndexSet;
			this.supRolesIndexSet = supRolesIndexSet;
			cost = 0;
			for(int j = 0 ; j < conceptIndexSet.length ; j++)
				cost += conceptIndexSet[j];
		}

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
	 
	 double TOLERANCE = 1E-5;
	// System.out.println(Math.abs(Math.floor(d) - d) < TOLERANCE);
	// System.out.println ((d == Math.floor(d)) && !Double.isInfinite(d));
	    //do not use (int)d, due to weird floating point conversions!
	  //  return Math.abs(Math.floor(d) - d) < TOLERANCE;
	 return (d == Math.floor(d)) && !Double.isInfinite(d);
		/*if(Math.abs(d % 1) <= RC_EPS)
			return true;
		return false;*/
	}
	
	public class RMPModel{
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
			
			
			System.out.println("total var : "+totalVar);
			//System.out.println("M : "+M);
			//System.out.println("qcrmap size : "+qcrMap.size());
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


		public IloObjective getObj() {
			return obj;
		}


		public IloRange[] getConstraint() {
			return Constraint;
		}


		public IloLinearNumExpr[] getExpr() {
			return expr;
		}


		public IloNumVarArray getH() {
			return h;
		}


		public ArrayList<SubSet> getSubsets() {
			return subsets;
		}


		public IloNumVarArray getX() {
			return x;
		}

		public void setX(IloNumVarArray x) {
			this.x = x;
		}
	}
	public class PPModel{
		IloCplex ppCplex;
		IloObjective reducedCost;
		IloNumVar[] r ;
		IloNumVar[] b ;
		IloNumVar[] sr ;
		IloNumVar[] hr ;
		
		public IloCplex getPpCplex() {
			return ppCplex;
		}
		public IloObjective getReducedCost() {
			return reducedCost;
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
		public IloNumVar[] getB() {
			return b;
		}
		
		@SuppressWarnings("unchecked")
		public PPModel GeneratePpModel() throws IloException {
			
			Map<OWLObjectPropertyExpression, Set<OWLClassExpression>> forAllMaps = new HashMap<OWLObjectPropertyExpression, Set<OWLClassExpression>>();
			if(forAllMap != null)
				forAllMaps = (Map<OWLObjectPropertyExpression, Set<OWLClassExpression>>) (Map<?, ?>) forAllMap.asMap();
			
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
			
			
			SetMultimap<OWLObjectPropertyExpression, Integer> axiomRolesMap = HashMultimap.create();
			
			for (int i = 0; i < totalVar; i++ ) {
				if(qcrMap.get(i).role!=null) {
					axiomRolesMap.put(qcrMap.get(i).role, i);
					if(tempRoleH.containsKey(qcrMap.get(i).role))
						ppCplex.addLe(r[i] , hr[tempRoleHMap.get(tempRoleH.get(qcrMap.get(i).role))]);
					//System.out.println("r["+i+"]: role "+"hr["+tempRoleHMap.get(tempRoleH.get(qcrMap.get(i).role.getNamedProperty()))+"] "+ tempRoleH.get(qcrMap.get(i).role.getNamedProperty()));
					//System.out.println("r["+i+"]: role "+qcrMap.get(i).role.getNamedProperty()+ "qualifier "+qcrMap.get(i).qualifier);
					
				}
				//System.out.println("r["+i+"]: role "+qcrMap.get(i).role + "qualifier "+qcrMap.get(i).qualifier);
				if(qcrMap.get(i).type.equals("MIN"))
					ppCplex.addLe(r[i] , b[qualifiers.get(qcrMap.get(i).qualifier)]);
				else if (qcrMap.get(i).type.equals("MAX"))
					ppCplex.addLe(b[qualifiers.get(qcrMap.get(i).qualifier)] , r[i]);
				else {
					//System.out.println("r["+i+"]: role "+qcrMap.get(i).role + "qualifier "+qcrMap.get(i).qualifier);
					ppCplex.addLe(r[i] , b[qualifiers.get(qcrMap.get(i).qualifier)]);
					ppCplex.addLe(b[qualifiers.get(qcrMap.get(i).qualifier)] , r[i]);
				}
			}
			
			
			
			// Role Hierarchy
			for (OWLObjectPropertyExpression role : superRoles.keySet()){
				if(superRoles.get(role) != null){
					OWLObjectPropertyExpression tempSupRole = tempRoleH.get(role);
					for(OWLObjectPropertyExpression supRole : superRoles.get(role)){
						//System.out.println("role : "+role+" H role "+tempSupRole+" sup role " +supRole);
					//	System.out.println("role : "+role+" sup role " +supRole);
						//System.out.println("hr["+tempRoleHMap.get(tempSupRole)+"] <= "+ "sr["+srRolesMap.get(supRole)+"]");
						if(axiomRoles.contains(supRole)) {
							//System.out.println("hr["+tempRoleHMap.get(tempSupRole)+"] <= "+ "hr["+tempRoleHMap.get(tempRoleH.get(supRole))+"]");
							ppCplex.addLe(hr[tempRoleHMap.get(tempSupRole)], hr[tempRoleHMap.get(tempRoleH.get(supRole))]);
							
						}
						ppCplex.addLe(hr[tempRoleHMap.get(tempSupRole)], sr[srRolesMap.get(supRole)]);
					}
				}
			}
			//For All Restrictions -- Semantics 
			//System.out.println("forAll restrictions : "+forAllMaps.keySet().size());
			
			for (OWLObjectPropertyExpression role : forAllMaps.keySet()){
				//System.out.println("forAll restrictions : "+forAllMaps.keySet().size());
				if(forAllMaps.get(role) != null){
					if(axiomRoles.contains(role)) {
						OWLObjectPropertyExpression tempSupRole = tempRoleH.get(role);
						
						for(OWLClassExpression C : forAllMaps.get(role)) {
							ppCplex.addLe(hr[tempRoleHMap.get(tempSupRole)], b[qualifiers.get(C)]);
							if(srRolesMap.get(role)!=null)
								ppCplex.addLe(sr[srRolesMap.get(role)], b[qualifiers.get(C)]);
						}
					}
					else {
						for(OWLClassExpression C : forAllMaps.get(role))
							ppCplex.addLe(sr[srRolesMap.get(role)], b[qualifiers.get(C)]);
					}
				}
			}
			//TOP max cardinality Restrictions -- Semantics 
			//System.out.println("TOP max cardinality Restrictions : "+topMaxMap.keySet().size());
			
			for (OWLObjectPropertyExpression role : topMaxMap.keySet()){
				//System.out.println("TOP max cardinality Restrictions : "+topMaxMap.keySet().size());
				if(topMaxMap.get(role) != null){
					if(axiomRoles.contains(role)) {
						OWLObjectPropertyExpression tempSupRole = tempRoleH.get(role);
						//System.out.println("role "+ role+ " tempSupRole "+tempSupRole);
						OWLClassExpression C = topMaxMap.get(role);
						//System.out.println("role "+ role+ " class  "+C);
							
						ppCplex.addLe(hr[tempRoleHMap.get(tempSupRole)], b[qualifiers.get(C)]);
							if(srRolesMap.get(role)!=null)
								ppCplex.addLe(sr[srRolesMap.get(role)], b[qualifiers.get(C)]);
						
					}
					else {
						OWLClassExpression C = topMaxMap.get(role);
							ppCplex.addLe(sr[srRolesMap.get(role)], b[qualifiers.get(C)]);
					}
				}
			}
			//TOP min cardinality Restrictions -- Semantics 
			//System.out.println("TOP min cardinality Restrictions : "+topMinMap.keySet().size());
			
			for (OWLObjectPropertyExpression role : topMinMap.keySet()){
				//System.out.println("TOP max cardinality Restrictions : "+topMaxMap.keySet().size());
				if(topMinMap.get(role) != null){
					int ri = 0;
					for(int i : qcrMap.keySet()) {
						QCR q = qcrMap.get(i);
						if(q.qualifier.equals(topMinMap.get(role)) && q.role.equals(role) && q.type.equals("MIN")) {
							ri = i;
						}
					}
					if(axiomRoles.contains(role)) {
						OWLObjectPropertyExpression tempSupRole = tempRoleH.get(role);
						
						ppCplex.addLe(hr[tempRoleHMap.get(tempSupRole)], r[ri]);
						if(srRolesMap.get(role)!=null)
							ppCplex.addLe(sr[srRolesMap.get(role)], r[ri]);
						
					}
					else {
						ppCplex.addLe(sr[srRolesMap.get(role)],  r[ri]);
					}
				}
			}
			
			// Checking subsumers
			for (OWLClassExpression C : allQualifiers){
				if(conceptSubsumersMap.get(C) != null){
					for(OWLClassExpression D : conceptSubsumersMap.get(C)){
						//System.out.println(""+C+" subsume by "+D);
						if(D instanceof OWLObjectUnionOf) {
							IloLinearNumExpr exprSub = ppCplex.linearNumExpr();
							D.asDisjunctSet().stream().forEach(dj -> {
								try {
									exprSub.addTerm(1, b[qualifiers.get(dj)]);
								} catch (IloException e) {
									e.printStackTrace();
								}
							});
							ppCplex.addLe(b[qualifiers.get(C)], exprSub);
						}
						else
							ppCplex.addLe(b[qualifiers.get(C)], b[qualifiers.get(D)]);
					}
				}
			}
			
			
			final Map<OWLClassExpression, Set<OWLClassExpression>> conceptDisjointsMap = 
					(Map<OWLClassExpression, Set<OWLClassExpression>>) (Map<?, ?>) conceptDisjoints.asMap();
			// checking disjoint concepts
			for (OWLClassExpression C : allQualifiers){
				if(conceptDisjointsMap.get(C) != null){
					for(OWLClassExpression D : conceptDisjointsMap.get(C)){
						//System.out.println(""+C+" disjoint "+D);
						ppCplex.addLe(ppCplex.sum(ppCplex.prod(1.0, b[qualifiers.get(C)]),
								ppCplex.prod(1.0, b[qualifiers.get(D)])), 1);
					}
				}
			}
			
			//adding binary subsumption 
			
			if(binarySubsumersMap.keySet() != null){
				for (OWLClassExpression sb : binarySubsumersMap.keySet()){
					IloLinearNumExpr exprBinarySub = ppCplex.linearNumExpr();
					for(OWLClassExpression X : sb.asConjunctSet()){
						//System.err.println(X);
						exprBinarySub.addTerm(1, b[qualifiers.get(X)]);
					}
					for(OWLClassExpression sp : binarySubsumersMap.get(sb))
						ppCplex.addLe(ppCplex.diff(exprBinarySub, sb.asConjunctSet().size() - 1), b[qualifiers.get(sp)]);
				}
			}
			
			// Checking disjoint groups          
			if(disjointGroups != null){
				//OWLClassExpression Nothing = OWLFunctionalSyntaxFactory.OWLNothing();
				for (Set<OWLClassExpression> disjoints : disjointGroups){
					IloLinearNumExpr exprDisjoints = ppCplex.linearNumExpr();
					for(OWLClassExpression X : disjoints){
						exprDisjoints.addTerm(1, b[qualifiers.get(X)]);
					}
					//exprDisjoints.addTerm(-1, b[qualifiers.get(Nothing)]);
					ppCplex.addLe(exprDisjoints, disjoints.size() - 1);
				}
			}
			
			// handle negation
			for (OWLClassExpression C : negations.keySet()){
				//System.out.println("neg "+ C);
				OWLClassExpression D = negations.get(C);
				//System.out.println("neg "+ C + " - "+ D);
				ppCplex.addLe(ppCplex.sum(ppCplex.prod(1.0, b[qualifiers.get(C)]),
							ppCplex.prod(1.0, b[qualifiers.get(D)])), 1);
			}
			
			///
			//ppCplex.addLe(b[qualifiers.get(qcrMap.get(0).qualifier)],b[qualifiers.get(qcrMap.get(3).qualifier)]);
			
		
			
		//	ppCplex.addLe(ppCplex.sum(ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(1).qualifier)]),
		//			ppCplex.prod(1.0, b[qualifiers.get(qcrMap.get(3).qualifier)])), 1);
			
			return this;
		}
	}
	private class RMPCopy{
		IloCplex rmpCplex;
		private RMPCopy() throws IloException{
			rmpCplex = new IloCplex();
		}
		private RMPCopy(RMPCopy rmpCopy){
			rmpCplex = rmpCopy.getRmpCplex();
			
			
		}
		public RMPCopy(IloCplex rmpCpOrig, RMPModel rmpModel) throws IloException {
			rmpCplex = new IloCplex();
		//	rmpCpOrig.exportModel("lpModel.lp");
		//	rmpCpOrig.clearModel();
		//	rmpCpOrig.importModel("lpModel.lp");
		//	rmpCplex.setModel(rmpCpOrig.getModel());
			

			//IloLPMatrix lp = (IloLPMatrix)rmpCpOrig.LPMatrixIterator().next(); 
			IloCopyManager cm = new IloCopyManager(rmpCpOrig);
			IloObjective obj;
			try {
				obj = (IloObjective)rmpCpOrig.getObjective().makeCopy(cm);
				rmpCplex.add(obj);
				
				int numRanges = rmpModel.getConstraint().length;
					for(int r=0;r<numRanges;r++)
				    {                                                       
				    	//System.out.println("Adding -> "+lp.getRange(r).toString());//uncomment to print constraints                                        
				        IloRange temp = (IloRange)rmpModel.getConstraint()[r].makeCopy(cm);                                          
				        rmpCplex.add(temp);//Adding the individual constraints                                                                           
				    }
				
			//	System.out.println("lp.getRanges() "+lp);
			//	int numRanges = lp.getRanges().length;
			//	for(int r=0;r<numRanges;r++)
			//    {                                                       
			    	//System.out.println("Adding -> "+lp.getRange(r).toString());//uncomment to print constraints                                        
			//        IloRange temp = (IloRange)lp.getRange(r).makeCopy(cm);                                          
			//        rmpCplex.add(temp);//Adding the individual constraints                                                                           
			//    }              
			} catch (IloException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} 
		}
		public IloCplex getRmpCplex() {
			return rmpCplex;
		}
		public void setRmpCplex(IloCplex rmpCplex) {
			this.rmpCplex = rmpCplex;
		
		/*	try {
			// Create byte array output stream and use it to create object output stream
			ByteArrayOutputStream bos = new ByteArrayOutputStream();
			ObjectOutputStream oos = new ObjectOutputStream(bos);
			
			oos.writeObject(rmpCplex);
			oos.flush();
			// toByteArray creates & returns a copy of stream’s byte array
			byte[] bytes = bos.toByteArray();

			// Create byte array input stream and use it to create object input stream
			ByteArrayInputStream bis = new ByteArrayInputStream(bytes);

			ObjectInputStream ois = new ObjectInputStream(bis);
			this.rmpCplex = (IloCplex) ois.readObject();		// deserialize & typecast
			} catch (IOException | ClassNotFoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}		// serialize
			*/
		}
		
	}
	private class PPCopy{
		IloCplex ppCplex;
		private PPCopy() throws IloException{
			ppCplex = new IloCplex();
		}
		private PPCopy(PPCopy rmpCopy){
			this.ppCplex = rmpCopy.ppCplex;
			
		}
		public PPCopy(IloCplex ppCpOrig, PPModel ppModel) throws IloException {
			ppCplex = new IloCplex();
			IloCopyManager cm = new IloCopyManager(ppCpOrig);
			IloObjective obj = (IloObjective)ppCpOrig.getObjective().makeCopy(cm);
			ppCplex.add(obj);
			//ppCpOrig.get
			//ppCplex.setModel(ppCpOrig.getModel());
			/*	int numRanges = ppModel.getConstraint().length;
					for(int r=0;r<numRanges;r++)
				    {                                                       
				    	//System.out.println("Adding -> "+lp.getRange(r).toString());//uncomment to print constraints                                        
				        IloRange temp = (IloRange)ppModel.getConstraint()[r].makeCopy(cm);                                          
				        ppCplex.add(temp);//Adding the individual constraints                                                                           
				    }*/
					
		}
		public IloCplex getPpCplex() {
			return ppCplex;
		}
		public void setPpCplex(IloCplex ppCplex) {
			this.ppCplex = ppCplex;
		}
		
	}
}

