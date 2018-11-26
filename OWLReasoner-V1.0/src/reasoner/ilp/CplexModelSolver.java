package reasoner.ilp;

import java.util.ArrayList;

import ilog.concert.IloColumn;
import ilog.concert.IloException;
import ilog.concert.IloLinearNumExpr;
import ilog.concert.IloNumVar;
import ilog.concert.IloNumVarType;
import ilog.concert.IloObjective;
import ilog.concert.IloRange;
import ilog.cplex.IloCplex;
import reasoner.ilp.CplexModelGenerator.IloNumVarArray;
import reasoner.ilp.CplexModelGenerator.PPModel;
import reasoner.ilp.CplexModelGenerator.RMPModel;
import reasoner.ilp.CplexModelGenerator.SubSet;

public class CplexModelSolver {
	IloCplex rmpCplex;
	IloObjective obj;
	IloCplex ppCplex;
	IloObjective reducedCost;
	IloRange[]   Constraint;
	IloLinearNumExpr[] expr;
	IloNumVarArray h;
	IloNumVarArray x;
	ArrayList<SubSet> subsets;
	
	IloNumVar[] r ;
	IloNumVar[] sr ;
	IloNumVar[] b ;

	int totalVar;
	static double RC_EPS = 1.0e-6;
	int M;
	
	public CplexModelSolver(RMPModel rmpModel, PPModel ppModel, int totalVar) {
		this.totalVar = totalVar;
		this.M = 100*totalVar;
		 rmpCplex = rmpModel.getRmpCplex();
		 obj = rmpCplex.getObjective();
		 ppCplex = ppModel.getPpCplex();
		
		 reducedCost = ppCplex.getObjective();
		
		 Constraint = rmpModel.getConstraint() ;
		expr = rmpModel.getExpr();
		h = rmpModel.getH();
		x = rmpModel.getX();
		subsets = rmpModel.getSubsets();
		
		r = ppModel.getR();
		sr = ppModel.getSR();
		b = ppModel.getB();
		
	}
	
	
	
	////////////

	public Result solve() throws IloException{
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
					
					reducedCost.setExpr(ppCplex.diff(objExpr,ppCplex.scalProd(r, price)));

					if(ppCplex.solve()){
						
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
							
						//System.out.println("cost " + cost);
						IloColumn column = rmpCplex.column(obj, cost);//Creates and returns a column from the specified objective and value.
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
					
					return null;
				}
			}
				//System.out.println("final relaxed_opt " + relaxed_opt);
			if( relaxed_opt < M ){
				
				//System.out.println("x.getSize() " + x.getSize());
				boolean nonInteger = false;
				for ( int i = 0; i < x.getSize(); i++ ) {
					double cardinality = rmpCplex.getValue(x.getElement(i));
					//System.out.println("cardinality!  "+ cardinality);
					if(!isInteger(cardinality)) {
						System.out.println("non integer cardinality! trying for integer solution ");
						nonInteger = true;
						break;
					}
				}
				if(nonInteger) {
					for ( int i = 0; i < x.getSize(); i++ ) {
						rmpCplex.add(rmpCplex.conversion(x.getElement(i),IloNumVarType.Int));//Adds object to the invoking model.
												//Converts a numeric variable to a specified type.
					}
					/////
					applyBranchAndPrice(rmpCplex, ppCplex, x, h,subsets, b, r);
					/////
				}
				else {
					for ( int i = 0; i < x.getSize(); i++ ) 
						rmpCplex.add(x.getElement(i));
				}
				
			/*	for ( int i = 0; i < x.getSize(); i++ ) {
					/// LP relaxation 
					//System.out.println("cardinality " + rmpCplex.getValue(x.getElement(i)));
					rmpCplex.add(rmpCplex.conversion(x.getElement(i),IloNumVarType.Int));//Adds object to the invoking model.
											//Converts a numeric variable to a specified type.
					


				}*/
				for ( int i = 0; i < h.getSize(); i++ ) {
					rmpCplex.add(rmpCplex.conversion(h.getElement(i),IloNumVarType.Int));
				}
				return new Result(rmpCplex, subsets, ppCplex);
			}
			return new Result(rmpCplex, null, ppCplex);
	}
	
	private void applyBranchAndPrice(IloCplex rmpCplex, IloCplex ppCplex, IloNumVarArray x, IloNumVarArray h,
			ArrayList<SubSet> subsets, IloNumVar[] b, IloNumVar[] r) throws IloException {
		int value = 0;
		IloRange[]   Constraint = new IloRange[x.getSize()*2];
		for ( int i = 0; i < x.getSize(); i++ ) {
			double cardinality = rmpCplex.getValue(x.getElement(i));
			IloObjective reducedCost = ppCplex.getObjective();
			
			if(!isInteger(cardinality)) {
				double part1 = cardinality % 1;
				double part2 = part1 + 1;
				SubSet tempSubSet = subsets.get(i);
				Constraint[value] =  rmpCplex.addGe(x.getElement(i), part2);
				
				boolean result = false;
				boolean infeasible = false;
				if(rmpCplex.solve()){
					result = true;
					double[] price = rmpCplex.getDuals(Constraint);
					//	for(int j = 0 ; j < price.length ; j++)
					//		System.out.println("dual value  "+price[j]);
						
						IloLinearNumExpr objExpr = ppCplex.linearNumExpr();
						for(int j = 0 ; j < b.length ; j++)
							objExpr.addTerm(1 , b[j]);
						
						reducedCost.setExpr(ppCplex.diff(objExpr,ppCplex.scalProd(r, price)));

						if(ppCplex.solve()){
							
							if ( ppCplex.getObjValue() > -RC_EPS ){
								break;
							}

					if( rmpCplex.getObjValue() < M){
						
						//System.out.println("rmpCplex.getObjValue() " + rmpCplex.getObjValue());
						for(int j = 0; j < h.getSize(); j++){
							double hValue = rmpCplex.getValue(h.getElement(i));
							//System.out.println("cardinality " + cardinality);
							if(hValue > 0){
								System.out.println("non zero cardinality " + hValue);
								infeasible = true ;
								break;
							}
						}
					}
					else {
						rmpCplex.remove(Constraint[value]);
						infeasible = true ;
					}
					if(infeasible != false) {
						Constraint[value] =  rmpCplex.addLe(x.getElement(i), part1);
						if(rmpCplex.solve()){
							result = true;
							if( rmpCplex.getObjValue() < M){
								
								//System.out.println("rmpCplex.getObjValue() " + rmpCplex.getObjValue());
								for(int j = 0; j < h.getSize(); j++){
									double hValue = rmpCplex.getValue(h.getElement(i));
									//System.out.println("cardinality " + cardinality);
									if(hValue > 0){
										System.out.println("non zero cardinality " + hValue);
										infeasible = true ;
										break;
									}
								}
							}
							else {
								rmpCplex.remove(Constraint[value]);
								infeasible = true ;
							}
						}
					}
				}
				//rmpCplex.remove(Constraint[value]);
						
			//rmpCplex.add(rmpCplex.conversion(x.getElement(i),IloNumVarType.Int));//Adds object to the invoking model.
									//Converts a numeric variable to a specified type.
			}
			}
			}
	}
	
	private boolean isInteger(double d) {
		//System.out.println(Math.abs(2.5 % 1) <= RC_EPS);
		if(Math.abs(d % 1) <= RC_EPS)
			return true;
		return false;
	}
	
	public class Result {
		IloCplex rmpCplex;
		IloCplex ppCplex;
		ArrayList<SubSet> subsets;
		Result(IloCplex rmpCplex, ArrayList<SubSet> subsets, IloCplex ppCplex){
			this.rmpCplex = rmpCplex;
			this.subsets = subsets;
			this.ppCplex = ppCplex;
 		}
		public IloCplex getRmpCplex() {
			return rmpCplex;
		}
		public IloCplex getPpCplex() {
			return ppCplex;
		}
		public void setRmpCplex(IloCplex rmpCplex) {
			this.rmpCplex = rmpCplex;
		}
		public ArrayList<SubSet> getSubsets() {
			return subsets;
		}
		public void setSubsets(ArrayList<SubSet> subsets) {
			this.subsets = subsets;
		}
	}
}
