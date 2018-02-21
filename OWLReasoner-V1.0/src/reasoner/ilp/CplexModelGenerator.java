package reasoner.ilp;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLObjectOneOf;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.Multimap;

import ilog.concert.*;
import ilog.cplex.*;


public class CplexModelGenerator {
	IloCplex cplexModel;
	ILPPreprocessor ilpPro;
	Set<QCR> qcrs;
	Set<OWLObjectOneOf> nominals;
	Set<OWLClassExpression> qcrQualifiers = null;
	Set<OWLClassExpression> allQualifiers;
	Map<Integer, QCR> qcrMap;
	
	public CplexModelGenerator(ILPPreprocessor ilpPr) {
		ilpPro = ilpPr;
		qcrs = ilpPro.getQcrs();
		qcrQualifiers = ilpPro.getQcrs().stream().map(qcr -> qcr.qualifier).collect(Collectors.toSet());
		nominals = new HashSet<OWLObjectOneOf>(ilpPro.getNominals());
		allQualifiers = new HashSet<OWLClassExpression>(qcrQualifiers);
		allQualifiers.addAll(nominals);
		qcrMap  = ilpPro.getQCRMap();
		try {
			cplexModel= new IloCplex();
		} catch (IloException e) {
			e.printStackTrace();
		}
	}
	
	
	public void generateCplexModel(/*OWLObjectMinCardinality minCard*/) {
		try {
			
			int tempQN = 0;
			BiMap<OWLClassExpression, Integer> qualifiers = HashBiMap.create();
			for(OWLClassExpression C : allQualifiers){
				qualifiers.put(C, tempQN);
				++tempQN;
			}
			
			
			int totalQCR = qcrs.size();
			int totalNominals = nominals.size();
			int totalVar = totalQCR+totalNominals;
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
		}
	}
	
	public IloCplex getCplexModel() {
		return this.cplexModel;
	}
}
