package reasoner.ilp;

import org.semanticweb.owlapi.model.*;

import ilog.concert.*;
import ilog.cplex.*;

public class InequalityGenerator {
public static void main(String[] args) {
	CplexModel();
}
	public static void CplexModel(/*OWLObjectMinCardinality minCard*/) {
		try {
			IloCplex cplex= new IloCplex();
			
			//variables
			IloNumVar h1 = cplex.numVar(0, Double.MAX_VALUE, "h1");
			IloNumVar h2 = cplex.numVar(0, Double.MAX_VALUE, "h2");
		
			//expressions -- min 10h1 + 10 h2
			IloLinearNumExpr objective = cplex.linearNumExpr();
			objective.addTerm(10, h1);
			objective.addTerm(10, h2);
			
			//define objective
			cplex.addMinimize(objective);
			
			//define constraints -- h1  >=1 
			//cplex.addGe(h1, minCard.getCardinality());
			cplex.addGe(h1, 1);
			cplex.addGe(h2, 1);
			//define constraints --  (60h1 + 60h2 >= 8)
			//cplex.addGe(cplex.sum(cplex.prod(60, h1), cplex.prod(60, h2)), 20);
			//define constraints --  (2h1 + 4h2 <= 20)
			//cplex.addLe(cplex.sum(cplex.prod(2, h1), cplex.prod(4, h2)), 20);
			//cplex.solve();
			if(cplex.solve()) {
				System.out.println("obj = "+cplex.getObjValue());
				System.out.println("h1 = "+cplex.getValue(h1));
				System.out.println("h2 = "+cplex.getValue(h2));
			}
			
		}
		catch(IloException e) {
			e.printStackTrace();
		}
	}
}
