package reasoner.Dependencies;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import javax.annotation.Nullable;

import org.semanticweb.owlapi.model.OWLClassExpression;

public class DependencySet {
	
	private OWLClassExpression ce = null;
	private OWLClassExpression ceNNF = null;
	private int branchPoint;
	private Set<Integer> bpList = new HashSet<Integer>();
	
	protected DependencySet(){
		
	}
	public static DependencySet create() {
        return new DependencySet();
    }
	
	 protected DependencySet(Set<Integer> bpList) {
		 this.bpList.addAll(bpList);
	    }
	 
	 public static DependencySet create(Set<Integer> bpList) {
	        return new DependencySet(bpList);
	    }
	 protected DependencySet(int i) {
		 branchPoint = i;
		 this.bpList.add(i);
	    }
	 
	 public static DependencySet create(int i) {
	        return new DependencySet(i);
	    }
	 
	 public static DependencySet create(@Nullable DependencySet dep) {
	        if (dep == null) {
	            return create();
	        }
	        return new DependencySet(dep.bpList);
	    }
	 public static DependencySet plus(@Nullable DependencySet ds1, @Nullable DependencySet ds2) {
	        if (ds1 == null && ds2 == null) {
	            return new DependencySet();
	        }
	        if (ds1 == null || ds1.isEmpty()) {
	            if (ds2 == null || ds2.isEmpty()) {
	                return new DependencySet();
	            }
	            return new DependencySet(ds2.bpList);
	        }
	        if (ds2 == null || ds2.isEmpty()) {
	            return new DependencySet(ds1.bpList);
	        }
	        DependencySet toReturn = new DependencySet();
	        toReturn.add(ds1);
	        toReturn.add(ds2);
	        return toReturn;
	    }
	 public static DependencySet update(@Nullable DependencySet ds1, @Nullable DependencySet ds2) {
	        if (ds1 == null || ds2 == null) {
	            return new DependencySet();
	        }
	        if(ds1.isEmpty() || ds2.isEmpty()) {
	        		return new DependencySet();
	        }
	        
	        DependencySet toReturn = new DependencySet();
	        toReturn.add(ds1);
	        toReturn.add(ds2);
	        return toReturn;
	    }
	 public boolean isEmpty() {
	        return this.bpList.size() == 0;
	    }
	 public Set<Integer> getbpList(){
		 return this.bpList;
	 }
	 public void clear() {
		 this.bpList.clear();
	 }
	 
	 public void add(@Nullable DependencySet toAdd) {
	        if (toAdd == null || toAdd.isEmpty()) {
	            return;
	        }
	        if (bpList.size() == 0) {
	        	bpList = toAdd.bpList;
	        	branchPoint = getMax();
	            return;
	        }
	        if (bpList.equals(toAdd.bpList)) {
	            return;
	        }
	        bpList.addAll(toAdd.bpList);
	        branchPoint = getMax();
	    }
	public int getBranchPoint() {
		return branchPoint;
	}
	public void setBranchPoint(int branchPoint) {
		this.branchPoint = branchPoint;
	}
	public int getMax() {
		if(bpList.isEmpty())
			return 0;
		return Collections.max(bpList);
	}
	public void removeLevel(int level) {
		bpList.remove((Integer)level);
		branchPoint = getMax();
		
	}
	public OWLClassExpression getCe() {
		return ce;
	}
	public void setCe(OWLClassExpression ce) {
		this.ce = ce;
	}
	public OWLClassExpression getCeNNF() {
		return ceNNF;
	}
	public void setCeNNF(OWLClassExpression ceNNF) {
		this.ceNNF = ceNNF;
	}
	
	
	
}
