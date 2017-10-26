package reasoner.Dependencies;

import java.util.ArrayList;
import java.util.Collections;

import javax.annotation.Nullable;

public class DependencySet {

	private int branchPoint;
	private ArrayList<Integer> bpList = new ArrayList<Integer>();
	
	protected DependencySet(){
		
	}
	public static DependencySet create() {
        return new DependencySet();
    }
	
	 protected DependencySet(ArrayList<Integer> bpList) {
		 this.bpList.addAll(bpList);
	    }
	 
	 public static DependencySet create(ArrayList<Integer> bpList) {
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
	 
	 public boolean isEmpty() {
	        return this.bpList.size() == 0;
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
	            return;
	        }
	        if (bpList.equals(toAdd.bpList)) {
	            return;
	        }
	        bpList.addAll(toAdd.bpList);
	    }
	public int getBranchPoint() {
		return branchPoint;
	}
	public void setBranchPoint(int branchPoint) {
		this.branchPoint = branchPoint;
	}
	public int getMax() {
		return Collections.max(bpList);
	}
	public void removeLevel(int level) {
		bpList.remove((Integer)level);
		
	}
	
}
