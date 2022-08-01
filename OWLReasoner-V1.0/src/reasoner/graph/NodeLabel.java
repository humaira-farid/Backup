package reasoner.graph;

import reasoner.state.SaveState;

public class NodeLabel {

	private static int idcounter = 0;
	private int id;
	private ConceptNDepList cndList ;
	
	public NodeLabel() {
		cndList = new ConceptNDepList();
	    id = getnewId();
	    
	}
	public NodeLabel(NodeLabel nl) {
		this.setCndList(new ConceptNDepList(nl.getCndList()));
	    this.setId(nl.getId());
	    
	}
	
	public int getId() {
		return id;
	}
	public void setId(int id) {
		this.id = id;
	}
	public void setCndList(ConceptNDepList cndList) {
		this.cndList = cndList;
	}
	private static int getnewId() {
        return idcounter++;
    }
	
	public void add(ConceptNDepSet cnd) {
		cndList.add(cnd);
	}
	
    public ConceptNDepList getCndList() {
    		return this.cndList;
    }
    
    
    public void restore(SaveState ss, int level, boolean ilp, boolean merge, boolean disjunction) {
    		cndList.restore(ss.getCc(), level, ilp, merge, disjunction);
    }
   
    
    public void removeLabel() {
		cndList.removeLabel();
	}

    
    public void save(SaveState ss) {
        ss.setCc(cndList.save());
    }

	public void init() {
		cndList.init();
	}
}
