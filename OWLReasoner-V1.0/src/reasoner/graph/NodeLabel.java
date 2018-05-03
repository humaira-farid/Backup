package reasoner.graph;

import reasoner.state.SaveState;

public class NodeLabel {

	private static int idcounter = 0;
	private final int id;
	private final ConceptNDepList cndList ;
	
	public NodeLabel() {
		cndList = new ConceptNDepList();
	    id = getnewId();
	    
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
    
    
    public void restore(SaveState ss, int level) {
    		cndList.restore(ss.getCc(), level);
    }

    public void save(SaveState ss) {
        ss.setCc(cndList.save());
    }

	public void init() {
		cndList.init();
		
	}
}
