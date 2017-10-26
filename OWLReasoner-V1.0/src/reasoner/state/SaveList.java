package reasoner.state;

import java.util.LinkedList;


public class SaveList extends LinkedList<NodeSaveState> {



    @Override
    public NodeSaveState pop() {
        if (!isEmpty()) {
            return super.pop();
        }
        return null;
    }

    /**
     * @param level
     *        level
     * @return element from stack with given level
     */
   
    public NodeSaveState pop(int level) {
    	NodeSaveState p = isEmpty() ? null : peek();
        while (p != null && p.level() > level) {
            this.pop();
            p = peek();
        }
        // here p==head and either both == NULL or points to proper element
        if (p != null) {
            this.pop();
        }
        return p;
    }
}
