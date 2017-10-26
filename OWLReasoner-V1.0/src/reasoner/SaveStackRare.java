package reasoner;


import java.util.LinkedList;
import static reasoner.Helper.INITBRANCHINGLEVELVALUE;

public class SaveStackRare {
	/** heap of saved objects */
    private final LinkedList<Restorer> base = new LinkedList<>();
    /** current level */
    private int curLevel;

    /** Default constructor. */
    public SaveStackRare() {
        curLevel = INITBRANCHINGLEVELVALUE;
    }

    /** inclrement current level */
    public void incLevel() {
        ++curLevel;
    }

    /**
     * add a new object to the stack
     * 
     * @param p
     *        p
     */
    public void push(Restorer p) {
        p.setRaresavestackLevel(curLevel);
        base.addLast(p);
    }

    /**
     * get all object from the top of the stack with levels greater or equal
     * LEVEL
     * 
     * @param level
     *        level
     */
   
    public void restore(int level) {
        curLevel = level;
        while (!base.isEmpty()
                && base.getLast().getRaresavestackLevel() > level) {
            // need to restore: restore last element, remove it from stack
            base.getLast().restore();
            base.removeLast();
        }
    }

    /** clear stack */
   
    public void clear() {
        base.clear();
        curLevel = INITBRANCHINGLEVELVALUE;
    }
}
