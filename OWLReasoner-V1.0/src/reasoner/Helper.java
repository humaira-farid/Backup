package reasoner;

import java.util.List;

import javax.annotation.Nullable;

public class Helper {
	/** brancing level value */
    public static final int INITBRANCHINGLEVELVALUE = 1;
    /** invalid bipolar pointer */
    public static final int BP_INVALID = 0;
    /** top bipolar pointer */
    public static final int BP_TOP = 1;
    /** bottom bipolar pointer */
    public static final int BP_BOTTOM = -1;

    private Helper() {}
    
    public static <T> void resize(List<T> l, int n, @Nullable T filler) {
        if (l.size() > n) {
            while (l.size() > n) {
                l.remove(l.size() - 1);
            }
        } else {
            while (l.size() < n) {
                l.add(filler);
            }
        }
    }
}
