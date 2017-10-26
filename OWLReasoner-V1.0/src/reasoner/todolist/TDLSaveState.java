package reasoner.todolist;

import java.util.List;


public class TDLSaveState {
	 /** key queue 0 */
    public int backup0key;
    /** key queue 0 */
    public int backup0value;
    /** key queue 1 */
    public int backup1key;
    /** key queue 1 */
    public int backup1value;
    /** key queue 2 */
    public int backup2key;
    /** key queue 2 */
    public int backup2value;
    /** key queue 3 */
    public int backup3key;
    /** key queue 3 */
    public int backup3value;
    /** key queue 4 */
    public int backup4key;
    /** key queue 4 */
    public int backup4value;
    /** key queue 5 */
    public int backup5key;
    /** key queue 5 */
    public int backup5value;
    /** key queue 6 */
    public int backup6key;
    /** value queue 6 */
    public int backup6value;
    /** save number-of-entries to do */
    protected int noe;
    protected int backupIDsp;
    protected int backupIDep;
    /** save whole array */
    protected List<ToDoEntry> waitingQueue;
    /** save start point of queue of entries */
    protected int sp;
    /** save end point of queue of entries */
    protected int ep;
    /** save flag of queue's consistency */
    protected boolean queueBroken;


    public String toString() {
        return noe + " " + backupIDsp + ',' + backupIDep + ' ' + waitingQueue + ' ' + sp + ' ' + ep + ' ' + queueBroken
            + ' ' + backup0key + ' ' + backup0value + ' ' + backup1key + ' ' + backup1value + ' ' + backup2key + ' '
            + backup2value + ' ' + backup3key + ' ' + backup3value + ' ' + backup4key + ' ' + backup4value + ' '
            + backup5key + ' ' + backup5value + ' ' + backup6key + ' ' + backup6value;
    }
}
