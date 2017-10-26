package reasoner.state;


public class NodeSaveState {
	 /** saving status of the label */
    private final SaveState lab = new SaveState();
    /** curLevel of the Node structure */
    private int curLevel;
    /** amount of neighbours */
    private int nNeighbours;
	private int nOutgoingEdges;
	private int nIncomingEdges;

    /** @return level of a saved node */
    public int level() {
        return curLevel;
    }

    /** @return save state label */
    public SaveState getLab() {
        return lab;
    }

    /** @return current level */
    public int getCurLevel() {
        return curLevel;
    }

    /** @return neighbors */
    public int getnNeighbours() {
        return nNeighbours;
    }

    /**
     * @param curLevel
     *        curLevel
     */
    public void setCurLevel(int curLevel) {
        this.curLevel = curLevel;
    }

    /**
     * @param nNeighbours
     *        nNeighbours
     */
    public void setnNeighbours(int nNeighbours) {
    	 	this.nNeighbours = nNeighbours;
    }
    public void setnOutgoingEdges(int nOutgoingEdges) {
	 	this.nOutgoingEdges = nOutgoingEdges;
    }
    public int getnOutgoingEdges() {
	 	return this.nOutgoingEdges;
    }
    public void setnIncommingEdges(int nIncomingEdges) {
	 	this.nIncomingEdges = nIncomingEdges;
    }
    public int getnIncomingEdges() {
	 	return this.nIncomingEdges;
    }
}
