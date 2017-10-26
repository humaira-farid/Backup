package reasoner.state;

public class CGSaveState {
	 /** number of valid nodes */
    private int nNodes = 0;
    /** end pointer of saved nodes */
    private int sNodes = 0;
    /** number of used edges */
    private int nEdges = 0;

    /** @return nNodes */
    public int getnNodes() {
        return nNodes;
    }

    /**
     * @param nNodes
     *        nNodes
     */
    public void setnNodes(int nNodes) {
        this.nNodes = nNodes;
    }

    /** @return s nodes */
    public int getsNodes() {
        return sNodes;
    }

    /**
     * @param sNodes
     *        sNodes
     */
    public void setsNodes(int sNodes) {
        this.sNodes = sNodes;
    }

    /** @return n edges */
    public int getnEdges() {
        return nEdges;
    }

    /**
     * @param nEdges
     *        nEdges
     */
    public void setnEdges(int nEdges) {
        this.nEdges = nEdges;
    }

    
    public String toString() {
        return "CGSaveState (" + nNodes + ',' + nEdges + ',' + sNodes + ')';
    }
}
