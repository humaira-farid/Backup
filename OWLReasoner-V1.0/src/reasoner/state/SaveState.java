package reasoner.state;

public class SaveState {
	private int cc;

    /** Default constructor. */
    public SaveState() {
       
        cc = Integer.MAX_VALUE;
    }

    

    /** @return cc */
    public int getCc() {
        return cc;
    }

   

    /**
     * @param cc
     *        cc
     */
    public void setCc(int cc) {
        this.cc = cc;
    }
}
