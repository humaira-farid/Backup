package reasoner;



public abstract class Restorer {
	
	private int raresavestackLevel;

    /** restore an object based on saved information */
   
    public abstract void restore();

    /** @return for accessing the level on TRareSaveStack */
    
    public int getRaresavestackLevel() {
        return raresavestackLevel;
    }

    /**
     * for accessing the level on TRareSaveStack
     * 
     * @param raresavestackLevel
     *        raresavestackLevel
     */
  
    public void setRaresavestackLevel(int raresavestackLevel) {
        this.raresavestackLevel = raresavestackLevel;
    }
}
