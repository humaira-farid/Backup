package reasoner.graph; 

import java.util.*;

import javax.annotation.Nullable;

import org.semanticweb.owlapi.model.*;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;

import reasoner.Dependencies.DependencySet;
import reasoner.state.NodeSaveState;
import reasoner.state.SaveList;
import reasoner.Helper;
import static reasoner.Helper.*;
public class Node implements Cloneable {
	
	private NodeType nodeType;
	private Set<OWLClassExpression> nodeLabel = new HashSet<OWLClassExpression>();
	private Set<OWLClassExpression> simpleLabel = new HashSet<OWLClassExpression>();
	private Multimap<OWLObjectCardinalityRestriction, DependencySet> qLE = HashMultimap.create();
	private final int id;
	private int cardinality = 1;
    private List<Edge> neighbour;
    private List<Edge> incomingEdge; 
    private List<Edge> outgoingEdge;
    private List<Edge> succEdge; 
    private List<Edge> predEdge;
    private Multimap<OWLClassExpression, DependencySet> conceptsDependencies = HashMultimap.create();
    private NodeLabel nLabel;
    private Node blocker;
    private boolean dBlocked; // directly blocked
    private Node blocked;
    private boolean merged = false;
    private List<Node> disjointNodes = new ArrayList<>();
    private boolean reset = false;
    
    protected int curLevel;
  
    /** pointer to last saved node */
    private final SaveList saves = new SaveList();
    private Map<Integer, NodeSaveState> saveMap = new HashMap<>();
	private boolean nomIntro;
    
    
	public int getCardinality() {
		return cardinality;
	}
    public void addDisjointNode(Node n){
    		this.disjointNodes.add(n);
    }
    public List<Node> getDisjointNodes(){
		return this.disjointNodes;
    }
    public List<Edge> getSuccEdges(){
    		List<Edge> succEdges = new ArrayList<>();
    		for(Edge e : this.getOutgoingEdges()) {
    			if(e.isSuccEdge()) {
    				succEdges.add(e);
    			}
    		}
    		return succEdges;
    }
    public List<Edge> getPredEdges(){
    	 	List<Edge> predEdges = new ArrayList<>();
    		for(Edge e : this.incomingEdge) {
			if(e.isPredEdge()) {
				predEdges.add(e);
			}
		}
		return predEdges;
    }
    public List<Edge> getSuccEdges1(){
		return succEdge;
    }
    public List<Edge> getPredEdges1(){
    		return predEdge;
    }
	public void setCardinality(int cardinality) {
		this.cardinality = cardinality;
	}

	public Node(Node.NodeType nodeType, OWLClassExpression nodeLabel, int id) {
        this.nodeType = nodeType;
        this.nodeLabel.add(nodeLabel);
        this.neighbour = new ArrayList<>();
        this.outgoingEdge = new ArrayList<>();
        this.incomingEdge = new ArrayList<>();
        this.succEdge = new ArrayList<>();
        this.predEdge = new ArrayList<>();
        this.id = id;
        this.nLabel = new NodeLabel();
        blocker = null;
        blocked = null;
    }
    
    public Node(NodeType nodeType, int id) {
    		this.nodeType = nodeType;
        this.neighbour = new ArrayList<>();
        this.outgoingEdge = new ArrayList<>();
        this.incomingEdge = new ArrayList<>();
        this.succEdge = new ArrayList<>();
        this.predEdge = new ArrayList<>();
        this.id = id;
        this.nLabel = new NodeLabel();
        blocker = null;
        blocked = null;
	}
  /*  public Node(Node n) {
        this.nodeType = n.getNodeType();
        this.nodeLabel = n.getLabel();
        this.neighbour = n.getNeighbour();
        this.outgoingEdge = n.getOutgoingEdges();
        this.incomingEdge = n.getIncomingEdges();
        this.succEdge = new ArrayList<>();
        this.predEdge = new ArrayList<>();
        this.id = n.getId();
        this.nLabel = n.getnLabel();
        blocker = n.getBlocker();
        blocked = n.getBlocked();
    }*/
	public int getId() {
    	return id;
    }

    public boolean isReset() {
		return reset;
	}

	public void setReset(boolean reset) {
		this.reset = reset;
	}

	public boolean getMergeStatus() {
    	 return this.merged;
    }
    public void setNodeMerged() {
    	 this.merged = true;
    }
    public void setNodeUnmerged() {
    	 this.merged = false;
    }

	public NodeType getNodeType() {
		return nodeType;
	}

	public void setNodeType(NodeType nodeType) {
		this.nodeType = nodeType;
	}

    public void init(int level) {
    	 curLevel = level;
    	 saves.clear();
    	 saveMap.clear();
    	 neighbour.clear();
    	 nLabel.init();
    }
	
  /*  public void addEdge(Node node, OWLObjectPropertyExpression edgeLabel) {
        if (hasEdge(node)) {
        	Edge edge = findEdge(node).get();
        	edge.addLabel(edge, edgeLabel);
            return;
        }
        Edge newEdge = new Edge(this, node, edgeLabel);
        edges.add(newEdge);
    } */
    
    public void addConcept(ConceptNDepSet cnd) {
    		nLabel.add(cnd);
    }
   
    public List<Edge> getIncomingEdges(){
    	 return this.incomingEdge;
    }
    public List<Edge> getOutgoingEdges(){
   	 return this.outgoingEdge;
   }
    
    public boolean hasEdge(Node from, Node to) {
        return findEdge(from, to).isPresent();
    }
    
    private Optional<Edge> findEdge(Node from, Node to) {
        return neighbour.stream()
                .filter(edge -> edge.isBetween(from, to))
                .findFirst();
    }
	
    
    public void addLabel(OWLClassExpression OWLClassExpression) {
    	this.nodeLabel.add(OWLClassExpression);
    }
    public void removeLabel(OWLClassExpression OWLClassExpression) {
    	this.nodeLabel.remove(OWLClassExpression);
    }
    
    public Set<OWLClassExpression> getLabel2() {
    		return this.nodeLabel;
    }
   /* public Set<OWLClassExpression> getLabel() {
    		return getnLabel().getCndList().getConcepts();
    }*/
    public ConceptNDepList getLabel3() {
		return getnLabel().getCndList();
    }
    public Set<OWLClassExpression> getLabel() {
    	Set<OWLClassExpression> concepts = new HashSet<>();
    	getnLabel().getCndList().getCdSet().forEach(cds -> {
	    		if(cds !=null ) {
	    		//	System.err.println("inside "+cds.getCe());
	    			concepts.add(cds.getCe());
	    		}
    		});
   // 	System.err.println("outside "+concepts);
		
		return concepts;
    }
    public List<Edge> getNeighbour() {
    		return this.neighbour;
    }
    
    public boolean isBlockingNode() {
    		if(blocked!=null)
    			return true;
    		return false;
    			
    }
    public Set<Node> getNodeAncestors(Node node) {
        Set<Node> ans = new HashSet<Node>();
        for (Edge edge : node.getIncomingEdges()) {
            ans.add(edge.getFromNode());
        }
        return ans;
    }

    public int getNodeId() {
    		return this.id;
    }
    public Multimap<OWLClassExpression, DependencySet> getConceptsDependencies() {
		return conceptsDependencies;
	}

	public void setConceptsDependencies(OWLClassExpression ce, DependencySet ds) {
		this.conceptsDependencies.put(ce, ds);
	}
	public NodeLabel getnLabel() {
		return nLabel;
	}

	public void setnLabel(NodeLabel nLabel) {
		this.nLabel = nLabel;
	}
	
	public boolean isBlockableNode() {
		return this.nodeType != NodeType.NOMINAL;
	}
	
	public boolean isNominalNode() {
		return this.nodeType == NodeType.NOMINAL;
	}
	public boolean isNINode() {
		return this.nomIntro;
	}
	public void makeNINode() {
		 this.nomIntro = true;
	}
	public boolean makeNominalNode() {
		if(this.cardinality>1)
			return false;
		else {
			this.nodeType = NodeType.NOMINAL;
			return true;
		}
	}
	// saving/restoring
    /**
     * @param newLevel
     *        newLevel
     * @return check if node needs to be saved
     */
    public boolean needSave(int newLevel) {
        return curLevel < newLevel;
    }

    /**
     * save node using internal stack
     * 
     * @param level
     *        level
     */
    public void save(int level) {
    	NodeSaveState node = new NodeSaveState();
//      saves.push(node);
    	// 5 mar
    	saves.push(node);
    	//
        save(node);
        saveMap.put(level-1, node);
       // System.out.println("node: node "+ this.getId() + " currlevel " + curLevel);
        curLevel = level;
       // System.err.println(" changed to " + curLevel);
    }

    /**
     * @param resetLevel
     *        resetLevel
     * @return check if node needs to be restored
     */
    public boolean needRestore(int restLevel) {
   // 	System.out.println("n id"+ this.getId()+" need restore? curr level: "+ curLevel + " restore level "+ restLevel);
        return curLevel > restLevel;
    }

    /**
     * @param level
     *        level number restore node to given level
     */
    public void restore(int level) {
       // restore(saves.pop(level));
    	/// 5 mar
   // 	restore(saves.pop(level));
    		restore(saveMap.get(level));
    		///
    }
	
	 private void save(NodeSaveState nss) {
	        nss.setCurLevel(curLevel);
	        nss.setCardinality(cardinality);
	        nss.setnNeighbours(neighbour.size());
	        nss.setnOutgoingEdges(outgoingEdge.size());
	        nss.setnIncommingEdges(incomingEdge.size());
	        nLabel.save(nss.getLab());
	        
	    }
	 private void restore(@Nullable NodeSaveState nss) {
	        if (nss == null) {
	            return;
	        }
	       
	        // level restore
	        curLevel = nss.getCurLevel();
	        cardinality = nss.getCardinality();
	      //  System.out.println("restore node: currlevel "+ curLevel +" restore level"+ nss.getCurLevel()); 
	        // label restore
	      
	        /// 5 mar 19
	    //    nLabel.restore(nss.getLab(), curLevel);
	        nLabel.restore(nss.getLab(), nss.getCurLevel());
	        ///
	        //nLabel.restore(nss.getLab(), curLevel);
	        // remove new neighbours
	       // if (!options.isUseDynamicBackjumping()) {
	       
	        resize(neighbour, nss.getnNeighbours(), null);
	        resize(outgoingEdge, nss.getnOutgoingEdges(), null);
	        resize(incomingEdge, nss.getnIncomingEdges(), null);
	        
	       
	       
	        //} else {
	          //  for (int j = neighbour.size() - 1; j >= 0; --j) {
	            //    if (neighbour.get(j).getArcEnd().curLevel <= curLevel) {
	              //      Helper.resize(neighbour, j + 1, null);
	                //    break;
	               // }
	           // }
	      //  }
	        // it's cheaper to dirty affected flag than to consistently save nodes
	      //  affected = true;
	        
	    }
	public void removeLabel(){
		 nLabel.removeLabel();
	 }
	 
	 public void remove() {
		 this.neighbour.clear();
		 this.incomingEdge.clear();
		 this.outgoingEdge.clear();
	 }
	
	public boolean isBlocked() {
			return blocker!=null;
		} 
	 
	public Node getBlocker() {
		return blocker;
	}

	public void setBlocker(Node blocker) {
		this.blocker = blocker;
	}
	
	public void setUnblock() {
		setBlocked(null, false);
	}

	public boolean isdBlocked() {
		return blocker!=null && dBlocked;
	}

	public void setdBlocked(Node blocker) {
		setBlocked(blocker, true);
	}

	public boolean isiBlocked() {
		return blocker!=null && !dBlocked;
	}

	public void setiBlocked(Node blocker) {
		setBlocked(blocker, false);
	}
	
	private void setBlocked(Node blocker, boolean directly) {
		setBlocker(blocker);
		dBlocked = directly;
	}

	public Node getBlocked() {
		return blocked;
	}

	public void setBlocked(Node blocked) {
		this.blocked = blocked;
	}

	public Set<OWLClassExpression> getSimpleLabel() {
		return simpleLabel;
	}

	public void setSimpleLabel(Set<OWLClassExpression> simpleLabel) {
		this.simpleLabel = simpleLabel;
	}
	public void addSimpleLabel(OWLClassExpression c) {
		this.simpleLabel.add(c);
	}
	public Object clone() throws CloneNotSupportedException {
        return super.clone();
    }

	public Multimap<OWLObjectCardinalityRestriction, DependencySet> getqLE() {
		return qLE;
	}
	public void addqLE(OWLObjectCardinalityRestriction card, DependencySet ds) {
		this.qLE.put(card, ds);
	}
	public void setqLE(Multimap<OWLObjectCardinalityRestriction, DependencySet> qLE) {
		this.qLE = qLE;
	}

	public static enum NodeType {
        ANONYMOUS,
        NOMINAL,
        BLOCKABLE,
        NOMINALINTRO,
        PROXY;
        

        private NodeType() {
        }
    }

}

