package reasoner.graph; 

import java.util.*;

import javax.annotation.Nullable;

import org.semanticweb.owlapi.model.*;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;

import reasoner.Dependencies.DependencySet;
import reasoner.state.NodeSaveState;
import reasoner.state.SaveList;
import static reasoner.Helper.*;
public class Node implements Cloneable {
	
	private NodeType nodeType;
	private Set<OWLClassExpression> nodeLabel = new HashSet<OWLClassExpression>();
	private Set<OWLClassExpression> simpleLabel = new HashSet<OWLClassExpression>();
	private Multimap<OWLObjectCardinalityRestriction, DependencySet> qLE = HashMultimap.create();
	private final int id;
    private List<Edge> neighbour;
    private List<Edge> incomingEdge; 
    private List<Edge> outgoingEdge;
    private Multimap<OWLClassExpression, DependencySet> conceptsDependencies = HashMultimap.create();
    private NodeLabel nLabel;
    private Node blocker;
    private boolean dBlocked; // directly blocked
    private Node blocked;
    
    
    protected int curLevel;
  
    /** pointer to last saved node */
    private final SaveList saves = new SaveList();
    private Map<Integer, NodeSaveState> saveMap = new HashMap<>();
    
    public Node(Node.NodeType nodeType, OWLClassExpression nodeLabel, int id) {
        this.nodeType = nodeType;
        this.nodeLabel.add(nodeLabel);
        this.neighbour = new ArrayList<>();
        this.outgoingEdge = new ArrayList<>();
        this.incomingEdge = new ArrayList<>();
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
        this.id = n.getId();
        this.nLabel = n.getnLabel();
        blocker = n.getBlocker();
        blocked = n.getBlocked();
    }*/
	public int getId() {
    	return id;
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
    public Set<OWLClassExpression> getLabel() {
    		return getnLabel().getCndList().getConcepts();
    }
    public ConceptNDepList getLabel3() {
		return getnLabel().getCndList();
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
	public void makeNominalNode() {
		this.nodeType = NodeType.NOMINAL;
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
    		restore(saveMap.get(level));
    }
	
	 private void save(NodeSaveState nss) {
	        nss.setCurLevel(curLevel);
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
	      //  System.out.println("restore node: currlevel "+ curLevel +" restore level"+ nss.getCurLevel()); 
	        // label restore
	        nLabel.restore(nss.getLab(), nss.getCurLevel());
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
        PROXY;
        

        private NodeType() {
        }
    }

}

