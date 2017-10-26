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
    
    public int getId() {
    	return id;
    }
    
    
    public void init(int level) {
    	 curLevel = level;
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
    
    public Set<OWLClassExpression> getLabel() {
    		return this.nodeLabel;
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
        saves.push(node);
        save(node);
        curLevel = level;
    }

    /**
     * @param restLevel
     *        restLevel
     * @return check if node needs to be restored
     */
    public boolean needRestore(int restLevel) {
        return curLevel > restLevel;
    }

    /**
     * @param level
     *        level number restore node to given level
     */
    public void restore(int level) {
        restore(saves.pop(level));
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
	        // label restore
	        nLabel.restore(nss.getLab(), curLevel);
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

	public static enum NodeType {
        ANONYMOUS,
        NOMINAL,
        BLOCKABLE,
        PROXY;
        

        private NodeType() {
        }
    }

}

