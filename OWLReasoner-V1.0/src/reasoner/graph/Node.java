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
	private Set<OWLClassExpression> simpleILPLabel = new HashSet<OWLClassExpression>();
	private Set<OWLClassExpression> backPropagatedLabel = new HashSet<OWLClassExpression>();
	private Multimap<OWLObjectCardinalityRestriction, DependencySet> qLE = HashMultimap.create();
	private int id;
	private int cardinality = 1;
	private List<Edge> neighbour;
	private List<Edge> incomingEdge;
	private List<Edge> outgoingEdge;
	private List<Edge> succEdge;
	private List<Edge> predEdge;
	private Multimap<OWLClassExpression, DependencySet> conceptsDependencies = HashMultimap.create();
	private NodeLabel nLabel;
	private Node blocker;
	private Node pairingNode;
	private boolean dBlocked; // directly blocked
	// private Node blocked;
	private boolean merged = false;
	private List<Node> disjointNodes = new ArrayList<>();
	private boolean reset = false;
	private DependencySet ds;
	protected int curLevel;
	/** pointer to last saved node */
	private SaveList saves = new SaveList();
	private Map<Integer, NodeSaveState> saveMap = new HashMap<>();
	private boolean nomIntro;
	private Set<Node> pairBlockerNodes;
	private Set<Node> pairBlockedNodes;
	private Set<Node> blockedNodes;

	public boolean isPairingNode() {
		if (pairBlockerNodes.size() > 0 || pairBlockedNodes.size() > 0)
			return true;
		else
			return false;
	}

	public int getCardinality() {
		return cardinality;
	}

	public void addDisjointNode(Node n) {
		this.disjointNodes.add(n);
	}

	public List<Node> getDisjointNodes() {
		return this.disjointNodes;
	}

	public List<Edge> getSuccEdges() {
		List<Edge> succEdges = new ArrayList<>();
		for (Edge e : this.getOutgoingEdges()) {
			if (e.isSuccEdge()) {
				succEdges.add(e);
			}
		}
		return succEdges;
	}

	public List<Edge> getPredEdges() {
		List<Edge> predEdges = new ArrayList<>();
		for (Edge e : this.incomingEdge) {
			if (e.isPredEdge()) {
				predEdges.add(e);
			}
		}
		return predEdges;
	}

	public List<Edge> getSuccEdges1() {
		return succEdge;
	}

	public List<Edge> getPredEdges1() {
		return predEdge;
	}

	public void setCardinality(int cardinality) {
		this.cardinality = cardinality;
	}

	public Node(Node.NodeType nodeType, OWLClassExpression nodeLabel, int id, DependencySet ds) {
		this.nodeType = nodeType;
		this.nodeLabel.add(nodeLabel);
		this.neighbour = new ArrayList<>();
		this.outgoingEdge = new ArrayList<>();
		this.incomingEdge = new ArrayList<>();
		this.succEdge = new ArrayList<>();
		this.predEdge = new ArrayList<>();
		this.id = id;
		this.nLabel = new NodeLabel();
		this.ds = ds;
		blocker = null;
		pairBlockerNodes = new HashSet<>();
		pairBlockedNodes = new HashSet<>();
		blockedNodes = new HashSet<>();
	}

	public Node(NodeType nodeType, int id, DependencySet ds) {
		this.nodeType = nodeType;
		this.neighbour = new ArrayList<>();
		this.outgoingEdge = new ArrayList<>();
		this.incomingEdge = new ArrayList<>();
		this.succEdge = new ArrayList<>();
		this.predEdge = new ArrayList<>();
		this.id = id;
		this.nLabel = new NodeLabel();
		this.ds = ds;
		blocker = null;
		pairBlockerNodes = new HashSet<>();
		pairBlockedNodes = new HashSet<>();
		blockedNodes = new HashSet<>();
	}

	public Node() {
		this.id = -1;
	}
// copy constructor
	public Node(Node mergeTo) {
		this.setId(mergeTo.getId());
		this.setNodeType(mergeTo.getNodeType());
		this.setNodeLabel(mergeTo.getNodeLabel()); 
		this.setSimpleLabel(mergeTo.getSimpleLabel());
		this.setSimpleILPLabel(mergeTo.getSimpleILPLabel());
		this.setBackPropagatedLabel(mergeTo.getBackPropagatedLabel()); 
		this.setqLE(mergeTo.getqLE());
		this.setCardinality(mergeTo.getCardinality());
		this.setNeighbour(mergeTo.getNeighbour());
		this.setIncomingEdge(mergeTo.getIncomingEdge());
		this.setOutgoingEdge(mergeTo.getOutgoingEdge());
		this.setSuccEdge(mergeTo.getSuccEdge());
		this.setPredEdge(mergeTo.getPredEdge());
		this.setConceptsDependencies(mergeTo.getConceptsDependencies());
		this.setnLabel(new NodeLabel(mergeTo.getnLabel()));
		this.setBlocker(mergeTo.getBlocker());
		this.setPairingNode(mergeTo.getPairingNode());
		this.setdBlocked(mergeTo.isdBlocked());
		merged = false;
		this.setDisjointNodes(mergeTo.getDisjointNodes());
		reset = false;
		this.setDs(mergeTo.getDs());
		this.setCurLevel(mergeTo.getCurLevel());
		/** pointer to last saved node */
		this.setSaves(mergeTo.getSaves());
		this.setSaveMap(mergeTo.getSaveMap());
		this.setNomIntro(mergeTo.isNomIntro());
		this.setPairBlockerNodes(mergeTo.getPairBlockerNodes());
		this.setPairBlockedNodes(mergeTo.getPairBlockedNodes());
		this.setBlockedNodes(mergeTo.getBlockedNodes());
		
	}

	public int getId() {
		return id;
	}

	public void addSimpleILPLabel(OWLClassExpression ce) {
		this.simpleILPLabel.add(ce);
	}

	public Set<OWLClassExpression> getSimpleILPLabel() {
		return this.simpleILPLabel;
	}

	public void addBackPropagatedLabel(OWLClassExpression ce) {
		this.backPropagatedLabel.add(ce);
	}

	public Set<OWLClassExpression> getBackPropagatedLabel() {
		return this.backPropagatedLabel;
	}

	public DependencySet getDs() {
		return ds;
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

	public void addConcept(ConceptNDepSet cnd) {
		nLabel.add(cnd);
	}

	public Set<OWLClassExpression> getNodeLabel() {
		return nodeLabel;
	}

	public void setNodeLabel(Set<OWLClassExpression> nodeLabel) {
		this.nodeLabel = nodeLabel;
	}

	public List<Edge> getIncomingEdge() {
		return incomingEdge;
	}

	public void setIncomingEdge(List<Edge> incomingEdge) {
		this.incomingEdge = incomingEdge;
	}

	public List<Edge> getOutgoingEdge() {
		return outgoingEdge;
	}

	public void setOutgoingEdge(List<Edge> outgoingEdge) {
		this.outgoingEdge = outgoingEdge;
	}

	public List<Edge> getSuccEdge() {
		return succEdge;
	}

	public void setSuccEdge(List<Edge> succEdge) {
		this.succEdge = succEdge;
	}

	public List<Edge> getPredEdge() {
		return predEdge;
	}

	public void setPredEdge(List<Edge> predEdge) {
		this.predEdge = predEdge;
	}

	public boolean isMerged() {
		return merged;
	}

	public void setMerged(boolean merged) {
		this.merged = merged;
	}

	public int getCurLevel() {
		return curLevel;
	}

	public void setCurLevel(int curLevel) {
		this.curLevel = curLevel;
	}

	public SaveList getSaves() {
		return saves;
	}

	public void setSaves(SaveList saves) {
		this.saves = saves;
	}

	public Map<Integer, NodeSaveState> getSaveMap() {
		return saveMap;
	}

	public void setSaveMap(Map<Integer, NodeSaveState> saveMap) {
		this.saveMap = saveMap;
	}

	public boolean isNomIntro() {
		return nomIntro;
	}

	public void setNomIntro(boolean nomIntro) {
		this.nomIntro = nomIntro;
	}

	public void setSimpleILPLabel(Set<OWLClassExpression> simpleILPLabel) {
		this.simpleILPLabel = simpleILPLabel;
	}

	public void setBackPropagatedLabel(Set<OWLClassExpression> backPropagatedLabel) {
		this.backPropagatedLabel = backPropagatedLabel;
	}

	public void setId(int id) {
		this.id = id;
	}

	public void setNeighbour(List<Edge> neighbour) {
		this.neighbour = neighbour;
	}

	public void setConceptsDependencies(Multimap<OWLClassExpression, DependencySet> conceptsDependencies) {
		this.conceptsDependencies = conceptsDependencies;
	}

	public void setdBlocked(boolean dBlocked) {
		this.dBlocked = dBlocked;
	}

	public void setDisjointNodes(List<Node> disjointNodes) {
		this.disjointNodes = disjointNodes;
	}

	public void setDs(DependencySet ds) {
		this.ds = ds;
	}

	public void setPairBlockerNodes(Set<Node> pairBlockerNodes) {
		this.pairBlockerNodes = pairBlockerNodes;
	}

	public void setPairBlockedNodes(Set<Node> pairBlockedNodes) {
		this.pairBlockedNodes = pairBlockedNodes;
	}

	public void setBlockedNodes(Set<Node> blockedNodes) {
		this.blockedNodes = blockedNodes;
	}

	public List<Edge> getIncomingEdges() {

		List<Edge> e2 = new ArrayList<Edge>();
		for (Edge e : this.incomingEdge) {
			if (e != null)
				e2.add(e);
		}
		this.incomingEdge = e2;
		return e2;
		// return this.incomingEdge.stream().filter(e -> e!=null
		// ).collect(Collectors.toList());
	}

	public List<Edge> getOutgoingEdges() {
		List<Edge> e2 = new ArrayList<Edge>();
		// System.out.println("size "+this.outgoingEdge.size());
		for (Edge e : this.outgoingEdge) {
			// System.out.println(e);
			if (e != null)
				e2.add(e);
		}
		this.outgoingEdge = e2;
		return e2;
		// return this.outgoingEdge.stream().filter(e -> e!=null
		// ).collect(Collectors.toList());
	}

	public boolean hasEdge(Node from, Node to) {
		return findEdge(from, to).isPresent();
	}

	private Optional<Edge> findEdge(Node from, Node to) {
		return neighbour.stream().filter(edge -> edge.isBetween(from, to)).findFirst();
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

	public ConceptNDepList getLabel3() {
		return getnLabel().getCndList();
	}

	public Set<OWLClassExpression> getLabel() {
		Set<OWLClassExpression> concepts = new HashSet<>();
		for (ConceptNDepSet cds : getnLabel().getCndList().getCdSet()) {
			if (cds != null) {
				// System.err.println("inside "+cds.getCe());
				concepts.add(cds.getCe());
			}
		}
		/*
		 * getnLabel().getCndList().getCdSet().forEach(cds -> { if(cds !=null ) { //
		 * System.err.println("inside "+cds.getCe()); concepts.add(cds.getCe()); } });
		 */
		// System.err.println("outside "+concepts);

		return concepts;
	}

	public List<Edge> getNeighbour() {
		return this.neighbour;
	}

	public boolean isBlockingNode() {
		if (this.getBlockedNodes().size() > 0)
			return true;
		return false;

	}

	public Set<Node> getBlockedNodes() {
		return blockedNodes;
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
		return this.nodeType != NodeType.NOMINAL && !this.nomIntro;
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
		if (this.cardinality > 1)
			return false;
		else {
			this.nodeType = NodeType.NOMINAL;
			return true;
		}
	}

	// saving/restoring
	/**
	 * @param newLevel
	 *            newLevel
	 * @return check if node needs to be saved
	 */
	public boolean needSave(int newLevel) {
		// System.err.println("need save? cur level: "+ curLevel + " new level: " +
		// newLevel + " " + (curLevel < newLevel));
		return curLevel < newLevel;
	}

	/**
	 * save node using internal stack
	 * 
	 * @param level
	 *            level
	 */

	public void save(int level) {
	//	System.out.println("node: node " + this.getId() + " level " + level);
		NodeSaveState nodeNSS = new NodeSaveState();
		// saves.push(node);
		// 5 mar
		// saves.push(node);
	//	System.out.println("node: node " + this.getId() + " currlevel " + curLevel);
		save(nodeNSS, level - 1);
		saveMap.put(level - 1, nodeNSS);
		curLevel = level;
		// System.err.println(" changed to " + curLevel);
	}
	public void save(int level, int branchingLevel) {
	//	System.out.println("node: node " + this.getId() + " level " + level + " currlevel " + curLevel);
		NodeSaveState nodeNSS = new NodeSaveState();
		save(nodeNSS, level);
		saveMap.put(level, nodeNSS);
		curLevel = branchingLevel;
	}
	/**
	 * @param resetLevel
	 *            resetLevel
	 * @return check if node needs to be restored
	 */
	public boolean needRestore(int restLevel) {
		// System.out.println("n id "+ this.getId()+" need restore? curr level: "+
		// curLevel + " restore level "+ restLevel);
		return curLevel > restLevel;
	}

	/**
	 * @param level
	 *            level number restore node to given level
	 * @param disjunction 
	 * @param merge 
	 * @param ilp 
	 */

	public void restore(int level, boolean ilp, boolean merge, boolean disjunction) {
	//	System.err.println("Node restore level " + level + " node " + this.getNodeId());
		restore(saveMap.get(level), ilp, merge, disjunction);
	}

	private void save(NodeSaveState nss, int level) {
	//	System.out.println("saving nss level: " + level + "node " + this.getId());
		nss.setCurLevel(level);
		nss.setCardinality(cardinality);
		// System.out.println("neighbour.size() " + neighbour.size());
		nss.setnNeighbours(neighbour.size());
		nss.setnOutgoingEdges(outgoingEdge.size());
		nss.setnIncommingEdges(incomingEdge.size());
		nLabel.save(nss.getLab());
	}

	private void restore(@Nullable NodeSaveState nss, boolean ilp, boolean merge, boolean disjunction) {
		//System.err.println("nss is null " + (nss == null));
		if (nss == null) {
			return;
		}
		// level restore
		curLevel = nss.getCurLevel();

		cardinality = nss.getCardinality();
		nLabel.restore(nss.getLab(), nss.getCurLevel(), ilp, merge, disjunction);

		resize(neighbour, nss.getnNeighbours(), null);
		resize(outgoingEdge, nss.getnOutgoingEdges(), null);
		resize(incomingEdge, nss.getnIncomingEdges(), null);

	}

	public void removeLabel() {
		nLabel.removeLabel();
	}

	public void remove() {
		this.neighbour.clear();
		this.incomingEdge.clear();
		this.outgoingEdge.clear();
	}

	public boolean isBlocked() {
		return blocker != null;
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
		return blocker != null && dBlocked;
	}

	public void setdBlocked(Node blocker) {
		setBlocked(blocker, true);
	}

	public boolean isiBlocked() {
		return blocker != null && !dBlocked;
	}

	public void setiBlocked(Node blocker) {
		setBlocked(blocker, false);
	}

	private void setBlocked(Node blocker, boolean directly) {
		setBlocker(blocker);
		dBlocked = directly;
	}

	public void addBlockedNode(Node blocked) {
		this.blockedNodes.add(blocked);
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
		ANONYMOUS, NOMINAL, BLOCKABLE, NOMINALINTRO, PROXY;

		private NodeType() {
		}
	}

	public void addPairBlockerNode(Node p) {
		this.pairBlockerNodes.add(p);

	}

	public void addPairBlockedNode(Node n) {
		this.pairBlockedNodes.add(n);

	}

	public void setPairingNode(Node x1) {
		this.pairingNode = x1;

	}

	public Node getPairingNode() {
		return pairingNode;
	}

	public Set<Node> getPairBlockerNodes() {
		return pairBlockerNodes;
	}

	public Set<Node> getPairBlockedNodes() {
		return pairBlockedNodes;
	}
    /*public void restore(int level) {
    
	System.err.println("Node restore level "+ level);
	restore(saves.pop(level));
}*/
    /*public void save(int level) {
	NodeSaveState node = new NodeSaveState();
	saves.push(node);
save(node);
 // System.out.println("node: node "+ this.getId() + " currlevel " + curLevel);
curLevel = level;
// System.err.println(" changed to " + curLevel);
}*/
	   /* public Set<OWLClassExpression> getLabel() {
	return getnLabel().getCndList().getConcepts();
}*/
	  /*  public void addEdge(Node node, OWLObjectPropertyExpression edgeLabel) {
    if (hasEdge(node)) {
    	Edge edge = findEdge(node).get();
    	edge.addLabel(edge, edgeLabel);
        return;
    }
    Edge newEdge = new Edge(this, node, edgeLabel);
    edges.add(newEdge);
} */
	
	/*	 private void restore(@Nullable NodeSaveState nss) {
	 System.err.println("before restore node "+ this.getId() +" edges " +outgoingEdge.size());
	    
	 if (nss == null) {
           return;
       }
	 System.out.println("restore node: currlevel "+ curLevel +" restore level"+ nss.getCurLevel()); 
      
       // level restore
       curLevel = nss.getCurLevel();
       cardinality = nss.getCardinality();
       // label restore
       nLabel.restore(nss.getLab(), curLevel);
       
       resize(neighbour, nss.getnNeighbours(), null);
       resize(outgoingEdge, nss.getnOutgoingEdges(), null);
       resize(incomingEdge, nss.getnIncomingEdges(), null);
      
   }*/
	
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
	
/*	 private void restore(@Nullable NodeSaveState nss) {
			System.err.println("nss is null "+ (nss == null));
		        if (nss == null) {
		            return;
		        }
		       
		        // level restore
		        curLevel = nss.getCurLevel();
		       
		        cardinality = nss.getCardinality();
		     //   System.out.println("restore node: currlevel "+ curLevel +" restore level"+ nss.getCurLevel()); 
		        // label restore
		      
		        /// 5 mar 19
		    //   nLabel.restore(nss.getLab(), curLevel);
		        nLabel.restore(nss.getLab(), nss.getCurLevel());
		        ///
		        //nLabel.restore(nss.getLab(), curLevel);
		        // remove new neighbours
		       // if (!options.isUseDynamicBackjumping()) {
		       
		        resize(neighbour, nss.getnNeighbours(), null);
		        resize(outgoingEdge, nss.getnOutgoingEdges(), null);
		        resize(incomingEdge, nss.getnIncomingEdges(), null);
		        
		   //     System.err.println("after restore node "+ this.getId() +" edges " +outgoingEdge.size());
		 	   
		       
		        //} else {
		            for (int j = neighbour.size() - 1; j >= 0; --j) {
		                if (neighbour.get(j).getToNode().curLevel <= curLevel) {
		                    Helper.resize(neighbour, j + 1, null);
		                    break;
		                }
		            }
		            for (int j = outgoingEdge.size() - 1; j >= 0; --j) {
		                if (outgoingEdge.get(j).getToNode().curLevel <= curLevel) {
		                    Helper.resize(outgoingEdge, j + 1, null);
		                    break;
		                }
		            }
		            for (int j = incomingEdge.size() - 1; j >= 0; --j) {
		                if (incomingEdge.get(j).getToNode().curLevel <= curLevel) {
		                    Helper.resize(incomingEdge, j + 1, null);
		                    break;
		                }
		            }
		      //  }
		        // it's cheaper to dirty affected flag than to consistently save nodes
		      //  affected = true;
		        
		    }*/
}

