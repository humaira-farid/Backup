package reasoner.graph; 

import static reasoner.Helper.INITBRANCHINGLEVELVALUE;

import java.util.*;
import java.util.stream.Collectors;

import org.semanticweb.owlapi.model.*;

import reasoner.SaveStackRare;
import reasoner.Dependencies.DependencySet;
import reasoner.state.*;
import reasoner.Helper;
import reasoner.RuleEngine;



public class CompletionGraph implements Cloneable {
	private int totalNodes=0; //endUsed

	private static int idcounter = 0;
	List<Node> savedNodes = new ArrayList<>();
	List<Node> copiedNodes = new ArrayList<>();
	Map<Integer, Node> copies = new HashMap<Integer, Node>();
	private int nNodeSaves;
	private int nNodeRestores;
	private Node currNode;
	SaveStack<CGSaveState> stack = new SaveStack<>();
	
	private int branchingLevel;
	private final SaveStackRare rareStack = new SaveStackRare();
	private final List<Edge> ctEdgeHeap = new ArrayList<>();
	private final List<Node> nodeBase;
	RuleEngine re;
	
	public CompletionGraph(RuleEngine r) {
		 nodeBase = new ArrayList<>();
		 branchingLevel = INITBRANCHINGLEVELVALUE;
		 clearStatistics();
		 re = r;
	}
	 
	 public void clearStatistics() {
	        nNodeSaves = 0;
	        nNodeRestores = 0;
	 }
	public Node addNode(Node.NodeType nodeType, OWLClassExpression nodeLabel) {
		 Node node = new Node(nodeType,nodeLabel, getnewId());
		 nodeBase.add(node);
		 node.init(branchingLevel);
		 
		 totalNodes++;
		 return node;
	 }
	public Node addNode(Node.NodeType nodeType) {
		 Node node = new Node(nodeType, getnewId());
		 nodeBase.add(node);
		 node.init(branchingLevel);
		 
		 totalNodes++;
		 return node;
	 }
	private static int getnewId() {
        return idcounter++;
    }
	 public void addConceptToNode(Node n, ConceptNDepSet cnd) {
		 n.addLabel(cnd.getCe());
		 n.addConcept(cnd);
		 checkBlockedStatus(n);
	 }
	
	 public void checkBlockedStatus(Node n) {
		if(n.isBlocked()) {
			n.setUnblock();
			re.processUnblockedNode(n);
		}
		else if(n.isBlockingNode()) {
			Node blocked = n.getBlocked();
			n.setBlocked(null);
			blocked.setUnblock();
			re.processUnblockedNode(n);
		}
		else {
			Node blocker = findAnywhereBlocker(n);
			if(blocker!=null)
				setNodeBlocked(n, blocker);
				
		}
	}

	public Edge addEdge(Node from, Node to, OWLObjectPropertyExpression edgeLabel, DependencySet ds) {
		Edge edge = new Edge(from, to, edgeLabel, ds);
		Edge invEdge = new Edge(to, from, edgeLabel.getInverseProperty(), ds);
		this.ctEdgeHeap.add(edge);
		this.ctEdgeHeap.add(invEdge);
		from.getNeighbour().add(edge);
		from.getOutgoingEdges().add(edge);
		from.getIncomingEdges().add(invEdge);
		//to.getNeighbour().add(invEdge);
		saveNode(from, branchingLevel);
        saveNode(to, branchingLevel);
		to.getIncomingEdges().add(edge);
		to.getOutgoingEdges().add(invEdge);
		return edge;
	 }
	public Edge addEdge(Node from, Node to, Set<OWLObjectPropertyExpression> edgeLabel, DependencySet ds) {
		Edge edge = new Edge(from, to, edgeLabel, ds);
		Set<OWLObjectPropertyExpression> invRoles = new HashSet<>(edgeLabel.stream().map(r -> r.getInverseProperty()).collect(Collectors.toSet()));
		Edge invEdge = new Edge(to, from, invRoles, ds);
		this.ctEdgeHeap.add(edge);
		this.ctEdgeHeap.add(invEdge);
		from.getNeighbour().add(edge);
		from.getOutgoingEdges().add(edge);
		from.getIncomingEdges().add(invEdge);
		//to.getNeighbour().add(invEdge);
		saveNode(from, branchingLevel);
        saveNode(to, branchingLevel);
		to.getIncomingEdges().add(edge);
		to.getOutgoingEdges().add(invEdge);
		return edge;
	 }
	 
	 public Edge getEdge(Node from, OWLClassExpression nodeLabel, OWLObjectPropertyExpression edgeLabel) {
		 for(Edge e : from.getOutgoingEdges()) {
			 if(e.getLabel().contains(edgeLabel)) {
				 if(e.getToNode().getLabel().contains(nodeLabel))
					 return e;
			 }
		 }
		 return null;
	 }
	 public Edge getEdge(Node from, Set<OWLClassExpression> nodeLabel, Set<OWLObjectPropertyExpression> edgeLabel) {
		 for(Edge e : from.getOutgoingEdges()) {
			 if(e.getLabel().containsAll(edgeLabel)) {
				 if(e.getToNode().getLabel().containsAll(nodeLabel))
					 return e;
			 }
		 }
		 return null;
	 }
	 public Set<Edge> getEdge(Node from, OWLObjectPropertyExpression edgeLabel) {
		 Set<Edge> edges = new HashSet<>();
		 from.getOutgoingEdges().stream().filter(e -> e.getLabel().contains(edgeLabel)).forEach(e -> edges.add(e));
			
		 return edges;
	 }

	public int getTotalNodes() {
		return totalNodes;
	}

	public void setTotalNodes(int totalNodes) {
		this.totalNodes = totalNodes;
	}
	public Node findAnywhereBlocker(Node n) {
		saveNode(n, branchingLevel);
		if(n.isBlockableNode()) {
			for(int i = 0 ; i < nodeBase.size() && i < n.getId(); i++) {
				if(nodeBase.get(i).getLabel().equals(n.getLabel()))
					return nodeBase.get(i);
			}
		}
		return null;
	}
	
	public void setNodeBlocked(Node node, Node blocker) {
		setNodeDBlocked(node, blocker);
	}
	
	private void setNodeDBlocked(Node node, Node blocker) {
        node.setdBlocked(blocker);
       // propagateIBlockedStatus(node, blocker);
        removeTree(node);
    }
	private void removeTree(Node n) {
		n.getNeighbour().stream().filter(q -> q.getToNode().isBlockableNode()).forEach(q -> removeNode(n, q.getToNode(), q));
	}
	private void removeNode(Node from, Node to, Edge q) {
		if(to.isNominalNode())
			return;
		else {
			Node p = to;
			to.remove();
			to = null;
			from.getNeighbour().remove(q);
			removeTree(p);
		}
	}

	private void propagateIBlockedStatus(Node node, Node blocker) {
       
		 node.getNeighbour().stream().filter(q -> q.getToNode().isBlockableNode() && !q.isIBlocked()).forEach(q -> setNodeIBlocked(q.getToNode(), blocker));
    }
	
	private void setNodeIBlocked(Node node, Node blocker) {
        // nominal nodes can't be blocked
        if (node.isNominalNode()) {
            return;
        }
       // node.clearAffected();
        // already iBlocked -- nothing changes
        if (node.isiBlocked() && node.getBlocker().equals(blocker)) {
            return;
        }
        // prevent node to be IBlocked due to reflexivity
        if (node.equals(blocker)) {
            return;
        }
        node.setiBlocked(blocker);
        propagateIBlockedStatus(node, blocker);
    }
	
	 public void saveNode(Node node, int level) {
	        if (node.needSave(level)) {
	            node.save(level);
	            savedNodes.add(node);
	            ++nNodeSaves;
	        }
	    }
	 
	 private void restoreNode(Node node, int level) {
	        if (node.needRestore(level)) {
	            node.restore(level);
	            ++nNodeRestores;
	        }
	    }
	 
	 public void save() {
	        CGSaveState s = new CGSaveState();
	        stack.push(s);
	        s.setnNodes(totalNodes);
	        s.setsNodes(savedNodes.size());
	        s.setnEdges(ctEdgeHeap.size());
	        rareStack.incLevel();
	        ++branchingLevel;
	    }
	 public void restore(int level) {
	        assert level > 0;
	        branchingLevel = level;
	        rareStack.restore(level);
	        CGSaveState s = stack.pop(level);
	        totalNodes = s.getnNodes();
	        int nSaved = s.getsNodes();
	        if (totalNodes < Math.abs(savedNodes.size() - nSaved)) {
	            // it's cheaper to restore all nodes
	            nodeBase.stream().limit(totalNodes).forEach(p -> restoreNode(p, level));
	        } else {
	            for (int i = nSaved; i < savedNodes.size(); i++) {
	                if (savedNodes.get(i).getId() < totalNodes) {
	                    // don't restore nodes that are dead anyway
	                    restoreNode(savedNodes.get(i), level);
	                }
	            }
	        }
	        Helper.resize(savedNodes, nSaved, null);
	        Helper.resize(ctEdgeHeap, s.getnEdges(), null);
	    }

	public Node getCurrNode() {

		return currNode;
	}

	public void setCurrNode(Node currNode) {

			this.currNode = currNode;
		
	}
	
	public Object clone() throws CloneNotSupportedException {
        return super.clone();
    }
	
	public Node findNominalNode(OWLClassExpression ce) {
		Node n = null;
		if(nodeBase.stream().anyMatch(node -> node.getLabel().contains(ce))) {

			n = nodeBase.stream().filter(node -> node.getLabel().contains(ce)).iterator().next();
			//System.out.println("node id : "+n.getId() + "expression: "+ce);
		}
		return n;
	}

	public void copyNodes() {
		//System.out.println("saved nodes : "+nodeBase.size());
	//	nodeBase.stream().forEach(n-> System.out.println("node id : "+n.getId() +"neighbours : "+n.getNeighbour().size()));
		nodeBase.stream().forEach(n -> {
			try {
				copies.put(n.getId(), (Node)n.clone());
			} catch (CloneNotSupportedException e) {
				e.printStackTrace();
			}
		});
		
	}
	
	public void restoreNode(Node n) {
		//System.out.println("node id : "+n.getId()+" node neighbours "+ n.getNeighbour().size());
		Node node = copies.get(n.getId());
		//System.out.println("restored node id : "+node.getId()+" node neighbours "+ node.getNeighbour().size());
		this.setCurrNode(node);
	}
}

