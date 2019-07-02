package reasoner.graph; 

import static reasoner.Helper.INITBRANCHINGLEVELVALUE;

import java.util.*;
import org.semanticweb.owlapi.model.*;
import reasoner.SaveStackRare;
import reasoner.Dependencies.DependencySet;
import reasoner.state.*;
import reasoner.Configuration;
import reasoner.Helper;
import reasoner.RuleEngine;



public class CompletionGraph implements Cloneable {
	private int totalNodes=0; //endUsed
	private int lastRestorednNodes=0;
	private static int idcounter = 0;
	List<Node> savedNodes = new ArrayList<>();
	List<Node> copiedNodes = new ArrayList<>();
	Map<Integer, Node> copies = new HashMap<Integer, Node>();
	private int nNodeSaves;
	private int nNodeRestores;
	private Node currNode;
	SaveStack<CGSaveState> stack = new SaveStack<>();
	private Map<Integer, CGSaveState> saveMap = new HashMap<>();
	private Node x1 = null;
	private Node x2 = null;
	private Node y1 = null;
	private Node y2 = null;
	private int branchingLevel;
	private final SaveStackRare rareStack = new SaveStackRare();
	private final List<Edge> ctEdgeHeap = new ArrayList<>();
	private final List<Node> nodeBase;
	RuleEngine re;
	Configuration config;
	
	public CompletionGraph(RuleEngine r) {
		 nodeBase = new ArrayList<>();
		 branchingLevel = INITBRANCHINGLEVELVALUE;
		 clearStatistics();
		 re = r;
	}
	 
	 public CompletionGraph(RuleEngine r, Configuration config) {
		 nodeBase = new ArrayList<>();
		 branchingLevel = INITBRANCHINGLEVELVALUE;
		 clearStatistics();
		 re = r;
		 this.config = config;
	}

	public void clearStatistics() {
	        nNodeSaves = 0;
	        nNodeRestores = 0;
	 }
	public Node addNode(Node.NodeType nodeType, OWLClassExpression nodeLabel) {
		 Node node = new Node(nodeType,nodeLabel, getnewId());
		 node.init(branchingLevel);
		 //System.err.println("ADD NODE: " + node.getId() +" bp "+ branchingLevel);
		 nodeBase.add(node); 
		 ++totalNodes;
		 return node;
	 }
	public Node addNode(Node.NodeType nodeType) {
		 Node node = new Node(nodeType, getnewId());
		 node.init(branchingLevel);
		// System.err.println("ADD NODE: " + node.getId() +" bp "+ branchingLevel);
		 nodeBase.add(node);
		 ++totalNodes;
		 return node;
	 }
	private static int getnewId() {
        return idcounter++;
    }
	public int getCurrentId() {
        return idcounter;
    }
	 public void addConceptToNode(Node n, ConceptNDepSet cnd) {
		 saveNode(n, branchingLevel);
		 n.addLabel(cnd.getCe());
		 n.addConcept(cnd);
		 checkBlockedStatus(n);
	 }
	public void unblockNode(Node node) {
		node.setUnblock();
		Node blocker = node.getBlocker();
		if(blocker !=null)
			blocker.setBlocked(null);
		re.processUnblockedNode(node);
		unblockNodeChildren(node);
	}
	 private void unblockNodeChildren(Node node) {
		 node.getNeighbour().stream().filter(q -> q.unblockable())
         // all of them are i-blocked
         .forEach(q -> unblockNode(q.getToNode()));
		
	}

	public void checkBlockedStatus(Node n) {
		if(n.isBlocked()) {
			unblockNode(n);
			
		}
		else if(n.isBlockingNode()) {
			Node blocked = n.getBlocked();
			n.setBlocked(null);
			blocked.setUnblock();
			//re.processUnblockedNode(n);
			re.processUnblockedNode(blocked);
		}
		else {
			Node blocker = findBlocker(n);
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
		to.getNeighbour().add(invEdge);
		saveNode(from, branchingLevel);
        saveNode(to, branchingLevel);
		to.getIncomingEdges().add(edge);
		to.getOutgoingEdges().add(invEdge);
		edge.setSuccEdge(true);
		invEdge.setSuccEdge(false);
		return edge;
	 }
/*	public Edge addEdge(Node from, Node to, Set<OWLObjectPropertyExpression> edgeLabel, DependencySet ds, Set<OWLObjectPropertyExpression> invEdgeLabel) {
		// System.err.println("edge label to be added " + edgeLabel);
		Edge edge = new Edge(from, to, edgeLabel, ds);
		//Set<OWLObjectPropertyExpression> invRoles = new HashSet<>(edgeLabel.stream().map(r -> r.getInverseProperty()).collect(Collectors.toSet()));
		//Set<OWLObjectPropertyExpression> invRoles = new HashSet<>();
		//edgeLabel.stream().forEach(r -> invRoles.add(r.getInverseProperty()));
		//System.err.println("inverse roles " + invRoles);
		Edge invEdge = new Edge(to, from, invEdgeLabel, ds);
		this.ctEdgeHeap.add(edge);
		this.ctEdgeHeap.add(invEdge);
		from.getNeighbour().add(edge);
		from.getOutgoingEdges().add(edge);
		from.getIncomingEdges().add(invEdge);
		//to.getNeighbour().add(invEdge);
		saveNode(from, branchingLevel);
        saveNode(to, branchingLevel);
		to.getIncomingEdges().add(edge);
		//System.err.println("getOutgoingEdges " + to.getOutgoingEdges().size());
		
		to.getOutgoingEdges().add(invEdge);
		//System.err.println("getOutgoingEdges " + to.getOutgoingEdges().size());
		return edge;
	 }*/
	public Edge addEdge(Node from, Node to, Set<OWLObjectPropertyExpression> edgeLabel, DependencySet ds) {
		// System.err.println("edge label to be added " + edgeLabel);
		Edge edge = new Edge(from, to, edgeLabel, ds);
		//Set<OWLObjectPropertyExpression> invRoles = new HashSet<>(edgeLabel.stream().map(r -> r.getInverseProperty()).collect(Collectors.toSet()));
		Set<OWLObjectPropertyExpression> invRoles = new HashSet<>();
		edgeLabel.stream().forEach(r -> invRoles.add(r.getInverseProperty()));
		//System.err.println("inverse roles " + invRoles);
		Edge invEdge = new Edge(to, from, invRoles, ds);
		this.ctEdgeHeap.add(edge);
		this.ctEdgeHeap.add(invEdge);
		from.getNeighbour().add(edge);
		from.getOutgoingEdges().add(edge);
		from.getIncomingEdges().add(invEdge);
		to.getNeighbour().add(invEdge);
		saveNode(from, branchingLevel);
        saveNode(to, branchingLevel);
		to.getIncomingEdges().add(edge);
		//System.err.println("getOutgoingEdges " + to.getOutgoingEdges().size());
		
		to.getOutgoingEdges().add(invEdge);
		//System.err.println("getOutgoingEdges " + to.getOutgoingEdges().size());
		edge.setSuccEdge(true);
		invEdge.setSuccEdge(false);
		return edge;
	 }
	public Edge getEdge(Node from, OWLClassExpression nodeLabel, OWLObjectPropertyExpression edgeLabel) {
		Set<OWLClassExpression> tempNL = new HashSet<>();
		tempNL.add(nodeLabel);
		Set<OWLObjectPropertyExpression> tempEL = new HashSet<>();
		tempEL.add(edgeLabel);
		for(Edge e : from.getOutgoingEdges()) {
			 if(e.getLabel().equals(tempNL)) {
				 if(e.getToNode().getLabel().equals(tempEL))
					 return e;
			 }
		 }
		 return null;
	 }
	 public Edge getEdge(Node from, Set<OWLClassExpression> nodeLabel, Set<OWLObjectPropertyExpression> edgeLabel) {
		 for(Edge e : from.getOutgoingEdges()) {
			 if(e.getLabel().equals(edgeLabel)) {
				 if(e.getToNode().getLabel().equals(nodeLabel))
					 return e;
			 }
		 }
		 return null;
	 }
	 public Edge getEdge(Node from, Node to, Edge edge) {
		 for(Edge e : from.getOutgoingEdges()) {
			 if(e.getToNode().equals(to) && e.getLabel().equals(edge.getLabel())) {
				 return e;
			 }
		 }
		 return null;
	 }
	 public Edge getEdge(Node from, Node to) {
		 for(Edge e : from.getOutgoingEdges()) {
			 if(e != null) {
				 if(e.getToNode().equals(to)) {
					 return e;
				 }
			 }
		 }
		 return null;
	 }
	 public Edge getInvEdge(Node from, Node to) {
		 for(Edge e : to.getOutgoingEdges()) {
			 if(e != null) {
				 if(e.getToNode().equals(from)) {
					 return e;
				 }
			 }
		 }
		 return null;
	 }
	 /**
	  * merge from node into to node
	  * @param from
	  * @param to
	  * @param ds
	  */
	 public void merge(Node from, Node to, DependencySet ds) {
		// 1. For all x: x->FROM make x->TO
		// 2. For all nominal x: FROM->x make TO->x
		 //saveNode(from);
		  Set<Edge> succEdges = new HashSet<>();
		 from.getNeighbour().forEach(q -> {
			 if(q != null) {
	           if(!q.getToNode().equals(to)) { 
	        	   if (q.isPredEdge()) {
	                moveEdge2(to, q, q.isPredEdge(), DependencySet.plus(DependencySet.create(q.getDepSet()), DependencySet.create(ds)));
	               
	            }
	            else if (q.isSuccEdge() && q.getToNode().isNominalNode()) {
	                moveEdge2(to, q, q.isPredEdge(), DependencySet.plus(DependencySet.create(q.getDepSet()), DependencySet.create(ds)));
	               
	            }
	            else if (q.isSuccEdge() && !q.getToNode().isNominalNode()) {
	            		succEdges.add(q);
	            }
	           }
			 }});
		// from.setNodeMerged();
		// for(Edge e : succEdges)
		//	 removeNode(from, e.getToNode(), e);
		/* from.getIncomingEdges().forEach(p -> {
	            if (p.isSuccEdge()) {
	                moveEdge(to, p, p.isPredEdge(), ds);
	            }
	            
	        });
		 from.getOutgoingEdges().forEach(p -> {
	            if (p.isSuccEdge() && p.getToNode().isNominalNode()) {
	                moveEdge(to, p, p.isPredEdge(), ds);
	            }
	            else if (p.isSuccEdge() && !p.getToNode().isNominalNode()) {
	               // purgeEdge(p, to, ds);
	            }
	        });*/
		 
	 }
	 
	 private void moveEdge(Node to, Edge q, boolean isPredEdge, DependencySet ds) {
		if(isPredEdge) {
			Node from = q.getToNode();
			Edge e = getEdge(from, to, q);
			if(e == null) {
				addEdge(from, to, q.getLabel(), ds);
			}
			else
				e.updateDepSet(ds);
		}
		else {
			Node nn = q.getToNode();
			Edge e = getEdge(to, nn, q);
			if(e == null) {
				addEdge(to, nn, q.getLabel(), ds);
			}
			else
				e.updateDepSet(ds);
		}
	}
	 private void moveEdge2(Node to, Edge q, boolean isPredEdge, DependencySet ds) {
			if(isPredEdge) {
				Node from = q.getToNode();
				Edge e = getEdge(from, to);
				if(e == null) {
					addEdge(from, to, q.getLabel(), ds);
				}
				else {
					e.addLabel(q.getLabel());
					e.updateDepSet(ds);
					Edge invE = getInvEdge(from, to);
					if(invE != null)
						q.getLabel().stream().forEach(el -> invE.addLabel(el.getInverseProperty()));
				}
			}
			else {
				Node nn = q.getToNode();
				Edge e = getEdge(to, nn);
				if(e == null) {
					addEdge(to, nn, q.getLabel(), ds);
				}
				else {
					e.addLabel(q.getLabel());
					e.updateDepSet(ds);
					Edge invE = getInvEdge(to, nn);
					if(invE != null)
						q.getLabel().stream().forEach(el -> invE.addLabel(el.getInverseProperty()));
				}
			}
		}

	/*public Edge getEdge(Node from, OWLClassExpression nodeLabel, OWLObjectPropertyExpression edgeLabel) {
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
	 }*/
	 public Edge findEdge(Node from, Set<OWLClassExpression> nodeLabel, Set<OWLObjectPropertyExpression> edgeLabel) {
		 for(Edge e : from.getOutgoingEdges()) {
			// System.out.println("edge label: " +e.getLabel());
			// System.out.println("node label: " +e.getToNode().getLabel());
			// System.out.println("new edge label: " +edgeLabel);
			// System.out.println("new node label: " +nodeLabel);
			 if(e != null) {
				 if(e.getLabel().containsAll(edgeLabel)) {
					 if(nodeLabel.containsAll(e.getToNode().getLabel()))
						 return e;
				 }
			 }
		 }
		 return null;
	 }
	 public Set<Edge> getEdge(Node from, OWLObjectPropertyExpression edgeLabel) {
		 Set<Edge> edges = new HashSet<>();
		// from.getOutgoingEdges().stream().filter(e -> e.getLabel().contains(edgeLabel)).forEach(e -> edges.add(e));
		 for(Edge e : from.getOutgoingEdges()) {
			 if(e != null) {
				 if(e.getLabel().contains(edgeLabel)) {
					 edges.add(e);
				 }
			 }
		 }
		 return edges;
	 }

	public int getTotalNodes() {
		return totalNodes;
	}

	public void setTotalNodes(int totalNodes) {
		this.totalNodes = totalNodes;
	}
	public Node findBlocker(Node n) {
		Node blocker = null;
		if(config.isUsePairwiseBlocking()) 
			blocker = findPairwiseBlocker(n);
		else 
			blocker = findEqualityBlocker(n);
		
		if(blocker != null) {
			if(!hasNominalInPath(blocker, n))
				return blocker;
		}
		return null;
			
		
	}
	public Node findPairwiseBlocker(Node n) {
		
		if(n.isBlockableNode()) {
			List<Edge> xEdges = n.getIncomingEdges();
			List<Node> xNodes = new ArrayList<>(); 
			for(Edge e : xEdges) {
				if(e.getFromNode().isBlockableNode())
					xNodes.add(e.getFromNode());
			}
			for(int i = 0 ; i < nodeBase.size() && i < n.getId(); i++) {
				Node p = nodeBase.get(i);
				if(p.isBlockableNode() && !p.isBlocked()) {
					if(p.getLabel().equals(n.getLabel())) {
						List<Edge> yEdges = p.getIncomingEdges();
						List<Node> yNodes = new ArrayList<>(); 
						for(Edge e : yEdges) {
							if(e.getFromNode().isBlockableNode())
								yNodes.add(e.getFromNode());
						}
						for(Node x : xNodes) {
							for(Node y : yNodes) {
								if(x.getLabel().equals(y.getLabel())) {
									if(getEdge(x,n).getLabel().equals(getEdge(y,p).getLabel())) {
										x1 = x;
										x2 = n;
										y1 = y;
										y2 = p;
										return p;
									}
								}
							}
						}
					}
						
				}
			}
		}
		return null;
	}
	public Node getX1() {
		return x1;
	}

	public Node getX2() {
		return x2;
	}

	public Node getY1() {
		return y1;
	}

	public Node getY2() {
		return y2;
	}

	public Node findEqualityBlocker(Node n) {
		
		if(n.isBlockableNode()) {
			for(int i = 0 ; i < nodeBase.size() && i < n.getId(); i++) {
				Node p = nodeBase.get(i);
				if(p.isBlockableNode() && !p.isBlocked()) {
					if(p.getLabel().equals(n.getLabel()))
						//return nodeBase.get(i);
						return p;
				}
			}
		}
		return null;
	}
	
	public void setNodeBlocked(Node node, Node blocker) {
		setNodeDBlocked(node, blocker);
	}
	
	private void setNodeDBlocked(Node node, Node blocker) {
        node.setdBlocked(blocker);
        propagateIBlockedStatus(node, blocker);
       // removeTree(node);
    }
	private void removeTree(Node n) {
		//n.getNeighbour().stream().filter(q -> q.getToNode().isBlockableNode()).forEach(q -> removeNode(n, q.getToNode(), q));
		n.getNeighbour().stream().filter(q -> q.getToNode().isBlockableNode() && q.isSuccEdge()).forEach(q -> removeNode(n, q.getToNode(), q));
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
       
		 node.getNeighbour().stream().filter(q -> q.getToNode().isBlockableNode() && q.isSuccEdge() && !q.isIBlocked()).forEach(q -> setNodeIBlocked(q.getToNode(), blocker));
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
	/* public void saveNode(Node node) {
	        node.save(node.curLevel);
	        savedNodes.add(node);
	        ++nNodeSaves;
	        
	    }*/
	 
	 private void restoreNode(Node node, int level) {
	        if (node.needRestore(level)) {
	            node.restore(level);
	            ++nNodeRestores;
	        }
	    }
	 
	 public void save() {
	        CGSaveState s = new CGSaveState();
	        //stack.push(s);
	        // 5 mar
	       // stack.push(s);
	        //
	        s.setnNodes(totalNodes);
	        s.setsNodes(savedNodes.size());
	        s.setnEdges(ctEdgeHeap.size());
	       // System.out.println("saving currentBranchingPoint : "+branchingLevel +" currentNode : "+currNode.getId() +" savedNodes: "+ savedNodes.size());

	        s.setCurrNode(currNode);
	        saveMap.put(branchingLevel, s);
	       // rareStack.incLevel();
	        // 5 mar
	       // rareStack.incLevel();
	        //
	        ++branchingLevel;
	    }
	 public void restore(int level) {
	        assert level > 0;
//	        branchingLevel = level;
	        //rareStack.restore(level);
	      //  CGSaveState s = stack.pop(level);
	        /// 5 mar
	     //   branchingLevel = level;
	      //  rareStack.restore(level);
	      //  CGSaveState s = stack.pop(level);
	        ///
	       CGSaveState s = saveMap.get(level);
	        totalNodes = s.getnNodes();
	        lastRestorednNodes = s.getnNodes();
	        currNode = s.getCurrNode();
	        System.out.println(level + " restore graph curr node" + s.getCurrNode().getId());
	        int nSaved = s.getsNodes();
	        System.out.println("total nodes: "+ totalNodes + " nsaved: "+ nSaved+ " saved nodes: "+ savedNodes.size());
	        if (totalNodes < Math.abs(savedNodes.size() - nSaved)) {
	            // it's cheaper to restore all nodes
	            nodeBase.stream().limit(totalNodes).forEach(p -> restoreNode(p, level));
	        } else {
	            for (int i = nSaved; i < savedNodes.size(); i++) {
	            	if(savedNodes.get(i) != null) {
	                if (savedNodes.get(i).getId() < totalNodes) {
	                    // don't restore nodes that are dead anyway
	                    restoreNode(savedNodes.get(i), level);
	                }
	            }
	            }
	        }
	        
	       
	        Helper.resize(savedNodes, nSaved, null);
	        Helper.resize(ctEdgeHeap, s.getnEdges(), null);
	        
	        /// 5 mar 19
	        for(Node n :  nodeBase) {
	        	 if(n.getId()>s.getCurrNode().getId()) {
	        		 n.removeLabel();
	        	 }
	        }
	        ///
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
	public boolean hasNominalInPath(Node y, Node x) {
        return checkAllPaths(x, y.getOutgoingEdges()); 
	}

	private boolean checkAllPaths(Node x, List<Edge> outgoingEdges) {
		for(Edge e : outgoingEdges) {
			 Node y = e.getToNode();
			if(y.isNominalNode()) {
				continue;
			}
			if(y.equals(x)) {
				return true;
			}
			else {
				checkAllPaths(x, y.getOutgoingEdges());
			}
		}
		return false;
	}
}

