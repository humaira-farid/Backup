package reasoner.graph;

import static reasoner.Helper.INITBRANCHINGLEVELVALUE;
import java.util.*;
import org.semanticweb.owlapi.model.*;
import reasoner.Dependencies.DependencySet;
import reasoner.state.*;
import reasoner.Configuration;
import reasoner.Helper;
import reasoner.RuleEngine;

public class CompletionGraph implements Cloneable {
	private int totalNodes = 0; // endUsed
	private static int idcounter = 0;
	List<Node> savedNodes = new ArrayList<>();
	// List<Node> copiedNodes = new ArrayList<>();
	// Map<Integer, Node> copies = new HashMap<Integer, Node>();
	private Node currNode;
	// SaveStack<CGSaveState> stack = new SaveStack<>();
	private Map<Integer, CGSaveState> saveMap = new HashMap<>();
	private Node x1 = null;
	private Node x2 = null;
	private Node y1 = null;
	private Node y2 = null;
	private int branchingLevel;
	private final List<Edge> ctEdgeHeap = new ArrayList<>();
	private final List<Node> nodeBase;
	RuleEngine re;
	Configuration config;
	OWLDataFactory df;

	public List<Node> getNodeBase() {
		return nodeBase;
	}

	public CompletionGraph(RuleEngine r) {
		nodeBase = new ArrayList<>();
		branchingLevel = INITBRANCHINGLEVELVALUE;
		re = r;
	}

	public CompletionGraph(RuleEngine r, Configuration config, OWLDataFactory df) {
		nodeBase = new ArrayList<>();
		branchingLevel = INITBRANCHINGLEVELVALUE;
		re = r;
		this.config = config;
		this.df = df;
	}

	public void addNodeInfo(Node node, DependencySet ds) {
		node.init(branchingLevel);
		ConceptNDepSet cnds = new ConceptNDepSet(df.getOWLThing(), ds);
		this.addConceptToNode(node, cnds);

		nodeBase.add(node);
		++totalNodes;
		// System.err.println("ADD NODE: " + node.getId() +" bp "+ branchingLevel +"
		// total node "+totalNodes);
	}

	public Node addNode(Node.NodeType nodeType, OWLClassExpression nodeLabel, DependencySet ds) {
		Node node = new Node(nodeType, nodeLabel, getnewId(), ds);
		addNodeInfo(node, ds);
		return node;
	}

	public Node addNode(Node.NodeType nodeType, DependencySet ds) {
		Node node = new Node(nodeType, getnewId(), ds);
		addNodeInfo(node, ds);
		return node;
	}

	private static int getnewId() {
		return idcounter++;
	}

	public int getCurrentId() {
		return idcounter;
	}

	public void updateNodeCardinality(Node n, int card) {
		saveNode(n, branchingLevel);
		n.setCardinality(card);
	}

	public void addConceptToNode(Node n, ConceptNDepSet cnd) {
		//System.out.println(cnd.getDs().getMax() + " level "+ cnd.getCe() + " addConceptToNode " + n.getId() + " bpList" + cnd.getDs().getbpList()+ " branchingLevel " + branchingLevel);
		saveNode(n, branchingLevel);
	//	saveNode(n, cnd.getDs().getMax());
	//	saveNode(n, cnd.getDs().getMax(), branchingLevel);
	//	System.out.println("addConceptToNode "+n.getId());
		n.addLabel(cnd.getCe());
		n.addConcept(cnd);
		checkBlockedStatus(n);
	}

	public void unblockNode(Node node) {
		node.setUnblock();
		Node blocker = node.getBlocker();
		if (blocker != null)
			blocker.getBlockedNodes().remove(node);
		re.processUnblockedNode(node);
		unblockNodeChildren(node);
	}

	private void unblockNodeChildren(Node node) {
		node.getNeighbour().stream().filter(q -> q.unblockable())
				// all of them are i-blocked
				.forEach(q -> unblockNode(q.getToNode()));

	}

	public void checkBlockedStatus(Node n) {
	//	System.out.println("checkBlockedStatus " + n.getId() + " blocked? " + n.isBlocked());
		if(n.isiBlocked()) {
			Node blocker = n.getBlocker(); // if indirectly blocked then used the directly blocked node to update blocking status
			unblockNode(n);
			if (config.isUsePairwiseBlocking())
				updatePairwiseBlockingStatus(blocker);
			else
				updateBlockingStatus(blocker);
		}
		else {
			if (config.isUsePairwiseBlocking())
				updatePairwiseBlockingStatus(n);
			else
				updateBlockingStatus(n);
		}
	}

	private void updateBlockingStatus(Node n) {
		if (n.isBlocked()) {
			unblockNode(n);

		} else if (n.isBlockingNode()) {
			Set<Node> blockedNodes = new HashSet<>(n.getBlockedNodes());
			for (Node blocked : blockedNodes) {
				unblockNode(blocked);
			}
		} else {
			Node blocker = findBlocker(n);
			if (blocker != null && !n.equals(blocker)) {
				setNodeBlocked(n, blocker);
			}
		}
	}

	private void updatePairwiseBlockingStatus(Node n) {
		if (n.isBlocked()) {
			Node x1 = n.getPairingNode();
			x1.getPairBlockedNodes().remove(n);
			Node blocker = n.getBlocker();
			Node y1 = blocker.getPairingNode();
			y1.getPairBlockerNodes().remove(blocker);
			unblockNode(n);

		} else if (n.isBlockingNode()) {
			Set<Node> blockedNodes = new HashSet<>(n.getBlockedNodes());
			Node y1 = n.getPairingNode();
			y1.getPairBlockerNodes().remove(n);
			for (Node blocked : blockedNodes) {
				Node x1 = blocked.getPairingNode();
				x1.getPairBlockedNodes().remove(blocked);
				unblockNode(blocked);
			}
		} else if (n.isPairingNode()) {
		//	System.out.println("isPairingNode " + n.getId());
			Set<Node> blockedNodes = new HashSet<>(n.getPairBlockedNodes());
			Set<Node> blockerNodes = new HashSet<>(n.getPairBlockerNodes());
			n.getPairBlockedNodes().clear();
			n.getPairBlockerNodes().clear();
			for (Node blocked : blockedNodes) {
				unblockNode(blocked);
			}
			for (Node blocker : blockerNodes) {
				Set<Node> blockedNodes2 = new HashSet<>(blocker.getBlockedNodes());
				Node y1 = blocker.getPairingNode();
				y1.getPairBlockerNodes().remove(blocker);
				for (Node blocked : blockedNodes2) {
					Node x1 = blocked.getPairingNode();
					x1.getPairBlockedNodes().remove(blocked);
					unblockNode(blocked);
				}
			}
		} else {
			//System.out.println("checkBlockedStatus " + n.getId() + " find blocker " );
			
			Node blocker = findBlocker(n);
			if (blocker != null && !n.equals(blocker)) {
				setNodeBlocked(n, blocker);
			}
		}

	}

	public Edge getEdge(Node from, OWLClassExpression nodeLabel, OWLObjectPropertyExpression edgeLabel) {
		Set<OWLClassExpression> tempNL = new HashSet<>();
		tempNL.add(nodeLabel);
		Set<OWLObjectPropertyExpression> tempEL = new HashSet<>();
		tempEL.add(edgeLabel);
		for (Edge e : from.getOutgoingEdges()) {
			if (e != null && !e.isReset()) {
				if (e.getLabel().equals(tempNL)) {
					if (e.getToNode().getLabel().equals(tempEL))
						return e;
				}
			}
		}
		return null;
	}

	public Edge getEdge(Node from, Set<OWLClassExpression> nodeLabel, Set<OWLObjectPropertyExpression> edgeLabel) {
		for (Edge e : from.getOutgoingEdges()) {
			if (e != null && !e.isReset()) {
				if (e.getLabel().equals(edgeLabel)) {
					if (e.getToNode().getLabel().equals(nodeLabel))
						return e;
				}
			}
		}
		return null;
	}

	public Edge getEdge(Node from, Node to, Edge edge) {
		for (Edge e : from.getOutgoingEdges()) {
			if (e != null && !e.isReset()) {
				if (e.getToNode().equals(to) && e.getLabel().equals(edge.getLabel())) {
					return e;
				}
			}
		}
		return null;
	}

	public Edge getEdge(Node from, Node to) {
		for (Edge e : from.getOutgoingEdges()) {
			if (e != null && !e.isReset()) {
				if (e.getToNode().equals(to)) {
					return e;
				}
			}
		}
		return null;
	}

	public Edge getInvEdge(Node from, Node to) {
		for (Edge e : to.getOutgoingEdges()) {
			if (e != null && !e.isReset()) {
				if (e.getToNode().equals(from)) {
					return e;
				}
			}
		}
		return null;
	}

	/**
	 * merge from node into to node
	 * 
	 * @param from
	 * @param to
	 * @param ds
	 */
	public void merge(Node from, Node to, DependencySet ds) {
		// 1. For all x: x->FROM make x->TO
		// 2. For all nominal nodes x: FROM->x make TO->x
		// 3. For all blockable nodes x: FROM->x prune x
		// saveNode(from);
		Set<Edge> succEdges = new HashSet<>();

		from.getNeighbour().forEach(q -> {
			if (q != null) {
				if (!q.getToNode().equals(to)) {
					if (q.isPredEdge()) {
						moveEdge2(to, q, q.isPredEdge(),
								DependencySet.plus(DependencySet.create(q.getDepSet()), DependencySet.create(ds)));
						if (this.getEdge(q.getToNode(), from) != null) {
							this.getEdge(q.getToNode(), from).setReset(true);
						}
						// from.setReset(true);
					} else if (q.isSuccEdge() && q.getToNode().isNominalNode()) {
						moveEdge2(to, q, q.isPredEdge(),
								DependencySet.plus(DependencySet.create(q.getDepSet()), DependencySet.create(ds)));
						if (this.getEdge(q.getToNode(), from) != null) {
							this.getEdge(q.getToNode(), from).setReset(true);
						}
						// from.setReset(true);
					} else if (q.isSuccEdge() && !q.getToNode().isNominalNode()) {
						succEdges.add(q);
						prune(from, q);
					}
				}
			}
		});
		from.setReset(true);
		/*
		 * from.getIncomingEdges().forEach(q -> { if (q.isSuccEdge()) { moveEdge2(to, q,
		 * q.isPredEdge(), DependencySet.plus(DependencySet.create(q.getDepSet()),
		 * DependencySet.create(ds))); } }); from.getOutgoingEdges().forEach(q -> { if
		 * (q.isSuccEdge() && q.getToNode().isNominalNode()) { moveEdge2(to, q,
		 * q.isPredEdge(), DependencySet.plus(DependencySet.create(q.getDepSet()),
		 * DependencySet.create(ds))); } else if (q.isSuccEdge() &&
		 * !q.getToNode().isNominalNode()) { succEdges.add(q); prune(from, q); } });
		 */

		/*
		 * from.getNeighbour().forEach(q -> { if(q != null) {
		 * if(!q.getToNode().equals(to)) { if (q.isPredEdge()) { moveEdge2(to, q,
		 * q.isPredEdge(), DependencySet.plus(DependencySet.create(q.getDepSet()),
		 * DependencySet.create(ds)));
		 * 
		 * } else if (q.isSuccEdge() && q.getToNode().isNominalNode()) { moveEdge2(to,
		 * q, q.isPredEdge(), DependencySet.plus(DependencySet.create(q.getDepSet()),
		 * DependencySet.create(ds)));
		 * 
		 * } else if (q.isSuccEdge() && !q.getToNode().isNominalNode()) {
		 * succEdges.add(q); prune(from, q); } } }});
		 */
		// from.setNodeMerged();
		// for(Edge e : succEdges)
		// removeNode(from, e.getToNode(), e);
		/*
		 * from.getIncomingEdges().forEach(p -> { if (p.isSuccEdge()) { moveEdge(to, p,
		 * p.isPredEdge(), ds); }
		 * 
		 * }); from.getOutgoingEdges().forEach(p -> { if (p.isSuccEdge() &&
		 * p.getToNode().isNominalNode()) { moveEdge(to, p, p.isPredEdge(), ds); } else
		 * if (p.isSuccEdge() && !p.getToNode().isNominalNode()) { // purgeEdge(p, to,
		 * ds); } });
		 */

	}

	private void prune(Node from, Edge e) {
		e.setReset(true);
		Node n = e.getToNode();
		if (this.getEdge(n, from) != null)
			this.getEdge(n, from).setReset(true);
		n.setReset(true);
		n.getOutgoingEdges().forEach(q -> {

			if (q != null) {
				if (!q.getToNode().equals(from)) {
					if (q.isSuccEdge() && !q.getToNode().isNominalNode()) {
						prune(n, q);
					} else if (q.isSuccEdge() && q.getToNode().isNominalNode()) {
						q.setReset(true);
						if (this.getEdge(q.getToNode(), n) != null) {
							this.getEdge(q.getToNode(), n).setReset(true);
						}
					}
				}
			}
		});

	}

	private void moveEdge2(Node node, Edge q, boolean isPredEdge, DependencySet ds) {
		if (isPredEdge) {
			Node to = q.getToNode();
			Edge e = getEdge(node, to);
			if (e == null) {
				addEdge(node, to, q.getLabel(), ds, !isPredEdge);
			} else {
				e.addLabel(q.getLabel());
				e.updateDepSet(ds);
				Edge invE = getInvEdge(to, node);
				if (invE != null && !q.equals(invE))
					q.getLabel().stream().forEach(el -> invE.addLabel(el.getInverseProperty()));
			}
			q.setReset(true);

		} else if (!isPredEdge && q.getToNode().isNominalNode()) {
			Node nn = q.getToNode();
			Edge e = getEdge(node, nn);
			if (e == null) {
				addEdge(node, nn, q.getLabel(), ds, !isPredEdge);
			} else {
				e.addLabel(q.getLabel());
				e.updateDepSet(ds);
				Edge invE = getInvEdge(nn, node);
				if (invE != null && !q.equals(invE))
					q.getLabel().stream().forEach(el -> invE.addLabel(el.getInverseProperty()));
			}
			q.setReset(true);
		}

	}

	public Edge findEdge(Node from, Set<OWLClassExpression> nodeLabel, Set<OWLObjectPropertyExpression> edgeLabel) {
		for (Edge e : from.getOutgoingEdges()) {
			// System.out.println("edge label: " +e.getLabel());
			// System.out.println("node label: " +e.getToNode().getLabel());
			// System.out.println("new edge label: " +edgeLabel);
			// System.out.println("new node label: " +nodeLabel);
			// if(e != null) {
			if (e != null && !e.isReset()) {
				if (e.getLabel().containsAll(edgeLabel)) {
					if (nodeLabel.containsAll(e.getToNode().getLabel()))
						return e;
				}
			}
		}
		return null;
	}

	public Edge findEdge(Node from, int nodeId) {
		for (Edge e : from.getOutgoingEdges()) {
			// if(e != null) {
			if (e != null && !e.isReset()) {
				if (e.getToNode().getNodeId() == nodeId) {
					return e;
				}
			}
		}
		return null;
	}

	public Set<Edge> findEdges(Node from, Set<Integer> nodeId) {
		Set<Edge> edges = new HashSet<>();
		for (Edge e : from.getOutgoingEdges()) {
			// if(e != null) {
			if (e != null && !e.isReset()) {
				if (nodeId.contains(e.getToNode().getNodeId())) {
					edges.add(e);
				}
			}
		}
		return edges;
	}

	public Set<Edge> getEdge(Node from, OWLObjectPropertyExpression edgeLabel) {
		Set<Edge> edges = new HashSet<>();
		// from.getOutgoingEdges().stream().filter(e ->
		// e.getLabel().contains(edgeLabel)).forEach(e -> edges.add(e));
		for (Edge e : from.getOutgoingEdges()) {
			// if(e != null) {
			if (e != null && !e.isReset()) {
				if (e.getLabel().contains(edgeLabel)) {
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
		// System.out.println("n node "+ n.getId() +"sunsetblocking "+config.isUsePairwiseBlocking());
		saveNode(n, branchingLevel);
		Node blocker = null;
		if (config.isUsePairwiseBlocking())
			blocker = findPairwiseBlocker(n);
		else if(config.isUseEqualityBlocking())
			blocker = findEqualityBlocker(n);
		else if(config.isUseSubsetBlocking())
			blocker = findSubsetBlocker(n);
		/*
		 * if (config.isSHO() || config.isSHOI() || config.isSHOIQ() || config.isSHOQ())
		 * { if (blocker != null) {
		 * 
		 * // System.err.println("blocker node "+blocker.getId() +" label: "+
		 * blocker.getLabel()); // System.err.println("blocked node "+n.getId()
		 * +" label: "+ n.getLabel());
		 * System.err.println("hasNominalInPath "+hasNominalInPath(blocker, n)); if
		 * (!hasNominalInPath(blocker, n)) { //
		 * System.err.println("blocker node "+blocker.getId() +" label: "+ //
		 * blocker.getLabel()); return blocker; } else return null; } }
		 */

		return blocker;

	}

	private Node findSubsetBlocker(Node n) {
		if (n.isBlockableNode() && !n.isReset()) {
			// System.out.println("nodeBase.size() "+nodeBase.size());
			for (int i = 0; i < nodeBase.size() /* && i < n.getId() */; i++) {
				Node p = nodeBase.get(i);
				if (p != null && p.getOutgoingEdges().size() > 0 && !p.equals(n) && p.isBlockableNode()
						&& !p.isBlocked() && !p.isReset()) {
					if (p.getLabel().containsAll(n.getLabel())) {
						if (config.isSHO() || config.isSHOI() || config.isSHOIQ() || config.isSHOQ()) {
							if (!hasNominalInPath(p, n)) {
								return p;
							}
						} else
							return p;
					}
				}
			}
		}
		return null;
	}

	public Node findPairwiseBlocker(Node n) {
	//	System.err.println("find blocker node for "+n.getId());
		if (n.isBlockableNode()) {
			// List<Edge> xEdges = n.getIncomingEdges();
			List<Edge> xEdges = n.getIncomingEdges();
			List<Node> xNodes = new ArrayList<>();
			for (Edge e : xEdges) {
				if (e == null)
					continue;
				if (e.isSuccEdge() && e.getFromNode().isBlockableNode() && !e.getFromNode().isBlocked()
						&& !e.getFromNode().isReset())
					xNodes.add(e.getFromNode());
			}
			for (int i = 0; i < nodeBase.size() && i < n.getId(); i++) {
				Node p = nodeBase.get(i);
				if (!p.equals(n) && p != null && p.getOutgoingEdges().size() > 0 && p.isBlockableNode() && !p.isBlocked()
						&& !p.isReset()) {
					if (this.re.hasUnprocessedEntries(p))
						continue;
					if (p.getLabel().equals(n.getLabel())) {
						List<Edge> yEdges = p.getIncomingEdges();
						List<Node> yNodes = new ArrayList<>();
						for (Edge e : yEdges) {
							if (e.isSuccEdge() && e.getFromNode().isBlockableNode() && !e.getFromNode().isBlocked()
									&& !e.getFromNode().isReset())
								yNodes.add(e.getFromNode());
						}
						for (Node x : xNodes) {
							for (Node y : yNodes) {
								if (x.getLabel().equals(y.getLabel())) {
									Edge e1 = getEdge(x, n);
									Edge e2 = getEdge(y, p);
									if (e1 != null && e2 != null) {
										if (e1.getLabel().equals(e2.getLabel())) {
											x1 = x;
											x2 = n;
											y1 = y;
											y2 = p;
											if (config.isSHO() || config.isSHOI() || config.isSHOIQ()
													|| config.isSHOQ()) {
												if (!hasNominalInPath(p, n)) {
												//	System.err.println("hasNominalInPath node for "+n.getId());
												//	System.out.println(p.getLabel());
												//	System.out.println(y1.getLabel());
													System.err.println("blocker node " + p.getId() + " pair with: "
															+ y1.getId() + y.isBlockableNode());

													y1.addPairBlockerNode(p);
													x1.addPairBlockedNode(n);
													n.setPairingNode(x1);
													p.setPairingNode(y1);
													return p;
												}
											} else {
												System.out.println(p.getLabel());
												System.out.println(x1.getLabel());
												System.err.println("blocker node " + p.getId() + " pair with: "
														+ y1.getId() + y.isBlockableNode() +"blocked node " + n.getId() + " pair with: "
																+ x1.getId());

												y1.addPairBlockerNode(p);
												x1.addPairBlockedNode(n);
												n.setPairingNode(x1);
												p.setPairingNode(y1);
												return p;
											}
										}
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

		if (n.isBlockableNode() && !n.isReset()) {
			// System.out.println("nodeBase.size() "+nodeBase.size());
			for (int i = 0; i < nodeBase.size() /* && i < n.getId() */; i++) {
				Node p = nodeBase.get(i);
				if (p != null && p.getOutgoingEdges().size() > 0 && !p.equals(n) && p.isBlockableNode()
						&& !p.isBlocked() && !p.isReset()) {
					if (p.getLabel().equals(n.getLabel())) {
						if (config.isSHO() || config.isSHOI() || config.isSHOIQ() || config.isSHOQ()) {
							if (!hasNominalInPath(p, n)) {
								return p;
							}
						} else
							return p;
					}
				}
			}
		}
		return null;
	}

	public void setNodeBlocked(Node node, Node blocker) {
		blocker.getBlockedNodes().add(node);
		setNodeDBlocked(node, blocker);
	}

	private void setNodeDBlocked(Node node, Node blocker) {
		node.setdBlocked(blocker);
	//	propagateIBlockedStatus(node, blocker);
		propagateIBlockedStatus(node, node);
		
		// removeTree(node);
	}

	/*private void removeTree(Node n) {
		// n.getNeighbour().stream().filter(q ->
		// q.getToNode().isBlockableNode()).forEach(q -> removeNode(n, q.getToNode(),
		// q));
		n.getNeighbour().stream().filter(q -> q.getToNode().isBlockableNode() && q.isSuccEdge())
				.forEach(q -> removeNode(n, q.getToNode(), q));
	}

	private void removeNode(Node from, Node to, Edge q) {
		if (to.isNominalNode())
			return;
		else {
			Node p = to;

			to.remove();
			to = null;

			from.getNeighbour().remove(q);
			removeTree(p);
		}
	}*/

	private void propagateIBlockedStatus(Node node, Node blocker) {

		node.getNeighbour().stream().filter(q -> q.getToNode().isBlockableNode() && q.isSuccEdge() && !q.isIBlocked())
				.forEach(q -> setNodeIBlocked(q.getToNode(), blocker));
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

	public void saveN(Node n) {
		saveNode(n, branchingLevel);
	}

	public void saveNode(Node node, int level) {
		if (node.needSave(level)) {
			node.save(level);
			savedNodes.add(node);
		}
	}
	public void saveNode(Node node, int level, int branchingLevel) {
		if (node.needSave(level)) {
			node.save(level, branchingLevel);
			savedNodes.add(node);
		}
	}
	/*
	 * public void saveNode(Node node) { node.save(node.curLevel);
	 * savedNodes.add(node); ++nNodeSaves;
	 * 
	 * }
	 */

	private void restoreNode(Node node, int level, boolean ilp, boolean merge, boolean disjunction) {
	//	System.err.println("level " + level + " need to restore node? " + node.getId() + " " + node.needRestore(level));

		if (node.needRestore(level)) {
			updateReset(node);
			node.restore(level, ilp, merge, disjunction);
		}
	}

	public void updateReset(Node n) {
		n.setReset(false);
		for (Edge e : n.getOutgoingEdges()) {
			if (e != null && e.isPredEdge()) {
				e.setReset(false);
			} else if (e != null && e.isSuccEdge()) {
				e.setReset(false);
				Node to = e.getToNode();
				if (to.isReset())
					updateReset(to);
			}
		}
		for (Edge e : n.getIncomingEdges()) {
			if (e != null && e.isSuccEdge()) {
				e.setReset(false);
			} else if (e != null && e.isPredEdge()) {
				e.setReset(false);
			}
		}
	}

	 public void setBranchingLevel(int bl) {
		 branchingLevel = bl;
	 }
	public void save() {
		CGSaveState s = new CGSaveState();
		// stack.push(s);
		// 5 mar
		// stack.push(s);
		//
		s.setnNodes(totalNodes);
		s.setbNodes(nodeBase.size());
		s.setsNodes(savedNodes.size());
		s.setnEdges(ctEdgeHeap.size());
		// System.out.println("saving currentBranchingPoint : "+branchingLevel +" currentNode : "+currNode.getId() +" savedNodes: "+
		 //savedNodes.size()+"totalNodes: "+ totalNodes);

		s.setCurrNode(currNode);
		s.setCurrNodeResetStatus(currNode.isReset());
		saveMap.put(branchingLevel, s);
		// rareStack.incLevel();
		// 5 mar
		// rareStack.incLevel();
		//
		++branchingLevel;
	}

	public void restore(int level, boolean ilp, boolean merge, boolean disjunction) {
		assert level > 0;
		branchingLevel = level;
		//System.out.println("cg level " + level + " curr node " + currNode.getId());
		// rareStack.restore(level);
		// CGSaveState s = stack.pop(level);
		/// 5 mar
		// branchingLevel = level;
		// rareStack.restore(level);
		// CGSaveState s = stack.pop(level);
		///
		CGSaveState s = saveMap.get(level);
		totalNodes = s.getnNodes();
		currNode = s.getCurrNode();
		// currNode.setReset(s.getCurrNodeResetStatus());
		//System.out.println("cg level " + level + " restore graph curr node " + s.getCurrNode().getId());
		int nSaved = s.getsNodes();
	//	System.err.println("total nodes: " + totalNodes + " nsaved: " + nSaved + " saved nodes: " + savedNodes.size());
		if (totalNodes < Math.abs(savedNodes.size() - nSaved)) {
			// it's cheaper to restore all nodes
			// nodeBase.stream().limit(totalNodes).filter(p -> p!=null).forEach(p ->
			// restoreNode(p, level));
			nodeBase.stream().filter(p -> p != null).forEach(p -> restoreNode(p, level, ilp, merge, disjunction));
		} else {
			for (int i = nSaved; i < savedNodes.size(); i++) {
				if (savedNodes.get(i) != null) {
				//	 System.err.println("Node id: "+ savedNodes.get(i).getId());
					// commented on 22-oct-2019
					// if (savedNodes.get(i).getId() < totalNodes) {
					// don't restore nodes that are dead anyway
					restoreNode(savedNodes.get(i), level, ilp, merge, disjunction);
					// }
				}
			}
		}

		Helper.resize(savedNodes, nSaved, null);
		Helper.resize(ctEdgeHeap, s.getnEdges(), null);
		// System.out.println("nodeBase before "+nodeBase.size());
		Helper.resize(nodeBase, s.getbNodes(), null);
		// System.out.println("nodeBase after "+nodeBase.size());

		/// 5 mar 19

		/*
		 * for(Node n : nodeBase) { if(n.getId()>s.getCurrNode().getId()) {
		 * restoreNode(n, level); // n.removeLabel(); } }
		 */

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
		// Node n = null;
		Set<Node> nodes = new HashSet<>();
		// System.err.println(ce);
		// nodeBase.stream().forEach(nb -> System.out.println(nb.getId()+" "+
		// nb.isReset() +" "+ nb.getLabel()));
		if (nodeBase.stream().anyMatch(node -> node != null && node.getLabel().contains(ce))) {
			nodeBase.stream().filter(node -> node != null && !node.isReset() && node.getLabel().contains(ce))
					.forEach(node -> {
						if (node != null && !node.isReset())
							nodes.add(node);
					});
			// n = nodeBase.stream().filter(node ->
			// node.getLabel().contains(ce)).iterator().next();
			// System.err.println("node id : "+n.getId() + "expression: "+ce);
		}
	//	System.err.println("nodes : " + nodes.size());
		/*
		 * if(n!=null) { if(!n.isReset()) return n; else return null; }
		 */
		if (nodes.size() == 1) {
			return nodes.iterator().next();
		}
		return null;
	}

	public boolean hasNominalInPath(Node y, Node x) {
		// System.out.println("node : "+ y.getId() + " n "+ y.getOutgoingEdges().iterator().next().getToNode().getId());
		Set<Node> proccessedNodes = new HashSet<>();
		proccessedNodes.add(y);
		return checkAllPaths(x, y, y.getOutgoingEdges(), proccessedNodes);
		// return checkAllPaths(x, y.getSuccEdges());
	}
	private boolean checkAllPaths(Node x, Node y, List<Edge> outgoingEdges, Set<Node> proccessedNodes) {
		for (Edge e : outgoingEdges) {
			if(!checkPath(x, y, e, proccessedNodes))
				return false;
		}
		return true;
	}
	private boolean checkPath(Node x, Node y, Edge e, Set<Node> proccessedNodes) {
		// System.out.println("out going edges : "+ outgoingEdges.size() + "node : "+ y.getId());
		
			Node to = e.getToNode();
			//System.out.println("out going node : "+ to.getId());
			
			if (!to.isReset()) {
				if (!proccessedNodes.contains(to)) {
					proccessedNodes.add(to);
					if (to.isNominalNode()) {
						return true;
					}
					if (to.equals(x)) {
						return false;
					} else {
						return checkAllPaths(x, to, to.getOutgoingEdges(), proccessedNodes);
						// checkAllPaths(x, y.getSuccEdges());
					}
				}
			}
			return true;
	}

	/*private boolean checkAllPaths(Node x, Node y, List<Edge> outgoingEdges, Set<Node> proccessedNodes) {
		// System.out.println("out going edges : "+ outgoingEdges.size() + "node : "+ y.getId());
		boolean hasNominal = false;
		for (Edge e : outgoingEdges) {
			 hasNominal = false;
			Node to = e.getToNode();
			System.out.println("out going node : "+ to.getId());
			
			if (!to.isReset()) {
				if (!proccessedNodes.contains(to)) {
					proccessedNodes.add(to);
					if (to.isNominalNode()) {
						hasNominal = true;
						continue;
					}
					if (to.equals(x)) {
						return false;
					} else {
						checkAllPaths(x, to, to.getOutgoingEdges(), proccessedNodes);
						// checkAllPaths(x, y.getSuccEdges());
					}
				}
			}
		}
		return hasNominal;
	}*/

	public Edge addEdge(Node from, Node to, Set<OWLObjectPropertyExpression> edgeLabel, DependencySet ds) {
		if (config.isSHI() || config.isSHOI() || config.isSHOIQ() || config.isSHIQ())
			return addEdge(from, to, edgeLabel, ds, true, true);
		return addEdge(from, to, edgeLabel, ds, true);
	}

	public Edge addEdge(Node from, Node to, Set<OWLObjectPropertyExpression> edgeLabel, DependencySet ds,
			boolean succEdge) {
		// System.err.println("edge label to be added " + edgeLabel);
		Edge edge = new Edge(from, to, edgeLabel, ds);
		// Set<OWLObjectPropertyExpression> invRoles = new
		// HashSet<>(edgeLabel.stream().map(r ->
		// r.getInverseProperty()).collect(Collectors.toSet()));
		// Set<OWLObjectPropertyExpression> invRoles = new HashSet<>();
		// edgeLabel.stream().forEach(r -> invRoles.add(r.getInverseProperty()));
		// System.err.println("inverse roles " + invRoles);
		// Edge invEdge = new Edge(to, from, invRoles, ds);
		this.ctEdgeHeap.add(edge);
		// this.ctEdgeHeap.add(invEdge);

		from.getNeighbour().add(edge);
		from.getOutgoingEdges().add(edge);
		// from.getIncomingEdges().add(invEdge);

		// to.getNeighbour().add(invEdge);
		// to.getOutgoingEdges().add(invEdge);
		// to.getIncomingEdges().add(edge);

		saveNode(from, branchingLevel);
		saveNode(to, branchingLevel);
		// System.err.println("getOutgoingEdges " + to.getOutgoingEdges().size());

		// System.err.println("getOutgoingEdges " + to.getOutgoingEdges().size());
		edge.setSuccEdge(succEdge);
		// invEdge.setSuccEdge(!succEdge);

		// from.getSuccEdges1().add(edge);
		// to.getPredEdges1().add(invEdge);
		return edge;
	}

	public Edge addEdge(Node from, Node to, Set<OWLObjectPropertyExpression> edgeLabel, DependencySet ds,
			boolean succEdge, boolean inverseEdge) {
		// System.err.println("edge label to be added " + edgeLabel);
		Edge edge = new Edge(from, to, edgeLabel, ds);
		// Set<OWLObjectPropertyExpression> invRoles = new
		// HashSet<>(edgeLabel.stream().map(r ->
		// r.getInverseProperty()).collect(Collectors.toSet()));
		Set<OWLObjectPropertyExpression> invRoles = new HashSet<>();
		edgeLabel.stream().forEach(r -> invRoles.add(r.getInverseProperty()));
		// System.err.println("inverse roles " + invRoles);
		Edge invEdge = new Edge(to, from, invRoles, ds);
		this.ctEdgeHeap.add(edge);
		this.ctEdgeHeap.add(invEdge);

		from.getNeighbour().add(edge);
		from.getOutgoingEdges().add(edge);
		from.getIncomingEdges().add(invEdge);

		to.getNeighbour().add(invEdge);
		to.getOutgoingEdges().add(invEdge);
		to.getIncomingEdges().add(edge);

		saveNode(from, branchingLevel);
		saveNode(to, branchingLevel);
		// System.err.println("getOutgoingEdges " + to.getOutgoingEdges().size());

		// System.err.println("getOutgoingEdges " + to.getOutgoingEdges().size());
		edge.setSuccEdge(succEdge);
		invEdge.setSuccEdge(!succEdge);

		// from.getSuccEdges1().add(edge);
		// to.getPredEdges1().add(invEdge);
		return edge;
	}

	public Node getNode(Integer id) {
		for(Node n : nodeBase) {
			if(n!=null && n.getId() == id) {
				return n;
			}
		}
	//	if (nodeBase.stream().filter(n -> n.getId() == id).iterator().hasNext())
	//		return nodeBase.stream().filter(n -> n.getId() == id).iterator().next();
		return null;

	}
	/*
	 * private void moveEdge3(Node to, Edge q, boolean isPredEdge, DependencySet ds)
	 * { if (isPredEdge) { Node from = q.getToNode(); Edge e = getEdge(from, to, q);
	 * if (e == null) { addEdge(from, to, q.getLabel(), ds); } else
	 * e.updateDepSet(ds); } else { Node nn = q.getToNode(); Edge e = getEdge(to,
	 * nn, q); if (e == null) { addEdge(to, nn, q.getLabel(), ds); } else
	 * e.updateDepSet(ds); } }
	 */
	/*
	 * public void copyNodes() { //
	 * System.out.println("saved nodes : "+nodeBase.size()); //
	 * nodeBase.stream().forEach(n-> System.out.println("node id : "+n.getId() //
	 * +"neighbours : "+n.getNeighbour().size())); nodeBase.stream().forEach(n -> {
	 * try { copies.put(n.getId(), (Node) n.clone()); } catch
	 * (CloneNotSupportedException e) { e.printStackTrace(); } });
	 * 
	 * }
	 */

	/*
	 * public void restoreNode(Node n) { //
	 * System.out.println("node id : "+n.getId()+" node neighbours "+ //
	 * n.getNeighbour().size()); Node node = copies.get(n.getId()); //
	 * System.out.println("restored node id : "+node.getId()+" node neighbours "+ //
	 * node.getNeighbour().size()); this.setCurrNode(node); }
	 */

	/*
	 * public void restore(int level) { assert level > 0; branchingLevel = level;
	 * rareStack.restore(level); CGSaveState s = stack.pop(level); totalNodes =
	 * s.getnNodes(); lastRestorednNodes = s.getnNodes(); currNode =
	 * s.getCurrNode(); System.out.println(level + " restore graph curr node" +
	 * s.getCurrNode().getId()); int nSaved = s.getsNodes();
	 * System.err.println("total nodes: "+ totalNodes + " nsaved: "+ nSaved+
	 * " saved nodes: "+ savedNodes.size()); if (totalNodes <
	 * Math.abs(savedNodes.size() - nSaved)) { // it's cheaper to restore all nodes
	 * nodeBase.stream().limit(totalNodes).forEach(p -> restoreNode(p, level)); }
	 * else { for (int i = nSaved; i < savedNodes.size(); i++) {
	 * if(savedNodes.get(i) != null) { System.err.println("Node id: "+
	 * savedNodes.get(i).getId()); if (savedNodes.get(i).getId() < totalNodes) { //
	 * don't restore nodes that are dead anyway restoreNode(savedNodes.get(i),
	 * level); } } } } Helper.resize(savedNodes, nSaved, null);
	 * Helper.resize(ctEdgeHeap, s.getnEdges(), null);
	 * 
	 * }
	 */
	/*
	 * private void moveEdge2(Node to, Edge q, boolean isPredEdge, DependencySet ds)
	 * { if(isPredEdge) { Node from = q.getToNode(); Edge e = getEdge(from, to);
	 * if(e == null) { addEdge(from, to, q.getLabel(), ds); } else {
	 * e.addLabel(q.getLabel()); e.updateDepSet(ds); Edge invE = getInvEdge(from,
	 * to); if(invE != null) q.getLabel().stream().forEach(el ->
	 * invE.addLabel(el.getInverseProperty())); } q.setReset(true);
	 * from.setReset(true);
	 * 
	 * } else { Node nn = q.getToNode(); Edge e = getEdge(to, nn); if(e == null) {
	 * addEdge(to, nn, q.getLabel(), ds); } else { e.addLabel(q.getLabel());
	 * e.updateDepSet(ds); Edge invE = getInvEdge(to, nn); if(invE != null)
	 * q.getLabel().stream().forEach(el -> invE.addLabel(el.getInverseProperty()));
	 * } q.setReset(true); nn.setReset(true); } }
	 */

	/*
	 * public Edge getEdge(Node from, OWLClassExpression nodeLabel,
	 * OWLObjectPropertyExpression edgeLabel) { for(Edge e :
	 * from.getOutgoingEdges()) { if(e.getLabel().contains(edgeLabel)) {
	 * if(e.getToNode().getLabel().contains(nodeLabel)) return e; } } return null; }
	 * public Edge getEdge(Node from, Set<OWLClassExpression> nodeLabel,
	 * Set<OWLObjectPropertyExpression> edgeLabel) { for(Edge e :
	 * from.getOutgoingEdges()) { if(e.getLabel().containsAll(edgeLabel)) {
	 * if(e.getToNode().getLabel().containsAll(nodeLabel)) return e; } } return
	 * null; }
	 */

	/*
	 * public void updateReset(Node n) { n.setReset(false); for (Edge e :
	 * n.getOutgoingEdges()) { if (e != null && e.isPredEdge()) { e.setReset(false);
	 * Node to = e.getToNode(); to.setReset(false); if (to.isReset())
	 * updateReset(to); } } for (Edge e : n.getIncomingEdges()) { if (e != null &&
	 * e.isSuccEdge()) { e.setReset(false); Node from = e.getFromNode();
	 * from.setReset(false); if (from.isReset()) updateReset(from); } } }
	 */
	/*
	 * public void save() { CGSaveState s = new CGSaveState(); stack.push(s); // 5
	 * mar // stack.push(s); // s.setnNodes(totalNodes);
	 * s.setsNodes(savedNodes.size()); s.setnEdges(ctEdgeHeap.size());
	 * System.out.println("saving currentBranchingPoint : "+branchingLevel
	 * +" currentNode : "+currNode.getId() +" savedNodes: "+
	 * savedNodes.size()+" totalNodes: "+ totalNodes);
	 * 
	 * s.setCurrNode(currNode); // saveMap.put(branchingLevel, s);
	 * rareStack.incLevel(); // 5 mar // rareStack.incLevel(); // ++branchingLevel;
	 * }
	 */

	/*
	 * public void checkBlockedStatus(Node n) { if (n.isBlocked()) { unblockNode(n);
	 * 
	 * } else if (n.isBlockingNode()) { Node blocked = n.getBlocked();
	 * n.setBlocked(null); blocked.setUnblock(); // re.processUnblockedNode(n);
	 * re.processUnblockedNode(blocked); } else { Node blocker = findBlocker(n); if
	 * (blocker != null && !n.equals(blocker)) { setNodeBlocked(n, blocker); } } }
	 */
}
