package reasoner.ilp;

import java.util.HashSet;
import java.util.Set;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;

import reasoner.Dependencies.DependencySet;
import reasoner.graph.ConceptNDepSet;

public class EdgeInformation
{
  private final Set<OWLObjectPropertyExpression> edges;
  private final Set<OWLClassExpression> fillers;
  private Set<ConceptNDepSet> cnds = new HashSet<>();
  private int cardinality;
  private DependencySet ds;
  private Set<Integer> nodeSet = new HashSet<>();
  private Set<Integer> insideBranchLevels = nodeSet = new HashSet<>();
  
  public EdgeInformation(Set<OWLObjectPropertyExpression> roles, Set<OWLClassExpression> fillers, int card)
  {
    this.edges = roles;
    this.fillers = fillers;
    this.cardinality = card;
  }
  public EdgeInformation(Set<OWLObjectPropertyExpression> roles, Set<OWLClassExpression> fillers, double card)
  {
    this.edges = roles;
    this.fillers = fillers;
    this.cardinality = (int) card;
  }
  public EdgeInformation(Set<OWLObjectPropertyExpression> roles, Set<OWLClassExpression> fillers, int card, DependencySet ds)
  {
    this.edges = roles;
    this.fillers = fillers;
    this.cardinality = card;
    this.setDs(ds);
  }
  public EdgeInformation(Set<OWLObjectPropertyExpression> roles, Set<OWLClassExpression> fillers, double card, DependencySet ds)
  {
    this.edges = roles;
    this.fillers = fillers;
    this.cardinality = (int) card;
    this.setDs(ds);
  }
  public EdgeInformation(Set<OWLObjectPropertyExpression> roles, Set<OWLClassExpression> fillers, int card, DependencySet ds, Set<Integer> nodeSet)
  {
    this.edges = roles;
    this.fillers = fillers;
    this.cardinality = card;
    this.setDs(ds);
    this.nodeSet = nodeSet;
  }
  public EdgeInformation(Set<OWLObjectPropertyExpression> roles, Set<OWLClassExpression> fillers, double card, DependencySet ds, Set<Integer> nodeSet)
  {
    this.edges = roles;
    this.fillers = fillers;
    this.cardinality = (int) card;
    this.setDs(ds);
    this.nodeSet = nodeSet;
  }
  public EdgeInformation(Set<OWLObjectPropertyExpression> roles, Set<ConceptNDepSet> cnds, Set<OWLClassExpression> fillers, double card, DependencySet ds, Set<Integer> nodeSet)
  {
    this.edges = roles;
    this.fillers = fillers;
    this.cardinality = (int) card;
    this.setDs(ds);
    this.setCnds(cnds);
    this.nodeSet = nodeSet;
  }
  
  public Set<OWLObjectPropertyExpression> getEdges()
  {
    return new HashSet<OWLObjectPropertyExpression>(this.edges);
  }
  
  public Set<OWLClassExpression> getFillers()
  {
    return new HashSet<OWLClassExpression>(this.fillers);
  }
  
  public void setCnds(Set<ConceptNDepSet> cnds) {
	this.cnds = cnds;
}
public Set<ConceptNDepSet> getCnds() {
	return cnds;
}
public Set<Integer> getNodeSet() {
	return nodeSet;
}
public int getCardinality()
  {
    return this.cardinality;
  }
  
  public DependencySet getDs() {
	return ds;
}
public void setDs(DependencySet ds) {
	this.ds = ds;
}
public void modifyCardinality(int paramInt)
  {
    this.cardinality = paramInt;
  }
  
  public void addFiller(OWLClassExpression paramOWLClassExpression)
  {
    this.fillers.add(paramOWLClassExpression);
  }
  
  public void removeFiller(OWLClassExpression paramOWLClassExpression)
  {
    this.fillers.remove(paramOWLClassExpression);
  }
public void addInsideILPBranchLevels(Set<Integer> insideBranches) {
	insideBranchLevels = insideBranches;
	
}
public Set<Integer> getInsideILPBranchLevels() {
	return insideBranchLevels;
	
}
}

