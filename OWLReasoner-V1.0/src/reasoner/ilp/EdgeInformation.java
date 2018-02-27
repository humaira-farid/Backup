package reasoner.ilp;

import java.util.HashSet;
import java.util.Set;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;

public class EdgeInformation
{
  private final Set<OWLObjectPropertyExpression> edges;
  private final Set<OWLClassExpression> fillers;
  private int cardinality;
  
  public EdgeInformation(Set<OWLObjectPropertyExpression> roles, Set<OWLClassExpression> fillers, int card)
  {
    this.edges = roles;
    this.fillers = fillers;
    this.cardinality = card;
  }
  
  public Set<OWLObjectPropertyExpression> getEdges()
  {
    return new HashSet<OWLObjectPropertyExpression>(this.edges);
  }
  
  public Set<OWLClassExpression> getFillers()
  {
    return new HashSet<OWLClassExpression>(this.fillers);
  }
  
  public int getCardinality()
  {
    return this.cardinality;
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
}

