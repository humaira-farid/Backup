\ENCODING=ISO-8859-1
\Problem name: ilog.cplex

Minimize
 obj: 5000 x1 + 5000 x3 + 5000 x5 + 5000 x7 + 5000 x9 + 4 x11 + 2 x12 + 2 x13
      + 2 x14 + 2 x15
Subject To
 c1: x1 + x11 + x13 + x14 >= 1
 c1: x3 + x11 + x13 + x15 >= 1
 c3: x5 + x11 + x14 + x15 >= 1
 c5: x7 + x12 >= 1
 c7: x9 + x11 + x12  = 1
End
