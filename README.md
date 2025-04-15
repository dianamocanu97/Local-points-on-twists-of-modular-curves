This repository contains the accompanying code of the paper "Local points on $X_E^{-}(p)" by Nuno Freitas and Diana Mocanu.

In our computations, we used Magma V2.28-20 on a machine running Ubuntu 22.04.4 with an AMD Opteron Processor 6380 with 8 cores and 32 GB RAM. 
Most of our computations finished within a few minutes; those taking longer than a day were halted, as we considered them impractical for the scope of this paper.

The files "Table1.m", "Table2.m", "Table3.m" verify the claims in Table 1, Table 2, and Table 3 respectively. All involve checking local properties of elliptic curves defined over the 2-adics or 3-adics.

The file "Table.5" verifies the claims of Table 5. In particular, it needs to check the four conditions given by the equations (9.5), (9.6). To optimize the computation of various Frobenius elements, 
we used the file "IntegralFrobeniusMatrix.m". This contains the construction of the integral matrix of the Frobenius element as given in the article (and its associated code) "Integral tate modules and splitting of primes in torsion fields of elliptic
curves" by Tommaso Giorgio Centeleghe. We note that the condition that p divides the order of the image of Frob_l is equivalent to p | Delta_l and p \nmid beta_l by Proposition 5 in the article
"On the symplectic type of isomorphisms of the p-torsion of elliptic curves" by the first author together with Alain Kraus.

The file "GoodReduction.m" verifies the claims in the Examples 4.8, 4.10 and 4.11 from Section 4: The case of good reduction.
