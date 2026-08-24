This repository contains the accompanying code of the paper "Local points on twists of X(p) and applications" by Nuno Freitas and Diana Mocanu.

In our computations, we used Magma V2.28-20 on a machine running Ubuntu 22.04.4 with an AMD Opteron Processor 6380 with 8 cores and 32 GB RAM. Most of our computations finish within a few minutes.

The files "Table3.m", "Table4.m", and "Table5.m" verify the claims in Table 3, Table 4, and Table 5, respectively. All involve checking local properties of elliptic curves defined over the 2-adics or 3-adics.

The file "Equation (3,3,p).m" verifies the claims in Section 11: The Diophantine Equation x^3+b^p=Cz^p. It relies on the code in "IntegralFrobeniusMatrix.m" attached, which is taken from the associated code of the article "Integral Tate modules and splitting of primes in torsion fields of elliptic curves" by Tommaso Giorgio Centeleghe.
