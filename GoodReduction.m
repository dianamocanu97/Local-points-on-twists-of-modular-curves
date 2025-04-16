//This code verifies the claims in Section 4: The case of good reduction.

/*The following function outputs a matrix representing the action of Frobenius in a symplectic basis, 
together with the basis P1, P2, given as points in the p-torsion field of E.*/

function symFrobMatrix2(E,p) 

Gp:=GL(2,p);
Fp:=GF(p);
Zp:=Integers(p);
Fq:=BaseField(E);
q:=Characteristic(Fq);
P<x>:=PolynomialRing(Rationals());
_:=exists(ns){ x : x in [1..p] | not IsSquare(Zp!x) }; // Fixes a non-square mod p.
assert LegendreSymbol(ns,p) eq -1;

EoFq:=E;
polE:=DivisionPolynomial(EoFq,p);
K:=SplittingField(polE);
PK<y>:=PolynomialRing(K);
roots:=Roots(polE,K);
r1:=roots[1,1];

EoK:=ChangeRing(EoFq,K);
pE:=PK!Evaluate(DefiningPolynomial(EoK),[r1,y,1]);

if #Factorisation(pE) eq 1 then
Kp:=ext<K | pE>; //Creating the p-torsion field.
else
Kp:=K;
end if;
EoKp:=ChangeRing(EoK,Kp);

/*Computing a symplectic basis. */

zeta:=Roots(x^p - 1,K)[2,1]; // Fixing a primitive root of unity to use within the Weil pairing.
assert zeta ne 1;

P1:=EoKp!Points(EoKp,r1)[1]; // Constructing a p-torsion point P1.

for i in [1..#roots] do //Finding a second p-torsion point P2, such that P1 and P2 form a symplectic basis. 
    pt:=Points(EoKp,roots[i,1])[1];
    if IsLinearlyIndependent([P1,pt],p) then
        pairing:=WeilPairing(P1,pt,p);
        k:=Index([zeta^k eq pairing : k in [1..p]],true);
        if IsSquare(Zp!k) then
            P2:=pt;
        else
            P2:=ns*pt;
        end if;
        break i;
    end if;
end for;
assert IsSquare(Zp!Index([zeta^k eq WeilPairing(P1,P2,p) : k in [1..p]],true));

/* Computing the image of of Frobenius in the computed symplectic basis P1, P2. */

Gal,_,toAut:=AutomorphismGroup(Kp,Fq); 
Frobq:=toAut(Gal.1); // Finding the Frobenius element.
assert Frobq(Kp.1) eq Kp.1^q;

FrP1:=EoKp![Frobq(P1[1]),Frobq(P1[2])];
FrP2:=EoKp![Frobq(P2[1]),Frobq(P2[2])];

for a, b in [1..p] do
    if (a*P1 + b*P2) eq FrP1 then
        vec1:=[a,b]; bol1:=true;
    else
        bol1:=false;
    end if;
    if (a*P1 + b*P2) eq FrP2 then
        vec2:=[a,b]; bol2:=true;
    else
        bol2:=false;
    end if;
    if bol1 and bol2 then break a; end if;
end for;

FrobMat:=Transpose(Gp!Matrix([vec1,vec2])); //Gives the Frobenius matrix in the symplectic basis P1, P2.

return FrobMat, [P1,P2];
end function;

//The following function outputs a list of all elliptic curves over the finite field Fl, for odd l.

function AllEllipticCurvesOverFl(l)
    if l eq 2 then
    aa2 := [[0,0,1,0,0],[0,0,1,0,1],[0,0,1,1,0],[0,0,1,1,1],[0,1,1,0,0],[0,1,1,0,1],[0,1,1,1,0],[0,1,1,1,1],[1,0,0,0,1],[1,0,0,1,0],[1,0,1,0,1],[1,0,1,1,1],[1,1,0,0,1],[1,1,0,1,0],[1,1,1,0,0],[1,1,1,1,0]];
    curves:=[ChangeRing(EllipticCurve(a),GF(2)) : a in aa2];
    else
    if l eq 3 then 
    aa3:=[[ 0, 0, 0, 1, 0 ],[ 0, 0, 0, 2, 0 ],[ 0, 0, 0, 2, 1 ],[ 0, 0, 0, 2, 2 ],[ 0, 1, 0, 0, 1 ],[ 0, 1, 0, 0, 2 ],[ 0, 2, 0, 0, 1 ],[ 0, 2, 0, 0, 2 ]];
    curves:=[ChangeRing(EllipticCurve(a),GF(3)) : a in aa3];
    else
    F := GF(l);
    curves := [];
    for a in F do
        for b in F do
            if 4*a^3 + 27*b^2 ne 0 then // Checking if the discriminant is non-zero.
                E := EllipticCurve([0,0,0,a,b]);
                Append(~curves, E);
            end if;
        end for;
    end for;
    end if;
    end if;
    return curves;
end function;

//The following code checks the claims in Example 4.8.
print "Checking claims in Example 4.8.";
l:=3;
p:=11;
FF:=GF(l); G:=GL(2,p);

P<x>:=PolynomialRing(FF);
E1:=EllipticCurve(x^3+x^2+2); Fr1,basis:=symFrobMatrix2(E1,p);
a:=TraceOfFrobenius(E1); D:= a^2-4*l;

print "The elliptic curve", E1, "has j-invariant", jInvariant(E1), ", a_l=", a, "Delta_l=", D;
print "The Frobenius matrix in the symplectic basis is given by", Fr1, "of order", Order(Fr1);

//The following searches for non-isomorphic E2 with conjugate Frobenius to E1.

found := false;
for E2 in AllEllipticCurvesOverFl(3) do
    if not IsIsomorphic(E2, E1) then
        Fr2, basis := symFrobMatrix2(E2, p);
        isConj, g := IsConjugate(G, Fr1, Fr2);
        if isConj then
            print "Found a non-isomorphic E2 with conjugate Frobenius:";
            E2;
            found := true;
            break; 
        end if;
    end if;
end for;

if not found then
    print "All elliptic curves E2 whose Frobenius matrix is conjugate to that of E1 are isomorphic to E1.";
end if;

//The following code checks the claims in Example 4.10.

print "Checking claims in Example 4.10.";
l:=11;
p:=7;
FF:=GF(l); G:=GL(2,p);

P<x>:=PolynomialRing(FF);
E1:=EllipticCurve(x^3+x+9); Fr1,b1:=symFrobMatrix2(E1,p);
a1:=TraceOfFrobenius(E1); D1:= a1^2-4*l;
E2:=EllipticCurve(x^3+x+7); Fr2,b2:=symFrobMatrix2(E2,p);
a2:=TraceOfFrobenius(E2); D2:= a2^2-4*l;

print "The elliptic curve", E1, "has j-invariant", jInvariant(E1), ", a_l=", a1, "Delta_l=", D1;
print "The Frobenius matrix in the symplectic basis is given by", Fr1, "of order", Order(Fr1);

print "The elliptic curve", E2, "has j-invariant", jInvariant(E2), ", a_l=", a2, "Delta_l=", D2;
print "The Frobenius matrix in the symplectic basis is given by", Fr2, "of order", Order(Fr2);

isConj, g := IsConjugate(G, Fr1, Fr2); 

print "The matrix conjugating Fr1 into Fr2 is",g^-1;

//The following code checks the claims in Example 4.11.

print "Checking claims in Example 4.11.";
p:=7; //Note that p mod 4 = 3. 
g:= 1+(p^2-1)*(p-6)/24; g:=Integers()!g;
G:=GL(2,p);
P<x>:=PolynomialRing(Rationals());
E:=EllipticCurve(x^3+x+9);
Disc:=Integers()!(Discriminant(E));
small_good_primes:=[p : p in PrimesInInterval(2,4*g^2) | Disc mod p ne 0]; //Generating a list with all primes of good reduction < 4*g^2.

//This function checks that for all primes q dividing \Delta_l (q/p) is not -1.
function Checkcond4(D, p)
    primeFactors := PrimeDivisors(D);
    for q in primeFactors do
        if LegendreSymbol(q, p) eq -1 then
            return false;
        end if;
    end for;
    return true;
end function;

for l in small_good_primes do
    found:=false;
    FF:=GF(l);
    E1:=ChangeRing(E,FF); E1;
    a:=TraceOfFrobenius(E1);
    D:=a^2-4*l;
    if IsSquare(-p*D) and Checkcond4(D,p) then 
        Fr1,b1:=symFrobMatrix2(E1,p);
        if Order(Fr1) mod p eq 0 then // Checking if Theorem 4.2 does not hold.
            for E2 in AllEllipticCurvesOverFl(l) do //Checking for elliptic curves E2 that give an explicit point on X_E^-(p).
                if not IsIsomorphic(E2, E1) then
                    Fr2, basis := symFrobMatrix2(E2, p);
                    isConj:= IsConjugate(G, Fr1, Fr2);
                    if isConj then
                        isConj,gg:= IsConjugate(G, Fr1, Fr2);
                        Det:=Integers()!(Determinant(gg)); 
                        if LegendreSymbol(Det,p) eq -1 then
                            found:=true; print "The curve X_E^-(p) has Q_l-points for l=",l;
                            print "because E2 gives rise to a point, where E2 is", E2;
                            break;
                        end if;
                    end if;
                end if;
            end for;
        else
            found:=true; print "The curve X_E^-(p) has Q_l-points for l=",l, "because Theorem 4.2 holds";
        end if;
    else
        found:=true; print "The curve X_E^-(p) has Q_l-points for l=",l, "because Theorem 4.2 holds";
    end if;
    if not found then
            print "The curve X_E^-(p) has NO Q_l-points for l=",l;
    end if;
end for;




