//This code verifies the claims in Section 10.

load "IntegralFrobeniusMatrix.m";

// This function checks that p divides the order of Frobenius.
function CheckpdivFrob(E,l,p)
    FF:=GF(l);
    E:=ChangeRing(E,FF);
    G:=GL(2,p);
    F:=G!IntegralFrobenius(E);
    if Order(F) mod p eq 0 then
        return true;
    else
        return false;
    end if;
end function;

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

//List of elliptic curves in the isogeny classes given in equation (10.9). These have v_5(\Delta_min)=2 which is important in the elimination step.
EC:=["90a4", "90b2", "90c2","180a2", "360a2", "360b2", "360c2","360d2","360e2" ]; 

//This function constructs the first Frey elliptic curve.
function Frey1(a,b,l) 
FF:=GF(l);
P<x>:=PolynomialRing(FF);
a:=FF!a; b:=FF!b;
f:=x^3+3*a*b*x+(b^3-a^3);
if Discriminant(f) ne 0 then
E:=EllipticCurve(f);
end if;
return E;
end function;

//This function computes the set S_\ell for the first Frey curve.
function traces1(l)
tr:=[];
FF:=GF(l);
for a in FF do
for b in FF do
try
t:=TraceOfFrobenius(Frey1(a,b,l));
Append(~tr,t);
catch e;
end try;
end for;
end for;
return tr;
end function;

//This function constructs the second Frey elliptic curve.
function Frey2(a,b,l)
FF:=GF(l);
P<x>:=PolynomialRing(FF);
a:=FF!a; b:=FF!b;
f:=x^3+(3*(b-a)+2)/8*x^2+3*(a+b)^2/64*x+9*((b-a)*(a+b)^2)/512;
if Discriminant(f) ne 0 then
E:=EllipticCurve(f);
end if;
return E;
end function;

//This function computes the set S_\ell for the second Frey curve.
function traces2(l)
tr:=[];
FF:=GF(l);
for a in FF do
for b in FF do
try
t:=TraceOfFrobenius(Frey2(a,b,l));
Append(~tr,t);
catch e;
end try;
end for;
end for;
return tr;
end function;

//This step computes B(E) with \ell<300, for all E in the above list. Then it eliminates the E's with B not 0.
for label in EC do
E:=EllipticCurve(label);
B:=0;
N:=Conductor(E);
if N eq 90 then //these curves correspond to the first Frey curve by equation (10.6).
for l in PrimesInInterval(7,300) do
if N mod l ne 0 then
al:=TraceOfFrobenius(E,l);
Bl:= ((l+1)^2-al^2);
for a in traces2(l) do
Bl:=Bl*(a-al);
end for;
B:=GCD(B,Bl);
end if;
end for;
else  //these curves correspond to the second Frey curve by equation (10.6).
for l in PrimesInInterval(7,300) do
if N mod l ne 0 then
al:=TraceOfFrobenius(E,l);
Bl:= ((l+1)^2-al^2);
for a in traces1(l) do
Bl:=Bl*(a-al);
end for;
B:=GCD(B,Bl);
end if;
end for;
end if;
if B ne 0 then
print "B is", Factorisation(B);
print "ELIMINATE", label, "for p not in the following factorisation", Factorisation(B);
else
print "B is", B;
end if;
end for;
// This step eliminated: 180a2, 360b2, 360c2

//This step checks for primes p in the interval 20..5000 satisfying the conditions in Theorem 5.3.
EC:=[ "90a4","90b2","90c2", "360a2","360d2","360e2"];
ps:=[];
for p in PrimesInInterval(20,5000) do
    if p mod 4 eq 3 then //Assumption (1) of Theorem 5.3.
        okp:=0;
    for label in EC do
    E:=EllipticCurve(label);
                for l in PrimesInInterval(5,Floor(p^2/16)) do //Assumption (5) of Theorem 5.3.
                    a:=TraceOfFrobenius(E,l);
                    D:=a^2-4*l;
                    if IsSquare(-p*D) and l ne p and CheckpdivFrob(E,l,p) and Checkcond4(D, p) then //Assumptions (2), (3), (4) of Theorem 5.3.
                        okp:=okp+1;
                        break l;
                    end if;
                end for;
    end for;    
        if okp eq #EC then
        print "p is good for all curves",p;
        Append(~ps,p);
        end if;
    end if;
end for;

// Primes p for which the equation x^3+y^3=5^\alphaz^p has no non-trivial primitive solutions when \alpha is a non-square mod p.
ps;
ps:=[ 167, 383, 503, 599, 647, 719, 743, 839, 863, 887, 911, 983, 1031, 1103, 1151,
1223, 1367, 1439, 1511, 1559, 1583, 1607, 1823, 1871, 2039, 2063, 2111, 2207,
2351, 2399, 2423, 2543 ];

