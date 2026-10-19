// This code verifies the claims in Section 11 and checks all five conditions
// of the revised Theorem 5.3.

// Condition (1): p = 3 (mod 4).  The lower bound p >= 7 from the
// hypotheses of Theorem 5.3 is included here as well.
function Checkcond1(p)
    return IsPrime(p) and p ge 7 and p mod 4 eq 3;
end function;

// Condition (2): -p*Delta_l is a square in Z.
function Checkcond2(D, p)
    return IsSquare(-p*D);
end function;

// Condition (3): for every prime q != l dividing Delta_l, (q/p) != -1.
function Checkcond3(D, l, p)
    primeFactors := PrimeDivisors(Abs(D));
    for q in primeFactors do
        if q ne l and LegendreSymbol(q, p) eq -1 then
            return false;
        end if;
    end for;
    return true;
end function;

// Condition (4): |a_l(E)| < p - 2*sqrt(l).
// This is checked exactly, without floating-point arithmetic: it is
// equivalent to p - |a_l(E)| > 0 and (p - |a_l(E)|)^2 > 4*l.
function Checkcond4(a, l, p)
    d := p - Abs(a);
    return d gt 0 and d^2 gt 4*l;
end function;

// Condition (5): l is not congruent to 1 modulo p.
function Checkcond5(l, p)
    return l mod p ne 1;
end function;

// Check the hypotheses and all five conditions of Theorem 5.3.

function CheckTheorem53(E, N, l, p)
    if not (IsPrime(l) and IsPrime(p) and p ge 7 and l ne p) then
        return false;
    end if;
    if N mod l eq 0 then
        return false;
    end if;
    if not Checkcond1(p) then
        return false;
    end if;

    a := TraceOfFrobenius(E, l);
    D := a^2 - 4*l;

    if not Checkcond2(D, p) then
        return false;
    end if;
    if not Checkcond4(a, l, p) then
        return false;
    end if;
    if not Checkcond5(l, p) then
        return false;
    end if;

    return Checkcond3(D, l, p);
end function;

// List of elliptic curves in the isogeny classes given in equation (11.8).
// These have v_5(Delta_min) = 2, which is important in the elimination step.
EC := [ "90a4", "90b2", "90c2", "180a2", "360a2", "360b2",
        "360c2", "360d2", "360e2" ];

// This function constructs the first Frey elliptic curve.
function Frey1(a, b, l)
    FF := GF(l);
    P<x> := PolynomialRing(FF);
    a := FF!a;
    b := FF!b;
    f := x^3 + 3*a*b*x + (b^3 - a^3);
    if Discriminant(f) ne 0 then
        E := EllipticCurve(f);
    end if;
    return E;
end function;

// This function computes the set S_l for the first Frey curve.
function traces1(l)
    tr := [];
    FF := GF(l);
    for a in FF do
        for b in FF do
            try
                t := TraceOfFrobenius(Frey1(a, b, l));
                Append(~tr, t);
            catch e;
            end try;
        end for;
    end for;
    return tr;
end function;

// This function constructs the second Frey elliptic curve.
function Frey2(a, b, l)
    FF := GF(l);
    P<x> := PolynomialRing(FF);
    a := FF!a;
    b := FF!b;
    f := x^3 + (3*(b-a)+2)/8*x^2 + 3*(a+b)^2/64*x
         + 9*((b-a)*(a+b)^2)/512;
    DiscE := -27/256*a^6 + 27/256*a^5 - 81/128*a^4*b - 315/1024*a^4
             - 27/128*a^3*b^3 - 189/256*a^3*b^2 + 9/256*a^3*b
             + 9/64*a^3 + 189/256*a^2*b^3 + 351/512*a^2*b^2
             + 9/64*a^2*b + 81/128*a*b^4 + 9/256*a*b^3
             - 9/64*a*b^2 - 27/256*b^6 - 27/256*b^5
             - 315/1024*b^4 - 9/64*b^3;
             // Discriminant of
             // y^2+xy=x^3+(3*(b-a)+2)/8*x^2+3*(a+b)^2/64*x
             //        +9*((b-a)*(a+b)^2)/512.
    if DiscE ne 0 then
        E := EllipticCurve(f, x);
    end if;
    return E;
end function;

// This function computes the set S_l for the second Frey curve.
function traces2(l)
    tr := [];
    FF := GF(l);
    for a in FF do
        for b in FF do
            try
                t := TraceOfFrobenius(Frey2(a, b, l));
                Append(~tr, t);
            catch e;
            end try;
        end for;
    end for;
    return tr;
end function;

// Compute B(E) with l < 300 for every E in the above list, and eliminate
// the curves for which B is nonzero.
for label in EC do
    E := EllipticCurve(label);
    B := 0;
    N := Conductor(E);
    if N eq 90 then
        // Use the family implemented by Frey2.
        for l in PrimesInInterval(7, 300) do
            if N mod l ne 0 then
                al := TraceOfFrobenius(E, l);
                Bl := (l+1)^2 - al^2;
                for a in traces2(l) do
                    Bl := Bl*(a-al);
                end for;
                B := GCD(B, Bl);
            end if;
        end for;
    else
        // Use the family implemented by Frey1.
        for l in PrimesInInterval(7, 300) do
            if N mod l ne 0 then
                al := TraceOfFrobenius(E, l);
                Bl := (l+1)^2 - al^2;
                for a in traces1(l) do
                    Bl := Bl*(a-al);
                end for;
                B := GCD(B, Bl);
            end if;
        end for;
    end if;
    if B ne 0 then
        print "B is", Factorisation(B);
        print "ELIMINATE", label,
              "for p not in the following factorisation", Factorisation(B);
    else
        print "B is", B;
    end if;
end for;
// This step eliminates 180a2, 360b2, and 360c2.

// Check the five conditions in the revised Theorem 5.3 for primes p in
// the interval 20..1000.
EC := [ "90a4", "90b2", "90c2", "360a2", "360d2", "360e2" ];
ps := [];
for p in PrimesInInterval(20, 1000) do
    if Checkcond1(p) then
        okp := 0;
        // Condition (4) implies 4*l < p^2, so this is an exhaustive finite
        // search for eligible l. The inequality is checked exactly.
        // For these curves, 2, 3 and 5 are bad-reduction primes,
        // so starting at 7 omits no eligible primes.
        lmax := (p^2 - 1) div 4;
        for label in EC do
            E := EllipticCurve(label);
            N := Conductor(E);
            for l in PrimesInInterval(7, lmax) do
                // Cheap hypotheses/condition (5) are tested before the
                // Frobenius trace calculation.
                if l ne p and N mod l ne 0 and Checkcond5(l, p) then
                    if CheckTheorem53(E, N, l, p) then
                        okp +:= 1;
                        print "Conditions (1)-(5) hold for", label,
                              "with p =", p, "and l =", l;
                        break l;
                    end if;
                end if;
            end for;
        end for;
        if okp eq #EC then
            print "p is good for all curves", p;
            Append(~ps, p);
        end if;
    end if;
end for;

// Primes p<1000 for which x^3+y^3=5^alpha*z^p has no non-trivial primitive
// solutions when alpha is a nonsquare modulo p.

ps;

//This gives:
// ps=[ 167, 191, 383, 431, 479, 503, 599, 647, 719, 743, 839, 863, 887, 911, 983];
