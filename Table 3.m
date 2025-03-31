//Verifying assumptions of Table 3:

P<x>:=PolynomialRing(Rationals());

// Examples with e=12
examples := [
    <x^12 + 3*x^4 + 3, "1728v1">,
    <x^12 + 3*x^4 + 3, "27a1">,
    <x^12 + 6*x^6 + 6*x^4 + 3, "12096dd1">,
    <x^12 + 6*x^6 + 6*x^4 + 3, "54a1">,
    <x^12 + 6*x^9 + 6*x^6 + 24*x^3 + 9*x^2 + 18*x + 6, "972b1">,
    <x^12 + 6*x^9 + 6*x^6 + 24*x^3 + 9*x^2 + 18*x + 6, "388800oh1">,
    <x^12 + 21*x^6 + 9*x^4 + 9*x^2 + 6, "15552c2">,
    <x^12 + 21*x^6 + 9*x^4 + 9*x^2 + 6, "243b1">,
    <x^12 + 3*x^9 + 15*x^6 + 9*x^5 + 9*x^4 + 18*x^2 + 24,"243a1">,
    <x^12 + 3*x^9 + 15*x^6 + 9*x^5 + 9*x^4 + 18*x^2 + 24,"15552bp2">
];

for  ex in examples do
    print "Example label:", ex[2];
    f:=ex[1]; F := NumberField(f);
    E := EllipticCurve(ex[2]); E := MinimalModel(E);
    t:=LocalInformation(E,3);
    
    print "Conductor exponent at 3 = ",t[3] ;
    
    // Compute invariants
    c4, c6 := Explode(cInvariants(E));
    c4 := Integers()!c4; c6 := Integers()!c6;
    Delta := Integers()!Discriminant(E);
    
    // Compute valuations
    v4 := Valuation(c4, 3);
    v6 := Valuation(c6, 3);
    vD := Valuation(Delta, 3);
    
    printf "(v(c_4), v(c_6), v(Delta_m)) = (%o, %o, %o)\n", v4, v6, vD;
    
    // Compute tilde invariants
    tD := Delta div 3^vD;
    print "tilde{Delta} =", tD mod 9, "mod 9";
    
    //Check good reduction at L'
    E := BaseChange(E, F);
    OF:=MaximalOrder(F);
    P:=Factorization(3*OF);
    t:=LocalInformation(E,P[1][1]);
    if t[3] eq 0 then
        print "E has good reduction over the extension of Q_3 by",f;
    end if;
        print "********************";
end for;
