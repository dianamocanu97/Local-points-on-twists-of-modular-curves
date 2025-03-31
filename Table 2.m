//Verifying assumptions of Table 2

P<x> := PolynomialRing(Rationals());

// Examples with e=8
examples := [
    <x^8 + 2*x^6 + 4*x^3 + 4*x + 2, "96a1">,
    <x^8 + 2*x^6 + 4*x^3 + 4*x + 2, "2592f1">,
    <x^8 + 2*x^6 + 4*x^3 + 4*x + 6, "288a1">,
    <x^8 + 2*x^6 + 4*x^3 + 4*x + 6, "288e2">,
    <x^8 + 8*x^7 + 12*x^6 + 14*x^4 + 4*x^2 + 8*x + 14, "256b2">,
    <x^8 + 8*x^7 + 12*x^6 + 14*x^4 + 4*x^2 + 8*x + 14, "2304a2">
];

for  ex in examples do
    print "Example label:", ex[2];
    f:=ex[1]; F := NumberField(f);
    E := EllipticCurve(ex[2]); E := MinimalModel(E);
    t:=LocalInformation(E,2);
    
    print "Conductor exponent at 2 = ",t[3] ;
    
    // Compute invariants
    c4, c6 := Explode(cInvariants(E));
    c4 := Integers()!c4; c6 := Integers()!c6;
    Delta := Integers()!Discriminant(E);
    
    // Compute valuations
    v4 := Valuation(c4, 2);
    v6 := Valuation(c6, 2);
    vD := Valuation(Delta, 2);
    
    printf "(v(c_4), v(c_6), v(Delta_m)) = (%o, %o, %o)\n", v4, v6, vD;
    
    // Compute tilde invariants
    tc4 := c4 div 2^v4;
    print "tilde{c_4} =", tc4 mod 4, "mod 4";
    
    //Check good reduction at L'
    E := BaseChange(E, F);
    OF:=MaximalOrder(F);
    P:=Factorization(2*OF);
    t:=LocalInformation(E,P[1][1]);
    if t[3] eq 0 then
        print "E has good reduction over the extension of Q_2 by",f;
    end if;
        print "********************";
end for;

// Examples with e=24

examples := [
    <x^8 + 2*x^3 + 2*x^2 + 2, "648b1">,
    <x^8 + 2*x^3 + 2*x^2 + 2, "6696q1">,
    <x^8 + 4*x^7 + 8*x^4 + 8*x^3 + 4*x^2 + 8*x + 10, "3456a1">,
    <x^8 + 4*x^7 + 8*x^4 + 8*x^3 + 4*x^2 + 8*x + 10, "289152l1">
];

for ex in examples do
    print "Example label:", ex[2];
    f := ex[1]; F := SplittingField(f);
    E := EllipticCurve(ex[2]); E := MinimalModel(E);
    t:=LocalInformation(E,2);
    
    print "Conductor exponent at 2 = ",t[3] ;
    
    // Compute invariants
    c4, c6 := Explode(cInvariants(E));
    c4 := Integers()!c4; c6 := Integers()!c6;
    Delta := Integers()!Discriminant(E);
    
    // Compute valuations
    v4 := Valuation(c4, 2);
    v6 := Valuation(c6, 2);
    vD := Valuation(Delta, 2);
    
    printf "(v(c_4), v(c_6), v(Delta_m)) = (%o, %o, %o)\n", v4, v6, vD;
    
    print "v_2(Delta_m) = ", vD mod 3, "mod 3";
    
//Check good reduction at L'
    E := BaseChange(E, F);
    OF:=MaximalOrder(F);
    P:=Factorization(2*OF);
    t:=LocalInformation(E,P[1][1]);
    if t[3] eq 0 then
        print "E has good reduction over the splitting field of",f, "over Q_2";
    end if;
        print "********************";
end for;
end for;
