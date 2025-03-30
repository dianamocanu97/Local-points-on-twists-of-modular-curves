//Verifying assumptions of Table 3:

Q3 := pAdicField(3, 500);
P<x>:=PolynomialRing(Q3);

// Examples with e=12
examples := [
    <x^12 + 3*x^4 + 3, [0, 0, 0, 0, -2]>,
    <x^12 + 3*x^4 + 3, [0, 0, 1, 0, -7]>,
    <x^12 + 6*x^6 + 6*x^4 + 3, [0, 0, 0, -6, -2]>,
    <x^12 + 6*x^6 + 6*x^4 + 3, [1, -1, 0, 12, 8]>,
    <x^12 + 6*x^9 + 6*x^6 + 24*x^3 + 9*x^2 + 18*x + 6, [0, 0, 0, 0, -3]>,
    <x^12 + 6*x^9 + 6*x^6 + 24*x^3 + 9*x^2 + 18*x + 6, [0, 0, 0, 0, 90]>,
    <x^12 + 21*x^6 + 9*x^4 + 9*x^2 + 6, [0, 0, 0, 0, -486]>,
    <x^12 + 21*x^6 + 9*x^4 + 9*x^2 + 6, [0, 0, 1, 0, 2]>,
    <x^12 + 3*x^9 + 15*x^6 + 9*x^5 + 9*x^4 + 18*x^2 + 24,[0, 0, 1, 0, -1]>,
    <x^12 + 3*x^9 + 15*x^6 + 9*x^5 + 9*x^4 + 18*x^2 + 24,[0, 0, 0, 0, -162]>
];

for  ex in examples do
    L := ext< Q3 |  ex[1]>;
    E := EllipticCurve( ex[2]);
    printf "Cremona label is %o\n", CremonaReference(E);
    
    E := MinimalModel(E);
    E := BaseChange(E,  Q3);
    
    print "Conductor of E is", Conductor(E);
    
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
    
    // Check good reduction over L'
    E := BaseChange(E, L);
    if Integers()!Conductor(E) eq 1 then
        print "E has good reduction over", L;
    end if;
    print "********************";
end for;