//Verifying assumptions of Table 2:

Q2 := pAdicField(2, 500);
P<x>:=PolynomialRing(Q2);

//Example 1

L:= ext<Q2| x^8 + 2*x^6 + 4*x^3 + 4*x + 2>;

E := EllipticCurve([0, 1, 0, -2, 0]);
printf "Cremona label is %o\n", CremonaReference(E);
print "E defined over",Q2;

E := MinimalModel(E);
E := BaseChange(E, Q2);

print "Conductor of E is", Conductor(E);

// Compute invariants
c4, c6 := Explode(cInvariants(E));
c4:=Integers()!c4; c6:=Integers()!c6;
Delta := Integers()!Discriminant(E);

// Compute valuations
v4 := Valuation(c4, 2);
v6 := Valuation(c6, 2);
vD := Valuation(Delta, 2);

printf "(v(c_4), v(c_6), v(Delta_m)) = (%o, %o, %o)\n", v4, v6, vD;

// Compute tilde invariants
tc4 := c4 div 2^v4;

print "tilde{c_4} =", tc4 mod 4, "mod 4";

//Check good reduction over L'
E:=BaseChange(E,L);
if Integers()!Conductor(E) eq 1 then
    print "E has good reduction over", L;
end if;
print "********************";

//Example 2

L:= ext<Q2| x^8 + 2*x^6 + 4*x^3 + 4*x + 2>;

E := EllipticCurve([0, 0, 0, -108, -864]);
printf "Cremona label is %o\n", CremonaReference(E);
print "E defined over",Q2;

E := MinimalModel(E);
E := BaseChange(E, Q2);

print "Conductor of E is", Conductor(E);

// Compute invariants
c4, c6 := Explode(cInvariants(E));
c4:=Integers()!c4; c6:=Integers()!c6;
Delta := Integers()!Discriminant(E);

// Compute valuations
v4 := Valuation(c4, 2);
v6 := Valuation(c6, 2);
vD := Valuation(Delta, 2);

printf "(v(c_4), v(c_6), v(Delta_m)) = (%o, %o, %o)\n", v4, v6, vD;

// Compute tilde invariants
tc4 := c4 div 2^v4;

print "tilde{c_4} =", tc4 mod 4, "mod 4";

//Check good reduction over L'
E:=BaseChange(E,L);
if Integers()!Conductor(E) eq 1 then
    print "E has good reduction over", L;
end if;
print "********************";

//Example 3

L:= ext<Q2| x^8 + 2*x^6 + 4*x^3 + 4*x + 6>;

E := EllipticCurve([0, 0, 0, 3, 0]);
printf "Cremona label is %o\n", CremonaReference(E);
print "E defined over",Q2;

E := MinimalModel(E);
E := BaseChange(E, Q2);

print "Conductor of E is", Conductor(E);

// Compute invariants
c4, c6 := Explode(cInvariants(E));
c4:=Integers()!c4; c6:=Integers()!c6;
Delta := Integers()!Discriminant(E);

// Compute valuations
v4 := Valuation(c4, 2);
v6 := Valuation(c6, 2);
vD := Valuation(Delta, 2);

printf "(v(c_4), v(c_6), v(Delta_m)) = (%o, %o, %o)\n", v4, v6, vD;

// Compute tilde invariants
tc4 := c4 div 2^v4;

print "tilde{c_4} =", tc4 mod 4, "mod 4";

//Check good reduction over L'
E:=BaseChange(E,L);
if Integers()!Conductor(E) eq 1 then
    print "E has good reduction over", L;
end if;
print "********************";

//Example 4

L:= ext<Q2| x^8 + 2*x^6 + 4*x^3 + 4*x + 6>;

 E := EllipticCurve([0, 0, 0, -108, 0]);
printf "Cremona label is %o\n", CremonaReference(E);
print "E defined over",Q2;

E := MinimalModel(E);
E := BaseChange(E, Q2);

print "Conductor of E is", Conductor(E);

// Compute invariants
c4, c6 := Explode(cInvariants(E));
c4:=Integers()!c4; c6:=Integers()!c6;
Delta := Integers()!Discriminant(E);

// Compute valuations
v4 := Valuation(c4, 2);
v6 := Valuation(c6, 2);
vD := Valuation(Delta, 2);

printf "(v(c_4), v(c_6), v(Delta_m)) = (%o, %o, %o)\n", v4, v6, vD;

// Compute tilde invariants
tc4 := c4 div 2^v4;

print "tilde{c_4} =", tc4 mod 4, "mod 4";

//Check good reduction over L'
E:=BaseChange(E,L);
if Integers()!Conductor(E) eq 1 then
    print "E has good reduction over", L;
end if;
print "********************";

//Example 5

L:= ext<Q2| x^8 + 8*x^7 + 12*x^6 + 14*x^4 + 4*x^2 + 8*x + 14>;

E := EllipticCurve([0, 0, 0, 8, 0]);
printf "Cremona label is %o\n", CremonaReference(E);
print "E defined over",Q2;

E := MinimalModel(E);
E := BaseChange(E, Q2);

print "Conductor of E is", Conductor(E);

// Compute invariants
c4, c6 := Explode(cInvariants(E));
c4:=Integers()!c4; c6:=Integers()!c6;
Delta := Integers()!Discriminant(E);

// Compute valuations
v4 := Valuation(c4, 2);
v6 := Valuation(c6, 2);
vD := Valuation(Delta, 2);

printf "(v(c_4), v(c_6), v(Delta_m)) = (%o, %o, %o)\n", v4, v6, vD;

// Compute tilde invariants
tc4 := c4 div 2^v4;

print "tilde{c_4} =", tc4 mod 4, "mod 4";

//Check good reduction over L'
E:=BaseChange(E,L);
if Integers()!Conductor(E) eq 1 then
    print "E has good reduction over", L;
end if;
print "********************";

//Example 6

L:= ext<Q2| x^8 + 8*x^7 + 12*x^6 + 14*x^4 + 4*x^2 + 8*x + 14>;

E := EllipticCurve([0, 0, 0, 216, 0]);
printf "Cremona label is %o\n", CremonaReference(E);
print "E defined over",Q2;

E := MinimalModel(E);
E := BaseChange(E, Q2);

print "Conductor of E is", Conductor(E);

// Compute invariants
c4, c6 := Explode(cInvariants(E));
c4:=Integers()!c4; c6:=Integers()!c6;
Delta := Integers()!Discriminant(E);

// Compute valuations
v4 := Valuation(c4, 2);
v6 := Valuation(c6, 2);
vD := Valuation(Delta, 2);

printf "(v(c_4), v(c_6), v(Delta_m)) = (%o, %o, %o)\n", v4, v6, vD;

// Compute tilde invariants
tc4 := c4 div 2^v4;

print "tilde{c_4} =", tc4 mod 4, "mod 4";

//Check good reduction over L'
E:=BaseChange(E,L);
if Integers()!Conductor(E) eq 1 then
    print "E has good reduction over", L;
end if;
print "********************";

//Example 7

f:=x^8 + 2*x^3 + 2*x^2 + 2;
F:=SplittingField(f);

E := EllipticCurve([0, 0, 0, -3, -1]);
printf "Cremona label is %o\n", CremonaReference(E);
print "E defined over",Q2;

E := MinimalModel(E);
E := BaseChange(E, Q2);

print "Conductor of E is", Conductor(E);

// Compute invariants
c4, c6 := Explode(cInvariants(E));
c4:=Integers()!c4; c6:=Integers()!c6;
Delta := Integers()!Discriminant(E);

// Compute valuations
v4 := Valuation(c4, 2);
v6 := Valuation(c6, 2);
vD := Valuation(Delta, 2);

printf "(v(c_4), v(c_6), v(Delta_m)) = (%o, %o, %o)\n", v4, v6, vD;

print "v_2(Delta_m) = ", vD mod 3, "mod 3";

//Check good reduction over F'
E:=BaseChange(E,F);
if Integers()!Conductor(E) eq 1 then
    print "E has good reduction over the splitting field of", L;
end if;
print "********************";


//Example 8
f:=x^8 + 2*x^3 + 2*x^2 + 2;
F:=SplittingField(f);

E := EllipticCurve([0, 0, 0, -135, -54]);
printf "Cremona label is %o\n", CremonaReference(E);
print "E defined over",Q2;

E := MinimalModel(E);
E := BaseChange(E, Q2);

print "Conductor of E is", Conductor(E);

// Compute invariants
c4, c6 := Explode(cInvariants(E));
c4:=Integers()!c4; c6:=Integers()!c6;
Delta := Integers()!Discriminant(E);

// Compute valuations
v4 := Valuation(c4, 2);
v6 := Valuation(c6, 2);
vD := Valuation(Delta, 2);

printf "(v(c_4), v(c_6), v(Delta_m)) = (%o, %o, %o)\n", v4, v6, vD;

print "v_2(Delta_m) = ", vD mod 3, "mod 3";

//Check good reduction over F'
E:=BaseChange(E,F);
if Integers()!Conductor(E) eq 1 then
    print "E has good reduction over the splitting field of", L;
end if;
print "********************";

//Example 9
f:=x^8 + 4*x^7 + 8*x^4 + 8*x^3 + 4*x^2 + 8*x + 10;
F:=SplittingField(f);

E := EllipticCurve([0, 0, 0, 3, 2]);
printf "Cremona label is %o\n", CremonaReference(E);
print "E defined over",Q2;

E := MinimalModel(E);
E := BaseChange(E, Q2);

print "Conductor of E is", Conductor(E);

// Compute invariants
c4, c6 := Explode(cInvariants(E));
c4:=Integers()!c4; c6:=Integers()!c6;
Delta := Integers()!Discriminant(E);

// Compute valuations
v4 := Valuation(c4, 2);
v6 := Valuation(c6, 2);
vD := Valuation(Delta, 2);

printf "(v(c_4), v(c_6), v(Delta_m)) = (%o, %o, %o)\n", v4, v6, vD;

print "v_2(Delta_m) = ", vD mod 3, "mod 3";

//Check good reduction over F'
E:=BaseChange(E,F);
if Integers()!Conductor(E) eq 1 then
    print "E has good reduction over the splitting field of", L;
end if;
print "********************";


//Example 10
f:=x^8 + 4*x^7 + 8*x^4 + 8*x^3 + 4*x^2 + 8*x + 10;
F:=SplittingField(f);

E := EllipticCurve([0, 0, 0, 1080, -864]);
printf "Cremona label is %o\n", CremonaReference(E);
print "E defined over",Q2;

E := MinimalModel(E);
E := BaseChange(E, Q2);

print "Conductor of E is", Conductor(E);

// Compute invariants
c4, c6 := Explode(cInvariants(E));
c4:=Integers()!c4; c6:=Integers()!c6;
Delta := Integers()!Discriminant(E);

// Compute valuations
v4 := Valuation(c4, 2);
v6 := Valuation(c6, 2);
vD := Valuation(Delta, 2);

printf "(v(c_4), v(c_6), v(Delta_m)) = (%o, %o, %o)\n", v4, v6, vD;

print "v_2(Delta_m) = ", vD mod 3, "mod 3";

//Check good reduction over F'
E:=BaseChange(E,F);
if Integers()!Conductor(E) eq 1 then
    print "E has good reduction over the splitting field of", L;
end if;
print "********************";