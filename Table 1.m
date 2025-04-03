for p in [2, 3] do
    Qp := pAdicField(p, 20);
    P<x> := PolynomialRing(Qp);
    
    if p eq 2 then
        f:=x^4 + 12*x^2 + 6;
        F:=ext<Qp |f >;
        examples := [
           "6912j1",
           "6912l1"
        ];
    else
        f:=x^3 + 3*x^2 + 3;
        F:=ext<Qp |f >;
        examples := [
            "25920z1",
            "25920v1"
        ];
    end if;
    
    for label in examples do
        print "Example with Cremona label", label, "defined over", Qp;
        E := EllipticCurve(label);

        E := MinimalModel(E);
        E := BaseChange(E, Qp);

        // Compute invariants
        c4, c6 := Explode(cInvariants(E));
        c4 := Integers()!c4; c6 := Integers()!c6;
        Delta := Integers()!Discriminant(E);

        // Compute valuations
        v4 := Valuation(c4, p);
        v6 := Valuation(c6, p);
        vD := Valuation(Delta, p);

        printf "(v(c_4), v(c_6), v(Delta_m)) = (%o, %o, %o)\n", v4, v6, vD;

        // Compute tilde invariants
        tc4 := c4 div p^v4;
        tc6 := c6 div p^v6;
        tD := Delta div p^vD;

        if p eq 2 then
            print "tilde{c_6} =", tc6 mod 4, "mod 4";
            if tc4 mod 8 eq 5*tD mod 8 then
                print "tilde{c_4} = 5 tilde{Delta} mod 8";
            end if;
            print "Conductor of E = ", Conductor(E);
        else
            print "tilde{c_6} =", tc6 mod 3, "mod 3";
            if tD mod 3 eq 2 then
                print "tilde{Delta} = 2 mod 3";
            end if;
        end if;

        // Check good reduction over F
        E := BaseChange(E, F);
        if Integers()!Conductor(E) eq 1 then
            print "E has good reduction over", F;
        end if;
        print "********************";
    end for;
end for;
