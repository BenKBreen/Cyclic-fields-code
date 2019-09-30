X := 10^33;
ell := 7;




defaultprec := 100;

ellicGaussianPeriod := function(f,plist,chilist : Precision := 0);
  if Precision eq 0 then
    prec := defaultprec;
  else
    prec := Precision;
  end if;
  CC<I> := ComplexField(prec);
  zf := Exp(2*Pi(CC)*I/f);

  z3ps := [* (Integers(p)!PrimitiveRoot(p))^(EulerPhi(p) div ell) : p in plist *];
  z3ps := [* [g^i : i in [0..ell-1]] : g in z3ps *];

  as := [];

  gsums := [CC | 0 : i in [1..ell]];
  for a := 1 to f do
    if Gcd(a,f) gt 1 then continue; end if;
    chia := Integers(ell)!0;
    for j := 1 to #plist do
      p := plist[j];
      chia +:= chilist[j]*(Index(z3ps[j],(Integers(p)!a)^(EulerPhi(p) div ell))-1);
    end for;
    
    gsums[(Integers()!chia)+1] +:= zf^a;
  end for;
  // print as;
  return [Re(gs) : gs in gsums];
end function;

ellicField := function(f,plist,chilist);
  gsums := ellicGaussianPeriod(f,plist,chilist : Precision := Round(10*Log(f)));
  _<T> := PolynomialRing(Universe(gsums));
  gsumpol := &*[T-g : g in gsums];
  fpol := Polynomial([Round(c) : c in Coefficients(gsumpol)]);
  K := NumberField(fpol);
  if ell^2 in plist then
    assert plist[1] eq ell^2;
    plist0 := [ell] cat plist[2..#plist];
  else
    plist0 := plist;
  end if;
  // print plist0;
  // print K;
  ZK := MaximalOrder(K : Ramification := plist0);
  assert Discriminant(ZK) eq f^(ell-1);
  assert IsAbelian(GaloisGroup(K));
  return K;
end function;





fmax := Floor(X^(1/(ell-1)));
for fcond := 2 to fmax do
  if not (fcond mod ell eq 1 or fcond mod ell^2 eq 0) then continue; end if;
  ffact := Factorization(fcond);
  if &and[(c[1] eq ell and c[2] eq 2) or (c[1] mod ell eq 1 and c[2] eq 1) : c in ffact] then
    plist := [c[1]^c[2] : c in ffact];
    if #plist eq 1 then
      F := ellicField(fcond,plist,[1]);
      printf "%o, %o\n", Eltseq(DefiningPolynomial(F)), fcond^6;
    else
      for chilisttup in CartesianPower([1..ell-1], #plist-1) do
        chilist := [1] cat [c : c in chilisttup];
        F := ellicField(fcond,plist,chilist);
        printf "%o, %o\n", Eltseq(DefiningPolynomial(F)), fcond^6;
      end for;
    end if;
  end if;
end for;
