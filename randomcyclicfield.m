ell := 3;  // prime degree of field
X := 10^7;

pmodelleq1 := function(p);
  return p mod ell eq 1 or p eq ell;
end function;

nellicdisc := function(n);
  return n gt 1 and (Valuation(n,ell) eq 0 and IsSquarefree(n)) or (Valuation(n,ell) eq 2 and IsSquarefree(n div ell^2));
end function;

nweightellic := function(plist);
  if #plist eq 0 then
    return 1;
  elif #plist ge 2 and Sort(plist)[1..2] eq [ell,ell] then
    return (ell-1)^(#plist-2);
  else
    return (ell-1)^(#plist-1);
  end if;
end function;

nweightmaxellic := function(n);
  p := NextPrime(ell);
  while not pmodelleq1(p) do 
    p := NextPrime(p);
  end while;
  weightmin := p;
  p := NextPrime(p);
  while not pmodelleq1(p) do 
    p := NextPrime(p);
  end while;
  p *:= weightmin;

  if n lt weightmin then 
    return ell-1;
  else
    nmax := PrimeFactors(weightmin);
    while &*nmax le n do
      p := NextPrime(nmax[#nmax]);
      while not pmodelleq1(p) do 
        p := NextPrime(p);
      end while;
      Append(~nmax,p);
    end while;
    return (ell-1)^(#nmax-1);
  end if;
end function;

RandomWeightedFactoredInteger := function(n : ptest := false, ntest := false, nweight := 1, nweightmax := 1);
  // returns a random factor from 1 to n
  // ptest is a function that keeps only certain primes
  // ntest is a requirement on the integer

  if Type(ptest) eq BoolElt then
    ptest := function(p); return true; end function;
  end if;
  if Type(ntest) eq BoolElt then
    ntest := function(n); return true; end function;
  end if;
  if Type(nweight) eq RngIntElt then
    nweight := function(n); return 1; end function;
  end if;
    
  while true do
    seq := [Random(1,n)];
    while seq[#seq] gt 1 do
      Append(~seq, Random(1,seq[#seq]));
    end while;
    seq := [si : si in seq | IsPrime(si)];
    if #seq eq 0 then 
      r := 1; 
    else 
      r := &*seq;
    end if;
    if r le n then
      if &and[ptest(si) : si in seq] and ntest(r) and Random(1,n) le r and Random(1,nweightmax) le nweight(seq) then //  r*nweight(seq) then
        return r, seq;
      end if;
    end if;
  end while;
end function;

RandomellicCharacter := function(plist);
  return [1] cat [Random(1,ell-1) : c in [2..#plist]];
end function;

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








h := function(x);
  if x eq 1 then return 0; else return 1; end if;
end function;

tworank := function(G);
  return #[c : c in G | c mod 2 eq 0];
end function;

r1 := ell;

SetClassGroupBounds("GRH");



f := 1;
while 2^f mod ell ne 1 do
  f +:= 1;
end while;

computdat := [];
computdatben := [];
FieldList := [];

for i := 1 to 1000 do
  fcond, plist := RandomWeightedFactoredInteger(X : 
           ptest := pmodelleq1, ntest := nellicdisc, nweight := nweightellic);
  plist := Sort(plist);
  if #plist ge 2 and plist[1..2] eq [ell,ell] then
    plist := [ell^2] cat plist[3..#plist];
  end if;         
  chilist := RandomellicCharacter(plist);
  F := ellicField(fcond,plist,chilist);
  fielddisc := fcond^(ell-1);
  fielddatseq := Eltseq(MinimalPolynomial(F.1));
  print "Field =", fielddatseq;  
  R := Integers(F);
  D := Discriminant(R);
  assert D eq fielddisc;
  assert Signature(F) eq ell;
  print "After field computation = ", Cputime();  
  twofact := Factorization(2*R);
  ClF := ClassGroup(R);
  /*
  ClFplus := RayClassGroup(1*R, [1..Degree(F)]);
  U, m := pFundamentalUnits(R, 2 : Al := "ClassGroup");
  Sel2, mS := pSelmerGroup(2, {Parent(2*R) | });
  Sel2gens := [Sel2.i@@mS : i in [1..#Generators(Sel2)]];
  for i := 1 to #Sel2gens do
    sel2i := Sel2gens[i];
    _, bbi := IsPower(sel2i*R,2);
    if Norm(bbi) mod 2 eq 0 then
      bbi2 := &*[pp[1]^pp[2] : pp in Factorization(bbi) | Norm(pp[1]) mod 2 eq 0];
      bbi2_basis := Basis(bbi2^-1);
      z := bbi2_basis[1];
      while Integers()!(Norm(sel2i*z^2)) mod 2 eq 0 do
        z +:= (-1)^(Random(2))*Random(bbi2_basis);
      end while;
      assert mS(sel2i*z^2) eq mS(sel2i);
      Sel2gens[i] := sel2i*z^2;
    end if;
  end for;
  R4R, m4R := quo<R | 4*R>;
  U4R, mU4R := UnitGroup(R4R);
  U4Rsq, mU4Rsq := quo<U4R | [2*U4R.i : i in [1..#Generators(U4R)]]>;
  E := Matrix(GF(2),[[h(ux) : ux in RealSigns(m(U.i))] cat Eltseq(mU4Rsq(m4R(m(U.i))@@mU4R)) : i in [1..Degree(F)]]);
  M := Matrix(GF(2),[[h(ux) : ux in RealSigns(s)] cat Eltseq(mU4Rsq(m4R(s)@@mU4R)) : s in Sel2gens]);
  k := Dimension(Kernel(Submatrix(M,1,r1+1,Nrows(M),r1))) - Dimension(Kernel(M));
  sgnrk := Rank(Submatrix(E,1,1,r1,r1));
  rhooo := r1-sgnrk;
  */
  rho := tworank(AbelianInvariants(ClF));
  print "After class group computation = ", Cputime();
  /*
  rhoplus := tworank(AbelianInvariants(ClFplus));
  is_split := (rhoplus eq rho+rhooo);
  */
  vv := [* D, fielddatseq, rho, AbelianInvariants(ClF)*];
  //vv := [* D, fielddatseq, rho, rhoplus, sgnrk, is_split, AbelianInvariants(ClF), AbelianInvariants(ClFplus), E, M *];
  Append(~computdat, vv);
  
  test := true;

  for K in FieldList do
    if IsIsomorphic(K,F) then 
      test := false;
      break;
    end if;
  end for;
  
  if test eq true then
    Append(~FieldList,F);
  end if;

  // Append(~computdatben, [*D,fielddatseq*]);
  if i mod 10 eq 0 then
    print i, #FieldList;
    print [#[v : v in computdat | v[3] eq i] : i in [0..Floor(ell/2)]];
    /*
    print [#[v : v in computdat | v[4] eq 0 and v[6] eq i] : i in [1..ell]];
    print [#[v : v in computdat | v[4] eq f and v[6] eq i] : i in [1..ell]];
    print [#[v : v in computdat | v[4] eq 2*f and v[6] eq i] : i in [1..ell]];
    print [#[v : v in computdat | v[6] eq i] : i in [1..ell]];
    print [#[v : v in computdat | v[4] eq i*f] : i in [0..2]];
    print [&+[2^(i*v[4]) : v in computdat] : i in [1..ell]];
    print [#[v : v in computdat | v[5] eq i] : i in [0..ell]];
    print [&+[2^(i*v[5]) : v in computdat] : i in [1..ell]];
    print #[v : v in computdat | v[7]];
    */
  end if;
end for;
