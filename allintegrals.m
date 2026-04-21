////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Built on https://github.com/jtuitman/Coleman/blob/master/singleintegrals.m
////////////////////////////////////////////////////////////////////////////////////////////////////////////



function cEvaluate(f,c)
if Type(f) ne FldRatElt and Type(f) ne RngIntElt and Type(f) ne FldPadElt then
return Evaluate(f,c);
else
return f;
end if;
end function;


max_prec:=function(Q,p,N,g,W0,Winf,e0,einf);

  // Compute the p-adic precision required for provable correctness

  d:=Degree(Q);
  W:=Winf*W0^(-1);
  
  Nmax:=N+Floor(log(p,-p*(ord_0_mat(W)+1)*einf));
  while (Nmax-Floor(log(p,p*(Nmax-1)*e0))-Floor(log(p,-(ord_inf_mat(W^(-1))+1)*einf)) lt N) do 
    Nmax:=Nmax+1;
  end while;

  Nmax:=Maximum(Nmax,2); 

  return Nmax; // precision to be used in the computations
end function;


frobmatrix:=function(Q,p,N,Nmax,g,r,W0,Winf,G0,Ginf,frobmatb0r,red_list_fin,red_list_inf,basis,integrals,quo_map);

  // Compute the matrix of F_p on H^1(X) mod p^N with respect to 'basis'.

  F:=ZeroMatrix(Rationals(),#basis,#basis);  
  f0list:=[];
  finflist:=[];
  fendlist:=[];

  for i:=1 to #basis do

    dif:=frobenius(basis[i],Q,p,Nmax,r,frobmatb0r);
    dif:=convert_to_Qxzzinvd(dif,Q);

    coefs,f0,finf,fend:=reduce_with_fs(dif,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map);

    for j:=1 to #basis do
      F[i,j]:=coefs[j];
    end for;
    
    f0list:=Append(f0list,f0);
    finflist:=Append(finflist,finf);
    fendlist:=Append(fendlist,fend);

  end for;
 
  return F,f0list,finflist,fendlist;

end function;


coleman_data:=function(Q,p,N:useU:=false,basis0:=[],basis1:=[],basis2:=[])

  // Takes a polynomial Q in two variables x,y over the rationals which is monic in y.
  // Returns the Coleman data of (the projective nonsingular model of) the curve defined
  // by Q at p to p-adic precision N.

  if not IsIrreducible(Q) then
    error "Curve is not irreducible";
  end if;

  if not IsMonic(Q) then
    error "Curve is not monic";
  end if;

  d:=Degree(Q);
  g:=genus(Q,p);
  r,Delta,s:=auxpolys(Q);

  W0:=mat_W0(Q);
  W0inv:=W0^(-1);
  Winf:=mat_Winf(Q);
  Winfinv:=Winf^(-1);
  W:=Winf*W0^(-1);

  if (FiniteField(p)!LeadingCoefficient(Delta) eq 0) or (Degree(r) lt 1) or (not smooth(r,p)) or (not (is_integral(W0,p) and is_integral(W0inv,p) and is_integral(Winf,p) and is_integral(Winfinv,p))) then
    error "bad prime";
  end if;


  G:=con_mat(Q,Delta,s);
  G0:=W0*Evaluate(G,Parent(W0[1,1]).1)*W0^(-1)+ddx_mat(W0)*W0^(-1);
  Ginf:=Winf*Evaluate(G,Parent(Winf[1,1]).1)*Winf^(-1)+ddx_mat(Winf)*Winf^(-1);
   
  Jinf,Tinf,Tinfinv:=jordan_inf(Ginf);
  J0,T0,T0inv:=jordan_0(r,G0);
  e0,einf:=ram(J0,Jinf);
 
  delta:=Floor(log(p,-(ord_0_mat(W)+1)*einf))+Floor(log(p,(Floor((2*g-2)/d)+1)*einf));

  basis,integrals,quo_map:=basis_coho(Q,p,r,W0,Winf,G0,Ginf,J0,Jinf,T0inv,Tinfinv,useU,basis0,basis1,basis2);

  Nmax:=max_prec(Q,p,N,g,W0,Winf,e0,einf);

  frobmatb0r:=froblift(Q,p,Nmax-1,r,Delta,s,W0);

  red_list_fin,red_list_inf:=red_lists(Q,p,Nmax,r,W0,Winf,G0,Ginf,e0,einf,J0,Jinf,T0,Tinf,T0inv,Tinfinv);

  F,f0list,finflist,fendlist:=frobmatrix(Q,p,N,Nmax,g,r,W0,Winf,G0,Ginf,frobmatb0r,red_list_fin,red_list_inf,basis,integrals,quo_map);

  // formatting the output into a record:

  format:=recformat<Q,p,N,g,W0,Winf,r,Delta,s,G0,Ginf,e0,einf,delta,basis,quo_map,integrals,F,f0list,finflist,fendlist,Nmax,red_list_fin,red_list_inf,minpolys>;
  out:=rec<format|>;
  out`Q:=Q; out`p:=p; out`N:=N; out`g:=g; out`W0:=W0; out`Winf:=Winf; out`r:=r; out`Delta:=Delta; out`s:=s; out`G0:=G0; out`Ginf:=Ginf; 
  out`e0:=e0; out`einf:=einf; out`delta:=delta; out`basis:=basis; out`quo_map:=quo_map; out`integrals:=integrals; out`F:=F; out`f0list:=f0list; 
  out`finflist:=finflist; out`fendlist:=fendlist; out`Nmax:=Nmax; out`red_list_fin:=red_list_fin; out`red_list_inf:=red_list_inf;

  return out;

end function;


set_point:=function(x0,y0,data)

  // Constructs a point from affine coordinates x0,y0. 

  Q:=data`Q; p:=data`p; N:=data`N; W0:=data`W0;
  d:=Degree(Q);

  if x0 in RationalField() then
    K:=pAdicField(p,N);
  else
    K:=Parent(x0);
  end if;
  x0:=K!x0; y0:=K!y0;

  if Valuation(x0) lt 0 then
    error "x0 has negative valuation";
  end if;
  
  if (not(W0 eq IdentityMatrix(BaseRing(W0),d))) and (Valuation(Evaluate(data`r,x0)) gt 0) then
    error "W0 is not the identity and r(x0) is zero mod p";
  end if;
  
  format:=recformat<x,b,inf,xt,bt,index>;
  P:=rec<format|>;
  P`inf:=false;
  P`x:=x0;

  y0powers:=[];
  y0powers[1]:=K!1;
  for i:=2 to d do
    y0powers[i]:=(y0)^(i-1);
  end for;
  y0powers:=Vector(y0powers);
  W0x0:=Transpose(Evaluate(W0,x0));

  P`b:=Eltseq(y0powers*W0x0); // the values of the b_i^0 at P

  return P;
end function;


set_bad_point:=function(x,b,inf,data)

  Q:=data`Q; p:=data`p; N:=data`N; 
  Qp:=pAdicField(p,N); d:=Degree(Q);

  format:=recformat<x,b,inf,xt,bt,index>;
  P:=rec<format|>;
  P`inf:=inf;
  P`x:=Qp!x;
  P`b:=[Qp!b[i]:i in [1..d]];

  return P; 

end function;


is_bad:=function(P,data)

  // check whether the point P is bad

  x0:=P`x; r:=data`r;

  if P`inf then // infinite point
    return true;
  end if;

  if Valuation(Evaluate(r,x0)) gt 0 then // finite bad point
    return true;
  end if;

  return false;
  
end function;


is_very_bad:=function(P,data)

  // check whether the point P is very bad

  x0:=P`x; r:=data`r; N:=data`N;

  if P`inf then // infinite point
    if Valuation(x0) ge N then // infinite very bad point
      return true;
    end if;
  else // finite point
    if Valuation(Evaluate(r,x0)) ge N then // finite very bad point
      return true;
    end if;
  end if;

  return false;

end function;


lie_in_same_disk:=function(P1,P2,data)

  // check whether two points P1,P2 lie in the same residue disk

  x1:=P1`x; b1:=P1`b; x2:=P2`x; b2:=P2`b; Q:=data`Q;
  d:=Degree(Q);
  
  if P1`inf ne P2`inf then // one point infinite, other not
    return false;
  else
    for i:=1 to d do
        if Valuation(b1[i]-b2[i]) lt 1 then
          return false;
        end if;
      end for;
      return true;
  end if;
 
end function;


minpoly:=function(f1,f2)

  // computes the minimum polynomial of f2 over Q(f1), where
  // f1,f2 are elements of a 1 dimensional function field over Q

  FF:=Parent(f1);

  d:=5;  

  done:=false;
  while not done do

    S:=[];
    for i:=0 to d do
      for j:=0 to d do
        S:=Append(S,f1^j*f2^i);
      end for;
    end for;

    denom:=1;
    for i:=1 to #S do
      E:=Eltseq(S[i]);
      for j:=1 to #E do
        denom:=LCM(denom,Denominator(E[j]));
      end for;
    end for;
  
    maxdeg:=0;
    for i:=1 to #S do
      E:=Eltseq(S[i]);
      for j:=1 to #E do
        deg:=Degree(Numerator(denom*E[j]));
        if  deg gt maxdeg then
          maxdeg:=deg;
        end if;
      end for;
    end for;

    T:=[];
    for i:=1 to #S do
      E:=Eltseq(S[i]);
      v:=[];
      for j:=1 to #E do
        for k:=0 to maxdeg do
          v[(j-1)*(maxdeg+1)+k+1]:=Coefficient(Numerator(denom*E[j]),k);
        end for;  
      end for;
      T:=Append(T,v);
    end for;

    b:=Basis(NullSpace(Matrix(T)));  

    if #b gt 0 then
      done:=true;
      R:=b[1];
    else
      d:=d+3;
    end if;
  
  end while;

  poly:=Qxy!0;
  for i:=0 to d do
    for j:=0 to d do
      poly:=poly+R[i*(d+1)+j+1]*Qx.1^j*Qxy.1^i;
    end for;
  end for;

  fac:=Factorisation(poly);

  for i:=1 to #fac do
    factor:=fac[i][1];
    test:=FF!0;
    for j:=0 to Degree(factor) do
      test:=test+Evaluate(Coefficient(factor,j),f1)*f2^j;
    end for;
    if test eq 0 then
      poly:=factor;
    end if;
  end for;

  return poly;
 
end function;


update_minpolys:=function(data,inf,index);

  // TODO comment

  Q:=data`Q; W0:=data`W0; Winf:=data`Winf; 
  d:=Degree(Q);

  if not assigned data`minpolys then
    data`minpolys:=[ZeroMatrix(Qxy,d+2,d+2),ZeroMatrix(Qxy,d+2,d+2)];
  end if;
  minpolys:=data`minpolys;

  Qt:=RationalFunctionField(RationalField()); Qty:=PolynomialRing(Qt);

  f:=Qty!0;
  for i:=0 to d do
    for j:=0 to Degree(Coefficient(Q,i)) do
      f:=f+Coefficient(Coefficient(Q,i),j)*Qty.1^i*Qt.1^j;
    end for;
  end for;  
  FF:=FunctionField(f); // function field of curve

  if inf then 
    W:=Winf;
  else
    W:=W0;
  end if;

  bfun:=[];
  for i:=1 to d do
    bi:=FF!0;
    for j:=1 to d do
      bi:=bi+W[i,j]*FF.1^(j-1);
    end for;
    bfun[i]:=bi;
  end for;

  if inf then // b=b^{infty}
    if index eq 0 then
       for i:=1 to d do
         if minpolys[2][1,i+1] eq 0 then
           minpolys[2][1,i+1]:=minpoly(FF!(1/Qt.1),bfun[i]);
         end if;
       end for;
    else
      if minpolys[2][index+1,1] eq 0 then
        minpolys[2][index+1,1]:=minpoly(bfun[index],FF!(1/Qt.1));
      end if;
      for i:=1 to d do
        if minpolys[2][index+1,i+1] eq 0 then
          minpolys[2][index+1,i+1]:=minpoly(bfun[index],bfun[i]);
        end if;
      end for;
    end if;
  else // b=b^0
    if index eq 0 then
      for i:=1 to d do
        if minpolys[1][1,i+1] eq 0 then
          minpolys[1][1,i+1]:=minpoly(FF!Qt.1,bfun[i]);
        end if;
      end for;
    else
      if minpolys[1][index+1,1] eq 0 then
        minpolys[1][index+1,1]:=minpoly(bfun[index],FF!Qt.1);
      end if;
      for i:=1 to d do
        if minpolys[1][index+1,i+1] eq 0 then
          minpolys[1][index+1,i+1]:=minpoly(bfun[index],bfun[i]);
        end if;
      end for;
    end if;
  end if;

  data`minpolys:=minpolys;

  return data;

end function;


frobenius_pt:=function(P,data);

  // Computes the image of P under Frobenius

  x0:=P`x; Q:=data`Q; p:=data`p; N:=data`N; W0:=data`W0; Winf:=data`Winf;
  d:=Degree(Q); K:=Parent(x0); Ky:=PolynomialRing(K);

  x0p:=x0^p;
  b:=P`b;

  Qt:=RationalFunctionField(RationalField()); Qty:=PolynomialRing(Qt);

  f:=Qty!0;
  for i:=0 to d do
    for j:=0 to Degree(Coefficient(Q,i)) do
      f:=f+Coefficient(Coefficient(Q,i),j)*Qty.1^i*Qt.1^j;
    end for;
  end for;  
  FF:=FunctionField(f); // function field of curve

  if not is_bad(P,data) then // finite good point
    
    W0invx0:=Transpose(Evaluate(W0^(-1),x0));

    ypowers:=Vector(b)*W0invx0;
    y0:=ypowers[2];
  
    C:=Coefficients(Q);
    D:=[];
    for i:=1 to #C do
      D[i]:=Evaluate(C[i],x0p);
    end for;
    fy:=Ky!D;

    y0p:=HenselLift(fy,y0^p); // Hensel lifting
  
    y0ppowers:=[];
    y0ppowers[1]:=K!1;
    for i:=2 to d do
      y0ppowers[i]:=y0p^(i-1);
    end for;
    y0ppowers:=Vector(y0ppowers);

    W0x0:=Transpose(Evaluate(W0,x0));
  
    b:=Eltseq(y0ppowers*W0x0);

  elif P`inf then // infinite point
  
    for i:=1 to d do
      bi:=FF!0;
      for j:=1 to d do
        bi:=bi+Winf[i,j]*FF.1^(j-1);
      end for;

      if assigned data`minpolys and data`minpolys[2][1,i+1] ne 0 then
        poly:=data`minpolys[2][1,i+1];
      else
        poly:=minpoly(FF!(1/Qt.1),bi);
      end if;

      C:=Coefficients(poly);
      D:=[];
      for i:=1 to #C do
        D[i]:=Evaluate(C[i],x0p); 
      end for;
      fy:=Ky!D;

      fac:=Factorisation(fy); // Roots has some problems that Factorisation does not
      zeros:=[];
      for j:=1 to #fac do
        if Degree(fac[j][1]) eq 1 then
          zeros:=Append(zeros,-Coefficient(fac[j][1],0)/Coefficient(fac[j][1],1));
        end if;
      end for;
      
      done:=false;
      j:=1;
      while not done and j le #zeros do
        if Valuation(zeros[j]-b[i]^p) gt p then // was gt 0 before 
          done:=true;
          b[i]:=zeros[j];
        end if;
        j:=j+1;
      end while;
      if not done then
        error "Frobenius does not converge at P";
      end if;
    end for;

  else // finite bad point

   for i:=1 to d do
      bi:=FF!0;
      for j:=1 to d do
        bi:=bi+W0[i,j]*FF.1^(j-1);
      end for;

      if assigned data`minpolys and data`minpolys[1][1,i+1] ne 0 then
        poly:=data`minpolys[1][1,i+1];
      else
        poly:=minpoly(FF!Qt.1,bi);
      end if;

      C:=Coefficients(poly);
      D:=[];
      for i:=1 to #C do
        D[i]:=Evaluate(C[i],x0p); 
      end for;
      fy:=Ky!D;

      fac:=Factorisation(fy); // Roots has some problems that Factorisation does not
      zeros:=[];
      for j:=1 to #fac do
        if Degree(fac[j][1]) eq 1 then
          zeros:=Append(zeros,-Coefficient(fac[j][1],0)/Coefficient(fac[j][1],1));
        end if;
      end for;

      done:=false;
      j:=1;
      while not done and j le #zeros do
        if Valuation(zeros[j]-b[i]^p) gt p then
          done:=true;
          b[i]:=zeros[j];
        end if;
        j:=j+1;
      end while;
      if not done then
        error "Frobenius does not converge at P";
      end if;
    end for;

  end if;
  
    P`x:=x0p;
    P`b:=b;
    delete P`xt;
    delete P`bt;
    delete P`index;

  return P;
end function;


teichmueller_pt:=function(P,data)

  // Compute the Teichmueller point in the residue disk at a good point P

  x0:=P`x; Q:=data`Q; p:=data`p; N:=data`N; W0:=data`W0; Winf:=data`Winf;
  d:=Degree(Q); K:=Parent(x0); Ky:=PolynomialRing(K);

  if is_bad(P,data) then
    error "Point is bad";
  end if;

  x0new:=K!TeichmuellerLift(FiniteField(p)!x0,pAdicQuotientRing(p,N)); 
  b:=P`b; 
  W0invx0:=Transpose(Evaluate(W0^(-1),x0));
  ypowers:=Vector(b)*W0invx0;
  y0:=ypowers[2];
  
  C:=Coefficients(Q);
  D:=[];
  for i:=1 to #C do
    D[i]:=Evaluate(C[i],x0new);
  end for;
  fy:=Ky!D;

  y0new:=HenselLift(fy,y0); // Hensel lifting
  y0newpowers:=[];
  y0newpowers[1]:=K!1;
  for i:=2 to d do
    y0newpowers[i]:=y0newpowers[i-1]*y0new;
  end for;
  y0newpowers:=Vector(y0newpowers);

  W0x0:=Transpose(Evaluate(W0,x0));
  b:=Eltseq(y0newpowers*W0x0);

  P`x:=x0new;
  P`b:=b;
  delete P`xt;
  delete P`bt;
  delete P`index;

  return P;

end function;


local_data:=function(P,data)

  // For a point P, returns the ramification index of the map x on the residue disk at P

  Q:=data`Q; p:=data`p; W0:=data`W0; Winf:=data`Winf; x0:=P`x; b:=P`b; d:=Degree(Q);

  if not is_bad(P,data) then
    eP:=1;
    index:=0;
    return eP,index;
  else     
    Fp:=FiniteField(p); Fpx:=RationalFunctionField(Fp); Fpxy:=PolynomialRing(Fpx);
    f:=Fpxy!0;
    for i:=0 to d do
      for j:=0 to Degree(Coefficient(Q,i)) do
        f:=f+(Fp!Coefficient(Coefficient(Q,i),j))*Fpxy.1^i*Fpx.1^j;
      end for;
    end for;  
    FFp:=FunctionField(f); // function field of curve mod p
    
    if P`inf then
      places:=InfinitePlaces(FFp); // infinite places of function field of curve mod p
      W:=Winf;
    else
      Px0:=Zeros(Fpx.1-Fp!x0)[1]; 
      places:=Decomposition(FFp,Px0); // places of function field of curve mod p lying over x0 mod p
      W:=W0;
    end if;

    bmodp:=[]; // elements of b mod p, where b is either b^0 or b^inf
    for i:=1 to d do
      f:=FFp!0;
      for j:=1 to d do
        f:=f+(Fpx!W[i,j])*FFp.1^(j-1);
      end for;
      bmodp[i]:=f;
    end for;

    done:=false;

    for i:=1 to #places do
      same:=true;
      for j:=1 to d do
        if Evaluate(bmodp[j],places[i]) ne Fp!b[j] then
          same:=false;
        end if;
      end for;    
      if same then
        place:=places[i];
        done:=true;
      end if;
    end for;

    if not done then
      error "Point does not lie on curve";
    end if;

    eP:=RamificationIndex(place);

    if eP eq 1 then
      index:=0;
    else
      done:=false;
      i:=1;
      while not done do
        ord:=Valuation(bmodp[i]-Evaluate(bmodp[i],place),place);
        if ord eq 1 then
          index:=i;
          done:=true;
        end if;
        i:=i+1;
      end while;
    end if;

    return eP,index,place,bmodp;
  end if;

end function;


hensel_lift:=function(fy,root);

  // Finds a root of the polynomial fy over Qp[[t]]
  // by Hensel lifting from an approximate root.
  //
  // Assumes that the starting criterion for Hensel's 
  // lemma is satisfied

  Kty:=Parent(fy);
  Kt:=BaseRing(Kty);
  K:=BaseRing(Kt);
  tprec:=Precision(Kt); // t-adic precision
  Qt:=PowerSeriesRing(RationalField(),tprec);
  Qty:=PolynomialRing(Qt);
  p:=Prime(K);
  pprec:=Precision(K);  // p-adic precision
  Zp:=pAdicRing(p,pprec);
  Zpt:=PowerSeriesRing(Zp,tprec);  

  fy:=Qty!fy;
  derfy:=Derivative(fy);  

  if not Valuation(LeadingCoefficient(Qt!Evaluate(derfy,root)),p) eq 0 then
    error "In Hensel lift of power series, derivative has leading term divisible by p";
  end if;

  v1:=Valuation(Qt!Zpt!Evaluate(fy,root));
  v2:=Valuation(Qt!Zpt!Evaluate(derfy,root));

  if not v1 gt 2*v2 then
    error "Condition Hensel's Lemma not satisfied";
  end if;

  prec_seq:=[];
  k:=tprec;
  
  while k gt v1 do
    prec_seq:=Append(prec_seq,k);
    k:=Ceiling(k/2+v2);
  end while;
  prec_seq:=Reverse(prec_seq);

  for j:=1 to #prec_seq do
    root:=Qt!root;
    root:=ChangePrecision(root,prec_seq[j]);
    root:=root-(Qt!Zpt!Evaluate(fy,root))/(Qt!Zpt!Evaluate(derfy,root));
    root:=Zpt!root;
  end for;

  return root;

end function;


mod_p_prec:=function(fy);

  // Finds the t-adic precision necessary to separate the roots
  // of the polynomial fy over Qp[[t]] modulo p and start Hensel lift.
  //
  // Temporarily uses intrinsic Factorisation instead of 
  // intrinsic Roots because of multiple problems with Roots.
  
  Kty:=Parent(fy);
  Kt:=BaseRing(Kty);
  tprec:=Precision(Kt);
  K:=BaseRing(Kt);
  p:=Prime(K);
  Fp:=FiniteField(p);
  Fpt:=PowerSeriesRing(Fp,tprec);
  Fpty:=PolynomialRing(Fpt);

  fymodp:=Fpty!fy;
  derfymodp:=Derivative(fymodp);

  zeros:=[];
  fac:=Factorisation(fymodp); // can be slow...
  for i:=1 to #fac do
    if fac[i][2] gt 1 then
      error "t-adic precision not high enough";
    end if;
    factor:=fac[i][1];
    if Degree(factor) eq 1 and LeadingCoefficient(factor) eq 1 then
      zeros:=Append(zeros,-Coefficient(factor,0));
    end if;
  end for;

  modpprec:=1;
  for i:=1 to #zeros do
    done:=false;
    prec:=1;
    while not done do
      v1:=Valuation(Evaluate(fymodp,ChangePrecision(zeros[i],prec)));
      v2:=Valuation(Evaluate(derfymodp,ChangePrecision(zeros[i],prec)));
      if Minimum(prec,v1) gt 2*v2 then
        done:=true;
      end if;
      prec:=prec+1;
    end while;
    modpprec:=Maximum(modpprec,prec);
  end for;

  for i:=1 to #zeros do
    for j:=i+1 to #zeros do
      modpprec:=Maximum(modpprec,Valuation(zeros[i]-zeros[j]));
    end for;
  end for;
 
  return modpprec;
 
end function;


approx_root:=function(fy,y0,modpprec,expamodp)

  // Computes an approximation to t-adic precision modpprec of 
  // a root of the polynomial fy over Qp[[t]] which is congruent to:
  //
  // y0 modulo t
  // expamodp modulo p 
  //
  // This approximation is then used as root in hensel_lift.

  Kty:=Parent(fy);
  Kt:=BaseRing(Kty);
  tprec:=Precision(Kt); // t-adic precision
  K:=BaseRing(Kt);

  p:=Prime(K);
  Fp:=FiniteField(p);
  pprec:=Precision(K);  // p-adic precision
  Zp:=pAdicRing(p,pprec);
  Zpt:=PowerSeriesRing(Zp,tprec);
  Zpz:=PolynomialRing(Zp);

  Qt:=PowerSeriesRing(RationalField(),tprec);
  Qty:=PolynomialRing(Qt);
  Qz:=PolynomialRing(RationalField());
  Qzt:=PowerSeriesRing(Qz,tprec);
  
  roots:=[[*Kt!y0,1*]];
  i:=1;
  while i le #roots do
    root:=roots[i][1];
    Nroot:=roots[i][2];
    if Nroot lt modpprec then
      roots:=Remove(roots,i);
      newroot:=root+Kty.1*Kt.1^Nroot;
      C:=Coefficients(fy);
      fynewroot:=Kty!0;
      for j:=1 to #C do
        fynewroot:=fynewroot+(Kt!C[j])*newroot^(j-1);
      end for;
      fynewroot:=Qty!Kty!fynewroot;
      fznewroot:=Qzt!0;
      for j:=0 to Degree(fynewroot) do
        for k:=0 to tprec-1 do
          fznewroot:=fznewroot+Coefficient(Coefficient(fynewroot,j),k)*(Qz.1)^j*(Qzt.1)^k;
        end for;
      end for;
      fac:=Factorisation(Zpz!Coefficient(fznewroot,Valuation(fznewroot)));
      for j:=1 to #fac do
        if (Degree(fac[j][1]) eq 1) and (Coefficient(fac[j][1],1) eq 1) then
          sol:=-Coefficient(fac[j][1],0); 
          if Fp!sol eq Coefficient(expamodp,Nroot) then
            roots:=Insert(roots,i,[*Evaluate(newroot,sol),Nroot+1*]);
          end if;
        end if;
      end for;
    else
      i:=i+1;
    end if;
  end while;

  if #roots ne 1 then
    error "something is wrong, number of approximate roots is different from 1";
  end if;

  root:=roots[1][1];
  root:=Zpt!Qt!root;

  v1:=Valuation(Zpt!Qt!Evaluate(fy,root));
  v2:=Valuation(Zpt!Qt!Evaluate(Derivative(fy),root));

  if v1 le 2*v2 then
    error "something is wrong, approximate root not good enough for Hensel lift";
  end if;

  return root;

end function;


mod_p_expansion:=function(f,place,tmodp,modpprec);

  // Finds the power series expansion of f in the function field
  // modulo p at place with respect to local parameter tmodp to
  // absolute precision modpprec.

  FFp:=Parent(f);
  Fpx:=BaseRing(FFp);
  Fp:=BaseRing(Fpx);
  Fpt:=PowerSeriesRing(Fp,modpprec);

  expamodp:=Fpt!0;
  for i:=0 to modpprec-1 do
    val:=Evaluate(f,place);
    expamodp:=expamodp+val*Fpt.1^i;
    f:=(f-val)/tmodp;
  end for;
  
  return expamodp;
  
end function;


local_coord:=function(P,prec,data);

  // Computes powerseries expansions of x and
  // the b^0_i or b^infty_i (depending on whether
  // P is infinite or not) in terms of the local
  // coordinate computed by local_data.

  if assigned P`xt and Precision(Parent(P`xt)) ge prec then
    xt:=P`xt;
    bt:=P`bt;
    index:=P`index;
    return xt,bt,index;
  end if;

  if is_bad(P,data) and not is_very_bad(P,data) then
    error "Cannot compute local parameter at a bad point which is not very bad";
  end if;

  x0:=P`x; Q:=data`Q; p:=data`p; N:=data`N; W0:=data`W0; Winf:=data`Winf; d:=Degree(Q); b:=P`b;
  K:=Parent(x0); Kt<t>:=PowerSeriesRing(K,prec); Kty:=PolynomialRing(Kt);
  Qt:=RationalFunctionField(RationalField()); Qty:=PolynomialRing(Qt);
  Fp:=FiniteField(p);

  f:=Qty!0;
  for i:=0 to d do
    for j:=0 to Degree(Coefficient(Q,i)) do
      f:=f+Coefficient(Coefficient(Q,i),j)*Qty.1^i*Qt.1^j;
    end for;
  end for;  
  FF:=FunctionField(f); // function field of curve

  if not is_bad(P,data) then // finite good point

    xt:=t+x0;

    W0invx0:=Transpose(Evaluate(W0^(-1),x0));
    ypowers:=Vector(b)*W0invx0;
    y0:=ypowers[2];

    C:=Coefficients(Q);
    D:=[];
    for i:=1 to #C do
      D[i]:=Evaluate(C[i],xt); 
    end for;
    fy:=Kty!D;
    derfy:=Derivative(fy);

    yt:=hensel_lift(fy,Kt!y0);

    ypowerst:=[];
    ypowerst[1]:=FieldOfFractions(Kt)!1;
    ypowerst[2]:=yt;
    for i:=3 to d do
      ypowerst[i]:=ypowerst[i-1]*yt;
    end for;
    bt:=Eltseq(Vector(ypowerst)*Transpose(Evaluate(W0,xt)));

    btnew:=[];
    for i:=1 to d do
      btnew[i]:=Kt!bt[i];
    end for;
    bt:=btnew;

    index:=0;

  elif P`inf then // infinite point

    eP,index,place,bmodp:=local_data(P,data);
    FFp:=Parent(bmodp[1]);
    Fpx:=BaseRing(FFp);

    bfun:=[];
    for i:=1 to d do
      bi:=FF!0;
      for j:=1 to d do
        bi:=bi+Winf[i,j]*FF.1^(j-1);
      end for;
      bfun[i]:=bi;
    end for;
    
    if eP eq 1 then // P is an infinite point that is not ramified
      
      xt:=t+x0;
      bt:=[];

      for i:=1 to d do

        if assigned data`minpolys and data`minpolys[2][1,i+1] ne 0 then
          poly:=data`minpolys[2][1,i+1]; 
        else 
          poly:=minpoly(FF!(1/Qt.1),bfun[i]);
        end if;

        C:=Coefficients(poly);
        D:=[];
        for j:=1 to #C do
          D[j]:=Evaluate(C[j],xt); 
        end for;
        fy:=Kty!D;
        derfy:=Derivative(fy);

        modpprec:=mod_p_prec(fy);

        if assigned P`bt and Precision(Parent(P`bt[i])) ge modpprec then
          approxroot:=P`bt[i];
        else
          tmodp:=1/Fpx.1-Fp!x0;
          expamodp:=mod_p_expansion(bmodp[i],place,tmodp,modpprec);
          approxroot:=approx_root(fy,b[i],modpprec,expamodp);
        end if;

        bti:=hensel_lift(fy,approxroot);
        bt[i]:=bti;

      end for;

    else // P is an infinite point that is ramified

      if assigned data`minpolys and data`minpolys[2][index+1,1] ne 0 then
        poly:=data`minpolys[2][index+1,1];
      else
        poly:=minpoly(bfun[index],FF!1/(Qt.1));
      end if;

      C:=Coefficients(poly);
      D:=[];
      for j:=1 to #C do
        D[j]:=Evaluate(C[j],t+b[index]); 
      end for;
      fy:=Kty!D;
      derfy:=Derivative(fy);

      modpprec:=mod_p_prec(fy);

      if assigned P`xt and Precision(Parent(P`xt)) ge modpprec then
        approxroot:=P`xt;
      else
        tmodp:=bmodp[index]-Fp!b[index];
        expamodp:=mod_p_expansion(FFp!1/Fpx.1,place,tmodp,modpprec);
        approxroot:=approx_root(fy,x0,modpprec,expamodp);
      end if;

      xt:=hensel_lift(fy,approxroot);

      bt:=[];
      for i:=1 to d do 
      
        if i eq index then
          bt[i]:=t+b[i];
        else
          
          if assigned data`minpolys and data`minpolys[2][index+1,i+1] ne 0 then
            poly:=data`minpolys[2][index+1,i+1];
          else
            poly:=minpoly(bfun[index],bfun[i]);
          end if;

          C:=Coefficients(poly);
          D:=[];
          for j:=1 to #C do
            D[j]:=Evaluate(C[j],t+b[index]); 
          end for;

          fy:=Kty!D;
          derfy:=Derivative(fy);

          modpprec:=mod_p_prec(fy);

          if assigned P`bt and Precision(Parent(P`bt[i])) ge modpprec then
            approxroot:=P`bt[i];
          else
            tmodp:=bmodp[index]-Fp!b[index];
            expamodp:=mod_p_expansion(bmodp[i],place,tmodp,modpprec);
            approxroot:=approx_root(fy,b[i],modpprec,expamodp);
          end if;

          bti:=hensel_lift(fy,approxroot);
          bt[i]:=bti;

        end if;
 
      end for;

    end if;

  else // finite bad point

    eP,index,place,bmodp:=local_data(P,data);
    FFp:=Parent(bmodp[1]);
    Fpx:=BaseRing(FFp);

    bfun:=[];
    for i:=1 to d do
      bi:=FF!0;
      for j:=1 to d do
        bi:=bi+W0[i,j]*FF.1^(j-1);
      end for;
      bfun[i]:=bi;
    end for;

    if eP eq 1 then // P is a finite point that is not ramified

      xt:=t+x0;
      bt:=[];
      for i:=1 to d do
        
        if assigned data`minpolys and data`minpolys[1][1,i+1] ne 0 then
          poly:=data`minpolys[1][1,i+1];
        else
          poly:=minpoly(FF!Qt.1,bfun[i]);
        end if;

        C:=Coefficients(poly);
        D:=[];
        for j:=1 to #C do
          D[j]:=Evaluate(C[j],xt); 
        end for;
        fy:=Kty!D;
        derfy:=Derivative(fy);

        modpprec:=mod_p_prec(fy);

        if assigned P`bt and Precision(Parent(P`bt[i])) ge modpprec then
          approxroot:=P`bt[i];
        else
          tmodp:=Fpx.1-Fp!x0;
          expamodp:=mod_p_expansion(bmodp[i],place,tmodp,modpprec);
          approxroot:=approx_root(fy,b[i],modpprec,expamodp);
        end if;

        bti:=hensel_lift(fy,approxroot);
        bt[i]:=bti;

      end for;

    else // P is a finite point that ramifies

      if assigned data`minpolys and data`minpolys[1][index+1,1] ne 0 then
        poly:=data`minpolys[1][index+1,1];
      else
        poly:=minpoly(bfun[index],FF!Qt.1);
      end if;

      C:=Coefficients(poly);
      D:=[];
      for j:=1 to #C do
        D[j]:=Evaluate(C[j],t+b[index]); 
      end for;
      fy:=Kty!D;
      derfy:=Derivative(fy);

      modpprec:=mod_p_prec(fy);

      if assigned P`xt and Precision(Parent(P`xt)) ge modpprec then
        approxroot:=P`xt;
      else
        tmodp:=bmodp[index]-Fp!b[index];
        expamodp:=mod_p_expansion(FFp!Fpx.1,place,tmodp,modpprec);
        approxroot:=approx_root(fy,x0,modpprec,expamodp);
      end if;

      xt:=hensel_lift(fy,approxroot);  

      bt:=[];
      for i:=1 to d do 
      
        if i eq index then
          bt[i]:=t+b[i];
        else
          
          if assigned data`minpolys and data`minpolys[1][index+1,i+1] ne 0 then
            poly:=data`minpolys[1][index+1,i+1];
          else
            poly:=minpoly(bfun[index],bfun[i]);
          end if;

          C:=Coefficients(poly);
          D:=[];
          for j:=1 to #C do
            D[j]:=Evaluate(C[j],t+b[index]);
          end for;

          fy:=Kty!D;

          derfy:=Derivative(fy);

          modpprec:=mod_p_prec(fy);

          if assigned P`bt and Precision(Parent(P`bt[i])) ge modpprec then
            approxroot:=P`bt[i];
          else
            tmodp:=bmodp[index]-Fp!b[index];
            expamodp:=mod_p_expansion(bmodp[i],place,tmodp,modpprec);
            approxroot:=approx_root(fy,b[i],modpprec,expamodp);
          end if;

          bti:=hensel_lift(fy,approxroot);
          bt[i]:=bti;

        end if;
 
      end for;

    end if;

  end if;

  return xt,bt,index;

end function;


tiny_integral_prec:=function(prec,e,maxpoleorder,maxdegree,mindegree,val,data);

  // Determines the p-adic precision to which tiny_integrals_on_basis is correct.

  N:=data`N; p:=data`p;

  // Precision loss from terms of positive order we do consider:

  m1:=N*e-val;
  for i:=1 to maxdegree do
    m1:=Minimum(m1,N*e+i-e*Floor(Log(p,i+1)));
  end for;  

  // Precision loss from terms we omit:

  m2:=mindegree+2-e*Floor(Log(p,mindegree+2));
  for i:=mindegree+2 to Ceiling(e/Log(p)) do
    m2:=Minimum(m2,i+1-e*Floor(Log(p,i+1)));
  end for;

  // Precision loss from terms of negative order

  m3:=N*e-val;
  if maxpoleorder ge 2 then
    m3:=N*e-val-maxpoleorder*val-e*Floor(Log(p,maxpoleorder-1));
  end if;

  m:=Minimum([m1,m2,m3]);

  return m/e;

end function;


find_bad_point_in_disk:=function(P,data);

  // Find the very bad point in the residue disk of a bad point P.

  x0:=P`x; b:=P`b; Q:=data`Q; p:=data`p; N:=data`N; W0:=data`W0; Winf:=data`Winf; r:=data`r;
  d:=Degree(Q); K:=Parent(x0); Ky:=PolynomialRing(K); 

  if not is_bad(P,data) then
    error "Residue disk does not contain a bad point";
  end if;

  if P`inf then
    x0:=K!0;
  else
    rQp:=Ky!Coefficients(r);
    x0:=HenselLift(rQp,x0);
  end if;

  Qt:=RationalFunctionField(RationalField()); Qty:=PolynomialRing(Qt);

  f:=Qty!0;
  for i:=0 to d do
    for j:=0 to Degree(Coefficient(Q,i)) do
      f:=f+Coefficient(Coefficient(Q,i),j)*Qty.1^i*Qt.1^j;
    end for;
  end for;  
  FF:=FunctionField(f); // function field of curve

  eP,index:=local_data(P,data);

  if P`inf then
    W:=Winf;
  else
    W:=W0;
  end if;

  bfun:=[];
  for i:=1 to d do
    bi:=FF!0;
    for j:=1 to d do
      bi:=bi+W[i,j]*FF.1^(j-1);
    end for;
    bfun:=Append(bfun,bi);
  end for;

  if index eq 0 then
    if P`inf then
      xfun:=FF!(1/Qt.1);
    else
      xfun:=FF!(Qt.1);
    end if;

    for i:=1 to d do
      poly:=minpoly(xfun,bfun[i]);
      C:=Coefficients(poly);
      D:=[];
      for i:=1 to #C do
        D[i]:=Evaluate(C[i],x0); 
      end for;
      fy:=Ky!D;
      fac:=Factorisation(fy);
      done:=false;
      j:=1;
      while not done and j le #fac do
        if Degree(fac[j][1]) eq 1 and Valuation(-Coefficient(fac[j][1],0)-b[i]) gt 0 then
          done:=true;
          b[i]:=-Coefficient(fac[j][1],0);
        end if;
        j:=j+1;
      end while;
    end for;
  else
   bindex:=bfun[index];
   if P`inf then
      xfun:=FF!(1/Qt.1);
    else
      xfun:=FF!(Qt.1);
    end if;
    poly:=minpoly(xfun,bindex);
    C:=Coefficients(poly);
    D:=[];
    for i:=1 to #C do
      D[i]:=Evaluate(C[i],x0); 
    end for;
    fy:=Ky!D;
    fac:=Factorisation(fy);
    done:=false;
    j:=1;
    while not done and j le #fac do
      if Degree(fac[j][1]) eq 1 and Valuation(-Coefficient(fac[j][1],0)-b[index]) gt 0 then
        done:=true;
        b[index]:=-Coefficient(fac[j][1],0);
      end if;
      j:=j+1;
    end while;
    for i:=1 to d do
      if i ne index then
        poly:=minpoly(bindex,bfun[i]);
        C:=Coefficients(poly);
        D:=[];
        for i:=1 to #C do
          D[i]:=Evaluate(C[i],b[index]); 
        end for;
        fy:=Ky!D;
        fac:=Factorisation(fy); // Roots has some problems that Factorisation does not
        done:=false;
        j:=1;
        while not done and j le #fac do
          if Degree(fac[j][1]) eq 1 and Valuation(-Coefficient(fac[j][1],0)-b[i]) gt 0 then
            done:=true;
            b[i]:=-Coefficient(fac[j][1],0);
          end if;
          j:=j+1;
        end while;
      end if;
    end for; 
  end if;

  Pbad:=set_bad_point(x0,b,P`inf,data);

  return Pbad;

end function;


tadicprec:=function(data,e);

  // Compute the necessary t-adic precision to compute tiny integrals

  p:=data`p; N:=data`N; W0:=data`W0; Winf:=data`Winf;
  W:=Winf*W0^(-1);

  prec:=1;
  while Floor(prec/e)+1-Floor(Log(p,prec+1)) lt N do
    prec:=prec+1;
  end while;
  prec:=Maximum([prec,100]); // 100 arbitrary, avoid problems with small precisions 

  return prec;

end function;


tiny_integrals_on_basis:=function(P1,P2,data:prec:=0,P:=0);

  // Compute tiny integrals of basis elements from P1 to P2.
  // If P1 is not defined over Qp (but a totally ramified 
  // extension) then a point P defined over Qp in the same
  // residue disk as P1 has to be specified.

  x1:=P1`x; x2:=P2`x; b1:=P1`b; b2:=P2`b; Q:=data`Q; p:=data`p; N:=data`N; W0:=data`W0; Winf:=data`Winf; r:=data`r; basis:=data`basis; N:=data`N;
  d:=Degree(Q); lc_r:=LeadingCoefficient(r); W:=Winf*W0^(-1); K:=Parent(x1); 

  if not lie_in_same_disk(P1,P2,data) then
    error "the points do not lie in the same residue disk";
  end if;

  //if ((x1 eq x2) and (b1 eq b2)) then 
  //  return RSpace(K,#basis)!0, N*Degree(K);
  //end if;

  if (Valuation(x1-x2)/Valuation(Parent(x1-x2)!p) ge N) and (Minimum([Valuation(b1[i]-b2[i])/Valuation(Parent(b1[i]-b2[i])!p):i in [1..d]]) ge N) then
    return RSpace(K,#basis)!0, N*Degree(K);
  end if; 

  if Degree(K) gt 1 then // P1 needs to be defined over Qp
    tinyPtoP2,NtinyPtoP2:=$$(P,P2,data);
    tinyPtoP1,NtinyPtoP1:=$$(P,P1,data);
    return tinyPtoP2-tinyPtoP1,Minimum(NtinyPtoP2,NtinyPtoP1);
  end if;

  if not Type(P) eq Rec then
    P:=P1;
  end if;

  if is_bad(P,data) and not is_very_bad(P,data) then // on a bad disk P1 needs to be very bad
    P:=find_bad_point_in_disk(P,data);
    tinyPtoP2,NtinyPtoP2:=$$(P,P2,data);
    tinyPtoP1,NtinyPtoP1:=$$(P,P1,data);
    return tinyPtoP2-tinyPtoP1,Minimum(NtinyPtoP2,NtinyPtoP1);
  end if;

  e:=Degree(Parent(x2));

  if prec eq 0 then // no t-adic precision specified
    prec:=tadicprec(data,e);
  end if;

  Kt:=LaurentSeriesRing(K,prec);
  OK:=RingOfIntegers(K);
  OKt:=LaurentSeriesRing(OK,prec);

  xt,bt,index:=local_coord(P1,prec,data);

  Qt<t>:=LaurentSeriesRing(RationalField(),prec);
  xt:=Qt!xt;
  btnew:=[Qt|];
  for i:=1 to d do
    btnew[i]:=Qt!bt[i];
  end for;
  bt:=Vector(btnew);

  if P1`inf then
    xt:=1/xt;
    xt:=Qt!Kt!xt; 
    Winv:=W0*Winf^(-1);          
    bt:=bt*Transpose(Evaluate(Winv,xt));
    for i:=1 to d do
      bt[i]:=Qt!(Kt!bt[i]);
    end for; 
  end if;

  if P1`inf or not is_bad(P1,data) then 
    denom:=Qt!Kt!(1/Evaluate(r,xt));
  else
    Qp:=pAdicField(p,N);
    Qpx:=PolynomialRing(Qp);
    rQp:=Qpx!r;
    zero:=HenselLift(rQp,x1);
    sQp:=rQp div (Qpx.1-zero);
    denom:=Qt!Kt!((Qt!OKt!(xt-Coefficient(xt,0)))^(-1)*(Qt!Kt!(1/Evaluate(sQp,xt))));
  end if;

  derxt:=Qt!Kt!Derivative(xt); 
  diffs:=[];
  for i:=1 to #basis do
    basisxt:=Evaluate(basis[i],xt);
    for j:=1 to d do
      basisxt[1][j]:=Qt!Kt!basisxt[1][j];
    end for;
    diffs[i]:=InnerProduct(Vector(basisxt*derxt*lc_r*denom),bt);
    diffs[i]:=Qt!Kt!diffs[i];
    if Coefficient(diffs[i],-1) ne 0 then
      diffs[i]:=diffs[i]-Coefficient(diffs[i],-1)*Kt.1^(-1); // deal with logs later, important for double integrals
    end if;
  end for;

  maxpoleorder:=-(Minimum([Valuation(diffs[i]): i in [1..#basis]])); 
  maxdegree:=Maximum([Degree(diffs[i]): i in [1..#basis]]);
  mindegree:=Minimum([Degree(diffs[i]): i in [1..#basis]]);

  indefints:=[];
  for i:=1 to #basis do
    indefints := Append(indefints, Integral(diffs[i]));
  end for;

  tinyP1toP2:=[];
  for i:=1 to #basis do
    if index eq 0 then // x-x(P1) is the local coordinate
      tinyP1toP2[i]:=Evaluate(indefints[i],x2-x1);
      val:=Valuation(x2-x1);
    else // b[index]-b[index](P1) is the local coordinate
      tinyP1toP2[i]:=Evaluate(indefints[i],b2[index]-b1[index]);
      val:=Valuation(b2[index]-b1[index]);
    end if;
  end for;

  NtinyP1toP2:=tiny_integral_prec(prec,e,maxpoleorder,maxdegree,mindegree,val,data);

  return Vector(tinyP1toP2),NtinyP1toP2;

end function;


pow:=function(x,k);

  if k eq 0 then
    return Parent(x)!1;
  else
    return x^k;
  end if;

end function;


evalf0:=function(f0,P,data);

  // Evaluate vector of functions f0 at P.
 
  x0:=P`x; b:=P`b; Q:=data`Q; r:=data`r; W0:=data`W0; Winf:=data`Winf; N:=data`N; Nmax:=data`Nmax; p:=data`p;
  d:=Degree(Q); lcr:=LeadingCoefficient(r); K:=Parent(x0);

  valf0:=0;

  if P`inf then 
    Winv:=W0*Winf^(-1); 
    Qt:=BaseRing(Winv);
    b:=Vector(b)*Transpose(Evaluate(Evaluate(Winv,1/Qt.1),x0)); // values of the b_i^0 at P
    
    z0:=Evaluate(r,1/x0)/lcr;
    invz0:=1/z0;
    invz0pow:=[K!1];
    for i:=1 to p*(Nmax-1) do
      invz0pow[i+1]:=invz0pow[i]*invz0;
    end for;
    
    invx0:=1/x0;
    invx0pow:=[K!1];
    for i:=1 to Degree(r)-1 do
      invx0pow[i+1]:=invx0pow[i]*invx0;
    end for;

    f0P:=K!0;
    for i:=1 to d do
      f0i:=f0[i];
      C:=Coefficients(f0i);
      val:=Valuation(f0i);
      for j:=1 to #C do
        D:=Coefficients(C[j]);
        for k:=1 to #D do
          f0P:=f0P+(K!D[k])*invx0pow[k]*invz0pow[2-j-val]*b[i];
          valf0:=Minimum(valf0,Valuation(K!D[k]));
        end for;
      end for;
    end for;
    Nf0P:=N*Degree(K)+(ord_inf_mat(Winv)+1)*Valuation(x0)+valf0;

  else
    
    z0:=Evaluate(r,x0)/lcr;  
    invz0:=1/z0;
    invz0pow:=[K!1];
    for i:=1 to p*(Nmax-1) do
      invz0pow[i+1]:=invz0pow[i]*invz0;
    end for;

    x0pow:=[K!1];
    for i:=1 to Degree(r)-1 do
      x0pow[i+1]:=x0pow[i]*x0;
    end for;  
 
    f0P:=K!0;
    for i:=1 to d do
      f0i:=f0[i];
      C:=Coefficients(f0i);
      val:=Valuation(f0i);
      for j:=1 to #C do
        D:=Coefficients(C[j]);
        for k:=1 to #D do
          f0P:=f0P+(K!D[k])*x0pow[k]*invz0pow[2-j-val]*b[i];
          valf0:=Minimum(valf0,Valuation(K!D[k]));
        end for;
      end for;
    end for;
    Nf0P:=N*Degree(K)-p*(Nmax-1)*Valuation(z0)+valf0; // this is error of terms we did consider, take error of terms we ignored into account as well
  end if;

  return f0P,Nf0P/Degree(K);

end function;


evalfinf:=function(finf,P,data);

  // Evaluate vector of functions finf at P.

  x0:=P`x; b:=P`b; Q:=data`Q; W0:=data`W0; Winf:=data`Winf; N:=data`N; p:=data`p;
  d:=Degree(Q); K:=Parent(x0); 

  W:=Winf*W0^(-1); 

  valfinf:=0;

  if P`inf then
    finfP:=K!0;
    for i:=1 to d do
      finfi:=finf[i];
      C:=Coefficients(finfi);
      val:=Valuation(finfi);
      for j:=1 to #C do
        finfP:=finfP+(K!C[j])*pow(1/x0,val+j-1)*b[i];
        valfinf:=Minimum(valfinf,Valuation(K!C[j]));
      end for;
    end for;
    NfinfP:=N*Degree(K)+p*(ord_0_mat(W)+1)*Valuation(x0)+valfinf;
  else 
    finf:=finf*ChangeRing(W,BaseRing(finf));
    finfP:=K!0;
    for i:=1 to d do
      finfi:=finf[i];
      C:=Coefficients(finfi);
      val:=Valuation(finfi);
      for j:=1 to #C do
        finfP:=finfP+(K!C[j])*pow(x0,val+j-1)*b[i];
        valfinf:=Minimum(valfinf,Valuation(K!C[j]));
      end for;
    end for;
    NfinfP:=N*Degree(K)+valfinf;
  end if;

  return finfP, NfinfP/Degree(K);

end function;


evalfend:=function(fend,P,data);

  // Evaluate vector of functions fend at P.

  x0:=P`x; b:=P`b; Q:=data`Q; W0:=data`W0; Winf:=data`Winf; N:=data`N;
  d:=Degree(Q);
  K:=Parent(x0);

  valfend:=0;

  if P`inf then
    Winv:=W0*Winf^(-1);
    Qt:=BaseRing(Winv);
    b:=Vector(b)*Transpose(Evaluate(Evaluate(Winv,1/Qt.1),x0)); // values of the b_i^0 at P
    fendP:=K!0;
    for i:=1 to d do
      fendi:=fend[i];
      C:=Coefficients(fendi);
      for j:=1 to #C do
        fendP:=fendP+(K!C[j])*pow(1/x0,j-1)*b[i];
        valfend:=Minimum(valfend,Valuation(K!C[j]));
      end for;
    end for;
    NfendP:=N*Degree(K)+(ord_0_mat(Winf)+1)*Valuation(x0)+valfend;
  else
    fendP:=K!0;
    for i:=1 to d do
      fendi:=fend[i];
      C:=Coefficients(fendi);
      for j:=1 to #C do
        fendP:=fendP+(K!C[j])*pow(x0,j-1)*b[i];
        valfend:=Minimum(valfend,Valuation(K!C[j]));
      end for;
    end for;
    NfendP:=N*Degree(K)+valfend;
  end if;

  return fendP, NfendP/Degree(K);

end function;


round_to_Qp:=function(L)

  // Rounds a vector over a totally ramified extension of Qp to one over Qp.

  K:=CoefficientRing(L);
  deg:=Degree(K);
  e:=Precision(K);

  l:=[];
  for i:=1 to #Eltseq(L) do
    l[i]:=Eltseq(L[i])[1];  
    e:=Minimum(e,Valuation(L[i]-l[i]));
  end for;

  return Vector(l),e/deg;

end function;


coleman_integrals_on_basis:=function(P1,P2,data:e:=1)

  // Integrals of basis elements from P1 to P2. 

  F:=data`F; Q:=data`Q; basis:=data`basis; x1:=P1`x; f0list:=data`f0list; finflist:=data`finflist; fendlist:=data`fendlist; p:=data`p; N:=data`N; delta:=data`delta;
  d:=Degree(Q); K:=Parent(x1); 

  // First make sure that if P1 or P2 is bad, then it is very bad

  if is_bad(P1,data) and not is_very_bad(P1,data) then
    S1:=find_bad_point_in_disk(P1,data);
    _,index:=local_data(S1,data);
    data:=update_minpolys(data,S1`inf,index);
    xt,bt,index:=local_coord(S1,tadicprec(data,e),data);
    S1`xt:=xt;
    S1`bt:=bt;
    S1`index:=index;
    IS1P1,NIS1P1:=tiny_integrals_on_basis(S1,P1,data:prec:=tadicprec(data,e));
    IS1P2,NIS1P2:=$$(S1,P2,data:e:=e);
    IP1P2:=IS1P2-IS1P1;
    NIP1P2:=Ceiling(Minimum([NIS1P1,NIS1P2]));
    return IP1P2,NIP1P2;
  end if;

  if is_bad(P2,data) and not is_very_bad(P2,data) then
    S2:=find_bad_point_in_disk(P2,data);
    _,index:=local_data(S2,data);
    data:=update_minpolys(data,S2`inf,index);
    xt,bt,index:=local_coord(S2,tadicprec(data,e),data);
    S2`xt:=xt;
    S2`bt:=bt;
    S2`index:=index;
    IP1S2,NIP1S2:=$$(P1,S2,data:e:=e);
    IP2S2,NIP2S2:=tiny_integrals_on_basis(P2,S2,data:prec:=tadicprec(data,e));
    IP1P2:=IP1S2-IP2S2;
    NIP1P2:=Ceiling(Minimum([NIP1S2,NIP2S2]));
    return IP1P2,NIP1P2;
  end if;

  // If P1,P2 is bad (hence very bad), use a near boundary point.

  _,index:=local_data(P1,data);
  data:=update_minpolys(data,P1`inf,index);
  _,index:=local_data(P2,data);
  data:=update_minpolys(data,P2`inf,index);

  if is_bad(P1,data) then
    xt,bt,index:=local_coord(P1,tadicprec(data,e),data);
    P1`xt:=xt;       
    P1`bt:=bt;       
    P1`index:=index; 
    Qp:=Parent(P1`x);
    Qpa<a>:=PolynomialRing(Qp);
    K<a>:=TotallyRamifiedExtension(Qp,a^e-p);
    format:=recformat<x,b,inf,xt,bt,index>;
    S1:=rec<format|>;                                                    
    S1`inf:=P1`inf;
    S1`x:=Evaluate(xt,a);
    S1`b:=[Evaluate(bt[i],a):i in [1..d]];
  else
    xt,bt,index:=local_coord(P1,tadicprec(data,1),data);
    P1`xt:=xt;       
    P1`bt:=bt;       
    P1`index:=index; 
    S1:=P1;
  end if;

  if is_bad(P2,data) then
    xt,bt,index:=local_coord(P2,tadicprec(data,e),data);
    P2`xt:=xt;       
    P2`bt:=bt;       
    P2`index:=index; 
    if not is_bad(P1,data) then
      Qp:=Parent(P2`x);
      Qpa<a>:=PolynomialRing(Qp);
      K<a>:=TotallyRamifiedExtension(Qp,a^e-p);
    end if;
    format:=recformat<x,b,inf,xt,bt,index>;
    S2:=rec<format|>;                                                    
    S2`inf:=P2`inf;
    S2`x:=Evaluate(xt,a);
    S2`b:=[Evaluate(bt[i],a):i in [1..d]];
  else
    xt,bt,index:=local_coord(P2,tadicprec(data,1),data);
    P2`xt:=xt;       
    P2`bt:=bt;       
    P2`index:=index; 
    S2:=P2;
  end if;

  // Split up the integral and compute the tiny ones.

  tinyP1toS1,NP1toS1:=tiny_integrals_on_basis(P1,S1,data);
  tinyP2toS2,NP2toS2:=tiny_integrals_on_basis(P2,S2,data);

  FS1:=frobenius_pt(S1,data);
  FS2:=frobenius_pt(S2,data);
  //JSB edit 03/31/21
  if is_bad(S1,data) and not is_very_bad(S1,data) then
    tinyP1toFS1,NP1toFS1:=tiny_integrals_on_basis(P1,FS1,data);
    tinyS1toFS1 := tinyP1toFS1 - tinyP1toS1;
    NS1toFS1:=Minimum([NP1toFS1,NP1toS1]);
  else 
    tinyS1toFS1,NS1toFS1:=tiny_integrals_on_basis(S1,FS1,data:P:=P1); 
  end if;
  //JSB edit 04/17/21
  if is_bad(S2,data) and not is_very_bad(S2,data) then
    tinyP2toFS2,NP2toFS2:=tiny_integrals_on_basis(P2,FS2,data);
    tinyS2toFS2 := tinyP2toFS2 - tinyP2toS2;
    NS2toFS2:=Minimum([NP2toFS2,NP2toS2]);
  else
      tinyS2toFS2,NS2toFS2:=tiny_integrals_on_basis(S2,FS2,data:P:=P2); 
  end if;
  NIP1P2:=Minimum([NP1toS1,NP2toS2,NS1toFS1,NS2toFS2]);  

  // Evaluate all functions.

  I:=[];
  for i:=1 to #basis do
    f0iS1,Nf0iS1:=evalf0(f0list[i],S1,data);
    f0iS2,Nf0iS2:=evalf0(f0list[i],S2,data);
    finfiS1,NfinfiS1:=evalfinf(finflist[i],S1,data);
    finfiS2,NfinfiS2:=evalfinf(finflist[i],S2,data);
    fendiS1,NfendiS1:=evalfend(fendlist[i],S1,data);
    fendiS2,NfendiS2:=evalfend(fendlist[i],S2,data);
    NIP1P2:=Minimum([NIP1P2,Nf0iS1,Nf0iS2,NfinfiS1,NfinfiS2,NfendiS1,NfendiS2]);
    I[i]:=(K!f0iS1)-(K!f0iS2)+(K!finfiS1)-(K!finfiS2)+(K!fendiS1)-(K!fendiS2)-(K!tinyS1toFS1[i])+(K!tinyS2toFS2[i]);
  end for; 

  valIP1P2:=Minimum([Valuation(I[i])/Valuation(K!p):i in [1..#basis]]);

  mat:=(F-IdentityMatrix(RationalField(),#basis));
  valdet:=Valuation(Determinant(mat),p);
  mat:=mat^-1;
  Nmat:=N-valdet-delta;
  valmat:=Minimum([Valuation(e,p):e in Eltseq(mat)]);

  NIP1P2:=Minimum([NIP1P2+valmat,Nmat+valIP1P2]);                            
  
  IS1S2:=Vector(I)*Transpose(ChangeRing(mat,K));    // Solve the linear system.

  IP1P2:=IS1S2+ChangeRing(tinyP1toS1,K)-ChangeRing(tinyP2toS2,K);

  IP1P2,Nround:=round_to_Qp(IP1P2);

  assert Nround ge NIP1P2;                          // Check that rounding error is within error bound.
  
  NIP1P2:=Ceiling(NIP1P2);

  for i:=1 to #basis do
    IP1P2[i]:=IP1P2[i]+O(Parent(IP1P2[i])!p^(NIP1P2));
  end for;

  return IP1P2,NIP1P2;
end function;


coleman_integral:=function(P1,P2,dif,data:e:=1,IP1P2:=0,NIP1P2:=0);

  // Integral of 1-form dif from P1 to P2.

  Q:=data`Q; p:=data`p; N:=data`N; Nmax:=data`Nmax; r:=data`r; W0:=data`W0; Winf:=data`Winf;
  G0:=data`G0; Ginf:=data`Ginf; red_list_fin:=data`red_list_fin; red_list_inf:=data`red_list_inf;
  basis:=data`basis; integrals:= data`integrals; quo_map:=data`quo_map;


  //this needs dif to be coerced properly with R and Qzs etc
  coefs,f0,finf,fend:=reduce_with_fs(dif,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map); // TODO: handle precision here

  if NIP1P2 eq 0 then 
    IP1P2,NIP1P2:=coleman_integrals_on_basis(P1,P2,data:e:=e);
  end if;
  
  f0P1,Nf0P1:=evalf0(f0,P1,data);
  f0P2,Nf0P2:=evalf0(f0,P2,data);
  finfP1,NfinfP1:=evalfinf(finf,P1,data);
  finfP2,NfinfP2:=evalfinf(finf,P2,data);
  fendP1,NfendP1:=evalfend(fend,P1,data);
  fendP2,NfendP2:=evalfend(fend,P2,data);

  IdifP1P2:=f0P2-f0P1+finfP2-finfP1+fendP2-fendP1;
  //print "IdifP1P2= ", IdifP1P2;
  NIdifP1P2:=Minimum([Nf0P1,Nf0P2,NfinfP1,NfinfP2,NfendP1,NfendP2]);
  
  for i:=1 to #coefs do
    IdifP1P2:=IdifP1P2+coefs[i]*IP1P2[i];
    NIdifP1P2:=Minimum(NIdifP1P2,NIP1P2+Valuation(coefs[i],p));
  end for;

  NIdifP1P2:=Ceiling(NIdifP1P2);
  IdifP1P2:=IdifP1P2+O(Parent(IdifP1P2)!p^NIdifP1P2);

  return IdifP1P2, NIdifP1P2;

end function;

//************************************************
//new code
//************************************************

function tiny_double_integrals_on_basis(P1,P2,data:prec:=0,P:=0);

  // Compute tiny double integrals of basis elements from P1 to P2.
  // If P1 is not defined over Qp (but a totally ramified 
  // extension) then a point P defined over Qp in the same
  // residue disk as P1 has to be specified.
  //
  // Returns the tiny *double* integrals on basis

 x1:=P1`x; x2:=P2`x; b1:=P1`b; b2:=P2`b; Q:=data`Q; p:=data`p; N:=data`N; W0:=data`W0; Winf:=data`Winf; r:=data`r; basis:=data`basis; N:=data`N;
 d:=Degree(Q); lc_r:=LeadingCoefficient(r); W:=Winf*W0^(-1); K:=Parent(x1); 

  if not lie_in_same_disk(P1,P2,data) then
    error "the points do not lie in the same residue disk";
  end if;

  if (Valuation(x1-x2)/Valuation(Parent(x1-x2)!p) ge N) and (Minimum([Valuation(b1[i]-b2[i])/Valuation(Parent(b1[i]-b2[i])!p):i in [1..d]]) ge N) then
    return RSpace(K,#basis^2)!0, N*Degree(K);
  end if; 

  //recursive call to tiny double integrals via P (defined over Qp)
  if Degree(K) gt 1 then // P1 needs to be defined over Qp
    tinysingPtoP2,NtinysingPtoP2:=tiny_integrals_on_basis(P,P2,data);
    tinydoubPtoP2,NtinydoubPtoP2:=$$(P,P2,data);
    tinysingPtoP1,NtinysingPtoP1:=tiny_integrals_on_basis(P,P1,data);
    tinydoubPtoP1,NtinydoubPtoP1:=$$(P,P1,data);
    tinydoub:=[];
    for i in [1..#basis] do
        for j in [1..#basis] do
        ij:=(i-1)*(#basis) + j;
        ji:=(j-1)*(#basis) + i;
        tinydoub:=Append(tinydoub, tinydoubPtoP2[ij]-tinydoubPtoP1[ji] - tinysingPtoP2[i]*tinysingPtoP1[j]);
        end for;
    end for;
    return tinydoub, Minimum(NtinysingPtoP2,NtinysingPtoP1, NtinydoubPtoP2,NtinydoubPtoP1);
  end if;

  if not Type(P) eq Rec then
    P:=P1;
  end if;

  if is_bad(P,data) and not is_very_bad(P,data) then // on a bad disk P1 needs to be very bad
    P:=find_bad_point_in_disk(P,data);
    tinysingPtoP2,NtinysingPtoP2:=tiny_integrals_on_basis(P,P2,data);
    tinydoubPtoP2,NtinydoubPtoP2:=$$(P,P2,data);
    tinysingPtoP1,NtinysingPtoP1:=tiny_integrals_on_basis(P,P1,data);
    tinydoubPtoP1,NtinydoubPtoP1:=$$(P,P1,data);
    tinydoub:=[];
    for i in [1..#basis] do
        for j in [1..#basis] do
        ij:=(i-1)*(#basis) + j;
        ji:=(j-1)*(#basis) + i;
        tinydoub:=Append(tinydoub, tinydoubPtoP2[ij]-tinydoubPtoP1[ji] - tinysingPtoP2[i]*tinysingPtoP1[j]);
        end for;
    end for;
    return tinydoub, Minimum(NtinysingPtoP2,NtinysingPtoP1, NtinydoubPtoP2,NtinydoubPtoP1);
  end if;

  e:=Degree(Parent(x2));

  if prec eq 0 then // no t-adic precision specified
    prec:=tadicprec(data,e);
  end if;

  Kt:=LaurentSeriesRing(K,prec);
  OK:=RingOfIntegers(K);
  OKt:=LaurentSeriesRing(OK,prec);

  xt,bt,index:=local_coord(P1,prec,data);

  Qt<t>:=LaurentSeriesRing(RationalField(),prec);
  xt:=Qt!xt;
  btnew:=[Qt|];
  for i:=1 to d do
    btnew[i]:=Qt!bt[i];
  end for;
  bt:=Vector(btnew);

  if P1`inf then
    xt:=1/xt;
    xt:=Qt!Kt!xt; 
    Winv:=W0*Winf^(-1);          
    bt:=bt*Transpose(Evaluate(Winv,xt));
    for i:=1 to d do
      bt[i]:=Qt!(Kt!bt[i]);
    end for; 
  end if;

  if P1`inf or not is_bad(P1,data) then 
    denom:=Qt!Kt!(1/Evaluate(r,xt));
  else
    Qp:=pAdicField(p,N);
    Qpx:=PolynomialRing(Qp);
    rQp:=Qpx!r;
    zero:=HenselLift(rQp,x1);
    sQp:=rQp div (Qpx.1-zero);
    denom:=Qt!Kt!((Qt!OKt!(xt-Coefficient(xt,0)))^(-1)*(Qt!Kt!(1/Evaluate(sQp,xt))));
  end if;

  derxt:=Qt!Kt!Derivative(xt); 
  diffs:=[];
  for i:=1 to #basis do
    basisxt:=Evaluate(basis[i],xt);
    for j:=1 to d do
      basisxt[1][j]:=Qt!Kt!basisxt[1][j];
    end for;
    diffs[i]:=InnerProduct(Vector(basisxt*derxt*lc_r*denom),bt);
    diffs[i]:=Qt!Kt!diffs[i];
    if Coefficient(diffs[i],-1) ne 0 then
      diffs[i]:=diffs[i]-Coefficient(diffs[i],-1)*Kt.1^(-1); // deal with logs later, important for double integrals
    end if;
  end for;

  maxpoleorder:=-(Minimum([Valuation(diffs[i]): i in [1..#basis]])); 
  maxdegree:=Maximum([Degree(diffs[i]): i in [1..#basis]]);
  mindegree:=Minimum([Degree(diffs[i]): i in [1..#basis]]);

  indefints:=[];
  for i:=1 to #basis do
    indefints := Append(indefints, Integral(diffs[i]));
  end for;

  indefdoubints:=[];
  for i in [1..#basis] do
     for j in [1..#basis] do
     indefdoubints:=Append(indefdoubints, Integral(diffs[i]*indefints[j]));
     end for;
  end for;

  tinydoubP1toP2:=[];
  for i:=1 to #basis do
    for j:= 1 to #basis do
    ij:=(i-1)*(#basis) + j;
    if index eq 0 then // x-x(P1) is the local coordinate
      tinydoubP1toP2[ij]:=Evaluate(indefdoubints[ij],x2-x1);
      val:=Valuation(x2-x1);
    else // b[index]-b[index](P1) is the local coordinate
      tinydoubP1toP2[ij]:=Evaluate(indefdoubints[ij],b2[index]-b1[index]);
      val:=Valuation(b2[index]-b1[index]);
    end if;
  end for;
  end for;

  //need to change this
  NtinyP1toP2:=tiny_integral_prec(prec,e,maxpoleorder,maxdegree,mindegree,val,data);

  return Vector(tinydoubP1toP2),NtinyP1toP2;

end function;
//////////////////////////////////////////////////////

function tiny_triple_integrals_on_basis(P1,P2,data:prec:=0,P:=0);

  // Compute tiny triple integrals of basis elements from P1 to P2.
  // If P1 is not defined over Qp (but a totally ramified 
  // extension) then a point P defined over Qp in the same
  // residue disk as P1 has to be specified.
  //
  // Returns the tiny *triple* integrals on basis

 x1:=P1`x; x2:=P2`x; b1:=P1`b; b2:=P2`b; Q:=data`Q; p:=data`p; N:=data`N; W0:=data`W0; Winf:=data`Winf; r:=data`r; basis:=data`basis; N:=data`N;
 d:=Degree(Q); lc_r:=LeadingCoefficient(r); W:=Winf*W0^(-1); K:=Parent(x1); 

  if not lie_in_same_disk(P1,P2,data) then
    error "the points do not lie in the same residue disk";
  end if;

  if (Valuation(x1-x2)/Valuation(Parent(x1-x2)!p) ge N) and (Minimum([Valuation(b1[i]-b2[i])/Valuation(Parent(b1[i]-b2[i])!p):i in [1..d]]) ge N) then
    return RSpace(K,#basis^3)!0, N*Degree(K);
  end if; 

  //recursive call to tiny triple integrals via P (defined over Qp)
  if Degree(K) gt 1 then // P1 needs to be defined over Qp
    tinysingPtoP2,NtinysingPtoP2:=tiny_integrals_on_basis(P,P2,data);
    tinydoubPtoP2,NtinydoubPtoP2:=tiny_double_integrals_on_basis(P,P2,data);
    tinytripPtoP2,NtinytripPtoP2:=$$(P,P2,data);
    tinysingPtoP1,NtinysingPtoP1:=tiny_integrals_on_basis(P,P1,data);
    tinydoubPtoP1,NtinydoubPtoP1:=tiny_double_integrals_on_basis(P,P1,data);
    tinytripPtoP1,NtinytripPtoP1:=$$(P,P1,data);
    tinytrip:=[];
    for i in [1..#basis] do
        for j in [1..#basis] do
            for k in [1..#basis] do
            ijk:=(i-1)*(#basis)^2 + (j-1) + k;
            kji:=(k-1)*(#basis)^2 + (j-1) + i;
            kj:=(k-1)*(#basis) + j;
            ij:=(i-1)*(#basis) + j;
            tinytrip:=Append(tinytrip, tinytripPtoP2[ijk] - tinytripPtoP1[kji] 
                            + tinysingPtoP2[i]*tinydoubPtoP1[kj] - tinysingPtoP1[k]*tinydoubPtoP2[ij]);
            end for;
        end for;
    end for;
    return tinytrip, Minimum(NtinysingPtoP2,NtinysingPtoP1, NtinydoubPtoP2,NtinydoubPtoP1);
  end if;

  if not Type(P) eq Rec then
    P:=P1;
  end if;

  if is_bad(P,data) and not is_very_bad(P,data) then // on a bad disk P1 needs to be very bad
    P:=find_bad_point_in_disk(P,data);
    tinysingPtoP2,NtinysingPtoP2:=tiny_integrals_on_basis(P,P2,data);
    tinydoubPtoP2,NtinydoubPtoP2:=tiny_double_integrals_on_basis(P,P2,data);
    tinytripPtoP2,NtinytripPtoP2:=$$(P,P2,data);
    tinysingPtoP1,NtinysingPtoP1:=tiny_integrals_on_basis(P,P1,data);
    tinydoubPtoP1,NtinydoubPtoP1:=tiny_double_integrals_on_basis(P,P1,data);
    tinytripPtoP1,NtinytripPtoP1:=$$(P,P1,data);
    tinytrip:=[];
    for i in [1..#basis] do
        for j in [1..#basis] do
            for k in [1..#basis] do
            ijk:=(i-1)*(#basis)^2 + (j-1) + k;
            kji:=(k-1)*(#basis)^2 + (j-1) + i;
            kj:=(k-1)*(#basis) + j;
            ij:=(i-1)*(#basis) + j;
            tinytrip:=Append(tinytrip, tinytripPtoP2[ijk] - tinytripPtoP1[kji] 
                            + tinysingPtoP2[i]*tinydoubPtoP1[kj] - tinysingPtoP1[k]*tinydoubPtoP2[ij]);
            end for;
        end for;
    end for;
    return tinytrip, Minimum(NtinysingPtoP2,NtinysingPtoP1, NtinydoubPtoP2,NtinydoubPtoP1);
  end if;

  e:=Degree(Parent(x2));

  if prec eq 0 then // no t-adic precision specified
    prec:=tadicprec(data,e);
  end if;

  Kt:=LaurentSeriesRing(K,prec);
  OK:=RingOfIntegers(K);
  OKt:=LaurentSeriesRing(OK,prec);

  xt,bt,index:=local_coord(P1,prec,data);

  Qt<t>:=LaurentSeriesRing(RationalField(),prec);
  xt:=Qt!xt;
  btnew:=[Qt|];
  for i:=1 to d do
    btnew[i]:=Qt!bt[i];
  end for;
  bt:=Vector(btnew);

  if P1`inf then
    xt:=1/xt;
    xt:=Qt!Kt!xt; 
    Winv:=W0*Winf^(-1);          
    bt:=bt*Transpose(Evaluate(Winv,xt));
    for i:=1 to d do
      bt[i]:=Qt!(Kt!bt[i]);
    end for; 
  end if;

  if P1`inf or not is_bad(P1,data) then 
    denom:=Qt!Kt!(1/Evaluate(r,xt));
  else
    Qp:=pAdicField(p,N);
    Qpx:=PolynomialRing(Qp);
    rQp:=Qpx!r;
    zero:=HenselLift(rQp,x1);
    sQp:=rQp div (Qpx.1-zero);
    denom:=Qt!Kt!((Qt!OKt!(xt-Coefficient(xt,0)))^(-1)*(Qt!Kt!(1/Evaluate(sQp,xt))));
  end if;

  derxt:=Qt!Kt!Derivative(xt); 
  diffs:=[];
  for i:=1 to #basis do
    basisxt:=Evaluate(basis[i],xt);
    for j:=1 to d do
      basisxt[1][j]:=Qt!Kt!basisxt[1][j];
    end for;
    diffs[i]:=InnerProduct(Vector(basisxt*derxt*lc_r*denom),bt);
    diffs[i]:=Qt!Kt!diffs[i];
    if Coefficient(diffs[i],-1) ne 0 then
      diffs[i]:=diffs[i]-Coefficient(diffs[i],-1)*Kt.1^(-1); // deal with logs later, important for double integrals
    end if;
  end for;

  maxpoleorder:=-(Minimum([Valuation(diffs[i]): i in [1..#basis]])); 
  maxdegree:=Maximum([Degree(diffs[i]): i in [1..#basis]]);
  mindegree:=Minimum([Degree(diffs[i]): i in [1..#basis]]);

  indefints:=[];
  for i:=1 to #basis do
    indefints := Append(indefints, Integral(diffs[i]));
  end for;

  indefdoubints:=[];
  for i in [1..#basis] do
     for j in [1..#basis] do
     indefdoubints:=Append(indefdoubints, Integral(diffs[i]*indefints[j]));
     end for;
  end for;

  indeftripints:=[];
  for i in [1..#basis] do
      for j in [1..#basis] do
          for k in [1..#basis] do
          jk:=(j-1)*(#basis) + k;
          indeftripints:=Append(indeftripints, Integral(diffs[i]*indefdoubints[jk]));
          end for;
      end for;
  end for;

  tinytripP1toP2:=[];
  for i:=1 to #basis do
    for j:= 1 to #basis do
        for k:=1 to #basis do
         ijk:=(i-1)*(#basis)^2 + (j-1)*(#basis) + k;
         if index eq 0 then // x-x(P1) is the local coordinate
           tinytripP1toP2[ijk]:=Evaluate(indeftripints[ijk],x2-x1);
           val:=Valuation(x2-x1);
         else // b[index]-b[index](P1) is the local coordinate
           tinytripP1toP2[ijk]:=Evaluate(indeftripints[ijk],b2[index]-b1[index]);
           val:=Valuation(b2[index]-b1[index]);
        end if;
  end for;
  end for;
  end for;

  //need to change this
  NtinyP1toP2:=tiny_integral_prec(prec,e,maxpoleorder,maxdegree,mindegree,val,data);

  return Vector(tinytripP1toP2),NtinyP1toP2;

end function;
//////////////////////////////////////////////////////

function compute_F(data,i);

  F:=data`F; Q:=data`Q; basis:=data`basis;  f0list:=data`f0list; finflist:=data`finflist; fendlist:=data`fendlist; p:=data`p; N:=data`N; delta:=data`delta;
  d:=Degree(Q); 


  W0:=data`W0; Winf:=data`Winf;
  W:=Winf*W0^(-1);
  f0 :=f0list[i];
  Qxzzinvd:=Parent(f0);
  Qxzzinv:=BaseRing(Qxzzinvd);
  x1:=Qxzzinv!(BaseRing(Qxzzinv).1);
  Qxxinv:=LaurentSeriesRing(RationalField());

  finf:=finflist[i];
  fend:=fendlist[i];

  conv:=Qxzzinvd!Evaluate(Evaluate(finf,Qxxinv.1)*Evaluate(W,Qxxinv.1),x1); // finf converted to basis b^0
  F:=f0+conv+fend;

  return F;
end function;

//////////////////////////////////////////////////////

function compute_fom(data,f0om,finfom,fendom);

  //adds fom0+fominf+fomend with the right coercions to get fom

  F:=data`F; Q:=data`Q; basis:=data`basis;  f0list:=data`f0list; finflist:=data`finflist; fendlist:=data`fendlist; p:=data`p; N:=data`N; delta:=data`delta;
  d:=Degree(Q); 


  W0:=data`W0; Winf:=data`Winf;
  W:=Winf*W0^(-1);

  f0 := f0om;
  finf:=finfom;
  fend:=fendom;

  Qxzzinvd:=Parent(f0);
  Qxzzinv:=BaseRing(Qxzzinvd);
  x1:=Qxzzinv!(BaseRing(Qxzzinv).1);
  Qxxinv:=LaurentSeriesRing(RationalField());

  conv:=Qxzzinvd!Evaluate(Evaluate(finf,Qxxinv.1)*Evaluate(W,Qxxinv.1),x1); // finf converted to basis b^0
  F:=f0+conv+fend;

  return F;
end function;

//////////////////////////////////////////////////////

function derivative_Qxzzinvd(f,Q,p,N,r);

  // differentiate an element of Q[x][z,z^(-1)] w.r.t. x

  d:=Degree(Q);
  Qxzzinv:=BaseRing(f);
  Qx:=BaseRing(Qxzzinv);
  z:=Qxzzinv.1;
  
  r:=Qx!r;
  lc:=LeadingCoefficient(r);
  r:=r/lc;
  dzdx:=Derivative(r);

  der:=Parent(f)!0;
  for i:=1 to d do
    if f[i] ne 0 then
      for j:=Valuation(f[i]) to Degree(f[i]) do
        coef:=Coefficient(f[i],j);
        der[i]:=der[i]+Derivative(coef)*z^j+coef*j*z^(j-1)*dzdx;
      end for; 
    end if;
  end for;

  return der;
end function;

//////////////////////////////////////////////////////

function ordp_Qxzzinv(f,p);

  // Compute the p-adic valuation of an element of Qxzzinv

  if f eq 0 then
    return Infinity();
  end if;

  val_list:=[];
 
  for i:=Valuation(f) to Degree(f) do
    poly:=Coefficient(f,i);
    for j:=0 to Degree(poly) do
      term:=Coefficient(poly,j);
      if term ne 0 then
        val_list:=Append(val_list,Valuation(term,p));
      end if;
    end for;
  end for;

  val:=Minimum(val_list);

  return val;  
end function;

//////////////////////////////////////////////////////

function ordp_Qxzzinvd(Q,f,p);

  // Compute the p-adic valuation of an element of Qxzzinvd

  d:=Degree(Q);

  if f eq 0 then
    return Infinity();
  end if;

  val_list:=[];

  for i:=1 to d do
    if f[i] ne 0 then
      val_list:=Append(val_list,ordp_Qxzzinv(f[i],p));
    end if;
  end for;

  val:=Minimum(val_list);

  return val;
end function;

//////////////////////////////////////////////////////

function Qxzzinvd_to_R(f,Q,p,R);

  // for now assuming W0=Id, change later to more general setting

  d:=Degree(Q);

  S:=BaseRing(R);
  Ox:=BaseRing(S);
  y:=R.1;
  z:=S.1;
  x:=Ox.1;

  f_R:=R!0;  
  for i:=1 to d do
    if f[i] ne 0 then
      for j:=Valuation(f[i]) to Degree(f[i]) do
        coef:=Ox!Coefficient(f[i],j);
        f_R:=f_R+coef*z^j*y^(i-1);
      end for;
    end if;
  end for;

  return f_R;
end function;

//////////////////////////////////////////////////////

function R_to_Qxzzinvd(f,Q,Qxzzinvd);
  
  // for now assuming W0=Id, change later to more general setting

  d:=Degree(Q);
  Qxzzinv:=BaseRing(Qxzzinvd);
  Qx:=BaseRing(Qxzzinv);
  z:=Qxzzinv.1;
  x:=Qx.1;

  v:=Qxzzinvd!0;
  for i:=1 to d do
    coef:=Coefficient(f,i-1);
    if coef ne 0 then
      for j:=Valuation(coef) to Degree(coef) do
        poly:=Coefficient(coef,j);
        for k:=0 to Degree(poly) do
          v[i]:=v[i]+(IntegerRing()!Coefficient(poly,k))*x^k*z^j;
        end for;
      end for;
    end if;
  end for;

  return v;  
end function;

//////////////////////////////////////////////////////
function compute_dF(data,F);

  // Compute dF as vector of coefficients w.r.t. b^0 dx/z
  G0:=data`G0;
  Q:=data`Q;
  p:=data`p;
  N:=data`N;
  r:=data`r;

  Qxzzinv:=BaseRing(F);
  Qx:=BaseRing(Qxzzinv);

  dF:=derivative_Qxzzinvd(F,Q,p,N,r)*(Qxzzinv.1)+F*ChangeRing(ChangeRing(G0*r/LeadingCoefficient(r),Qx),Qxzzinv); 

  return dF;
end function;

//////////////////////////////////////////////////////
function compute_omegaj(data,j);

  // Compute omega_j as vector of coefficients w.r.t. b^0 dx/z
  F:=data`F; Q:=data`Q; basis:=data`basis; f0list:=data`f0list; finflist:=data`finflist; fendlist:=data`fendlist; p:=data`p; N:=data`N; delta:=data`delta;
  d:=Degree(Q);  

  Qxzzinvd:=Parent(f0list[1]);
  Qxzzinv:=BaseRing(Qxzzinvd);
  Qx:=BaseRing(Qxzzinv);
  
  v:=Qxzzinvd!0;
  for i:=1 to d do
    v[i]:=Qx!(basis[j][i]);
  end for;

  return v;
end function;

//////////////////////////////////////////////////////

function Fi_dFj_data(data,i,j,P1,P2);
  F:=data`F; Q:=data`Q; basis:=data`basis; f0list:=data`f0list; finflist:=data`finflist; fendlist:=data`fendlist; p:=data`p; N:=data`N; delta:=data`delta;
  d:=Degree(Q);  r:=data`r;
  Nmax:=data`Nmax;
  W0:=data`W0;
  Winf:=data`Winf;
  G0:=data`G0;
  Ginf:=data`Ginf;
  red_list_fin:=data`red_list_fin;
  red_list_inf:=data`red_list_inf;
  integrals:=data`integrals;
  quo_map:=data`quo_map;
  // for now assuming W0=Id, change later to more general setting
   
  d:=Degree(Q);

  Fi:=compute_F(data,i);
  Fj:=compute_F(data,j);
  dFj:=compute_dF(data,Fj);
  
  val_Fi:=ordp_Qxzzinvd(Q,Fi,p);
  val_dFj:=ordp_Qxzzinvd(Q,dFj,p);


  Fi:=Fi*p^(-val_Fi);
  dFj:=dFj*p^(-val_dFj);
  N1:=Nmax-val_Fi-val_dFj; // multiplying out by denominators, so have to increase p-adic precision accordingly

  O,Ox,S,R:=getrings(p,N1);
  
  C:=[];
  for i:=1 to d+1 do
    C[i]:=Ox!(Coefficient(Q,i-1));
  end for;
  Q:=(R!C);

  Fi_R:=Qxzzinvd_to_R(Fi,Q,p,R);
  dFj_R:=Qxzzinvd_to_R(dFj,Q,p,R);

  Fi_dFj_R:=Fi_R*dFj_R;

  r_Ox:=Ox!r;
  lc:=LeadingCoefficient(r_Ox); 
  r_Ox:=r_Ox/lc;               

  Fi_dFj_R:=reduce_mod_Q(Fi_dFj_R,Q,r_Ox);

  Qxzzinvd:=Parent(Fi);
  Fi_dFj_Qxzzinvd:=p^(val_Fi+val_dFj)*R_to_Qxzzinvd(Fi_dFj_R,Q,Qxzzinvd); // putting the denominators back in

  coefs,f0,finf,f:=reduce_with_fs(Fi_dFj_Qxzzinvd,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map);

f0P1,Nf0P1:=evalf0(f0,P1,data);
f0P2,Nf0P2:=evalf0(f0,P2,data);
finfP1,NfinfP1:=evalfinf(finf,P1,data);
finfP2,NfinfP2:=evalfinf(finf,P2,data);
fendP1,NfendP1:=evalfend(f,P1,data);
fendP2,NfendP2:=evalfend(f,P2,data);
IdifP1P2:=f0P2-f0P1+finfP2-finfP1+fendP2-fendP1;

return coefs, IdifP1P2;
end function;

//////////////////////////////////////////////////////


function Fi_dFj_Fk_data(data,i,j,k,P1,P2);
  // for now assuming W0=Id, change later to more general setting

  Q:=data`Q; basis:=data`basis; f0list:=data`f0list; finflist:=data`finflist; fendlist:=data`fendlist; p:=data`p; N:=data`N; delta:=data`delta;
  d:=Degree(Q);  r:=data`r;
  Nmax:=data`Nmax;
  W0:=data`W0;
  Winf:=data`Winf;
  G0:=data`G0;
  Ginf:=data`Ginf;
  red_list_fin:=data`red_list_fin;
  red_list_inf:=data`red_list_inf;
  integrals:=data`integrals;
  quo_map:=data`quo_map;
   
  d:=Degree(Q);

  Fi:=compute_F(data,i);
  Fj:=compute_F(data,j);
  dFj:=compute_dF(data,Fj);
  Fk:=compute_F(data,k);

  
  val_Fi:=ordp_Qxzzinvd(Q,Fi,p);
  val_dFj:=ordp_Qxzzinvd(Q,dFj,p);
  val_Fk:=ordp_Qxzzinvd(Q,Fk,p);

  Fi:=Fi*p^(-val_Fi);
  dFj:=dFj*p^(-val_dFj);
  Fk:=Fk*p^(-val_Fk);

  N1:=Nmax-val_Fi-val_dFj-val_Fk; // multiplying out by denominators, so have to increase p-adic precision accordingly

  O,Ox,S,R:=getrings(p,N1);
  
  C:=[];
  for i:=1 to d+1 do
    C[i]:=Ox!(Coefficient(Q,i-1));
  end for;
  Q:=(R!C);

  Fi_R:=Qxzzinvd_to_R(Fi,Q,p,R);
  dFj_R:=Qxzzinvd_to_R(dFj,Q,p,R);
  Fk_R:=Qxzzinvd_to_R(Fk,Q,p,R);

  Fi_dFj_Fk_R:=Fi_R*dFj_R*Fk_R;

  r_Ox:=Ox!r;
  lc:=LeadingCoefficient(r_Ox); 
  r_Ox:=r_Ox/lc;               

  Fi_dFj_Fk_R:=reduce_mod_Q(Fi_dFj_Fk_R,Q,r_Ox);

  Qxzzinvd:=Parent(Fi);
  Fi_dFj_Fk_Qxzzinvd:=p^(val_Fi+val_dFj+val_Fk)*R_to_Qxzzinvd(Fi_dFj_Fk_R,Q,Qxzzinvd); // putting the denominators back in

  coefs,f0,finf,f:=reduce_with_fs(Fi_dFj_Fk_Qxzzinvd,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map);

f0P1,Nf0P1:=evalf0(f0,P1,data);
f0P2,Nf0P2:=evalf0(f0,P2,data);
finfP1,NfinfP1:=evalfinf(finf,P1,data);
finfP2,NfinfP2:=evalfinf(finf,P2,data);
fendP1,NfendP1:=evalfend(f,P1,data);
fendP2,NfendP2:=evalfend(f,P2,data);
IdifP1P2:=f0P2-f0P1+finfP2-finfP1+fendP2-fendP1;

return coefs, IdifP1P2;
end function;



function feta_omegaj_data(data,feta,j,P1,P2);

  // data to compute the integral f_{eta}*omega_j
  // for now assuming W0=Id, change later to more general setting

  F:=data`F; Q:=data`Q; basis:=data`basis; f0list:=data`f0list; finflist:=data`finflist; fendlist:=data`fendlist; p:=data`p; N:=data`N; delta:=data`delta;
  d:=Degree(Q); 


  Nmax:=data`Nmax;
  W0:=data`W0;
  Winf:=data`Winf;
  r:=data`r;
  G0:=data`G0;
  Ginf:=data`Ginf;
  red_list_fin:=data`red_list_fin;
  red_list_inf:=data`red_list_inf;
  integrals:=data`integrals;
  quo_map:=data`quo_map;


  val_feta:=ordp_Qxzzinvd(Q,feta,p);

  //edited 02/21/22 to deal with 0
  if not IsFinite(val_feta) then
    val_feta:=0;
  end if;

  omegaj:=compute_omegaj(data,j);  

  val_omegaj:=ordp_Qxzzinvd(Q,omegaj,p);
  if not IsFinite(val_omegaj) then
    val_omegaj:=0;
  end if;

  feta:=feta*p^(-val_feta);
  omegaj:=omegaj*p^(-val_omegaj);
  N1:=Nmax-val_feta-val_omegaj; // multiplying out by denominators, so have to increase p-adic precision accordingly

  O,Ox,S,R:=getrings(p,N1);
  
  C:=[];
  for i:=1 to d+1 do
    C[i]:=Ox!(Coefficient(Q,i-1));
  end for;
  Q:=(R!C);

  feta_R:=Qxzzinvd_to_R(feta,Q,p,R);
  omegaj_R:=Qxzzinvd_to_R(omegaj,Q,p,R);

  feta_omegaj_R:=feta_R*omegaj_R;
  
  r_Ox:=Ox!r;
  lc:=LeadingCoefficient(r_Ox); 
  r_Ox:=r_Ox/lc;               

  feta_omegaj_R:=reduce_mod_Q(feta_omegaj_R,Q,r_Ox);
  Qxzzinvd:=Parent(feta);
  feta_omegaj_Qxzzinvd:=p^(val_feta+val_omegaj)*R_to_Qxzzinvd(feta_omegaj_R,Q,Qxzzinvd); // putting the denominators back in

  coefs,f0,finf,f:=reduce_with_fs(feta_omegaj_Qxzzinvd,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map);
  
  f0P1,Nf0P1:=evalf0(f0,P1,data);
  f0P2,Nf0P2:=evalf0(f0,P2,data);
  finfP1,NfinfP1:=evalfinf(finf,P1,data);
  finfP2,NfinfP2:=evalfinf(finf,P2,data);
  fendP1,NfendP1:=evalfend(f,P1,data);
  fendP2,NfendP2:=evalfend(f,P2,data);
  IdifP1P2:=f0P2-f0P1+finfP2-finfP1+fendP2-fendP1;

  return coefs, IdifP1P2;

end function;
//////////////////////////////////////////////////////
function Fi_omegaj_data(data,i,j,P1,P2);

  // for now assuming W0=Id, change later to more general setting

  F:=data`F; Q:=data`Q; basis:=data`basis; f0list:=data`f0list; finflist:=data`finflist; fendlist:=data`fendlist; p:=data`p; N:=data`N; delta:=data`delta;
  d:=Degree(Q); 

  Nmax:=data`Nmax;
  W0:=data`W0;
  Winf:=data`Winf;
  r:=data`r;
  G0:=data`G0;
  Ginf:=data`Ginf;
  red_list_fin:=data`red_list_fin;
  red_list_inf:=data`red_list_inf;
  integrals:=data`integrals;
  quo_map:=data`quo_map;


  Fi:=compute_F(data,i);
  omegaj:=compute_omegaj(data,j);  

  val_Fi:=ordp_Qxzzinvd(Q,Fi,p);
  val_omegaj:=ordp_Qxzzinvd(Q,omegaj,p);

  Fi:=Fi*p^(-val_Fi);
  omegaj:=omegaj*p^(-val_omegaj);
  N1:=Nmax-val_Fi-val_omegaj; // multiplying out by denominators, so have to increase p-adic precision accordingly

  O,Ox,S,R:=getrings(p,N1);
  
  C:=[];
  for i:=1 to d+1 do
    C[i]:=Ox!(Coefficient(Q,i-1));
  end for;
  Q:=(R!C);

  Fi_R:=Qxzzinvd_to_R(Fi,Q,p,R);
  omegaj_R:=Qxzzinvd_to_R(omegaj,Q,p,R);

  Fi_omegaj_R:=Fi_R*omegaj_R;
  
  r_Ox:=Ox!r;
  lc:=LeadingCoefficient(r_Ox); 
  r_Ox:=r_Ox/lc;               

  Fi_omegaj_R:=reduce_mod_Q(Fi_omegaj_R,Q,r_Ox);
  Qxzzinvd:=Parent(Fi);
  Fi_omegaj_Qxzzinvd:=p^(val_Fi+val_omegaj)*R_to_Qxzzinvd(Fi_omegaj_R,Q,Qxzzinvd); // putting the denominators back in

  coefs,f0,finf,f:=reduce_with_fs(Fi_omegaj_Qxzzinvd,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map);
  
f0P1,Nf0P1:=evalf0(f0,P1,data);
f0P2,Nf0P2:=evalf0(f0,P2,data);
finfP1,NfinfP1:=evalfinf(finf,P1,data);
finfP2,NfinfP2:=evalfinf(finf,P2,data);
fendP1,NfendP1:=evalfend(f,P1,data);
fendP2,NfendP2:=evalfend(f,P2,data);
IdifP1P2:=f0P2-f0P1+finfP2-finfP1+fendP2-fendP1;

return coefs, IdifP1P2;

end function;

//////////////////////////////////////////////////////


function Fisquare_omegaj_data(data,i,j,P1,P2);

  // for now assuming W0=Id, change later to more general setting

  F:=data`F; Q:=data`Q; basis:=data`basis; f0list:=data`f0list; finflist:=data`finflist; fendlist:=data`fendlist; p:=data`p; N:=data`N; delta:=data`delta;
  d:=Degree(Q); 

  Nmax:=data`Nmax;
  W0:=data`W0;
  Winf:=data`Winf;
  G0:=data`G0;
  Ginf:=data`Ginf;
  red_list_fin:=data`red_list_fin;
  red_list_inf:=data`red_list_inf;
  integrals:=data`integrals;
  quo_map:=data`quo_map;
  r:=data`r;

  Fi:=compute_F(data,i);
  omegaj:=compute_omegaj(data,j);  

  val_Fi:=ordp_Qxzzinvd(Q,Fi,p);
  val_omegaj:=ordp_Qxzzinvd(Q,omegaj,p);
  Fi:=(Fi*p^(-val_Fi));
  omegaj:=omegaj*p^(-val_omegaj);
  N1:=Nmax-2*val_Fi-val_omegaj; // multiplying out by denominators, so have to increase p-adic precision accordingly

  O,Ox,S,R:=getrings(p,N1);
  
  C:=[];
  for i:=1 to d+1 do
    C[i]:=Ox!(Coefficient(Q,i-1));
  end for;
  Q:=(R!C);

  Fi_R:=Qxzzinvd_to_R(Fi,Q,p,R);
  omegaj_R:=Qxzzinvd_to_R(omegaj,Q,p,R);

  Fisquare_omegaj_R:=Fi_R^2*omegaj_R;
  
  r_Ox:=Ox!r;
  lc:=LeadingCoefficient(r_Ox); 
  r_Ox:=r_Ox/lc;               

  Fisquare_omegaj_R:=reduce_mod_Q(Fisquare_omegaj_R,Q,r_Ox);
  Qxzzinvd:=Parent(Fi);
  Fisquare_omegaj_Qxzzinvd:=p^(2*val_Fi+val_omegaj)*R_to_Qxzzinvd(Fisquare_omegaj_R,Q,Qxzzinvd); // putting the denominators back in

  coefs,f0,finf,f:=reduce_with_fs(Fisquare_omegaj_Qxzzinvd,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map);

f0P1,Nf0P1:=evalf0(f0,P1,data);
f0P2,Nf0P2:=evalf0(f0,P2,data);
finfP1,NfinfP1:=evalfinf(finf,P1,data);
finfP2,NfinfP2:=evalfinf(finf,P2,data);
fendP1,NfendP1:=evalfend(f,P1,data);
fendP2,NfendP2:=evalfend(f,P2,data);
IdifP1P2:=f0P2-f0P1+finfP2-finfP1+fendP2-fendP1;

return coefs, IdifP1P2;
  //return coefs,f0,finf,f; 
end function;

//////////////////////////////////////////////////////

function Fi_Fj_omegak_data(data,i,j,k,P1,P2);

  // for now assuming W0=Id, change later to more general setting

  F:=data`F; Q:=data`Q; basis:=data`basis; f0list:=data`f0list; finflist:=data`finflist; fendlist:=data`fendlist; p:=data`p; N:=data`N; delta:=data`delta;
  d:=Degree(Q); 

  Nmax:=data`Nmax;
  W0:=data`W0;
  Winf:=data`Winf;
  G0:=data`G0;
  Ginf:=data`Ginf;
  red_list_fin:=data`red_list_fin;
  red_list_inf:=data`red_list_inf;
  integrals:=data`integrals;
  quo_map:=data`quo_map;
  r:=data`r;

  Fi:=compute_F(data,i);
  Fj:=compute_F(data,j);
  omegak:=compute_omegaj(data,k);  

  val_Fi:=ordp_Qxzzinvd(Q,Fi,p);
  val_Fj:=ordp_Qxzzinvd(Q,Fj,p);
  val_omegak:=ordp_Qxzzinvd(Q,omegak,p);
  Fi:=(Fi*p^(-val_Fi));
  Fj:=(Fj*p^(-val_Fj));
  omegak:=omegak*p^(-val_omegak);
  N1:=Nmax-val_Fi-val_Fj-val_omegak; // multiplying out by denominators, so have to increase p-adic precision accordingly

  O,Ox,S,R:=getrings(p,N1);
  
  C:=[];
  for i:=1 to d+1 do
    C[i]:=Ox!(Coefficient(Q,i-1));
  end for;
  Q:=(R!C);

  Fi_R:=Qxzzinvd_to_R(Fi,Q,p,R);
  Fj_R:=Qxzzinvd_to_R(Fj,Q,p,R);
  omegak_R:=Qxzzinvd_to_R(omegak,Q,p,R);

  FiFjomegak_R:=Fi_R*Fj_R*omegak_R;
  
  r_Ox:=Ox!r;
  lc:=LeadingCoefficient(r_Ox); 
  r_Ox:=r_Ox/lc;               

  FiFjomegak_R:=reduce_mod_Q(FiFjomegak_R,Q,r_Ox);
  Qxzzinvd:=Parent(Fi);
  FiFjomegak_Qxzzinvd:=p^(val_Fi+val_Fj+val_omegak)*R_to_Qxzzinvd(FiFjomegak_R,Q,Qxzzinvd); // putting the denominators back in

  coefs,f0,finf,f:=reduce_with_fs(FiFjomegak_Qxzzinvd,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map);

f0P1,Nf0P1:=evalf0(f0,P1,data);
f0P2,Nf0P2:=evalf0(f0,P2,data);
finfP1,NfinfP1:=evalfinf(finf,P1,data);
finfP2,NfinfP2:=evalfinf(finf,P2,data);
fendP1,NfendP1:=evalfend(f,P1,data);
fendP2,NfendP2:=evalfend(f,P2,data);
IdifP1P2:=f0P2-f0P1+finfP2-finfP1+fendP2-fendP1;

return coefs, IdifP1P2;
  //return coefs,f0,finf,f; 
end function;


////////////////////////////////////////

function coleman_integral_all_feta_omegaj(feta,P1,P2,data:e:=1)
Q:=data`Q; basis:=data`basis; x1:=P1`x; p:=data`p; N:=data`N; d:=Degree(Q); K:=Parent(x1); 
g:=genus(Q,p);
basisintegrals:=coleman_integrals_on_basis(P1,P2,data:e:=1);
V:=VectorSpace(K,#basis);
allfeta_omegaj:=[];
for j in [1..#basis] do
  coefs,If:=feta_omegaj_data(data,feta,j,P1,P2);
  coefs:=Vector(V!coefs);
  I:=DotProduct(coefs,basisintegrals) + If; //int_df(df,P2,P1,data); //allfs;
  allfeta_omegaj:=Append(allfeta_omegaj,I);
end for;
V:=VectorSpace(K,#basis);
return V!allfeta_omegaj;
end function;


//////////////////////////////////////////////////////
function coleman_integral_all_Fi_omegaj(P1,P2,data:e:=1)
//This is a helper function for double integrals.
//Note that the output values are not precisely the coleman integrals on F_i omega_j, 
//but rather the coleman integrals between P1 to P2 of the projection of F_i omega_j on H^1(X).

Q:=data`Q; basis:=data`basis; x1:=P1`x; p:=data`p; N:=data`N; d:=Degree(Q); K:=Parent(x1); 
basisintegrals:=coleman_integrals_on_basis(P1,P2,data:e:=1);
V:=VectorSpace(K,#basis);
allFi_omegaj:=[];
for i in [1..#basis] do
  for j in [1..#basis] do
    coefs,If:=Fi_omegaj_data(data,i,j,P1,P2);
    coefs:=Vector(V!coefs);
    I:=DotProduct(coefs,basisintegrals) + If; 
    allFi_omegaj:=Append(allFi_omegaj,I);
  end for;
end for;
V:=VectorSpace(K,(#basis)^2);
return V!allFi_omegaj;
end function;
//////////////////////////////////////////////////////

//////////////////////////////////////////////////////
function coleman_integral_all_Fisquare_omegaj(P1,P2,data:e:=1)
//This is a helper function for double integrals.
//Note that the output values are not precisely the coleman integrals on F_i omega_j, 
//but rather the coleman integrals between P1 to P2 of the projection of F_i omega_j on H^1(X).

Q:=data`Q; basis:=data`basis; x1:=P1`x; p:=data`p; N:=data`N; d:=Degree(Q); K:=Parent(x1); 
basisintegrals:=coleman_integrals_on_basis(P1,P2,data:e:=1);
V:=VectorSpace(K,#basis);

allFisquare_omegaj:=[];
for i in [1..#basis] do
  for j in [1..#basis] do
    coefs,If:=Fisquare_omegaj_data(data,i,j,P1,P2);
    coefs:=Vector(V!coefs);
    I:=DotProduct(coefs,basisintegrals) + If; 
    allFisquare_omegaj:=Append(allFisquare_omegaj,I);
  end for;
end for;
V:=VectorSpace(K,(#basis)^2);
return V!allFisquare_omegaj;
end function;
//////////////////////////////////////////////////////

function coleman_integral_all_Fi_Fj_omegak(P1,P2,data:e:=1);
Q:=data`Q; basis:=data`basis; x1:=P1`x; p:=data`p; N:=data`N; d:=Degree(Q); K:=Parent(x1); 
basisintegrals:=coleman_integrals_on_basis(P1,P2,data:e:=1);
V:=VectorSpace(K,#basis);

allFiFj_omegak:=[];
for i in [1..#basis] do
  for j in [1..#basis] do
    for k in [1..#basis] do
      coefs, If:=Fi_Fj_omegak_data(data,i,j,k,P1,P2);
      coefs:=Vector(V!coefs);
      I:=DotProduct(coefs,basisintegrals) + If;
      allFiFj_omegak:=Append(allFiFj_omegak,I);
    end for;
  end for;
end for;
V:=VectorSpace(K,(#basis)^3);
return V!allFiFj_omegak;
end function;

//////////////////////////////////////////////////////


function coleman_integral_all_Fi_dFj_Fk(P1,P2,data:e:=1);
Q:=data`Q; basis:=data`basis; x1:=P1`x; p:=data`p; N:=data`N; d:=Degree(Q); K:=Parent(x1); 
basisintegrals:=coleman_integrals_on_basis(P1,P2,data:e:=1);
V:=VectorSpace(K,#basis);

allFi_dFj_Fk:=[];
for i in [1..#basis] do
  for j in [1..#basis] do
    for k in [1..#basis] do
      coefs, If:=Fi_dFj_Fk_data(data,i,j,k,P1,P2);
      coefs:=Vector(V!coefs);
      I:=DotProduct(coefs,basisintegrals) + If;
      allFi_dFj_Fk:=Append(allFi_dFj_Fk,I);
    end for;
  end for;
end for;
V:=VectorSpace(K, (#basis)^3);
return V!allFi_dFj_Fk;
end function;

//////////////////////////////////////////////////////
function coleman_integral_all_Fi_dFj(P1,P2,data:e:=1);
//This is a helper function for double integrals.
//Note that the output values are not precisely the coleman integrals \int_{P1}^{P2} F_i dF_j,
//but rather the coleman integrals between P1 to P2 of the projection of F_i dF_j on H^1(X).
Q:=data`Q; basis:=data`basis; x1:=P1`x; p:=data`p; N:=data`N; d:=Degree(Q); K:=Parent(x1); 
basisintegrals:=coleman_integrals_on_basis(P1,P2,data:e:=1);
V:=VectorSpace(K,#basis);
allFi_dFj:=[];
for i in [1..#basis] do
   for j in [1..#basis] do
     coefs,If:=Fi_dFj_data(data,i,j,P1,P2);
     coefs:=Vector(V!coefs);
     I:=DotProduct(coefs,basisintegrals) + If; 
     allFi_dFj:=Append(allFi_dFj,I);
     end for;
end for;
V:=VectorSpace(K,(#basis)^2);
return V!allFi_dFj;
end function;
//////////////////////////////////////////////////////


//////////////////////////////////////////////////////
double_integrals_on_basis:=function(P1,P2,data:e:=1)

  // Double Coleman integrals of basis elements from P1 to P2. 

  F:=data`F; Q:=data`Q; basis:=data`basis; x1:=P1`x; f0list:=data`f0list; finflist:=data`finflist; fendlist:=data`fendlist; p:=data`p; N:=data`N; delta:=data`delta;
  d:=Degree(Q); K:=Parent(x1); 

  // First make sure that if P1 or P2 is bad, then it is very bad

  if is_bad(P1,data) and not is_very_bad(P1,data) then
    S1:=find_bad_point_in_disk(P1,data);
    _,index:=local_data(S1,data);
    data:=update_minpolys(data,S1`inf,index);
    xt,bt,index:=local_coord(S1,tadicprec(data,e),data);
    S1`xt:=xt;
    S1`bt:=bt;
    S1`index:=index;
    IdoubS1P1,NdoubIS1P1:=tiny_double_integrals_on_basis(S1,P1,data:prec:=tadicprec(data,e));
    IdoubS1P2,NdoubIS1P2:=$$(S1,P2,data:e:=e);
    IsingS1P1,NsingIS1P1:=tiny_integrals_on_basis(S1,P1,data);
    IsingS1P2,NsingIS1P2:=coleman_integrals_on_basis(S1,P2,data);
    doub:=[];
    for i in [1..#basis] do
        for j in [1..#basis] do
        ij := (i-1)*(#basis) + j;
        ji := (j-1)*(#basis) + i;
        doub:=Append(doub, IdoubS1P2[ij]-IdoubS1P1[ji]-IsingS1P2[i]*IsingS1P1[j]);
        end for;
    end for;
    NIP1P2:=Ceiling(Minimum([NdoubIS1P1,NdoubIS1P2,NsingIS1P1,NsingIS1P2]));
    return doub,NIP1P2;
  end if;


  if is_bad(P2,data) and not is_very_bad(P2,data) then
    S2:=find_bad_point_in_disk(P2,data);
    _,index:=local_data(S2,data);
    data:=update_minpolys(data,S2`inf,index);
    xt,bt,index:=local_coord(S2,tadicprec(data,e),data);
    S2`xt:=xt;
    S2`bt:=bt;
    S2`index:=index;
    IdoubP1S2,NdoubIP1S2:=$$(P1,S2,data:e:=e);
    IdoubP2S2,NdoubIP2S2:=tiny_double_integrals_on_basis(P2,S2,data:prec:=tadicprec(data,e));
    IsingP1S2,NsingIP1S2:=coleman_integrals_on_basis(P1,S2,data);
    IsingP2S2,NsingIP2S2:=tiny_integrals_on_basis(P2,S2,data);
    doub:=[];
    for i in [1..#basis] do
        for j in [1..#basis] do
        ij := (i-1)*(#basis) + j;
        ji := (j-1)*(#basis) + i;
        doub:=Append(doub, -IdoubP2S2[ji] + IdoubP1S2[ij]- IsingP1S2[j]*IsingP2S2[i]);
        end for;
    end for;
    NIP1P2:=Ceiling(Minimum([NdoubIP1S2,NdoubIP2S2,NsingIP1S2,NsingIP2S2]));
    return doub,NIP1P2; //fix this
  end if;

  // If P1,P2 is bad (hence very bad), use a near boundary point.

  _,index:=local_data(P1,data);
  data:=update_minpolys(data,P1`inf,index);
  _,index:=local_data(P2,data);
  data:=update_minpolys(data,P2`inf,index);

  if is_bad(P1,data) then
    xt,bt,index:=local_coord(P1,tadicprec(data,e),data);
    P1`xt:=xt;       
    P1`bt:=bt;       
    P1`index:=index; 
    Qp:=Parent(P1`x);
    Qpa<a>:=PolynomialRing(Qp);
    K<a>:=TotallyRamifiedExtension(Qp,a^e-p);
    format:=recformat<x,b,inf,xt,bt,index>;
    S1:=rec<format|>;                                                    
    S1`inf:=P1`inf;
    S1`x:=Evaluate(xt,a);
    S1`b:=[Evaluate(bt[i],a):i in [1..d]];
  else
    xt,bt,index:=local_coord(P1,tadicprec(data,1),data);
    P1`xt:=xt;       
    P1`bt:=bt;       
    P1`index:=index; 
    S1:=P1;
  end if;

  if is_bad(P2,data) then
    xt,bt,index:=local_coord(P2,tadicprec(data,e),data);
    P2`xt:=xt;       
    P2`bt:=bt;       
    P2`index:=index; 
    if not is_bad(P1,data) then
      Qp:=Parent(P2`x);
      Qpa<a>:=PolynomialRing(Qp);
      K<a>:=TotallyRamifiedExtension(Qp,a^e-p);
    end if;
    format:=recformat<x,b,inf,xt,bt,index>;
    S2:=rec<format|>;                                                    
    S2`inf:=P2`inf;
    S2`x:=Evaluate(xt,a);
    S2`b:=[Evaluate(bt[i],a):i in [1..d]];
  else
    xt,bt,index:=local_coord(P2,tadicprec(data,1),data);
    P2`xt:=xt;       
    P2`bt:=bt;       
    P2`index:=index; 
    S2:=P2;
  end if;

  // Split up the integral and compute the single ones and the tiny doubles

  singP1toS1,NsingP1toS1:=tiny_integrals_on_basis(P1,S1,data);
  singP2toS2,NsingP2toS2:=tiny_integrals_on_basis(P2,S2,data);
  singS1toP2,NsingS1toP2:=coleman_integrals_on_basis(S1,P2,data);
  singS1toS2,NsingS1toS2:=coleman_integrals_on_basis(S1,S2,data);
  
  doubP1toS1,NdoubP1toS1:=tiny_double_integrals_on_basis(P1,S1,data);
  doubS2toP2,NdoubS2toP2:=tiny_double_integrals_on_basis(S2,P2,data);

  //the main part of the algorithm is computing the double integral from S1 to S2, which we do now

  FS1:=frobenius_pt(S1,data);
  FS2:=frobenius_pt(S2,data);

  //JSB edit 03/31/21
  if is_bad(S1,data) and not is_very_bad(S1,data) then
    tinyP1toFS1,NP1toFS1:=tiny_integrals_on_basis(P1,FS1,data);
    tinyS1toFS1 := tinyP1toFS1 - singP1toS1;
    NS1toFS1:=Minimum([NP1toFS1,NsingP1toS1]);
  else 
    tinyS1toFS1,NS1toFS1:=tiny_integrals_on_basis(S1,FS1,data:P:=P1); 
  end if;
  //JSB edit 04/17/21
  if is_bad(S2,data) and not is_very_bad(S2,data) then
    tinyP2toFS2,NP2toFS2:=tiny_integrals_on_basis(P2,FS2,data);
    tinyS2toFS2 := tinyP2toFS2 - singP2toS2;
    NS2toFS2:=Minimum([NP2toFS2,NsingP2toS2]);
  else
      tinyS2toFS2,NS2toFS2:=tiny_integrals_on_basis(S2,FS2,data:P:=P2); 
  end if;
  NIP1P2:=Minimum([NsingP1toS1,NsingP2toS2,NS1toFS1,NS2toFS2]);  


  doubFS1toS1, NdoubFS1toS1:=tiny_double_integrals_on_basis(FS1,S1,data);
  doubFS2toS2, NdoubFS2toS2:=tiny_double_integrals_on_basis(FS2,S2,data);

  singFS1toFS2 := -tinyS1toFS1 + singS1toS2 + tinyS2toFS2;

  // Evaluate all functions at S1, S2

  fS1:=[];
  fS2:=[];
  for i:=1 to #basis do
    f0iS1,Nf0iS1:=evalf0(f0list[i],S1,data);
    f0iS2,Nf0iS2:=evalf0(f0list[i],S2,data);
    finfiS1,NfinfiS1:=evalfinf(finflist[i],S1,data);
    finfiS2,NfinfiS2:=evalfinf(finflist[i],S2,data);
    fendiS1,NfendiS1:=evalfend(fendlist[i],S1,data);
    fendiS2,NfendiS2:=evalfend(fendlist[i],S2,data);
    NIP1P2:=Minimum([NIP1P2,Nf0iS1,Nf0iS2,NfinfiS1,NfinfiS2,NfendiS1,NfendiS2]);
    fS1[i]:=(K!f0iS1) + (K!finfiS1) + (K!fendiS1);
    fS2[i]:=(K!f0iS2) + (K!finfiS2) + (K!fendiS2);
  end for; 

  dim:=(#basis)^2;
  rowdim:=#basis;

  V:=VectorSpace(K,rowdim);
  Arows:=Rows(F);

  intfidfk_all:=coleman_integral_all_Fi_dFj(S1,S2,data:e:=1);
  intxpowldxfk_all:=coleman_integral_all_Fi_omegaj(S1,S2,data:e:=1);
  intxpowldxfk:= [];
  for i in [1..rowdim] do
    W:=[];
    for j in [1..rowdim] do
    W:=Append(W, intxpowldxfk_all[rowdim*(i-1)+j]);
    end for;
    intxpowldxfk:=Append(intxpowldxfk,W);
  end for;

  cons:=[];
  fix:=[];
  for i in [1..rowdim] do
    Ai:=V!Arows[i];
    for k in [1..rowdim] do
      Ak:=V!Arows[k];
      fkS1:=fS1[k];
      fiS1:=fS1[i];
      fiS2:=fS2[i];
      p1:= -fkS1*(fiS2-fiS1);
      p2:= intfidfk_all[rowdim*(k-1) + i]; //note this is the kith term not hte ikth term because it's fi dfk not dfi fk
      p3:= -fkS1*DotProduct(Ai,singS1toS2);
      p4:= DotProduct(Ai,Vector(intxpowldxfk[k])) - DotProduct(Ak,Vector(intxpowldxfk[i]));
      p5:= fiS2*DotProduct(Ak,singS1toS2);
      cons:=Append(cons, p1+p2+p3+p4+p5);
      fix:= Append(fix, -doubFS1toS1[rowdim*(i-1)+k] + singS1toS2[i]*tinyS1toFS1[k] - tinyS2toFS2[i]*singFS1toFS2[k] + doubFS2toS2[rowdim*(i-1)+k]);
   end for;   
  end for;      
  cons:=Vector(cons);
  fix:=Vector(fix);
  constantvec:=cons+fix;

  F2:=TensorProduct(F,F);
  F2:=ChangeRing(F2,K);
  mat:=(IdentityMatrix(K,dim)-Transpose(F2))^-1;
  valdet:=Valuation(Determinant(mat));//,p);
  Nmat:=N-valdet-delta;
  //valmat:=Minimum([Valuation(e,p):e in Eltseq(mat)]);
  //NIP1P2:=Minimum([NIP1P2+valmat,Nmat+valIP1P2]);   

  doubS1toS2:= constantvec*mat;
  doubP1toP2:=[];
  for i in [1..rowdim] do
    for k in [1..rowdim] do
        ik:=(i-1)*rowdim + k;
        doubP1toP2:=Append(doubP1toP2, doubP1toS1[ik] + doubS1toS2[ik] + doubS2toP2[ik] + singP1toS1[k]*singS1toP2[i] - singS1toS2[k]*singP2toS2[i]);
    end for;
  end for;


  NIP1P2:=Ceiling(NIP1P2);

  return doubP1toP2,NIP1P2;
end function;
//////////////////////////////////////////////////////

double_integral:=function(P1,P2,omega,eta, data:e:=1,IP1P2:=0,NIP1P2:=0);

  // Double integral of omega eta from P1 to P2.

  Q:=data`Q; p:=data`p; N:=data`N; Nmax:=data`Nmax; r:=data`r; W0:=data`W0; Winf:=data`Winf;
  G0:=data`G0; Ginf:=data`Ginf; red_list_fin:=data`red_list_fin; red_list_inf:=data`red_list_inf;
  basis:=data`basis; integrals:= data`integrals; quo_map:=data`quo_map;d:=Degree(Q);

  V:=VectorSpace(Parent(P1`x),#basis);
  //what gets passed into reduce_with_fs needs to be of a special form with the Rs and Qzs...
  val_omega:=ordp_Qxzzinvd(Q,omega,p);
  val_eta:=ordp_Qxzzinvd(Q,eta,p);

  omega:=omega*p^(-val_omega);
  eta:=eta*p^(-val_eta);
  N1:=Nmax-val_omega-val_eta; // multiplying out by denominators, so have to increase p-adic precision accordingly

  O,Ox,S,R:=getrings(p,N1);
  
  C:=[];
  for i:=1 to d+1 do
    C[i]:=Ox!(Coefficient(Q,i-1));
  end for;
  Q:=(R!C);

  omega_R:=Qxzzinvd_to_R(omega,Q,p,R);
  eta_R:=Qxzzinvd_to_R(eta,Q,p,R);

  r_Ox:=Ox!r;
  lc:=LeadingCoefficient(r_Ox); 
  r_Ox:=r_Ox/lc;               

  omega_R:=reduce_mod_Q(omega_R,Q,r_Ox);
  eta_R:=reduce_mod_Q(eta_R,Q,r_Ox);

  Qxzzinvd:=Parent(omega);
  omega_Qxzzinvd:=p^(val_omega)*R_to_Qxzzinvd(omega_R,Q,Qxzzinvd); // putting the denominators back in
  eta_Qxzzinvd:=p^(val_eta)*R_to_Qxzzinvd(eta_R,Q,Qxzzinvd); // putting the denominators back in

  coefsom,f0om,finfom,fendom:=reduce_with_fs(omega_Qxzzinvd,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map); // TODO: handle precision here
  coefseta,f0eta,finfeta,fendeta:=reduce_with_fs(eta_Qxzzinvd,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map); // TODO: handle precision here

  IP1P2,prec:=coleman_integrals_on_basis(P1,P2,data:e:=e);
  
  if NIP1P2 eq 0 then 
    doubP1P2:=Vector(double_integrals_on_basis(P1,P2,data:e:=e));
  end if;

  coeffs := Vector(TensorProduct(Matrix(Vector(coefsom)), Matrix(Vector(coefseta)))); //it seems this is the right order, not the other way around

  f0omP1,Nf0P1:=evalf0(f0om,P1,data);
  f0omP2,Nf0P2:=evalf0(f0om,P2,data);
  finfomP1,NfinfP1:=evalfinf(finfom,P1,data);
  finfomP2,NfinfP2:=evalfinf(finfom,P2,data);
  fendomP1,NfendP1:=evalfend(fendom,P1,data);
  fendomP2,NfendP2:=evalfend(fendom,P2,data);
  fomP1:=f0omP1+finfomP1+fendomP1;
  fomP2:=f0omP2+finfomP2+fendomP2;
  fom_P1P2:=fomP2-fomP1;
  NIdifP1P2:=Minimum([Nf0P1,Nf0P2,NfinfP1,NfinfP2,NfendP1,NfendP2]);

  f0etaP1,Nf0P1:=evalf0(f0eta,P1,data);
  f0etaP2,Nf0P2:=evalf0(f0eta,P2,data);
  finfetaP1,NfinfP1:=evalfinf(finfeta,P1,data);
  finfetaP2,NfinfP2:=evalfinf(finfeta,P2,data);
  fendetaP1,NfendP1:=evalfend(fendeta,P1,data);
  fendetaP2,NfendP2:=evalfend(fendeta,P2,data);
  fetaP1:=f0etaP1+finfetaP1+fendetaP1;
  fetaP2:=f0etaP2+finfetaP2+fendetaP2;
  fetaP1P2:=fetaP2-fetaP1;


  fom:=compute_fom(data,f0om,finfom,fendom);
  feta:=compute_fom(data,f0eta,finfeta,fendeta);
  fom_diff:=compute_dF(data,fom);

  coefsom:=V!coefsom;
  coefseta:=V!coefseta;

  a1:= -fetaP1*fom_P1P2;
  a2:= coleman_integral(P1,P2, fom_diff*feta, data); 
  a3:= -fetaP1*(coefsom,IP1P2);
  a4:= (coefsom,coleman_integral_all_feta_omegaj(feta,P1,P2,data));
  a5:= -(coefseta,coleman_integral_all_feta_omegaj(fom,P1,P2,data)); 
  a6:= fomP2*(coefseta,IP1P2);
  W:=VectorSpace(Parent(P1`x),#basis^2);
  return a1+a2+a3+a4+a5+a6+(W!coeffs,doubP1P2);

end function;

  double_integral_Fkomegaj_omegah:=function(P1,P2,k,j,h, data:e:=1,IP1P2:=0,NIP1P2:=0);

  // Double integral of omega eta from P1 to P2.

  Q:=data`Q; p:=data`p; N:=data`N; Nmax:=data`Nmax; r:=data`r; W0:=data`W0; Winf:=data`Winf;
  G0:=data`G0; Ginf:=data`Ginf; red_list_fin:=data`red_list_fin; red_list_inf:=data`red_list_inf;
  basis:=data`basis; integrals:= data`integrals; quo_map:=data`quo_map;d:=Degree(Q);

  V:=VectorSpace(Parent(P1`x),#basis);
  //what gets passed into reduce_with_fs needs to be of a special form with the Rs and Qzs...
  omegah:=compute_omegaj(data,h);  
  val_omegah:=ordp_Qxzzinvd(Q,omegah,p);
  Fk:=compute_F(data,k);
  val_Fk:=ordp_Qxzzinvd(Q,Fk,p);
  omegaj:=compute_omegaj(data,j);  
  val_omegaj:=ordp_Qxzzinvd(Q,omegaj,p);

  omegah:=omegah*p^(-val_omegah);
  omegaj:=omegaj*p^(-val_omegaj);
  Fk:=Fk*p^(-val_Fk);

  N1:=Nmax-val_omegah-val_Fk-val_omegaj; // multiplying out by denominators, so have to increase p-adic precision accordingly

  O,Ox,S,R:=getrings(p,N1);
  
  C:=[];
  for i:=1 to d+1 do
    C[i]:=Ox!(Coefficient(Q,i-1));
  end for;
  Q:=(R!C);

  omegah_R:=Qxzzinvd_to_R(omegah,Q,p,R);
  omegaj_R:=Qxzzinvd_to_R(omegaj,Q,p,R);
  Fk_R:=Qxzzinvd_to_R(Fk,Q,p,R);
  r_Ox:=Ox!r;
  lc:=LeadingCoefficient(r_Ox); 
  r_Ox:=r_Ox/lc;  

  omegah_R:=reduce_mod_Q(omegah_R,Q,r_Ox);
  Fkomegaj_R:=reduce_mod_Q(Fk_R*omegaj_R, Q,r_Ox);

  Qxzzinvd:=Parent(omegaj);
  omegah_Qxzzinvd:=p^(val_omegah)*R_to_Qxzzinvd(omegah_R,Q,Qxzzinvd); // putting the denominators back in
  Fkomegaj_Qxzzinvd:=p^(val_Fk+val_omegaj)*R_to_Qxzzinvd(Fkomegaj_R, Q,Qxzzinvd); // putting the denominators back in

  coefsom,f0om,finfom,fendom:=reduce_with_fs(Fkomegaj_Qxzzinvd,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map); // TODO: handle precision here
  coefseta,f0eta,finfeta,fendeta:=reduce_with_fs(omegah_Qxzzinvd,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map); // TODO: handle precision here

  IP1P2,prec:=coleman_integrals_on_basis(P1,P2,data:e:=e);
  
  if NIP1P2 eq 0 then 
    doubP1P2:=Vector(double_integrals_on_basis(P1,P2,data:e:=e));
  end if;

  coeffs := Vector(TensorProduct(Matrix(Vector(coefsom)), Matrix(Vector(coefseta)))); //it seems this is the right order, not the other way around

  f0omP1,Nf0P1:=evalf0(f0om,P1,data);
  f0omP2,Nf0P2:=evalf0(f0om,P2,data);
  finfomP1,NfinfP1:=evalfinf(finfom,P1,data);
  finfomP2,NfinfP2:=evalfinf(finfom,P2,data);
  fendomP1,NfendP1:=evalfend(fendom,P1,data);
  fendomP2,NfendP2:=evalfend(fendom,P2,data);
  fomP1:=f0omP1+finfomP1+fendomP1;
  fomP2:=f0omP2+finfomP2+fendomP2;
  fom_P1P2:=fomP2-fomP1;
  NIdifP1P2:=Minimum([Nf0P1,Nf0P2,NfinfP1,NfinfP2,NfendP1,NfendP2]);

  f0etaP1,Nf0P1:=evalf0(f0eta,P1,data);
  f0etaP2,Nf0P2:=evalf0(f0eta,P2,data);
  finfetaP1,NfinfP1:=evalfinf(finfeta,P1,data);
  finfetaP2,NfinfP2:=evalfinf(finfeta,P2,data);
  fendetaP1,NfendP1:=evalfend(fendeta,P1,data);
  fendetaP2,NfendP2:=evalfend(fendeta,P2,data);
  fetaP1:=f0etaP1+finfetaP1+fendetaP1;
  fetaP2:=f0etaP2+finfetaP2+fendetaP2;
  fetaP1P2:=fetaP2-fetaP1;

  fom:=compute_fom(data,f0om,finfom,fendom);
  feta:=compute_fom(data,f0eta,finfeta,fendeta);
  fom_diff:=compute_dF(data,fom);

  coefsom:=V!coefsom;
  coefseta:=V!coefseta;

  a1:= -fetaP1*fom_P1P2;
  a2:= coleman_integral(P1,P2, fom_diff*feta, data); 
  a3:= -fetaP1*(coefsom,IP1P2);
  a4:= (coefsom,coleman_integral_all_feta_omegaj(feta,P1,P2,data));
  a5:= -(coefseta,coleman_integral_all_feta_omegaj(fom,P1,P2,data)); 
  a6:= fomP2*(coefseta,IP1P2);
  W:=VectorSpace(Parent(P1`x),#basis^2);
  return a1+a2+a3+a4+a5+a6+(W!coeffs,doubP1P2);

end function;

  double_integral_omegah_Flomegai:=function(P1,P2,h,l,i, data:e:=1,IP1P2:=0,NIP1P2:=0);

  // Double integral of omega eta from P1 to P2.

  Q:=data`Q; p:=data`p; N:=data`N; Nmax:=data`Nmax; r:=data`r; W0:=data`W0; Winf:=data`Winf;
  G0:=data`G0; Ginf:=data`Ginf; red_list_fin:=data`red_list_fin; red_list_inf:=data`red_list_inf;
  basis:=data`basis; integrals:= data`integrals; quo_map:=data`quo_map;d:=Degree(Q);

  V:=VectorSpace(Parent(P1`x),#basis);
  //what gets passed into reduce_with_fs needs to be of a special form with the Rs and Qzs...
  omegah:=compute_omegaj(data,h);  
  val_omegah:=ordp_Qxzzinvd(Q,omegah,p);
  Fl:=compute_F(data,l);
  val_Fl:=ordp_Qxzzinvd(Q,Fl,p);
  omegai:=compute_omegaj(data,i);  
  val_omegai:=ordp_Qxzzinvd(Q,omegai,p);

  omegah:=omegah*p^(-val_omegah);
  omegai:=omegai*p^(-val_omegai);
  Fl:=Fl*p^(-val_Fl);

  N1:=Nmax-val_omegah-val_Fl-val_omegai; // multiplying out by denominators, so have to increase p-adic precision accordingly

  O,Ox,S,R:=getrings(p,N1);
  
  C:=[];
  for i:=1 to d+1 do
    C[i]:=Ox!(Coefficient(Q,i-1));
  end for;
  Q:=(R!C);

  omegah_R:=Qxzzinvd_to_R(omegah,Q,p,R);
  omegai_R:=Qxzzinvd_to_R(omegai,Q,p,R);
  Fl_R:=Qxzzinvd_to_R(Fl,Q,p,R);

  r_Ox:=Ox!r;
  lc:=LeadingCoefficient(r_Ox); 
  r_Ox:=r_Ox/lc;  

  omegah_R:=reduce_mod_Q(omegah_R,Q,r_Ox);
  Flomegai_R:=reduce_mod_Q(Fl_R*omegai_R, Q,r_Ox);

  Qxzzinvd:=Parent(omegai);
  omegah_Qxzzinvd:=p^(val_omegah)*R_to_Qxzzinvd(omegah_R,Q,Qxzzinvd); // putting the denominators back in
  Flomegai_Qxzzinvd:=p^(val_Fl+val_omegai)*R_to_Qxzzinvd(Flomegai_R, Q,Qxzzinvd); // putting the denominators back in

  coefsom,f0om,finfom,fendom:=reduce_with_fs(omegah_Qxzzinvd,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map); // TODO: handle precision here
  coefseta,f0eta,finfeta,fendeta:=reduce_with_fs(Flomegai_Qxzzinvd,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map); // TODO: handle precision here

  IP1P2,prec:=coleman_integrals_on_basis(P1,P2,data:e:=e);
  
  if NIP1P2 eq 0 then 
    doubP1P2:=Vector(double_integrals_on_basis(P1,P2,data:e:=e));
  end if;

  coeffs := Vector(TensorProduct(Matrix(Vector(coefsom)), Matrix(Vector(coefseta)))); //it seems this is the right order, not the other way around

  f0omP1,Nf0P1:=evalf0(f0om,P1,data);
  f0omP2,Nf0P2:=evalf0(f0om,P2,data);
  finfomP1,NfinfP1:=evalfinf(finfom,P1,data);
  finfomP2,NfinfP2:=evalfinf(finfom,P2,data);
  fendomP1,NfendP1:=evalfend(fendom,P1,data);
  fendomP2,NfendP2:=evalfend(fendom,P2,data);
  fomP1:=f0omP1+finfomP1+fendomP1;
  fomP2:=f0omP2+finfomP2+fendomP2;
  fom_P1P2:=fomP2-fomP1;
  NIdifP1P2:=Minimum([Nf0P1,Nf0P2,NfinfP1,NfinfP2,NfendP1,NfendP2]);

  f0etaP1,Nf0P1:=evalf0(f0eta,P1,data);
  f0etaP2,Nf0P2:=evalf0(f0eta,P2,data);
  finfetaP1,NfinfP1:=evalfinf(finfeta,P1,data);
  finfetaP2,NfinfP2:=evalfinf(finfeta,P2,data);
  fendetaP1,NfendP1:=evalfend(fendeta,P1,data);
  fendetaP2,NfendP2:=evalfend(fendeta,P2,data);
  fetaP1:=f0etaP1+finfetaP1+fendetaP1;
  fetaP2:=f0etaP2+finfetaP2+fendetaP2;
  fetaP1P2:=fetaP2-fetaP1;

  fom:=compute_fom(data,f0om,finfom,fendom);
  feta:=compute_fom(data,f0eta,finfeta,fendeta);
  fom_diff:=compute_dF(data,fom);
   
  coefsom:=V!coefsom;
  coefseta:=V!coefseta;

  a1:= -fetaP1*fom_P1P2;
  a2:= coleman_integral(P1,P2, fom_diff*feta, data); 
  a3:= -fetaP1*(coefsom,IP1P2);
  a4:= (coefsom,coleman_integral_all_feta_omegaj(feta,P1,P2,data));
  a5:= -(coefseta,coleman_integral_all_feta_omegaj(fom,P1,P2,data)); 
  a6:= fomP2*(coefseta,IP1P2);
  W:=VectorSpace(Parent(P1`x),#basis^2);
  return a1+a2+a3+a4+a5+a6+(W!coeffs,doubP1P2);

end function;

  double_integral_fidfk_omegaj:=function(P1,P2,i,k,j, data:e:=1,IP1P2:=0,NIP1P2:=0);

  // Double integral of omega eta from P1 to P2.

  Q:=data`Q; p:=data`p; N:=data`N; Nmax:=data`Nmax; r:=data`r; W0:=data`W0; Winf:=data`Winf;
  G0:=data`G0; Ginf:=data`Ginf; red_list_fin:=data`red_list_fin; red_list_inf:=data`red_list_inf;
  basis:=data`basis; integrals:= data`integrals; quo_map:=data`quo_map;d:=Degree(Q);

  V:=VectorSpace(Parent(P1`x),#basis);
  //what gets passed into reduce_with_fs needs to be of a special form with the Rs and Qzs...
  omegaj:=compute_omegaj(data,j);  
  val_omegaj:=ordp_Qxzzinvd(Q,omegaj,p);
  Fi:=compute_F(data,i);
  Fk:=compute_F(data,k);
  dFk:=compute_dF(data,Fk);
  val_dFk:=ordp_Qxzzinvd(Q,dFk,p);
  val_Fi:=ordp_Qxzzinvd(Q,Fi,p);

  omegaj:=omegaj*p^(-val_omegaj);
  dFk:=dFk*p^(-val_dFk);
  Fi:=Fi*p^(-val_Fi);
  N1:=Nmax-val_omegaj-val_dFk-val_Fi; // multiplying out by denominators, so have to increase p-adic precision accordingly

  O,Ox,S,R:=getrings(p,N1);
  
  C:=[];
  for i:=1 to d+1 do
    C[i]:=Ox!(Coefficient(Q,i-1));
  end for;
  Q:=(R!C);

  omegaj_R:=Qxzzinvd_to_R(omegaj,Q,p,R);
  dFk_R:=Qxzzinvd_to_R(dFk,Q,p,R);
  Fi_R:=Qxzzinvd_to_R(Fi,Q,p,R);

  r_Ox:=Ox!r;
  lc:=LeadingCoefficient(r_Ox); 
  r_Ox:=r_Ox/lc;               


  omegaj_R:=reduce_mod_Q(omegaj_R,Q,r_Ox);
  FidFk_R:=reduce_mod_Q(dFk_R*Fi_R, Q,r_Ox);

  Qxzzinvd:=Parent(omegaj);
  omegaj_Qxzzinvd:=p^(val_omegaj)*R_to_Qxzzinvd(omegaj_R,Q,Qxzzinvd); // putting the denominators back in
  FidFk_Qxzzinvd:=p^(val_dFk+val_Fi)*R_to_Qxzzinvd(FidFk_R, Q,Qxzzinvd); // putting the denominators back in

  coefsom,f0om,finfom,fendom:=reduce_with_fs(FidFk_Qxzzinvd,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map); // TODO: handle precision here
  coefseta,f0eta,finfeta,fendeta:=reduce_with_fs(omegaj_Qxzzinvd,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map); // TODO: handle precision here

  IP1P2,prec:=coleman_integrals_on_basis(P1,P2,data:e:=e);
  
  if NIP1P2 eq 0 then 
    doubP1P2:=Vector(double_integrals_on_basis(P1,P2,data:e:=e));
  end if;
  //print "doubP1P2 = ", doubP1P2;

  coeffs := Vector(TensorProduct(Matrix(Vector(coefsom)), Matrix(Vector(coefseta)))); // this is the right order, not the other way around

  //print "coeffs = ", coeffs;
  f0omP1,Nf0P1:=evalf0(f0om,P1,data);
  f0omP2,Nf0P2:=evalf0(f0om,P2,data);
  finfomP1,NfinfP1:=evalfinf(finfom,P1,data);
  finfomP2,NfinfP2:=evalfinf(finfom,P2,data);
  fendomP1,NfendP1:=evalfend(fendom,P1,data);
  fendomP2,NfendP2:=evalfend(fendom,P2,data);
  fomP1:=f0omP1+finfomP1+fendomP1;
  fomP2:=f0omP2+finfomP2+fendomP2;
  fom_P1P2:=fomP2-fomP1;
  NIdifP1P2:=Minimum([Nf0P1,Nf0P2,NfinfP1,NfinfP2,NfendP1,NfendP2]);

  f0etaP1,Nf0P1:=evalf0(f0eta,P1,data);
  f0etaP2,Nf0P2:=evalf0(f0eta,P2,data);
  finfetaP1,NfinfP1:=evalfinf(finfeta,P1,data);
  finfetaP2,NfinfP2:=evalfinf(finfeta,P2,data);
  fendetaP1,NfendP1:=evalfend(fendeta,P1,data);
  fendetaP2,NfendP2:=evalfend(fendeta,P2,data);
  fetaP1:=f0etaP1+finfetaP1+fendetaP1;
  fetaP2:=f0etaP2+finfetaP2+fendetaP2;
  fetaP1P2:=fetaP2-fetaP1;

  fom:=compute_fom(data,f0om,finfom,fendom);
  feta:=compute_fom(data,f0eta,finfeta,fendeta);
  fom_diff:=compute_dF(data,fom);
   
  coefsom:=V!coefsom;
  coefseta:=V!coefseta;


  a1:= -fetaP1*fom_P1P2;
  a2:= coleman_integral(P1,P2, fom_diff*feta, data); 
  a3:= -fetaP1*(coefsom,IP1P2);
  a4:= (coefsom,coleman_integral_all_feta_omegaj(feta,P1,P2,data));
  a5:= -(coefseta,coleman_integral_all_feta_omegaj(fom,P1,P2,data)); 
  a6:= fomP2*(coefseta,IP1P2);
  W:=VectorSpace(Parent(P1`x),#basis^2);
  return a1+a2+a3+a4+a5+a6+(W!coeffs,doubP1P2);
end function;

double_integral_omegaj_dfkfl:=function(P1,P2,j,k,l, data:e:=1,IP1P2:=0,NIP1P2:=0);

  // Double integral of omega eta from P1 to P2.

  Q:=data`Q; p:=data`p; N:=data`N; Nmax:=data`Nmax; r:=data`r; W0:=data`W0; Winf:=data`Winf;
  G0:=data`G0; Ginf:=data`Ginf; red_list_fin:=data`red_list_fin; red_list_inf:=data`red_list_inf;
  basis:=data`basis; integrals:= data`integrals; quo_map:=data`quo_map;d:=Degree(Q);

  V:=VectorSpace(Parent(P1`x),#basis);
  //what gets passed into reduce_with_fs needs to be of a special form with the Rs and Qzs...
  omegaj:=compute_omegaj(data,j);  
  val_omegaj:=ordp_Qxzzinvd(Q,omegaj,p);

  Fk:=compute_F(data,k);
  dFk:=compute_dF(data,Fk);
  val_dFk:=ordp_Qxzzinvd(Q,dFk,p);

  Fl:=compute_F(data,l);
  val_Fl:=ordp_Qxzzinvd(Q,Fl,p);


  omegaj:=omegaj*p^(-val_omegaj);
  dFk:=dFk*p^(-val_dFk);
  Fl:=Fl*p^(-val_Fl);
  N1:=Nmax-val_omegaj-val_dFk-val_Fl; // multiplying out by denominators, so have to increase p-adic precision accordingly

  O,Ox,S,R:=getrings(p,N1);
  
  C:=[];
  for i:=1 to d+1 do
    C[i]:=Ox!(Coefficient(Q,i-1));
  end for;
  Q:=(R!C);

  omegaj_R:=Qxzzinvd_to_R(omegaj,Q,p,R);
  dFk_R:=Qxzzinvd_to_R(dFk,Q,p,R);
  Fl_R:=Qxzzinvd_to_R(Fl,Q,p,R);

  r_Ox:=Ox!r;
  lc:=LeadingCoefficient(r_Ox); 
  r_Ox:=r_Ox/lc;               

  omegaj_R:=reduce_mod_Q(omegaj_R,Q,r_Ox);
  dFkFl_R:=reduce_mod_Q(dFk_R*Fl_R, Q,r_Ox);

  Qxzzinvd:=Parent(omegaj);
  omegaj_Qxzzinvd:=p^(val_omegaj)*R_to_Qxzzinvd(omegaj_R,Q,Qxzzinvd); // putting the denominators back in
  dFkFl_Qxzzinvd:=p^(val_dFk+val_Fl)*R_to_Qxzzinvd(dFkFl_R,Q,Qxzzinvd); // putting the denominators back in

  coefsom,f0om,finfom,fendom:=reduce_with_fs(omegaj_Qxzzinvd,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map); //  precision here
  coefseta,f0eta,finfeta,fendeta:=reduce_with_fs(dFkFl_Qxzzinvd,Q,p,N,Nmax,r,W0,Winf,G0,Ginf,red_list_fin,red_list_inf,basis,integrals,quo_map); // handle precision here

  IP1P2,prec:=coleman_integrals_on_basis(P1,P2,data:e:=e);
  
  if NIP1P2 eq 0 then 
    doubP1P2:=Vector(double_integrals_on_basis(P1,P2,data:e:=e));
  end if;

  coeffs := Vector(TensorProduct(Matrix(Vector(coefsom)), Matrix(Vector(coefseta)))); // this is the right order

  f0omP1,Nf0P1:=evalf0(f0om,P1,data);
  f0omP2,Nf0P2:=evalf0(f0om,P2,data);
  finfomP1,NfinfP1:=evalfinf(finfom,P1,data);
  finfomP2,NfinfP2:=evalfinf(finfom,P2,data);
  fendomP1,NfendP1:=evalfend(fendom,P1,data);
  fendomP2,NfendP2:=evalfend(fendom,P2,data);
  fomP1:=f0omP1+finfomP1+fendomP1;
  fomP2:=f0omP2+finfomP2+fendomP2;
  fom_P1P2:=fomP2-fomP1;
  NIdifP1P2:=Minimum([Nf0P1,Nf0P2,NfinfP1,NfinfP2,NfendP1,NfendP2]);

  f0etaP1,Nf0P1:=evalf0(f0eta,P1,data);
  f0etaP2,Nf0P2:=evalf0(f0eta,P2,data);
  finfetaP1,NfinfP1:=evalfinf(finfeta,P1,data);
  finfetaP2,NfinfP2:=evalfinf(finfeta,P2,data);
  fendetaP1,NfendP1:=evalfend(fendeta,P1,data);
  fendetaP2,NfendP2:=evalfend(fendeta,P2,data);
  fetaP1:=f0etaP1+finfetaP1+fendetaP1;
  fetaP2:=f0etaP2+finfetaP2+fendetaP2;
  fetaP1P2:=fetaP2-fetaP1;

  fom:=compute_fom(data,f0om,finfom,fendom);
  feta:=compute_fom(data,f0eta,finfeta,fendeta);
  fom_diff:=compute_dF(data,fom);
   
  coefsom:=V!coefsom;
  coefseta:=V!coefseta;

  a1:= -fetaP1*fom_P1P2;
  a2:= coleman_integral(P1,P2, fom_diff*feta, data); 
  a3:= -fetaP1*(coefsom,IP1P2);
  a4:= (coefsom,coleman_integral_all_feta_omegaj(feta,P1,P2,data));
  a5:= -(coefseta,coleman_integral_all_feta_omegaj(fom,P1,P2,data)); 
  a6:= fomP2*(coefseta,IP1P2);
  W:=VectorSpace(Parent(P1`x),#basis^2);

  return a1+a2+a3+a4+a5+a6+(W!coeffs,doubP1P2);

end function;


//////////////////////////////////////////////////////
function double_integral_all_omegai_omegaj(P1,P2,data:e:=1);
//Note that the output values are not precisely the double coleman integrals \int_{P1}^{P2} omega_i omega_j*Fk,
//but rather the doulbe integrals between P1 to P2 of the projection of omega_i omega_j*Fk on H^1(X).
Q:=data`Q; basis:=data`basis; x1:=P1`x; p:=data`p; N:=data`N; d:=Degree(Q); K:=Parent(x1); 
V:=VectorSpace(K,#basis);
allomegai_omegaj:=[];
for i in [1..#basis] do
   omegai:=compute_omegaj(data,i);  
   for j in [1..#basis] do
       omegaj:=compute_omegaj(data,j);  
       allomegai_omegaj:= Append(allomegai_omegaj, double_integral(P1,P2,omegai,omegaj, data));
    end for;
end for;
V:=VectorSpace(K,(#basis)^2);
return V!allomegai_omegaj;
end function;
//////////////////////////////////////////////////////


//////////////////////////////////////////////////////
function double_integral_all_omegai_omegajFk(P1,P2,data:e:=1);
//Note that the output values are not precisely the double coleman integrals \int_{P1}^{P2} omega_i omega_j*Fk,
//but rather the doulbe integrals between P1 to P2 of the projection of omega_i omega_j*Fk on H^1(X).
Q:=data`Q; basis:=data`basis; x1:=P1`x; p:=data`p; N:=data`N; d:=Degree(Q); K:=Parent(x1); 
V:=VectorSpace(K,#basis);
allomegai_omegajFk:=[];
for i in [1..#basis] do
   omegai:=compute_omegaj(data,i);  
   for j in [1..#basis] do
       omegaj:=compute_omegaj(data,j);  
       for k in [1..#basis] do
           Fk:=compute_F(data,k);
           omega_jFk := omegaj*Fk;
           allomegai_omegajFk:= Append(allomegai_omegajFk, double_integral(P1,P2,omegai,omega_jFk, data));
       end for;
    end for;
end for;
V:=VectorSpace(K,(#basis)^3);
return V!allomegai_omegajFk;
end function;
//////////////////////////////////////////////////////




//////////////////////////////////////////////////////
function double_integral_all_Fiomegaj_omegak(P1,P2,data:e:=1);
//Note that the output values are not precisely the double coleman integrals \int_{P1}^{P2} omega_i omega_j*Fk,
//but rather the doulbe integrals between P1 to P2 of the projection of omega_i omega_j*Fk on H^1(X).
Q:=data`Q; basis:=data`basis; x1:=P1`x; p:=data`p; N:=data`N; d:=Degree(Q); K:=Parent(x1); 
V:=VectorSpace(K,#basis);
allFiomegaj_omegak:=[];
for i in [1..#basis] do
   Fi:=compute_F(data,i);
   for j in [1..#basis] do
       omegaj:=compute_omegaj(data,j); 
       Fiomegaj:=Fi*omegaj; 
       for k in [1..#basis] do
           omegak:=compute_omegaj(data,k);
           allFiomegaj_omegak:= Append(allFiomegaj_omegak, double_integral(P1,P2,Fiomegaj,omegak, data));
       end for;
    end for;
end for;
V:=VectorSpace(K,(#basis)^3);
return V!allFiomegaj_omegak;
end function;
//////////////////////////////////////////////////////



function double_integral_all_FidFk_omegaj(P1,P2,data:e:=1);
//this should be written with the same bracketing as the Sage code
//print "checking bracketing";
Q:=data`Q; basis:=data`basis; x1:=P1`x; p:=data`p; N:=data`N; d:=Degree(Q); K:=Parent(x1); 
V:=VectorSpace(K,#basis);
all_FidFk_omegaj:=[];
for i in [1..#basis] do
  Fi:=compute_F(data,i);
  for k in [1..#basis] do
      Fk:=compute_F(data,k);
      dFk:=compute_dF(data,Fk);
      A:=[];
      for j in [1..#basis] do
         omegaj:=compute_omegaj(data,j);
         A:=Append(A,double_integral(P1,P2,Fi*dFk,omegaj,data));
      end for;
      all_FidFk_omegaj:=Append(all_FidFk_omegaj,A);
end for;
end for;
V:=VectorSpace(K,#basis);
return all_FidFk_omegaj;
//return V!all_dFi_omegaj;
end function;


//////////////////////////////////////////////////////
function double_integral_all_dFi_omegaj(P1,P2,data:e:=1);
//this should be written with the same bracketing as the Sage code
Q:=data`Q; basis:=data`basis; x1:=P1`x; p:=data`p; N:=data`N; d:=Degree(Q); K:=Parent(x1); 
V:=VectorSpace(K,#basis);
all_dFi_omegaj:=[];
for i in [1..#basis] do
  A:=[];
  Fi:=compute_F(data,i);
  dFi:=compute_dF(data,Fi);
  for j in [1..#basis] do
    //print [i,j];
    omegaj:=compute_omegaj(data,j);
    A:=Append(A,double_integral(P1,P2,dFi,omegaj,data));
  end for;
  all_dFi_omegaj:=Append(all_dFi_omegaj,A);
end for;
V:=VectorSpace(K,#basis);
return all_dFi_omegaj;
//return V!all_dFi_omegaj;
end function;
//////////////////////////////////////////////////////



//////////////////////////////////////////////////////
function triple_integrals_on_basis(P1,P2,data:e:=1)

//this returns the triple integrals between P1 and P2: 
// \int_{P1}^{P2} \omega_i \omega_j \omega_k

F:=data`F; Q:=data`Q; basis:=data`basis; x1:=P1`x; f0list:=data`f0list; finflist:=data`finflist; fendlist:=data`fendlist; p:=data`p; N:=data`N; delta:=data`delta;
d:=Degree(Q); K:=Parent(x1); 

dim:=(#basis)^3;
rowdim:=#basis;

// First make sure that if P1 or P2 is bad, then it is very bad

  if is_bad(P1,data) and not is_very_bad(P1,data) then
    S1:=find_bad_point_in_disk(P1,data);
    _,index:=local_data(S1,data);
    data:=update_minpolys(data,S1`inf,index);
    xt,bt,index:=local_coord(S1,tadicprec(data,e),data); //so we work from S1 as the very bad point in the disk of P1
    S1`xt:=xt;
    S1`bt:=bt;
    S1`index:=index;
    IsingS1P1,NsingIS1P1:=tiny_integrals_on_basis(S1,P1,data);
    IsingS1P2,NsingIS1P2:=coleman_integrals_on_basis(S1,P2,data);
    IdoubS1P1,NdoubIS1P1:=tiny_double_integrals_on_basis(S1,P1,data:prec:=tadicprec(data,e));
    IdoubS1P2,NdoubIS1P2:=double_integrals_on_basis(S1,P2,data:e:=e);
    ItripS1P1,NtripIS1P1:=tiny_triple_integrals_on_basis(S1,P1,data:prec:=tadicprec(data,e));
    ItripS1P2,NtripIS1P2:=$$(S1,P2,data:e:=e);

    trip:=[];
    for i in [1..#basis] do
        for j in [1..#basis] do
          for k in [1..#basis] do
             ij  := (i-1)*(#basis) + j;
             kj  := (k-1)*(#basis) + j;
             ijk := (i-1)*(#basis)^2 + (j-1)*(#basis) + k;
             kji := (k-1)*(#basis)^2 + (j-1)*(#basis) + i;
             trip:=Append(trip, -ItripS1P1[kji] + IsingS1P2[i]*IdoubS1P1[kj] - IdoubS1P2[ij]*IsingS1P1[k] + ItripS1P2[ijk]);
          end for;
        end for;
    end for;
    NIP1P2:=Ceiling(Minimum([NdoubIS1P1,NdoubIS1P2,NsingIS1P1,NsingIS1P2])); //adjust this
    return trip,NIP1P2;
  end if;

  if is_bad(P2,data) and not is_very_bad(P2,data) then
    S2:=find_bad_point_in_disk(P2,data);
    _,index:=local_data(S2,data);
    data:=update_minpolys(data,S2`inf,index);
    xt,bt,index:=local_coord(S2,tadicprec(data,e),data);
    S2`xt:=xt;
    S2`bt:=bt;
    S2`index:=index;
    IsingP1S2,NsingIP1S2:=coleman_integrals_on_basis(P1,S2,data);
    IsingP2S2,NsingIP2S2:=tiny_integrals_on_basis(P2,S2,data);
    IdoubP1S2,NdoubIP1S2:=double_integrals_on_basis(P1,S2,data:e:=e);
    IdoubP2S2,NdoubIP2S2:=tiny_double_integrals_on_basis(P2,S2,data:prec:=tadicprec(data,e));
    ItripP1S2,NtripIP1S2:=$$(P1,S2,data);
    ItripP2S2,NtripIP2S2:=tiny_triple_integrals_on_basis(P2,S2,data:prec:=tadicprec(data,e));
    trip:=[];
    for i in [1..#basis] do
        for j in [1..#basis] do
          for k in [1..#basis] do
            ji := (j-1)*(#basis) + i;
            jk := (j-1)*(#basis) + k;
            ijk:= (i-1)*(#basis)^2 + (j-1)*(#basis) + k;
            kji:= (k-1)*(#basis)^2 + (j-1)*(#basis) + i;
            trip:= Append(trip, ItripP1S2[ijk] - IsingP2S2[i]*IdoubP1S2[jk] + IdoubP2S2[ji]*IsingP1S2[k] - ItripP2S2[kji]);
          end for;
        end for;
    end for;
    NIP1P2:=Ceiling(Minimum([NdoubIP1S2,NdoubIP2S2,NsingIP1S2,NsingIP2S2]));
    return trip,NIP1P2; // this
  end if;

  // If P1,P2 is bad (hence very bad), use a near boundary point.

  _,index:=local_data(P1,data);
  data:=update_minpolys(data,P1`inf,index);
  _,index:=local_data(P2,data);
  data:=update_minpolys(data,P2`inf,index);

  if is_bad(P1,data) then
    xt,bt,index:=local_coord(P1,tadicprec(data,e),data);
    P1`xt:=xt;       
    P1`bt:=bt;       
    P1`index:=index; 
    Qp:=Parent(P1`x);
    Qpa<a>:=PolynomialRing(Qp);
    K<a>:=TotallyRamifiedExtension(Qp,a^e-p);
    format:=recformat<x,b,inf,xt,bt,index>;
    S1:=rec<format|>;                                                    
    S1`inf:=P1`inf;
    S1`x:=Evaluate(xt,a);
    S1`b:=[Evaluate(bt[i],a):i in [1..d]];
  else
    xt,bt,index:=local_coord(P1,tadicprec(data,1),data);
    P1`xt:=xt;       
    P1`bt:=bt;       
    P1`index:=index; 
    S1:=P1;
  end if;

  if is_bad(P2,data) then
    xt,bt,index:=local_coord(P2,tadicprec(data,e),data);
    P2`xt:=xt;       
    P2`bt:=bt;       
    P2`index:=index; 
    if not is_bad(P1,data) then
      Qp:=Parent(P2`x);
      Qpa<a>:=PolynomialRing(Qp);
      K<a>:=TotallyRamifiedExtension(Qp,a^e-p);
    end if;
    format:=recformat<x,b,inf,xt,bt,index>;
    S2:=rec<format|>;                                                    
    S2`inf:=P2`inf;
    S2`x:=Evaluate(xt,a);
    S2`b:=[Evaluate(bt[i],a):i in [1..d]];
  else
    xt,bt,index:=local_coord(P2,tadicprec(data,1),data);
    P2`xt:=xt;       
    P2`bt:=bt;       
    P2`index:=index; 
    S2:=P2;
  end if;

  // Split up the integral and compute the single ones and the tiny doubles and tiny triples

  singP1toS1,NsingP1toS1:=tiny_integrals_on_basis(P1,S1,data);
  singP2toS2,NsingP2toS2:=tiny_integrals_on_basis(P2,S2,data);
  singS1toP2,NsingS1toP2:=coleman_integrals_on_basis(S1,P2,data);
  singS1toS2,NsingS1toS2:=coleman_integrals_on_basis(S1,S2,data);
  
  doubP1toS1,NdoubP1toS1:=tiny_double_integrals_on_basis(P1,S1,data);
  doubS2toP2,NdoubS2toP2:=tiny_double_integrals_on_basis(S2,P2,data);

  tripP1toS1,NtripP1toS1:=tiny_triple_integrals_on_basis(P1,S1,data);
  tripS2toP2,NtripS2toP2:=tiny_triple_integrals_on_basis(S2,P2,data);


  //the main part of the algorithm is computing the triple integral from S1 to S2, which we do now

  FS1:=frobenius_pt(S1,data);
  FS2:=frobenius_pt(S2,data);

  if is_bad(S1,data) and not is_very_bad(S1,data) then
    tinyP1toFS1,NP1toFS1:=tiny_integrals_on_basis(P1,FS1,data);
    tinyS1toFS1 := tinyP1toFS1 - singP1toS1;
    NS1toFS1:=Minimum([NP1toFS1,NsingP1toS1]);
  else 
    tinyS1toFS1,NS1toFS1:=tiny_integrals_on_basis(S1,FS1,data:P:=P1); 
  end if;
  if is_bad(S2,data) and not is_very_bad(S2,data) then
    tinyP2toFS2,NP2toFS2:=tiny_integrals_on_basis(P2,FS2,data);
    tinyS2toFS2 := tinyP2toFS2 - singP2toS2;
    NS2toFS2:=Minimum([NP2toFS2,NsingP2toS2]);
  else
      tinyS2toFS2,NS2toFS2:=tiny_integrals_on_basis(S2,FS2,data:P:=P2); 
  end if;
  NIP1P2:=Minimum([NsingP1toS1,NsingP2toS2,NS1toFS1,NS2toFS2]);  

  singFS1toFS2 := -tinyS1toFS1 + singS1toS2 + tinyS2toFS2;
  singFS1toS2 := -tinyS1toFS1 + singS1toS2;

  doubFS1toS1, NdoubFS1toS1:=tiny_double_integrals_on_basis(FS1,S1,data);
  doubFS2toS2, NdoubFS2toS2:=tiny_double_integrals_on_basis(FS2,S2,data);

  doubS1toS2, Ndoub := double_integrals_on_basis(S1,S2,data);

  doubFS1toFS2 := [];
  for i in [1..rowdim] do
    for j in [1..rowdim] do
      ij:=rowdim*(i-1)+j;
      ji:=rowdim*(j-1)+i;
      doubFS1toFS2:=Append(doubFS1toFS2, doubFS1toS1[ij] + doubS1toS2[ij] + doubFS2toS2[ji] -tinyS1toFS1[j]*singS1toS2[i] + singFS1toS2[j]*tinyS2toFS2[i]);
  end for;
  end for;

  doubFS1toFS2 := Vector(doubFS1toFS2);
  tripFS1toS1, NtripFS1toS1:=tiny_triple_integrals_on_basis(FS1,S1,data);
  tripFS2toS2, NtripFS2toS2:=tiny_triple_integrals_on_basis(FS2,S2,data);
 
  // Evaluate all functions at S1, S2

  fS1:=[];
  fS2:=[];
  for i:=1 to rowdim do
    f0iS1,Nf0iS1:=evalf0(f0list[i],S1,data);
    f0iS2,Nf0iS2:=evalf0(f0list[i],S2,data);
    finfiS1,NfinfiS1:=evalfinf(finflist[i],S1,data);
    finfiS2,NfinfiS2:=evalfinf(finflist[i],S2,data);
    fendiS1,NfendiS1:=evalfend(fendlist[i],S1,data);
    fendiS2,NfendiS2:=evalfend(fendlist[i],S2,data);
    NIP1P2:=Minimum([NIP1P2,Nf0iS1,Nf0iS2,NfinfiS1,NfinfiS2,NfendiS1,NfendiS2]);
    fS1[i]:=(K!f0iS1) + (K!finfiS1) + (K!fendiS1);
    fS2[i]:=(K!f0iS2) + (K!finfiS2) + (K!fendiS2);
  end for; 

  V:=VectorSpace(K,rowdim);
  Arows:=Rows(F);

  //double integrals of dFk omegaj
  doubledfkxpow :=[];
  for k in [1..rowdim] do
     W:=[];
     Fk:=compute_F(data,k);
     dFk:=compute_dF(data,Fk);
     for j in [1..rowdim] do
        omegaj:=compute_omegaj(data,j);
        W:=Append(W, double_integral(S1, S2, dFk, omegaj, data));
     end for;
     doubledfkxpow:=Append(doubledfkxpow, W);
  end for;

  //single integrals of Fi dFj
  intfidfk_all:=coleman_integral_all_Fi_dFj(S1,S2,data:e:=1);
  intdfifk_all:=[];
  for i in [1..rowdim] do
      for j in [1..rowdim] do
            intdfifk_all:=Append(intdfifk_all, intfidfk_all[(j-1)*rowdim + i]);
      end for;
  end for;

  //single integrals of Fi omegaj
  intxpowldxfk_all:=coleman_integral_all_Fi_omegaj(S1,S2,data:e:=1);
  intxpowldxfk:= [];
  for i in [1..rowdim] do
    W:=[];
    for j in [1..rowdim] do
    W:=Append(W, intxpowldxfk_all[rowdim*(i-1)+j]);
    end for;
    intxpowldxfk:=Append(intxpowldxfk,W);
  end for;

  //single integrals of FiFjomegak
  intxpowjdxflfi_all:=coleman_integral_all_Fi_Fj_omegak(S1,S2,data:e:=1);
  intxpowjdxflfi:=[];
  for i in [1..rowdim] do
    for l in [1..rowdim] do
        W:=[];
        for j in [1..rowdim] do
            W:=Append(W, intxpowjdxflfi_all[rowdim^2*(i-1) + rowdim*(l-1) + j]);
        end for;
        intxpowjdxflfi:=Append(intxpowjdxflfi, W);
    end for;
  end for;

  //single integrals of Fi dFj Fk
  intfidfkfl_all:= coleman_integral_all_Fi_dFj_Fk(S1,S2,data:e:=1);

  //double integrlas of Fkomegaj omegah
  doublexpowfkxpow:=[];
  for k in [1..rowdim] do
   Fk:=compute_F(data,k);
   W:= [];
   W1:=[];
    for j in [1..rowdim] do
        omegaj:=compute_omegaj(data,j);
        for h in [1..rowdim] do
          omegah:=compute_omegaj(data,h);
          W:=Append(W, double_integral_Fkomegaj_omegah(S1, S2, k,j,h,data));
        end for;
    end for;
    doublexpowfkxpow:=Append(doublexpowfkxpow, W);
  end for;

  //double integrals of omegah Fl*omegai
  doublexpowxpowfk2:=[];
  for l in [1..rowdim] do
    W:= [];          
    for h in [1..rowdim] do
        for i in [1..rowdim] do
          W:=Append(W, double_integral_omegah_Flomegai(S1, S2, h,l,i,data));
        end for;
    end for;
    doublexpowxpowfk2:=Append(doublexpowxpowfk2, W);
  end for;

  //fixed splitting it up into j,k,l, 03/10/22
  doublexpowdfkfl:=[]; 
  for k in [1..rowdim] do
    for l in [1..rowdim] do
        W:=[];
        for j in [1..rowdim] do
             W:=Append(W,double_integral_omegaj_dfkfl(S1,S2,j,k,l,data));
        end for;
        doublexpowdfkfl:=Append(doublexpowdfkfl, W);
    end for;
  end for;

//had to change pole order here
  doubledfkflxpow:=[];
  //double integrals of FidFk, omegaj
  for i in [1..rowdim] do
    for k in [1..rowdim] do
        W:=[];
        for j in [1..rowdim] do
            W:=Append(W, double_integral_fidfk_omegaj(S1,S2,i,k,j,data));
        end for;
        doubledfkflxpow:=Append(doubledfkflxpow,W);
    end for;
  end for;

  cons:=[];
  fix:=[];
  F2:=TensorProduct(F,F);
  Atens:=Rows(F2);
  W:=VectorSpace(K, #basis^2);
  doubS1toS2:=W!doubS1toS2;
  for i in [1..rowdim] do
    Ai:=V!Arows[i];
    fiS1:=fS1[i];
    fiS2:=fS2[i];    
    sing_basisfi:=  Vector(intxpowldxfk[i]);
    for k in [1..rowdim] do
      Ak:=V!Arows[k];
      ik := rowdim*(i-1) + k;
      ki := rowdim*(k-1) + i;
      fkS1:=fS1[k];
      fkS2:=fS2[k];
      sing_basisfk := Vector(intxpowldxfk[k]);
      for l in [1..rowdim] do
         sing_basisfl:=Vector(intxpowldxfk[l]);
         Al := V!Arows[l];
         flS1:= fS1[l];
         ikl := rowdim^2*(i-1) + rowdim*(k-1) + l;
         lki := rowdim^2*(l-1) + rowdim*(k-1) + i;
         li := rowdim*(l-1) + i;
         il := rowdim*(i-1) + l;
         kl := rowdim*(k-1) + l;
         lk := rowdim*(l-1) + k;

         AlAi := W!Vector(Atens[li]); 
         AkAl := W!Vector(Atens[kl]);
         AiAk := W!Vector(Atens[ik]); 
         AiAl := W!Vector(Atens[il]);

         t10 := - flS1*intdfifk_all[ik]-flS1*(Ai,sing_basisfk)+flS1*(Ak,sing_basisfi);
         t9 := fiS2*intdfifk_all[kl] + fiS2*(Ak,sing_basisfl) + fiS2*(Al,Vector(doubledfkxpow[k]));
         t8 := (Ai,Vector(doublexpowdfkfl[kl])) + (AiAk,Vector(doublexpowxpowfk2[l])) + -(AiAl,Vector(doublexpowxpowfk2[k]));

         t11:=-(Al,Vector(doubledfkflxpow[ik])) +(Al,singS1toS2)*(Ai,sing_basisfk)-(AlAi,Vector(doublexpowxpowfk2[k]))-(AkAl,Vector(doublexpowfkxpow[i]));

         t1:=  - intfidfkfl_all[ikl] +flS1*fkS1*(fiS2-fiS1);
         t2:= flS1*fkS1*(Ai,singS1toS2);
         t3:= -(Ak,Vector(intxpowjdxflfi[li]))-flS1*fiS2*(Ak,singS1toS2); 
         t4:=  -flS1*(AiAk,doubS1toS2); 
         t5:= 0;
         term61:= (Al,singS1toS2)*(-fkS1*(Ai,singS1toS2)) ;   
         term62:= -fkS1*(AlAi,doubS1toS2) ;  
         term63:= -fkS1*(AiAl,doubS1toS2) ;  
         t6:= term61-term62-term63;  
         t7:=fiS2*(AkAl,doubS1toS2);

         cons:=Append(cons, t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11);

         //fix is the correction factors using "corr" FS1 and S1, FS2, S2 etc 
         fix:= Append(fix, -tripFS1toS1[lki] + singFS1toFS2[i]*doubFS1toS1[lk] + doubFS1toFS2[ik]*tinyS1toFS1[l]+
                -tinyS2toFS2[i]*doubFS1toS1[lk] - tinyS2toFS2[i]*singFS1toFS2[k]*tinyS1toFS1[l] +
                -tinyS2toFS2[i]*doubFS1toFS2[kl] + doubFS2toS2[ik]*tinyS1toFS1[l] + 
                doubFS2toS2[ik]*singFS1toFS2[l] + tripFS2toS2[ikl]);
      end for;   
  end for;  
  end for;    
  cons:=Vector(cons);
  fix:=Vector(fix);

  constantvec:=cons+fix;
  
  F3:=TensorProduct(F2,F);
  F3:=ChangeRing(F3,K);
  mat:=(IdentityMatrix(K,dim)-Transpose(F3))^-1;
  valdet:=Valuation(Determinant(mat));//,p);
  Nmat:=N-valdet-delta;
  tripS1toS2:= constantvec*mat;

  tripP1toP2:=[];
  for i in [1..rowdim] do
    for k in [1..rowdim] do
        for l in [1..rowdim] do
          ikl := rowdim^2*(i-1) + rowdim*(k-1) + l;
          ik := rowdim*(i-1) + k;
          kl := rowdim*(k-1) + l;
          tripP1toP2:=Append(tripP1toP2, tripP1toS1[ikl] + singS1toS2[i]*doubP1toS1[kl] + doubS1toS2[ik]*singP1toS1[l] + 
                tripS1toS2[ikl] -singP2toS2[i]*doubP1toS1[kl] - singP2toS2[i]*singS1toS2[k]*singP1toS1[l]+
                -singP2toS2[i]*doubS1toS2[kl] + doubS2toP2[ik]*singP1toS1[l] + doubS2toP2[ik]*singS1toS2[l] + tripS2toP2[ikl]);
        end for;
    end for;
  end for;
  NIP1P2:=Ceiling(NIP1P2);
  return tripP1toP2,NIP1P2;

end function;

////////////////////////////////////////////////////////////

tiny_integrals_on_basis_to_z:=function(P,data:prec:=0);

  // Compute tiny integrals of basis elements from P to an
  // arbitrary point in its residue disk as a power series
  // in the local parameter there. The series expansions xt
  // and bt of the coordinates on the curve in terms of this 
  // local parameter are also returned.

  x0:=P`x; b:=P`b; Q:=data`Q; p:=data`p; N:=data`N; basis:=data`basis; r:=data`r; W0:=data`W0; Winf:=data`Winf;
  d:=Degree(Q); lc_r:=LeadingCoefficient(r); W:=Winf*W0^(-1); K:=Parent(x0);

  if is_bad(P,data) and not is_very_bad(P,data) then // on a bad disk P needs to be very bad
    P1:=find_bad_point_in_disk(P,data);  
  else
    P1:=P;
  end if;
  x1:=P1`x;

  IPP1,NIPP1:=tiny_integrals_on_basis(P,P1,data:prec:=prec);

  if prec eq 0 then // no t-adic precision specified
    prec:=tadicprec(data,1);
  end if;

  Kt<t>:=LaurentSeriesRing(K,prec);
  OK:=RingOfIntegers(K);
  OKt:=LaurentSeriesRing(OK,prec);

  xt,bt,index:=local_coord(P1,prec,data);

  xtold:=xt;
  btold:=bt;

  Qt<t>:=LaurentSeriesRing(RationalField(),prec);
  xt:=Qt!xt;
  btnew:=[Qt|];
  for i:=1 to d do
    btnew[i]:=Qt!bt[i];
  end for;
  bt:=Vector(btnew);

  if P1`inf then
    xt:=1/xt;
    xt:=Qt!Kt!xt; 
    Winv:=W0*Winf^(-1);          
    bt:=bt*Transpose(Evaluate(Winv,xt));
    for i:=1 to d do
      bt[i]:=Qt!(Kt!bt[i]);
    end for; 
  end if;

  if P1`inf or not is_bad(P1,data) then 
    denom:=Qt!Kt!(1/Evaluate(r,xt));
  else
    Qp:=pAdicField(p,N);
    Qpx:=PolynomialRing(Qp);
    rQp:=Qpx!r;
    zero:=HenselLift(rQp,x1);
    sQp:=rQp div (Qpx.1-zero);
    denom:=Qt!Kt!((Qt!OKt!(xt-Coefficient(xt,0)))^(-1)*(Qt!Kt!(1/Evaluate(sQp,xt))));
  end if;

  derxt:=Qt!Kt!Derivative(xt); 
  diffs:=[];
  for i:=1 to #basis do
    basisxt:=Evaluate(basis[i],xt);
    for j:=1 to d do
      basisxt[1][j]:=Qt!Kt!basisxt[1][j];
    end for;
    diffs[i]:=InnerProduct(Vector(basisxt*derxt*lc_r*denom),bt);
    diffs[i]:=Qt!Kt!diffs[i];
    if Coefficient(diffs[i],-1) ne 0 then
      diffs[i]:=diffs[i]-Coefficient(diffs[i],-1)*t^(-1); // deal with logs later, important for double integrals
    end if;
  end for;

  indefints:=[];
  for i:=1 to #basis do
    indefints := Append(indefints, Integral(diffs[i]));
  end for;

  xt:=xtold;
  bt:=Vector(btold);

  return Vector(indefints)+IPP1,xt,bt,NIPP1;

end function;


tiny_double_integrals_on_basis_to_z:=function(P,data:prec:=0, all:=false);

    //Returns all tiny double integrals on basis unless b is infinity:
    //then just returns \int w0 w0, \int w0 \int w_{2g-1}... \int w_{g-1} w_{2g-1}

  x0:=P`x; b:=P`b; Q:=data`Q; p:=data`p; N:=data`N; basis:=data`basis; r:=data`r; W0:=data`W0; Winf:=data`Winf;
  d:=Degree(Q); lc_r:=LeadingCoefficient(r); W:=Winf*W0^(-1); K:=Parent(x0);
  g:=data`g;

  if is_bad(P,data) and not is_very_bad(P,data) then // on a bad disk P needs to be very bad
    P1:=find_bad_point_in_disk(P,data);  
  else
    P1:=P;
  end if;
  x1:=P1`x;

  IPP1,NIPP1:=tiny_integrals_on_basis(P,P1,data:prec:=prec);

  if prec eq 0 then // no t-adic precision specified
    prec:=tadicprec(data,1);
  end if;

  Kt<t>:=LaurentSeriesRing(K,prec);
  OK:=RingOfIntegers(K);
  OKt:=LaurentSeriesRing(OK,prec);

  xt,bt,index:=local_coord(P1,prec,data);

  xtold:=xt;
  btold:=bt;

  Qt<t>:=LaurentSeriesRing(RationalField(),prec);
  xt:=Qt!xt;
  btnew:=[Qt|];
  for i:=1 to d do
    btnew[i]:=Qt!bt[i];
  end for;
  bt:=Vector(btnew);

  if P1`inf then
    xt:=1/xt;
    xt:=Qt!Kt!xt; 
    Winv:=W0*Winf^(-1);          
    bt:=bt*Transpose(Evaluate(Winv,xt));
    for i:=1 to d do
      bt[i]:=Qt!(Kt!bt[i]);
    end for; 
  end if;

  if P1`inf or not is_bad(P1,data) then 
    denom:=Qt!Kt!(1/Evaluate(r,xt));
  else
    Qp:=pAdicField(p,N);
    Qpx:=PolynomialRing(Qp);
    rQp:=Qpx!r;
    zero:=HenselLift(rQp,x1);
    sQp:=rQp div (Qpx.1-zero);
    denom:=Qt!Kt!((Qt!OKt!(xt-Coefficient(xt,0)))^(-1)*(Qt!Kt!(1/Evaluate(sQp,xt))));
  end if;

  derxt:=Qt!Kt!Derivative(xt); 
  diffs:=[];
  for i:=1 to #basis do
    basisxt:=Evaluate(basis[i],xt);
    for j:=1 to d do
      basisxt[1][j]:=Qt!Kt!basisxt[1][j];
    end for;
    diffs[i]:=InnerProduct(Vector(basisxt*derxt*lc_r*denom),bt);
    diffs[i]:=Qt!Kt!diffs[i];
    if Coefficient(diffs[i],-1) ne 0 then
      diffs[i]:=diffs[i]-Coefficient(diffs[i],-1)*t^(-1); // deal with logs later, important for double integrals
    end if;
  end for;

  indefints:=[];
  for i:=1 to #basis do
    indefints := Append(indefints, Integral(diffs[i]));
  end for;
  doubles:=[];
  for i in [1..2*g] do 
    for j in [1..2*g] do
        doubles := Append(doubles, (Integral(diffs[i]*indefints[j])));
    end for;
  end for;

  xt:=xtold;
  bt:=Vector(btold);
  
  if all eq true then
     return Vector(indefints)+IPP1, Vector(doubles)+IPP1,xt,bt,NIPP1;
  else
    return Vector(doubles)+IPP1,xt,bt,NIPP1;
  end if;

end function;


tiny_triple_integrals_on_basis_to_z:=function(P,data:prec:=0,all:=false);

   // Returns all tiny triple integrals on basis unless b is infinity:
   // then just returns \int w0 w0 w0, ... \int w0 w0 w1 ... \int w_{g-1} w_{g-1} w_{2g-1}

   // TODO: all (2g)^3 integrals at infinity; issues integrating with t^-1 terms

  x0:=P`x; b:=P`b; Q:=data`Q; p:=data`p; N:=data`N; basis:=data`basis; r:=data`r; W0:=data`W0; Winf:=data`Winf;
  d:=Degree(Q); lc_r:=LeadingCoefficient(r); W:=Winf*W0^(-1); K:=Parent(x0);
  g:=data`g;

  if is_bad(P,data) and not is_very_bad(P,data) then // on a bad disk P needs to be very bad
    print "we will need to correct this -------------- TO DO!";
    P1:=find_bad_point_in_disk(P,data);  
  else
    P1:=P;
  end if;
  x1:=P1`x;

  IPP1,NIPP1:=tiny_integrals_on_basis(P,P1,data:prec:=prec);

  if prec eq 0 then // no t-adic precision specified
    prec:=tadicprec(data,1);
  end if;

  Kt<t>:=LaurentSeriesRing(K,prec);
  OK:=RingOfIntegers(K);
  OKt:=LaurentSeriesRing(OK,prec);

  xt,bt,index:=local_coord(P1,prec,data);

  xtold:=xt;
  btold:=bt;

  Qt<t>:=LaurentSeriesRing(RationalField(),prec);
  xt:=Qt!xt;
  btnew:=[Qt|];
  for i:=1 to d do
    btnew[i]:=Qt!bt[i];
  end for;
  bt:=Vector(btnew);

  if P1`inf then
    xt:=1/xt;
    xt:=Qt!Kt!xt; 
    Winv:=W0*Winf^(-1);          
    bt:=bt*Transpose(Evaluate(Winv,xt));
    for i:=1 to d do
      bt[i]:=Qt!(Kt!bt[i]);
    end for; 
  end if;

  if P1`inf or not is_bad(P1,data) then 
    denom:=Qt!Kt!(1/Evaluate(r,xt));
  else
    Qp:=pAdicField(p,N);
    Qpx:=PolynomialRing(Qp);
    rQp:=Qpx!r;
    zero:=HenselLift(rQp,x1);
    sQp:=rQp div (Qpx.1-zero);
    denom:=Qt!Kt!((Qt!OKt!(xt-Coefficient(xt,0)))^(-1)*(Qt!Kt!(1/Evaluate(sQp,xt))));
  end if;

  derxt:=Qt!Kt!Derivative(xt); 
  diffs:=[];
  for i:=1 to #basis do
    basisxt:=Evaluate(basis[i],xt);
    for j:=1 to d do
      basisxt[1][j]:=Qt!Kt!basisxt[1][j];
    end for;
    diffs[i]:=InnerProduct(Vector(basisxt*derxt*lc_r*denom),bt);
    diffs[i]:=Qt!Kt!diffs[i];
    if Coefficient(diffs[i],-1) ne 0 then
      diffs[i]:=diffs[i]-Coefficient(diffs[i],-1)*t^(-1); //  deal with logs later, important for double integrals
    end if;
  end for;

  indefints:=[];
  for i:=1 to #basis do
    indefints := Append(indefints, Integral(diffs[i]));
  end for;
  doubles:=[];
  for i in [1..2*g] do 
    for j in [1..2*g] do
        doubles := Append(doubles, (Integral(diffs[i]*indefints[j])));
    end for;
  end for;

  triples:=[];
  for i in [1..2*g] do 
    for j in [1..4*g^2] do
      triples:= Append(triples, (Integral(diffs[i]*doubles[j])));
    end for;
  end for;

  xt:=xtold;
  bt:=Vector(btold);
  

  if all eq true then
      return Vector(indefints), Vector(doubles),Vector(triples), xt,bt,NIPP1;
  else
    return Vector(triples),xt,bt,NIPP1;
  end if;

end function;


function funcW(E,prec,R) // pAdicRing isfaster than pAdicField here
   a1,a2,a3,a4,a6:=Explode([R!x : x in aInvariants(E)]);
   _<t>:=PowerSeriesRing(R,prec); // Laurent to get the Precision type right
   w:=t^3+a1*t^4+(a1^2+a2)*t^5+(a1^3+2*a1*a2+a3)*t^6+O(t^7); PREC:=[prec];
   while PREC[1] ge 8 do PREC:=[(PREC[1]+1) div 2] cat PREC; end while;
   PREC:=Reverse(PREC);
   while #PREC ne 0 do wp:=PREC[#PREC]; Prune(~PREC);
    w:=ChangePrecision(w,wp); w2:=w^2;
    w:=w-(-t^3+(1-a1*t-a2*t^2)*w-(a3+a4*t+a6*w)*w2)/
    (1-a1*t-a2*t^2-(a3+a4*t)*(2*w)-3*a6*w2); 
       end while;
   return w;
 end function;

function fint(F) //integral of F;
   c,e:=Coefficients(F); 
   if c eq [] then
    return Parent(F)!0;
   end if;
   FF:=FieldOfFractions(Parent(c[1])); c:=[FF!x : x in c];
   for i in [1..#c] do
    if e+i eq 0 then c[i]:=0;
    else c[i]/:=(e+i);
    end if;
  end for;
  return (Parent(F)!c)*(Parent(F).1)^(1+e);
end function;

function brent(C,n) // old function
  R<t>:=PowerSeriesRing(Universe(C),n); F:=R!1+O(t); f:=R!C; w:=1;
  while w le n do 
    w+:=w;
    F:=ChangePrecision(F,Min(w,n));
    G:=fint(Derivative(F)/F-f);
    F:=F*(1-G);
  end while;
  return F;
end function;

function NaiveSigmaAlmostBernardi(E,N)
  K:=BaseRing(E);
  A:=aInvariants(E);
  a1,a2,a3,a4,a6:=Explode([x : x in A]);
  w:=funcW(E,N+4,K); //w is divisible by t^3, so this prec ensures absolute prec N-2 in y and N-1 in x
  //then prec N in s;
  //prec N in fint((x+c)*s).
  t:=Parent(w).1; y:=-1/w; x:=-t*y;
  s:=Derivative(x)/(2*y+a1*x+a3); c:=0;//c:=(a1^2+4*a2)/12;
  h:=-1/t-s*(a1/2+fint((x+c)*s)); 
  C:=[Coefficient(h,i) : i in [0..N-1]];
  theta:=brent(C,N-1);
  return t*theta;
end function;



//20/06/22: functions to deal with double integrals to torsion points:
function LocalHeight(P, q, p, n) 
    //Based on Magma's LocalHeight.
    E := Scheme(P);
    K := Ring(Parent(P));
    assert K cmpeq NumberField(q);
    EK := E(K);
    //retain_attributes(EK);
    E, trans := MinimalModel(E, Ideal(q));
    P := trans(P);
    a1,a2,a3,a4,a6 := Explode(ChangeUniverse(aInvariants(E), K));
    b2,b4,b6,b8 := Explode(ChangeUniverse(bInvariants(E), K));
    c4 := K!cInvariants(E)[1];
    delta := K!Discriminant(E);
    vd := Valuation(delta, q);
    vc4 := Valuation(c4, q);
    x := P[1];
    y := P[2];
    f2 := Valuation(2*y + a1*x + a3, q);
    f3 := Valuation(3*x^4 + b2*x^3 + 3*b4*x^2 + 3*b6*x + b8, q);
    if Valuation(3*x^2 + 2*a2*x + a4 - a1*y, q) le 0 or f2 le 0 then
        lambda := Max(0, -Valuation(x, q));
  vprintf Height : "%o, nonsingular reduction: %o\n", q, lambda;
    elif vd gt 0 and vc4 eq 0 then
  assert(vd gt 0);
  alpha := Min(1/2, f2/vd);
  lambda := vd*alpha*(alpha - 1);
  vprintf Height : "%o, multiplicative reduction: %o\n", q, lambda;
    elif vd gt 0 and vc4 gt 0 then
        assert(vd gt 0);
  if f3 ge 3*f2 then
      lambda := -2*f2/3;
  else
      lambda := -f3/4;
  end if;
  vprintf Height : "%o, additive reduction: %o\n", q, lambda;
    end if;
  //lambda +:= vd/6;

    logp := Log(pAdicField(p,n)!Generator(Integers() meet Ideal(q)));
    height := lambda * logp;

    return height;
end function;

function LocalHeightp(P,p,n)
    //Height at p. P must be defined over the rationals.
    E := Scheme(P);
    K:=Ring(Parent(P));
    assert K eq Rationals();
    K:=RationalsAsNumberField();
    E, trans := MinimalModel(ChangeRing(E,K));
    P := trans(P);
    assert Order(P) ne 0;
    D := Discriminant(E);
    Primes:=PrimeFactors(Integers()!D);
    if (2 in Primes) eq false then
        Append(~Primes,2);
    end if;
    height:=0;
    for q in Primes do
  height +:= -LocalHeight(P,Place(q*MaximalOrder(K)),p,n);
    end for;
    return height;
end function;


function NaiveSigmaAlmostBernardiPrec(p,n)
  return n*Ceiling((p-1)/(p-2));
end function;

 function DivisionPolynomialEven(E,m)
  assert m mod 2 eq 0;
  _,divm0,_ := DivisionPolynomial(E,m);
  div2 := TwoTorsionPolynomial(E);
  Pdiv2 := Parent(div2);
  return div2*MultivariatePolynomial(Pdiv2, divm0, 1);
end function;

 function doub_AB_via_sigma(E, p, prec: sigma:=false)
  //Currently implemented only for non-torsion point.
  //If you need this at a torsion point,use that 
  // the global height is 0,
  //so here -1/2*sum of local heights away from p.
  prec:= prec+1;
  Emin:=MinimalModel(E);
  D := Integers()!((Discriminant(E)/Discriminant(Emin))^(1/12));
  m := Exponent(AbelianGroup(ChangeRing(E,GF(p))));
  adj_prec:= NaiveSigmaAlmostBernardiPrec(p,prec);
  if Type(sigma) eq BoolElt then
    sigma := NaiveSigmaAlmostBernardi(E, adj_prec);
  end if;
  if m mod 2 eq 1 then
    divm := DivisionPolynomial(E,m);
  else
    divm := DivisionPolynomialEven(E,m);
  end if;

  function doubAB(Q)
     //20/06/22: added following 3 lines for torsion cases (over Q)
     //to do: torsion not defined over Q.
    try
        if Order(Q) ne 0 then
           return 1/2*LocalHeightp(E!Q,p,prec+2); //Precision bounds
        end if;
    catch e
       e := e;
    end try;
    
    mQ := m*Q;
    tmQ := - pAdicField(p, adj_prec)!(mQ[1]/mQ[2]);
    sigmamQ := Evaluate(sigma, tmQ);
    newprec:=Minimum(AbsolutePrecision(sigmamQ), prec) - Valuation(sigmamQ);
    sigmamQ := ChangePrecision(sigmamQ, newprec);
    if m mod 2 eq 1 then
      lambdapQ := -2*Log(sigmamQ/Evaluate(divm, Q[1]))/m^2;
    else
      lambdapQ := -2*Log(sigmamQ/Evaluate(divm, [Q[1],Q[2]]))/m^2;
    end if;
    return lambdapQ/2 - Log(pAdicField(p,prec)!D);
  end function;
  return  doubAB;
end function;

function NaivepAdicHeight(E, p, prec: sigma:=false)
  //Currently implemented only for non-torsion point.
  //At a torsion point this is just 0
  prec:= prec+1;
  Emin:=MinimalModel(E);
  A:=aInvariants(Emin);
  a1,a2,a3,a4,a6:=Explode([x : x in A]);
  finv :=Isomorphism(E,Emin);
  n1 := Exponent(AbelianGroup(ChangeRing(E,GF(p))));
  n2:=LCM([TamagawaNumber(Emin,p) : p in BadPrimes(Emin)]); 
  n:=LCM(n1,n2);  
  
  adj_prec:= NaiveSigmaAlmostBernardiPrec(p,prec);
  if Type(sigma) eq BoolElt then
    if aInvariants(E)[2] eq 0 then
      sigma := NaiveSigmaAlmostBernardi(Emin, adj_prec, (a1^2+4*a2)/12);
    else
      sigma := NaiveSigmaAlmostBernardi(Emin, adj_prec, 0);
    //sigma := NaiveSigmaAlmostBernardi(E, adj_prec);
    end if;
  end if;

  function NaivepAdicHeightQ(Q)
    Q := finv(Q);
    mQ:=n*Q;
     _,d:=IsSquare(Denominator(mQ[1]));
    tmQ := - pAdicField(p, adj_prec)!(mQ[1]/mQ[2]);
    sigmamQ := Evaluate(sigma, tmQ);
    newprec:=Minimum(AbsolutePrecision(sigmamQ), prec) - Valuation(sigmamQ);
    sigmamQ := ChangePrecision(sigmamQ, newprec);
    hpQ := -2*Log(sigmamQ/d)/n^2;
    return hpQ; //- Log(pAdicField(p,prec)!D);
  end function;
  return  NaivepAdicHeightQ;
end function;

//////////////////////////////////////////////
//Triple integrals from b

function b_to_P_alltrip(P,data:all:=false)
  //So far assumes point does not reduce to infinity.
  if P`inf eq true then
    if all eq true then
      return Zero(VectorSpace(Rationals(),2)), Zero(VectorSpace(Rationals(),4)), Zero(VectorSpace(Rationals(),8));
    else
      return Zero(VectorSpace(Rationals(), 8));
    end if;
  end if;
  P0:= [P`x, (P`b)[2]];
  p:=data`p;
  N:=data`N;
  Q:=data`Q;
  K:=pAdicField(p,N);
  if Integers()!(P0[2]) mod p eq 0 then
    W:=find_bad_point_in_disk(P,data);
    WPtrip:=tiny_triple_integrals_on_basis(W,P,data);
    WPsing:=tiny_integrals_on_basis(W,P,data);
    def_pol := -Evaluate(Q,0);
    Qprime:=Derivative(def_pol);
    E:=EllipticCurve(def_pol);
    Emin:=MinimalModel(E);
    D:=Integers()!((Discriminant(E)/Discriminant(Emin))^(1/12));
    bWdoubAB:= Log(Evaluate(Qprime,W`x)) - 4*Log(K!D);
    bWdoubBA:=-bWdoubAB;
    bWdoub:=[0,bWdoubAB,bWdoubBA,0];
    alltrip:=[];
    for i:=0 to 1 do
      for j:=0 to 1 do
        for k:=0 to 1 do
          Append(~alltrip, WPsing[i+1]*bWdoub[2*j+k+1]+WPtrip[4*i+2*j+k+1]);
        end for;
      end for;
    end for;
    alltrip := Vector(alltrip);
    if all eq false then
      return alltrip;
    else
      WPdoub:=tiny_double_integrals_on_basis(W,P,data);
      bPdoub:=Vector([1/2*WPsing[1]^2,bWdoub[2]+WPdoub[2], bWdoub[3] + WPdoub[3], 1/2*WPsing[2]^2]);
      return WPsing, bPdoub, alltrip;
    end if;
  end if;
  negP :=set_point(P0[1], -P0[2],data);
  O:=set_bad_point(0,[1,0],true,data); //point at infinity
  b_to_P_A_and_B := coleman_integrals_on_basis(O,P,data);
  b_to_P_A := b_to_P_A_and_B[1];
  b_to_P_B := b_to_P_A_and_B[2];
  E:=EllipticCurve(-Evaluate(Q,0));
  b_to_P_AB := doub_AB_via_sigma(E, p, N)(ChangeRing(E,K)![P0[1],P0[2]])*4; //normalised to agree with Magma
  b_to_P_BA := b_to_P_A*b_to_P_B - b_to_P_AB;
  JQP :=triple_integrals_on_basis(negP,P,data);
  dP := Vector([b_to_P_A^2/2, b_to_P_AB, b_to_P_BA, b_to_P_B^2/2]);
  AAA := 1/6*(b_to_P_A)^3;
  ABA := 1/2*JQP[3] - b_to_P_A*b_to_P_AB;
  AAB := 1/2*(b_to_P_A*b_to_P_AB - ABA);
  BAA := 1/2*(b_to_P_A*b_to_P_BA - ABA);
  BAB := 1/2*JQP[6] - b_to_P_B*b_to_P_BA;
  ABB := 1/2*(b_to_P_B*b_to_P_AB - BAB);
  BBA := 1/2*(b_to_P_B*b_to_P_BA - BAB);
  BBB := 1/6*(b_to_P_B)^3;
  V := Vector([AAA,AAB,ABA,ABB,BAA,BAB,BBA,BBB]);
  if all eq true then
    return b_to_P_A_and_B, dP, V;
  else
    return V;
  end if;
end function;


function f1_f2_f3_f4(I,D,TT)
  f1:=I[1];
  f2:=D[2];
  f3:=TT[2];
  f4:=TT[4]-2*I[2];
  return f1,f2,f3,f4;
end function;


triples_on_basis_to_z := function(P,data:prec:=0);

  g:=data`g;
  sP, dP, tP := b_to_P_alltrip(P,data:all:=true);
  st, dt, tt := tiny_triple_integrals_on_basis_to_z(P,data:all:=true);
  dim := 2*g;
  trip := [];
  for i in [1..dim] do
        for k in [1..dim] do
            ik := dim*(i-1) + k;
            for l in [1..dim] do
                ikl := dim^2*(i-1) + dim*(k-1) +l;
                li := dim*(l-1) + i;
                il := dim*(i-1) + l;
                kl := dim*(k-1) + l;
                lk := dim*(l-1) + k;
                trip := Append(trip, tP[ikl] + st[i]*dP[kl] + dt[ik]*sP[l] + tt[ikl]);
            end for;
        end for;
  end for;
  
  return trip;
end function;