///////////////////////////////////////////////////////////////////////////////////
// This code is applicable to rank 0 elliptic curves satisfying the following conditions:
// (1) Tamagawa number 1 at primes of split multiplicative reduction;
// (2) A torsion point of order >= 3 (and even then, this might not work if there is some degeneracy).
// Then this computes roots of the depth 3 function F(z) = f_3(z) - c*f_4(z),
// where c is computed using a torsion point of order >=3, as in (2).
//
// When f_3(z), f_4(z) are non-zero for two distinct z=P1, z=P2
// that are not inverses of each other, it is also of interest to compute
// the quotients f_3(P1)/f_3(P2) and f_4(P1)/f_4(P2),
// which should be equal, rational, and equal to the corresponding
// quotients of complex dilogarithms (cf. Goncharov-Levin).
// [If P1,P2 are additive inverses of each other, the quotients, if well-defined,
// are going to be = -1 trivially, so that is not an interesting case to consider.]
// Uses root-finding code from QCMod kindly shared by Steffen Mueller (in mueller.m)
//
// Input: an elliptic curve with model Q as y^2 - f(x), a prime p, precision N.
//
// This is Example 6.2 of [BBD], which is the example of E = 36.a4 and p = 7.
///////////////////////////////////////////////////////////////////////////////////

load "coleman.m";
load "mueller.m";
load "aux.m";
t1 := Cputime();


Q:= y^2 -(x^3 + 1); //36.a4
Eshort:=EllipticCurve(-Evaluate(Q,0));
E:=MinimalModel(Eshort);
gens:=Generators(Eshort);
P:=gens[#gens];
p:=7;
N:=50;

data:=coleman_data(Q,p,N);
P:=set_point(P[1],P[2],data);
S,D,T:=b_to_P_alltrip(P,data:all:=true);
f1,f2,f3,f4:=f1_f2_f3_f4(S,D,T);
c:=f3/f4;
print "c = ", c;


function find_pt(E,P,N);
//C an elliptic curve over QQ
//P a point over Fp
  p := #(Parent(P[1]));
  QpN := pAdicField(p,N);
  Qp1:=pAdicField(p,1);
  Ep:=ChangeRing(E,GF(p));
  T3:=PolynomialRing(QpN,3);
  des := DefiningEquations(E);
  polylist := [ T3!des[i] : i in [1..#des]];
  ptlift := LiftPoint(polylist,2,[Qp1!P[1], Qp1!P[2], QpN!1],N);
  return ptlift;
end function;

function prune(D);
  p := #(Parent(D[1][1]));
  GFp := GF(p);
  newlist := [];
  for x in D do
    if x[3] ne 0 then
        if ([GFp!(x[1]), GFp!(-x[2])] in newlist) eq false then
            Append(~newlist, x);
        end if;
    end if;
   end for;
return newlist;
end function;


function F_for_E(Eshort, p, N, c, data);
 g:=data`g;
 W0:=data`W0;
 Ep:=ChangeRing(Eshort,GF(p));
 D:=RationalPoints(Ep);

 K:=pAdicField(p,N);
 Qptt := PowerSeriesRing(K,N);

 found:=[];

 D:=prune(D); //so only half of the residue disks up to hyperelliptic involution

 for P in D do
    ptQ := find_pt(Eshort, P, N);
	parptQ:=Parent(ptQ);
    ptQ := set_point(ptQ[1],ptQ[2],data);
    xt,bt,index:=local_coord(ptQ,N,data);
    W0invxt := Evaluate(W0^(-1), xt);
    b_vector := Matrix(Parent(xt), Degree(Q), 1, bt);
    yt := &+[W0invxt[2,j]*b_vector[j,1] : j in [1..Degree(Q)]];
	try
		sP, dP, tP := b_to_P_alltrip(ptQ, data: all:=true);
	catch e
		ptQ := parptQ![Evaluate(xt,p), Evaluate(yt,p)];
		 ptQ := set_point(ptQ[1],ptQ[2],data);
		xt,bt,index:=local_coord(ptQ,N,data);
		W0invxt := Evaluate(W0^(-1), xt);
		b_vector := Matrix(Parent(xt), Degree(Q), 1, bt);
		yt := &+[W0invxt[2,j]*b_vector[j,1] : j in [1..Degree(Q)]];
		sP, dP, tP := b_to_P_alltrip(ptQ, data: all:=true);
	end try;
    st, dt, tt := tiny_triple_integrals_on_basis_to_z(ptQ,data: all:=true);
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
     sing_A := sP[1] + st[1];
     sing_B := sP[2] + st[2];
     doub_AB := dP[2] + dt[2] + st[1]*sP[2];

    f3 := trip[2]; //f3 = w0 w0 w1

    // note that in the article f4 is given as
    // \int dx/2y x dx/2y x dx/2y - 1/2  \int x dx/2y
    // while here the basis of differentials that is being used is
    // w0 = dx/y and w1 = x dx/y
    // so f4 is accordingly \int dx/y x dx/y x dx/y - 2\int x dx/y

    f4 := trip[4] -2*sing_B;  
    j3z := f3 - c*f4;
	  F:=j3z;
    t:=Parent(F).1;
    F := Evaluate(Qptt!F,p*Qptt.1);
    val := Minimum([Valuation(a): a in Coefficients(F)]);
    F := F*p^(-val);
    roots, root_prec, f := roots_with_prec(F,N);
    for j in [1..#roots] do
         r:=roots[j,1];
         pt := [Evaluate(cc, p*r) : cc in [xt, yt]];
	       f3_f4_vals := [Evaluate(cc, p*r) : cc in [f3,f4]];
         Append(~found, pt);
    end for;
end for;
return found;
end function;


foundpts:=F_for_E(Eshort,p,N,c,data);
print "==============================================";
print "Points z such that j_3(z)= 0: ", foundpts;
ratpts:=[];
fakepts:=[];
for P in foundpts do
    try
       Append(~ratpts, Eshort![Integers()!P[1], Integers()!P[2]]);
    catch e;
        Append(~fakepts, P);
    end try;
end for;

//checking that the mock rational points does not include the 6-torsion point 
//with y-coordinate 3 in depth 2 (see Table 2 of https://arxiv.org/pdf/1904.04622):
print "We now check that the set of mock rational points in depth 3 does not include the 6-torsion point with y-coordinate 3 found in depth 2:";
for P in fakepts do
   if Valuation(P[2]-3) eq 1 then //we find that the valuation of this extra root from j_3 = 0 has the property that v(y(z)-3) == 1
       print "Excluding point z =", P, "since j_2(z) != 0";  // print Valuation(P[2]-3);       
       Exclude(~fakepts,P);
   end if;
end for;
t2 := Cputime();
print "==============================================";
print "integral points on X  = ", ratpts;
print "mock integral points in X(Z_p)_3 = ", fakepts;
print "Time for computation: ", t2-t1;
