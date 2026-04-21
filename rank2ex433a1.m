///////////////////////////////////////////////////////////////////////////////////
// This code is applicable to rank 2 elliptic curves E satisfying the following conditions:
// (1) Tamagawa number 1 at all primes;
// (2) At least 7 distinct integral points, distinct also up to additive inverses.
//
// Uses root-finding code from QCMod kindly shared by Steffen Mueller (in mueller.m)
//
// Input: an elliptic curve with model Q as y^2 - f(x), a prime p, precision N,
// and generators Q1, Q2 on the minimal model Emin such that Q1, Q2 are both integral.
//
// This is Example 6.5 of [BBD], which is the example of E = 433.a1 and p = 3.
///////////////////////////////////////////////////////////////////////////////////

load "coleman.m";
load "resultant.m";
load "mueller.m";
load "aux.m";
t1 := Cputime();

//Input:
Q:=y^2-(x^3 + x^2 + 64); //433.a1
p:=3;
N:=50;


Eshort:=EllipticCurve(-Evaluate(Q,0));
E:=MinimalModel(Eshort);
assert Rank(E) eq 2;

Q1:=E![-1,1]; //433.a1 generator
Q2:=E![0,-1]; //433.a1 generator

Q1plusQ2 :=Q1+Q2;
Qs:=[Q1,Q2];

lambdas:=[];
Pmins:=[];
Q1plusQ2_ind := 0;
for c1 in [0..10] do
	for c2 in [-10..10] do
		P:=c1*Qs[1] + c2*Qs[2];
		if P[3] ne 0 and Denominator(P[1]) eq 1  then
			if not -P in Pmins then 
				Append(~lambdas, [c1,c2]);
				Append(~Pmins, P);
				if P eq Q1 then
					Q1_ind:=[#Pmins,1];
				elif P eq -Q1 then
					Q1_ind:=[#Pmins,-1];
				elif P eq Q2 then
					Q2_ind := [#Pmins,1];
				elif P eq -Q2 then
					Q2_ind := [#Pmins, -1];
				elif P eq Q1plusQ2 or P eq -Q1plusQ2 then
					Q1plusQ2_ind:=#Pmins;
				else
					
				end if;							
			end if;
		end if;
	end for;
end for;

assert #Pmins ge 7; //To do: allow torsion? 


phi:=Isomorphism(E,Eshort);
data:=coleman_data(Q,p,N);

Ps:=[phi(Pmin) : Pmin in Pmins];
Ps_data:=[set_point(P[1],P[2],data) : P in Ps];

f1s:=[];
f2s:=[];
f3s:=[];
f4s:=[];
for P in Ps_data do
	S,D,T:=b_to_P_alltrip(P,data:all:=true);
	f1,f2,f3,f4:=f1_f2_f3_f4(S,D,T);
	Append(~f1s,f1);
	Append(~f2s,f2);
	Append(~f3s,f3);
	Append(~f4s,f4);
end for;

j2s := f2s;

Mbig:=Matrix([[lambdas[i][1]^3, lambdas[i][2]^3, lambdas[i][1]^2*lambdas[i][2],lambdas[i][1]*lambdas[i][2]^2,lambdas[i][1],lambdas[i][2], f4s[i]] : i in [1..#Pmins]]);
if Rank(Mbig) lt 7 then
	print "Rank is too small to compute the function";
end if;

SS:=Subsets({1..#Pmins},7);
SSlists:=[];
for s in SS do
        Append(~SSlists,IndexedSetToSequence(SetToIndexedSet(s)));
end for;

for s in SSlists do
        M:=Matrix([Mbig[i]: i in s]);
        if Rank(M) eq 7 then
                s_rel:=s;
                M_rel:=M;
                break s;
        end if;
end for;

cis:=M_rel^(-1)*Transpose(Matrix([[f3s[i] : i in s_rel]]));
cis:=Vector(cis);

//on gens
f1Q1:=Q1_ind[2]*f1s[Q1_ind[1]]; 
f1Q2:=Q2_ind[2]*f1s[Q2_ind[1]];
j2Q1:=j2s[Q1_ind[1]]; 
j2Q2:=j2s[Q2_ind[1]]; 
if Q1plusQ2_ind eq 0 then
	j2sQ1Q2 :=2*NaivepAdicHeight(E, p,N)(Q1plusQ2);
else
	j2sQ1Q2 := j2s[Q1plusQ2_ind];
end if;
Q1Q2:=1/2*(j2sQ1Q2 - j2Q1 - j2Q2);
f3Q1:=Q1_ind[2]*f3s[Q1_ind[1]]; 
f3Q2:=Q2_ind[2]*f3s[Q2_ind[1]];
f4Q1:=Q1_ind[2]*f4s[Q1_ind[1]]; 
f4Q2:=Q2_ind[2]*f4s[Q2_ind[1]];

K:=pAdicField(p,N);
R3<j1z,j2z,j3z> := PolynomialRing(K,3);
res_eg:=Evaluate(res, [j1z, K!f1Q1, K!f1Q2, j2z, K!j2Q1, K!j2Q2, K!Q1Q2, j3z, K!cis[1],K!cis[2],K!cis[3],K!cis[4],K!cis[5], K!cis[6]]);
c:=K!cis[7];
//print "c = ", c;
j3s:=[f3s[i] - c*f4s[i] : i in [1..#Pmins]];

//print "----checking resultant vanishes----";

//for i:=1 to #f1s do
//	Evaluate(res_eg, [f1s[i],j2s[i],j3s[i]]);
//end for;
//
//print "----completed----";
//print "res_eg = ", res_eg;


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
    ptQ := set_point(ptQ[1],ptQ[2],data);
    xt,bt,index:=local_coord(ptQ,N,data);
    W0invxt := Evaluate(W0^(-1), xt);
    b_vector := Matrix(Parent(xt), Degree(Q), 1, bt);
    yt := &+[W0invxt[2,j]*b_vector[j,1] : j in [1..Degree(Q)]];
    sP, dP, tP := b_to_P_alltrip(ptQ, data: all:=true);
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

    f3 := trip[2]; 

    // note that in the article f4 is given as
    // \int dx/2y x dx/2y x dx/2y - 1/2  \int x dx/2y
    // while here the basis of differentials that is being used is
    // w0 = dx/y and w1 = x dx/y
    // so f4 is accordingly \int dx/y x dx/y x dx/y - 2\int x dx/y
    
    f4 := trip[4] -2*sing_B; 
    j3z := f3 - c*f4;
    j1z := sing_A; 
    j2z := doub_AB;
    F:=Evaluate(res_eg,[j1z,j2z,j3z]);
    t:=Parent(F).1;
    F := Evaluate(Qptt!F,p*Qptt.1);
    val := Minimum([Valuation(a): a in Coefficients(F)]);
    F := F*p^(-val);
    roots, root_prec, f := roots_with_prec(F,N);
    for j in [1..#roots] do
         r:=roots[j,1];
         pt := [Evaluate(c, p*r) : c in [xt, yt]];
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
t2 := Cputime();

print "==============================================";
print "integral points on X  = ", ratpts;
print "mock integral points in X(Z_p)_3 = ", fakepts;
print "Time for computation: ", t2-t1;
