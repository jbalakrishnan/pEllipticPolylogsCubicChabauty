///////////////////////////////////////////////////////////////////////////////////
// This code is applicable to rank 1 elliptic curves E satisfying the following conditions:
// (1) Tamagawa number 1 at primes of split multiplicative reduction;
// (2) At least 3 distinct integral points, distinct also up to additive inverses.
// (even then, this might not work if there is some degeneracy)
// Then this computes roots of the depth 3 function F(z) = f_3(z) - c*f_4(z) - c1/f1(Q1)^3*f1(z)^3 - c2/f1(Q1)*f1(z)
// where Q1 generates E(Q)/tors and c,c1,c2 are computed using a collection of known integral points.
//
// Uses root-finding code from QCMod kindly shared by Steffen Mueller (in mueller.m)
//
// Input: an elliptic curve with model Q as y^2 - f(x), a prime p, precision N.
//
// This is Example 6.3 of [BBD], which is the example of E = 37.a1 and p = 7.
///////////////////////////////////////////////////////////////////////////////////

load "coleman.m";
load "mueller.m";
load "aux.m";
t1 := Cputime();

//Input:
Q:=y^2 - (x^3 - 16*x + 16); //37.a1
p:=7;
N:=50;

Eshort:=EllipticCurve(-Evaluate(Q,0));
E:=MinimalModel(Eshort);
assert Rank(E) eq 1;
Q1:=Generators(E)[1];

lambdas:=[];
Pmins:=[];
for c in [0..10] do
	P:=c*Q1;
	if P[3] ne 0 and Denominator(P[1]) eq 1  then
		if not -P in Pmins then 
			Append(~lambdas, c);
			Append(~Pmins, P);
			if P eq Q1 then
				Q_ind:=[#Pmins,1];
		    elif P eq -Q1 then
				Q_ind:=[#Pmins,-1];
			else					
				end if;							
			end if;
		end if;
end for;

assert #Pmins ge 3; //To do: allow torsion too?

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
  f3new := -f3 - (1/2 + 1/12*log(p,pAdicField(p,N)!Discriminant(Eshort)))*S[1]; 
	Append(~f1s,f1);
	Append(~f2s,f2);
	Append(~f3s,f3new); 
	Append(~f4s,f4);
end for;

j2s := f2s;

Mbig:=Matrix([[lambdas[i]^3, lambdas[i], f4s[i]] : i in [1..#Pmins]]);
if Rank(Mbig) lt 3 then
	print "Rank is too small to compute the function";
end if;

SS:=Subsets({1..#Pmins},3);
SSlists:=[];
for s in SS do
        Append(~SSlists,IndexedSetToSequence(SetToIndexedSet(s)));
end for;

for s in SSlists do
        M:=Matrix([Mbig[i]: i in s]);
        if Rank(M) eq 3 then
                s_rel:=s;
                M_rel:=M;
                break s;
        end if;
end for;

cis:=M_rel^(-1)*Transpose(Matrix([[f3s[i] : i in s_rel]]));
cis:=Vector(cis);

//on gens
f1Q1:=Q_ind[2]*f1s[Q_ind[1]]; 
j2Q1:=j2s[Q_ind[1]]; 
f3Q1:=Q_ind[2]*f3s[Q_ind[1]]; 

K:=pAdicField(p,N);

c:=K!cis[3];
c1:=K!cis[1];
c2:=K!cis[2];
j3s:=[f3s[i] - c*f4s[i] : i in [1..#Pmins]];

function F_for_E(Eshort, p, N, c, data);
 g:=data`g;
 W0:=data`W0;
 Ep:=ChangeRing(Eshort,GF(p));
 D:=RationalPoints(Ep);
 K:=pAdicField(p,N);
 Qptt := PowerSeriesRing(K,N);

 found:=[];

 D:=prune(D); //so only half of the residue disks up to negation

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

    f3 := -trip[2]- (1/2 + 1/12*log(p,pAdicField(p,N)!Discriminant(Eshort)))*sing_A; //f3 = w0 w0 w1

    // note that in the article f4 is given as
    // \int dx/2y x dx/2y x dx/2y - 1/2  \int x dx/2y
    // while here the basis of differentials that is being used is
    // w0 = dx/y and w1 = x dx/y
    // so f4 is accordingly \int dx/y x dx/y x dx/y - 2\int x dx/y

    f4 := trip[4] -2*sing_B;  
    j3z := f3 - c*f4;
    j1z := sing_A; 
    F:= j3z - c1/f1Q1^3*j1z^3 - c2/f1Q1*j1z;
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
print "A zero of F_3(z) that is not a zero of F_2(z) = ", fakepts;
print "Time for computation: ", t2-t1;
