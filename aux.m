
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