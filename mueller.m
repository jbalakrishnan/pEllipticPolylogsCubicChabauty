////////////////////////////////////////////////////////////////////////////////////////////////////////////
// This file includes functions from the files
// https://github.com/steffenmueller/QCMod/blob/main/misc.m and
// https://github.com/steffenmueller/QCMod/blob/main/applications.m
// which were written by Steffen Mueller.
////////////////////////////////////////////////////////////////////////////////////////////////////////////

procedure compare_vals(L1, L2, N)
  //from misc.m
  for i in [1..#L1] do
    if L1[i,1] gt N then 
      L1[i,1] := N;
    end if;
  end for;
  for i in [1..#L2] do
    if L2[i] gt N then 
      L2[i] := N;
    end if;
    m := #[d : d in L2 | d eq L2[i]];
    valsi := [L1[j,2] : j in [1..#L1] | L1[j,1] eq L2[i]];
    if #valsi eq 0 then
      error "Root finding returned a root with incorrect valuation";
    end if;
    if m gt &+valsi then
      error "Root finding returned the wrong number of roots";
    end if;

  end for;
end procedure;

function count_roots_in_unit_ball(f, N)
  // from misc.m
  // TODO: Deal with zero poly
  vals := ValuationsOfRoots(f);
  number_of_roots := 0;
  univ := Universe(vals);
  for pair in vals do
    if pair[1] ge 0 then
    // Had to include this workaround because magma's extended reals 
    // are counterintuitive (to say the least)
      val_root := pair[1];
      if val_root ge N then 
        val_root := N;
      end if;
      val_root := Rationals()!val_root;
      if IsIntegral(val_root) then
        number_of_roots +:= pair[2];     
      end if;
    end if;
  end for;
  return number_of_roots;
end function;


function roots_with_prec(G, N);
  // from applications.m
  // return the integral roots of a p-adic polynomial f, and the precision
  // to which they are known.
  // As in Lemma 4.7, our G(t) is F(pt)
  // We throw an error if there are multiple roots 
  coeffsG := Coefficients(G);
  p := Prime(Universe(coeffsG));
  Qp := pAdicField(p,N); 
  Qptt := PowerSeriesRing(Qp);
  Zp := pAdicRing(p,N);
  Zpt := PolynomialRing(Zp);
  Qpt := PolynomialRing(Qp);
  precG := #coeffsG;
  min_val := Min([Valuation(c) : c in coeffsG]); // this is k in Lemma 4.7
  max_N_index := Max([i : i in [1..precG] | Valuation(coeffsG[i]) le N]);
  // TODO: Could lower t-adic precision according to Lemma 4,7. 
  //valG := Min(0, Valuation(G));
  valG := Valuation(G);
  G_poly := Zpt!(p^(-min_val)*Qpt.1^valG*(Qpt![Qp!c : c in coeffsG ])); 
  G_series := (p^(-min_val)*Qptt.1^valG*(Qptt![Qp!c : c in coeffsG ])); 
  upper_bd_number_of_roots := count_roots_in_unit_ball(G_poly, N-min_val); 
  if upper_bd_number_of_roots eq 0 then 
    return [], N, G_series;
  end if;
  roots := roots_Zpt(G_poly);  // compute the roots.
  assert &and[z[2] gt 0 : z in roots]; // First check that roots are simple.
  if #roots gt 0 then 
    root_prec := Floor((N - min_val)/#roots); // Lemma 4.7
    vals := [Valuation(rt[1]) : rt in roots];
    if #roots gt 0 and root_prec le 0 then
      error "Precision of roots too small. Rerun with higher p-adic precision (increase the optional parameter N)";
    end if;
    min_coeff_prec := Min([Precision(c) : c in Coefficients(G_poly)]);
    root_prec := Min(root_prec, min_coeff_prec);
    compare_vals(ValuationsOfRoots(G_poly), vals, root_prec);
  else  // no root, so no precision loss.
    root_prec := N;
  end if;
  return roots, root_prec, G_series;
end function;