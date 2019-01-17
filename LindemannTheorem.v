From mathcomp Require Import all_ssreflect.
From mathcomp Require Import perm ssralg poly ssrnum polydiv mxpoly ssrint rat.
From mathcomp Require Import polyorder finmap order.
From SsrMultinomials Require Import mpoly.
From Lindemann Require Import archi Rstruct Cstruct prelim.
From Lindemann Require Import Lind_part1 Lind_part2 Lind_part3.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.
Import GRing.Theory Num.Theory Archi.Theory Archi.Order.

Local Notation RtoC := Cstruct.RtoC.
Local Notation Cnat := Cstruct.Cnat.
Local Notation Cint := Cstruct.Cint.

Notation "x 'is_algebraic'" := (algebraicOver QtoC x)
  (at level 55).

Definition lin_indep_over (P : pred_class) {n : nat} (x : complexR ^ n) :=
  forall (lambda : complexR ^ n), lambda \in ffun_on P ->
    lambda != 0 -> \sum_(i < n) (lambda i * x i) != 0.

Definition alg_indep_over (P : pred_class) {n : nat} (x : complexR ^ n) :=
  forall (p : {mpoly complexR[n]}), p \is a mpolyOver _ P ->
    p != 0 -> p.@[x] != 0.

Local Notation setZroots := ((fset_roots Cint) : 
    complexR -> qualifier 1 {fset complexR}).




(******************************************************************************)
(*                          Lindemann's theorems                              *)
(******************************************************************************)

Theorem LindemannBaker : forall (l : nat) (alpha : complexR ^ l) (a : complexR ^ l),
  (0%N < l)%N -> injective alpha -> (forall i : 'I_l, alpha i is_algebraic) ->
  (forall i : 'I_l, a i != 0) -> (forall i : 'I_l, a i is_algebraic) ->
  (Cexp_span a alpha != 0).
Proof.
apply: wlog1_Lindemann.
apply: wlog2_Lindemann.
by apply: Lindemann_last.
Qed.

Theorem LindemannWeierstrass n (alpha : complexR ^ n) :
  (n > 0)%N -> (forall i : 'I_n, alpha i is_algebraic) ->
  lin_indep_over Cint alpha -> alg_indep_over Cint (finfun (Cexp \o alpha)).
Proof.
move=> Hn alph_alg alph_lind P /mpolyOverP P_int P0.
pose t := finfun (tnth (in_tuple (msupp P))).
pose beeta :=  (finfun ((fun m : 'X_{1..n} => \sum_(i < n) 
  (alpha i *+ m i)) \o t)).
pose a := (finfun ((fun m => P@_m) \o t)).
have -> : P.@[finfun (Cexp \o alpha)] = Cexp_span a beeta.
  rewrite /Cexp_span mevalE /beeta /a /t /= big_tnth.
  apply: eq_bigr => m _; rewrite !ffunE /=.
  congr (_ * _); first by rewrite ffunE.
  rewrite [RHS](big_morph Cexp Cexp_morph Cexp0).
  by apply: eq_bigr => i _; rewrite !ffunE /= CexpRX.
apply: LindemannBaker.
+ by rewrite lt0n size_eq0 msupp_eq0.
+ move=> i j; apply: contra_eq; rewrite /beeta !ffunE /= => i_neqj.
  rewrite -subr_eq0 -sumrB.
  pose lambda := finfun (fun i0 => (((t i) i0)%:R - ((t j) i0)%:R) : complexR).
  rewrite (eq_bigr (fun i0 => (lambda i0) * alpha i0)); last first.
    by move=> k _; rewrite /lambda !ffunE /= mulrBl !mulr_natl.
  apply: alph_lind.
  - by apply/ffun_onP => k; rewrite ffunE /= rpredB // Cint_Cnat // Cnat_nat.
  have := (nth_uniq 0%MM (ltn_ord i) (ltn_ord j) (msupp_uniq P)). 
  rewrite [RHS](inj_eq (@ord_inj _)) => H_neq.
  move: i_neqj; rewrite -H_neq -[msupp P]/(tval (in_tuple _)) -!tnth_nth.
  have H_k k : tnth (in_tuple (msupp P)) k = t k by rewrite /t ffunE /=.
  apply: contra => /eqP Hlambda; rewrite !H_k => {H_k}.
  apply/eqP/mnmP => k.
  have /eqP : lambda k = 0 by rewrite Hlambda ffunE.
  by rewrite /lambda ffunE subr_eq0 eqr_nat => /eqP ->.
+ move=> i; rewrite /beeta !ffunE /=.
  apply: big_rec; first by apply: algebraic0.
  move=> j x _; apply: algebraic_add; rewrite -mulr_natr.
  apply: algebraic_mul; first by apply: alph_alg.
  by rewrite integral_algebraic; apply: integral_nat.
+ by move=> i; rewrite /a ffunE /= -mcoeff_msupp /t ffunE /= mem_tnth.
move=> i; rewrite /a ffunE /=.
have := (P_int (t i)); rewrite CintE => /orP [/CnatP[m ->] | /CnatP[m]].
  by rewrite integral_algebraic; apply: integral_nat.
rewrite -[X in algebraicOver _ X]opprK => Heq.
apply: algebraic_opp; rewrite Heq integral_algebraic.
by apply: integral_nat.
Qed.

(* Print Assumptions LindemannWeierstrass *)






Lemma ffun1_lin_indep_over (P : pred_class) (x : complexR) :
  x != 0 -> lin_indep_over P (finfun (fun (i : 'I_1) => x)).
Proof.
move=> x_neq0; rewrite /lin_indep_over => l /ffun_onP _ l_neq0.
rewrite big_ord_recl /= big_ord0 addr0 ffunE. 
apply/mulf_neq0/x_neq0.
apply: (contra _ l_neq0) => /eqP n0_eq0.
apply/eqP/ffunP => i; rewrite zmodp.ord1 n0_eq0.
by rewrite [in RHS]/GRing.zero /= /ffun_zero ffunE.
Qed.

Lemma ffun1_alg_indep_over (x : complexR) :
   (x is_algebraic) -> ~ (alg_indep_over Cint (finfun (fun (i : 'I_1) => x))).
Proof.
rewrite /alg_indep_over => x_alg.
pose p := polyMin x_alg.
pose F := (fun (i : nat) => p`_i *: 'X_[U_(@ord0 0) *+ i]).
pose q := \sum_(i < size p) F i : {mpoly complexR[1]}.
have q_over : q \is a mpolyOver 1 Cint.
  apply/mpolyOverP => m; rewrite /q raddf_sum /= rpred_sum // => i _.
  rewrite mcoeffZ mcoeffX rpredM //; last by apply/Cint_Cnat/Cnat_nat.
  by have /polyOverP/(_ i) := (polyMin_over x_alg).
have q_neq0 : q != 0.
  suff H_in : (U_(@ord0 0) *+ (size p).-1)%MM \in (msupp q).
    by apply/negP => /eqP Hq; move: H_in; rewrite Hq msupp0 inE.
  rewrite /q -(big_mkord xpredT) (polySpred (polyMin_neq0 x_alg)).
  rewrite big_nat_recr //= (perm_eq_mem (msuppD _)) ?mem_cat.
    apply/orP; right; rewrite /F msuppMCX; first by rewrite inE.
    by rewrite -lead_coefE lead_coef_eq0 polyMin_neq0.
  move=> y /=; rewrite {2}/F msuppMCX; last first.
    by rewrite -lead_coefE lead_coef_eq0 polyMin_neq0.
  rewrite inE; case: eqP => [-> | ]; last by rewrite andbF.
  rewrite andbT; apply/negP; move/msupp_sum_le/flatten_mapP => [i].
  rewrite filter_predT mem_index_iota => /andP[i_gt0 i_lt].
  move/msuppZ_le; rewrite msuppX inE.
  move/eqP/mnmP/(_ (@ord0 0)); rewrite !mulmnE !mnmE /= !muln1 => H.
  by move: i_lt; rewrite H ltnn.
move/(_ q q_over q_neq0)/negP; apply; apply/eqP; rewrite /q raddf_sum /=.
have /rootP := (polyMin_root x_alg) => {2}<-; rewrite -/p horner_coef.
apply: eq_bigr => i _; rewrite /F mevalZ /meval mmapX /mmap1 /=.
by rewrite big_ord_recl /= big_ord0 mulr1 mulmnE mnmE /= muln1 ffunE /=.
Qed.




(******************************************************************************)
(*                          Hermite-Lindemann theorem                         *)
(******************************************************************************)

Theorem HermiteLindemann (x : complexR) :
  x != 0 -> x is_algebraic -> ~ ((Cexp x) is_algebraic).
Proof.
move=> x_neq0 x_alg; move/ffun1_alg_indep_over; apply.
have -> : (finfun (fun _ : 'I_1 => Cexp x)) = 
          (finfun (Cexp \o (finfun (fun _ : 'I_1 => x)))).
  by apply/ffunP => i; rewrite !ffunE /= ffunE.
apply/LindemannWeierstrass.
+ by [].
+ by move=> i; rewrite ffunE.
by apply/ffun1_lin_indep_over/x_neq0.
Qed.

(* Print Assumptions HermiteLindemann *)




(******************************************************************************)
(*                          Transcendence of e                                *)
(******************************************************************************)

Theorem e_trans_by_LB :
  ~ (RtoC (Rtrigo_def.exp 1) is_algebraic).
Proof.
have -> : RtoC (Rtrigo_def.exp 1) = Cexp 1 by rewrite Cexp_exp ?real1.
move=> e_alg.
pose p := polyMin e_alg.
pose t := enum ((fun i => p`_i != 0) : pred 'I_(size p)).
pose alpha := (finfun (fun i => ((tnth (in_tuple t) i)%:R : complexR))).
pose a := (finfun (fun i => p`_(tnth (in_tuple t) i))).
have /eqP : Cexp_span a alpha = 0.
  move/rootP: (polyMin_root e_alg) => <-; rewrite -/p horner_coef.
  rewrite /Cexp_span /alpha /a -/p.
  pose f := (fun (i : 'I_(size p)) => p`_i * Cexp 1 ^+ i).
  rewrite [LHS](eq_bigr (fun i => (f \o (tnth (in_tuple t))) i)); first last.
    by move=> i _; rewrite /f !ffunE /= CexpRX.
  rewrite -(big_tnth _ _ _ xpredT) /f big_filter big_mkcond /=.
  by apply: eq_bigr => i _; case: ifP => [// | /negbFE/eqP ->]; rewrite mul0r.
have ord_p : ((size p).-1 < size p)%N.
  by rewrite -(polySpred (polyMin_neq0 e_alg)).
apply/negP/LindemannBaker.
+ have := (polyMin_neq0 e_alg); rewrite -/p -lead_coef_eq0 lead_coefE => H.
  rewrite size_filter -has_count.
  by apply/hasP; exists (Ordinal ord_p) => //=; rewrite mem_index_enum.
+ move=> i j /eqP; rewrite /alpha !ffunE eqr_nat. 
  rewrite !(tnth_nth (Ordinal ord_p)) /= => /eqP /ord_inj /eqP.
  by rewrite nth_uniq // /t ?enum_uniq // => /eqP /ord_inj //.
+ move=> i; rewrite /alpha ffunE -ratr_nat.
  by apply: algebraic_id.
+ move=> i; rewrite /a ffunE.
  by have := (mem_tnth i (in_tuple t)); rewrite mem_filter => /andP[].
move=> i; rewrite /a ffunE.
have /polyOverP/(_ (tnth (in_tuple t) i)) := (polyMin_over e_alg); rewrite -/p.
move/CintP => [m ->]; rewrite -ratr_int.
by apply: algebraic_id.
Qed.

Theorem e_trans_by_LW :
  ~ (RtoC (Rtrigo_def.exp 1) is_algebraic).
Proof.
have -> : RtoC (Rtrigo_def.exp 1) = Cexp 1 by rewrite Cexp_exp ?real1.
move/ffun1_alg_indep_over; apply.
have -> : (finfun (fun _ : 'I_1 => Cexp 1)) = 
          (finfun (Cexp \o (finfun (fun _ : 'I_1 => 1)))).
  by apply/ffunP => i; rewrite !ffunE /= ffunE.
apply/LindemannWeierstrass.
+ by [].
+ by move=> i; rewrite ffunE; apply/algebraic1.
by apply/ffun1_lin_indep_over/oner_neq0.
Qed.

Theorem e_trans_by_HL :
  ~ (RtoC (Rtrigo_def.exp 1) is_algebraic).
Proof.
have -> : RtoC (Rtrigo_def.exp 1) = Cexp 1 by rewrite Cexp_exp ?real1.
by apply/HermiteLindemann/algebraic1/oner_neq0.
Qed.




(******************************************************************************)
(*                          Transcendence of pi                               *)
(******************************************************************************)

Lemma eiPI_eqm1 : Cexp (RtoC Rtrigo1.PI * 'i) = -1.
Proof.
rewrite /Cexp; RtoC_simpl.
rewrite !mulr0 !mulr1 subr0 addr0 expR0 Rtrigo1.cos_PI Rtrigo1.sin_PI.
by rewrite /= mul1r mulr0 addr0 -!RtoCE.
Qed.

Theorem Pi_trans_by_LB : ~ (RtoC Rtrigo1.PI is_algebraic).
Proof.
suff : ~ (RtoC Rtrigo1.PI * 'i) is_algebraic.
  move=> iPi_nalg Pi_alg; apply: iPi_nalg.
  apply: algebraic_mul => //; exists ('X^2 + 1). 
    by rewrite -size_poly_eq0 size_addl size_polyXn ?size_poly1.
  apply/rootP; rewrite rmorphD  hornerD rmorphX /= map_polyX map_polyC hornerC.
  by rewrite hornerXn /= rmorph1 sqrCi addNr.
move=> iPi_alg.
pose a := (finfun (fun (i : 'I_2) => (1 : complexR))).
pose alpha := (finfun (fun (i : 'I_2) => if (i == ord0) then
   RtoC Rtrigo1.PI * 'i else 0)).
have : Cexp_span a alpha == 0.
  rewrite /Cexp_span big_ord_recl /= big_ord_recl /= big_ord0 addr0 /=.
  by rewrite !ffunE /= !mul1r Cexp0 eiPI_eqm1 addNr.
have Hord2 (j : 'I_2) : (j == ord0) || (j == Ordinal (ltnSn 1)).
  case: j; case => [//= | ]; case => //=.
apply/negP/LindemannBaker => //.
+ move=> i j; apply: contra_eq; move/negbTE; rewrite /alpha !ffunE eq_sym.
  have PI_neq0 : RtoC Rtrigo1.PI * 'i != 0.
    apply/mulf_neq0/neq0Ci/negP; rewrite -RtoCE.
    by move/eqP; apply: Rtrigo1.PI_neq0.
  have /orP[/eqP -> -> //= | /eqP ] := (Hord2 i).
  have /orP[/eqP -> -> /= _ | /eqP -> -> //] := (Hord2 j).
  by rewrite eq_sym.
+ move=> i; have /orP[/eqP -> | /eqP ->] := (Hord2 i); rewrite ffunE /=.
    by apply: iPi_alg.
  by apply: algebraic0.
+ by move=> i; rewrite ffunE /= oner_neq0.
by move=> i; rewrite ffunE /=; apply: algebraic1. 
Qed.

Theorem Pi_trans_by_LW : ~ (RtoC Rtrigo1.PI is_algebraic).
Proof.
suff : ~ (RtoC Rtrigo1.PI * 'i) is_algebraic.
  move=> iPi_nalg Pi_alg; apply: iPi_nalg.
  apply: algebraic_mul => //; exists ('X^2 + 1). 
    by rewrite -size_poly_eq0 size_addl size_polyXn ?size_poly1.
  apply/rootP; rewrite rmorphD  hornerD rmorphX /= map_polyX map_polyC hornerC.
  by rewrite hornerXn /= rmorph1 sqrCi addNr.
move=> ipi_alg.
have /(@ffun1_lin_indep_over Cint) : RtoC Rtrigo1.PI * 'i != 0.
  apply/mulf_neq0/neq0Ci/negP; rewrite -RtoCE.
  by move/eqP; apply: Rtrigo1.PI_neq0.
move/(LindemannWeierstrass (ltnSn _) _).
set alpha := finfun _.
have Halg : (forall i : 'I_1, alpha i is_algebraic).
  by move=> i; rewrite /alpha ffunE; apply: ipi_alg.
move/(_ Halg). 
have -> : (finfun (Cexp \o alpha)) =
          (finfun (fun _ : 'I_1 => Cexp (RtoC Rtrigo1.PI * 'i))).
  by apply/ffunP => i; rewrite /alpha !ffunE /= ffunE.
apply/ffun1_alg_indep_over; rewrite eiPI_eqm1.
by apply/algebraic_opp/algebraic1.
Qed.

Theorem Pi_trans_by_HL : ~ (RtoC Rtrigo1.PI is_algebraic).
Proof.
suff : ~ (RtoC Rtrigo1.PI * 'i) is_algebraic.
  move=> iPi_nalg Pi_alg; apply: iPi_nalg.
  apply: algebraic_mul => //; exists ('X^2 + 1). 
    by rewrite -size_poly_eq0 size_addl size_polyXn ?size_poly1.
  apply/rootP; rewrite rmorphD  hornerD rmorphX /= map_polyX map_polyC hornerC.
  by rewrite hornerXn /= rmorph1 sqrCi addNr.
move/HermiteLindemann; apply.
+ apply/mulf_neq0/neq0Ci/negP; rewrite -RtoCE.
  by move/eqP; apply: Rtrigo1.PI_neq0.
by rewrite eiPI_eqm1; apply/algebraic_opp/algebraic1.
Qed.