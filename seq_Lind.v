From mathcomp Require Import all_ssreflect.
From mathcomp
Require Import ssralg ssrnum mxpoly rat poly ssrint polyorder polydiv perm.
From mathcomp
Require Import finfun.
From structs
Require Import Cstruct Rstruct.
From SsrMultinomials
Require Import finmap order mpoly.
From Lind
Require Import seq_ajouts seq_wlog1 seq_wlog2 seq_wlog3.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.
Import GRing.Theory Num.Theory ArchimedeanTheory Cstruct.ComplexTotalOrder.

Local Notation RtoC := Cstruct.RtoC.
Local Notation Cnat := Cstruct.Cnat.
Local Notation Cint := Cstruct.Cint.

Notation "x 'is_algebraic'" := (algebraicOver QtoC x)
  (at level 55).

Local Notation setZroots := ((set_roots Cint) : 
    complexR -> qualifier 1 {fset complexR}).

Definition lin_indep_over (P : pred_class) {n : nat} (x : complexR ^ n) :=
  forall (lambda : complexR ^ n), lambda \in ffun_on P ->
    lambda != 0 -> \sum_(i < n) (lambda i * x i) != 0.

Definition alg_indep_over (P : pred_class) {n : nat} (x : complexR ^ n) :=
  forall (p : {mpoly complexR[n]}), p \is a mpolyOver _ P ->
    p != 0 -> p.@[x] != 0.


Theorem LindemannBaker : forall (l : nat) (alpha : complexR ^ l) (a : complexR ^ l),
  (0%N < l)%N -> injective alpha -> (forall i : 'I_l, alpha i is_algebraic) ->
  (forall i : 'I_l, a i != 0) -> (forall i : 'I_l, a i is_algebraic) ->
  (Cexp_span a alpha != 0).
Proof.
apply: wlog1_Lindemann.
apply: wlog2_Lindemann.
by apply: Lindemann_last.
Qed.

(* Print Assumptions LindemannBaker. *)

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

Theorem e_trans_by_LW :
  ~ (RtoC (Rtrigo_def.exp 1) is_algebraic).
Proof.
have -> : RtoC (Rtrigo_def.exp 1) = Cexp 1 by rewrite Cexp_exp ?real1.
move=> e_alg.
pose p := polyMin e_alg.
pose t := filter (fun (x : 'I_(size p)) => p`_x != 0) (index_enum (ordinal_finType (size p))).
pose n := size t.
pose alpha := (finfun (fun (i : 'I_n) => (i%:R : complexR))).
pose a := (finfun (fun (i : 'I_n) => p`_i)).
have /eqP : Cexp_span a alpha = 0.
  move/rootP: (polyMin_root e_alg) => <-; rewrite -/p horner_coef -/n.
  rewrite /Cexp_span /alpha /a -/p /n /t.


(*  big_index_uniq; first last. *)
(*     by rewrite filter_uniq // /index_enum -enumT enum_uniq. *)
(*   rewrite big_filter big_mkcond /=. *)
(*   apply/eq_bigr => i _. *)
(*   case: ifP => [pi_neq0 /= | pi_eq0]. *)

(* About insub. *)
(* Print insub. *)
(* Search _ insub. *)

(*   by apply/eq_bigr => i _; rewrite !ffunE CexpRX. *)
(* apply/negP/Lindemann. *)
(* + by rewrite /n lt0n size_poly_eq0 polyMin_neq0. *)
(* + by move=> i j /eqP; rewrite /alpha !ffunE eqr_nat => /eqP /ord_inj. *)
(* + move=> i; rewrite /alpha ffunE -ratr_nat. *)
(*   by apply: algebraic_id. *)
(* + move=> i. *)
(* Search _ algebraicOver. *)

Admitted.

Theorem Pi_trans_by_LW : ~ (RtoC Rtrigo1.PI is_algebraic).
Proof.
suff : ~ ('i * RtoC Rtrigo1.PI) is_algebraic.
  move=> iPi_nalg Pi_alg; apply: iPi_nalg.
  apply: algebraic_mul => //; exists ('X^2 + 1). 
    by rewrite -size_poly_eq0 size_addl size_polyXn ?size_poly1.
  apply/rootP; rewrite rmorphD  hornerD rmorphX /= map_polyX map_polyC hornerC.
  by rewrite hornerXn /= rmorph1 sqrCi addNr.
move=> iPi_alg.
pose a := (finfun (fun (i : 'I_2) => (1 : complexR))).
pose alpha := (finfun (fun (i : 'I_2) => if (nat_of_ord i == 0%N) then
   'i * RtoC Rtrigo1.PI else 0)).
have : Cexp_span a alpha == 0.
  rewrite /Cexp_span big_ord_recl /= big_ord_recl /= big_ord0 addr0 /=.
  rewrite !ffunE /= !mul1r Cexp0 /Cexp; RtoC_simpl.
  rewrite !mulr0 !mul1r mul0r subr0 add0r expR0 Rtrigo1.cos_PI Rtrigo1.sin_PI.
  by rewrite /= mul1r mulr0 addr0 -!RtoCE addNr.
have Hord2 (j : 'I_2) : (j == ord0) || (j == Ordinal (ltnSn 1)). 
  move: (ltn_ord j); rewrite ltnS leq_eqVlt => /orP[/eqP|].
    rewrite -[X in nat_of_ord j = X]/(nat_of_ord (Ordinal (ltnSn 1%N))).
    by move/ord_inj => ->; rewrite /=.
  by rewrite ltnS leqn0 -[0%N]/(nat_of_ord (@ord0 1)) => /eqP/ord_inj ->.
apply/negP/Lindemann => //.
+ apply/uniq_codomP.
  have -> : codom alpha = 'i * RtoC Rtrigo1.PI :: [:: 0].
    apply/(@eq_from_nth _ 0); rewrite ?codomE ?size_map -?enumT ?size_enum_ord.
      by [].
    move=> j ord_j; rewrite -[j]/(nat_of_ord (Ordinal ord_j)).
    have /orP[/eqP -> | /eqP ->] := (Hord2 (Ordinal ord_j)).
      by rewrite (nth_map ord0) ?size_enum_ord // nth_ord_enum ffunE /=.
    by rewrite (nth_map ord0) ?size_enum_ord // nth_ord_enum ffunE /=.
  rewrite /uniq /= andbT inE mulf_neq0 ?neq0Ci //.
  apply/negP; move/eqP; rewrite -[0]RtoCE.
  by move/RtoC_inj/eqP; apply/negP/eqP/Rtrigo1.PI_neq0.
+ move=> i; have /orP[/eqP -> | /eqP ->] := (Hord2 i); rewrite ffunE //=.
  by apply: algebraic0.
+ by move=> i; have /orP[/eqP -> | /eqP ->] := (Hord2 i); 
    rewrite ffunE /= oner_neq0.
move=> i; have /orP[/eqP -> | /eqP ->] := (Hord2 i); rewrite ffunE /=.
  by apply: algebraic1.
by apply: algebraic1. 
Qed.