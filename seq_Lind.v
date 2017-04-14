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

Theorem Lindemann n (alpha : complexR ^ n) :
  (n > 0)%N -> (forall i : 'I_n, alpha i is_algebraic) ->
  (forall (lambda : complexR ^ n), (forall i : 'I_n, lambda i \is a Cint) ->
    (exists i : 'I_n, lambda i != 0) -> \sum_(i < n) (lambda i * alpha i) != 0) ->
  forall P, P \is a mpolyOver _ Cint -> P != 0 -> P.@[finfun (Cexp \o alpha)] != 0.
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
  - by move=> k; rewrite /lambda ffunE /= rpredB // Cint_Cnat // Cnat_nat.
  have := (nth_uniq 0%MM (ltn_ord i) (ltn_ord j) (msupp_uniq P)). 
  rewrite [RHS](inj_eq (@ord_inj _)) => H_neq.
  apply/existsP.
  move: i_neqj; rewrite -H_neq -[msupp P]/(tval (in_tuple _)) -!tnth_nth.
  have H_k k : tnth (in_tuple (msupp P)) k = t k by rewrite /t ffunE /=.
  rewrite !H_k => {H_k}.
  apply: contra_eqT; rewrite negb_exists => /forallP Hx.
  apply/eqP/negP/negPn/eqP/mnmP => k; apply/eqP.
  by move/negPn: (Hx k); rewrite /lambda ffunE /= subr_eq0 eqr_nat.
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
apply: integral_nat.
Qed.