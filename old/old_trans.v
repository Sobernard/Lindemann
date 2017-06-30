Require Import Rtrigo1.
From mathcomp Require Import all_ssreflect.
From mathcomp
Require Import ssralg ssrnum mxpoly rat poly ssrint polyorder polydiv perm.
From mathcomp
Require Import finfun fingroup complex.
From structs
Require Import Cstruct Rstruct.
From SsrMultinomials
Require Import finmap order mpoly.
From Lind
Require Import seq_ajouts seq_wlog2.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.
Import GRing.Theory Num.Theory ArchimedeanTheory Cstruct.ComplexTotalOrder.

Notation "x 'is_algebraic'" := (algebraicOver QtoC x)
  (at level 55).

Theorem Pi_algebraic : ~ (RtoC PI is_algebraic).
Proof.
suff : ~ ('i * RtoC PI) is_algebraic.
  move=> iPi_nalg Pi_alg; apply: iPi_nalg.
  apply: algebraic_mul => //; exists ('X^2 + 1). 
    by rewrite -size_poly_eq0 size_addl size_polyXn ?size_poly1.
  apply/rootP; rewrite rmorphD  hornerD rmorphX /= map_polyX map_polyC hornerC.
  by rewrite hornerXn /= rmorph1 sqrCi addNr.
move=> iPi_alg.
pose a := (finfun (fun (i : 'I_2) => (1 : complexR))).
pose alpha := (finfun (fun (i : 'I_2) => if (nat_of_ord i == 0%N) then
   'i * RtoC PI else 0)).
have : Cexp_span a alpha == 0.
  rewrite /Cexp_span big_ord_recl /= big_ord_recl /= big_ord0 addr0 /=.
  rewrite !ffunE /= !mul1r Cexp0 /Cexp; RtoC_simpl.
  rewrite !mulr0 !mul1r mul0r subr0 add0r expR0 cos_PI sin_PI /= mul1r mulr0.
  by rewrite addr0 Ropp_opp !rmorphN addNr.
have Hord2 (j : 'I_2) : (j == ord0) || (j == Ordinal (ltnSn 1)). 
  move: (ltn_ord j); rewrite ltnS leq_eqVlt => /orP[/eqP|].
    rewrite -[X in nat_of_ord j = X]/(nat_of_ord (Ordinal (ltnSn 1%N))).
    by move/ord_inj => ->; rewrite /=.
  by rewrite ltnS leqn0 -[0%N]/(nat_of_ord (@ord0 1)) => /eqP/ord_inj ->.
apply/negP/Lindemann => //.
+ apply/uniq_codomP.
  have -> : codom alpha = 'i * RtoC PI :: [:: 0].
    apply/(@eq_from_nth _ 0); rewrite ?codomE ?size_map -?enumT ?size_enum_ord.
      by [].
    move=> j ord_j; rewrite -[j]/(nat_of_ord (Ordinal ord_j)).
    have /orP[/eqP -> | /eqP ->] := (Hord2 (Ordinal ord_j)).
      by rewrite (nth_map ord0) ?size_enum_ord // nth_ord_enum ffunE /=.
    by rewrite (nth_map ord0) ?size_enum_ord // nth_ord_enum ffunE /=.
  rewrite /uniq /= andbT inE mulf_neq0 ?neq0Ci //.
  apply/negP; move/eqP; rewrite -[0]RtoCE.
  by move/RtoC_inj/eqP; apply/negP/eqP/PI_neq0.
+ move=> i; have /orP[/eqP -> | /eqP ->] := (Hord2 i); rewrite ffunE //=.
  by apply: algebraic0.
+ by move=> i; have /orP[/eqP -> | /eqP ->] := (Hord2 i); 
    rewrite ffunE /= oner_neq0.
move=> i; have /orP[/eqP -> | /eqP ->] := (Hord2 i); rewrite ffunE /=.
  by apply: algebraic1.
by apply: algebraic1. 
Qed.


(*
Theorem Lindemann : forall (l : nat) (alpha : complexR ^ l) (a : complexR ^ l),
  (0%N < l)%N -> injective alpha -> (forall i : 'I_l, alpha i is_algebraic) ->
  (forall i : 'I_l, a i != 0) -> (forall i : 'I_l, a i is_algebraic) ->
  (Cexp_span a alpha != 0).
*)



