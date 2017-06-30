From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
From mathcomp
Require Import bigop finset finfun perm fingroup quotient action morphism ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope group_scope.
Local Open Scope ring_scope.

Section test.

Variable (gT : finGroupType) (G : {group gT}).
Variable (R : ringType) (N n : nat) (X_ : R ^ n).

Lemma ffperm_subproof (s : 'S_n) : 
  injective ((fun x => finfun (x \o (s^-1)%g)) : 'I_N ^ n -> 'I_N ^ n).
Proof.
move=> a b eq_ab; apply/ffunP=> i; have /ffunP /(_ (s i)%g) := eq_ab.
by rewrite !ffunE /= -permM mulgV perm1.
Qed.

Definition ffperm_def s : {perm 'I_N ^ n}:= perm (@ffperm_subproof s).
Lemma ffperm_morphism : {in setT & , {morph ffperm_def : x y / x * y}}%g.
Proof.
move=> s s' _ _; apply/permP => a; do ?rewrite permE /=.
by apply/ffunP=> i; do ?rewrite ffunE /=; rewrite invMg permM.
Qed.

Canonical ffperm := Morphism ffperm_morphism.

Definition symmetrized (a : 'I_N ^ n) (H := [group of 'C[a|<<ffperm>>]]) :=
 \sum_(s : coset_of H) \prod_(i < n) (X_ i) ^+ a (('P %% H)%act i s).

End test.
