(* --------------------------------------------------------------------
 * (c) Copyright 2014--2015 INRIA.
 *
 * You may distribute this file under the terms of the CeCILL-B license
 * -------------------------------------------------------------------- *)

Require Import Reals.
From Coquelicot Require Import Coquelicot Hierarchy.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype bigop ssralg poly ssrnum ssrint complex.
From Lindemann Require Import Rstruct Cstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.
Import GRing.Theory Num.Theory archi complex ComplexField.




(*
Local Notation RtoC := (complex.ComplexField.real_complex_rmorphism R_rcfType :
           R -> complexR).

Local Notation R2toC := (fun x y : R => (RtoC x) + 'i * (RtoC y)). *)



Section Cprop.

(* Coercion RtoC : R >-> complexR. *)

Lemma Ceq_dec (z1 z2 : complexR) : { z1 = z2 } + { z1 <> z2 }.
Proof.
move: (@eqVneq complexR_eqType z1 z2) => [Heq | Hneq]; first by left.
by right; apply: (@elimN _ (z1 == z2)) => //=; apply: eqP.
Qed.

(*
Definition Crdiv (x y : complexR) := x / y.  
Definition Crsub (x y : complexR) := x - y.

Lemma Cpluscalc x y :
  Cplus x y = (x.1 + y.1, x.2 + y.2).
Proof. by done. Qed.

Lemma Coppcalc x :
  Copp x = (- x.1, -x.2).
Proof. by done. Qed.
*)
End Cprop.

Section Cstruct.

Definition Cr_AbelianGroup_mixin :=
  AbelianGroup.Mixin _ _ _ _
    (@addrC complexR_zmodType) (@addrA complexR_zmodType) 
    (@addr0 complexR_zmodType) (@addrN complexR_zmodType).

Canonical Cr_AbelianGroup :=
  AbelianGroup.Pack complexR Cr_AbelianGroup_mixin complexR.

(* Ring *)
Definition Cr_Ring_mixin :=
  Ring.Mixin _ _ _ (@mulrA complexR_ringType)
   (@mulr1 complexR_ringType) (@mul1r complexR_ringType) 
    (@mulrDl complexR_ringType) (@mulrDr complexR_ringType).

Canonical Cr_Ring :=
  Ring.Pack complexR (Ring.Class _ Cr_AbelianGroup_mixin Cr_Ring_mixin) 
      complexR.

(* Field *)
Lemma Cr_field_theory : 
  field_theory (@GRing.zero complexR_zmodType) (@GRing.one complexR_ringType) 
  (@GRing.add complexR_zmodType) (@GRing.mul complexR_ringType) 
  (fun x y => GRing.add x (GRing.opp y)) (@GRing.opp complexR_zmodType) 
  (fun x y => GRing.mul x (GRing.inv y)) (@GRing.inv complexR_unitRingType) eq.
constructor.
+ constructor.
  - by move=> x; rewrite add0r.
  - by move=> x y; rewrite addrC.
  - by move=> x y z; rewrite addrA.
  - by move=> x; rewrite mul1r.
  - by move=> x y; rewrite mulrC.
  - by move=> x y z; rewrite mulrA.
  - by move=> x y z; rewrite mulrDl.
  - by move=> x y.
  - by move=> x; rewrite addrN.
+ by apply/eqP/oner_neq0.
+ by move=> x y.
by move=> x Hneq0; rewrite mulVf //=; apply/eqP.
Qed.

Add Field Cr_field_field : Cr_field_theory.

(* UniformSpace *)
Definition Cr_ball (x : complexR) (eps : R) (y : complexR) :=
  ball (Re x) eps (Re y) /\ ball (Im x) eps (Im y).

Lemma Cr_ball_center (x : complexR) (eps : posreal) :
  Cr_ball x eps x.
Proof. by split; apply ball_center. Qed.

Lemma Cr_ball_sym (x y : complexR) (eps : R) :
  Cr_ball x eps y -> Cr_ball y eps x.
Proof. by move=> [Hr Hi]; split; apply: ball_sym. Qed.

Lemma Cr_ball_triangle (x y z : complexR) (e1 e2 : R) :
  Cr_ball x e1 y -> Cr_ball y e2 z -> Cr_ball x (e1 + e2) z.
Proof.
move=> [/= H1 H2] [/= H3 H4]; split; rewrite /=.
apply: (ball_triangle _ _ _ _ _ H1 H3).
apply: (ball_triangle _ _ _ _ _ H2 H4).
Qed.

Lemma Cr_ball_le (x : complexR) (e1 e2 : R) :
   Rle e1 e2 -> (forall y : complexR, Cr_ball x e1 y -> Cr_ball x e2 y).
Proof. by move=> H y [/=H1 H2]; split; rewrite /=; apply: (ball_le _ e1). Qed.

Definition Cr_UniformSpace_mixin :=
  UniformSpace.Mixin complexR _ Cr_ball_center Cr_ball_sym 
      Cr_ball_triangle.

Canonical Cr_UniformSpace :=
  UniformSpace.Pack complexR Cr_UniformSpace_mixin complexR.



(* R - ModuleSpace *)(*
Definition Cr_scal (x : R) (u : complexR) :=
  (scal x (Re u)) +i* (scal x (Im u)).

Lemma Cr_scal_assoc (x y : R) (u : complexR) :
  Cr_scal x (Cr_scal y u) = Cr_scal (x * y) u.
Proof.
rewrite /Cr_scal /=; apply/eqP.
by rewrite eq_complex /= !scal_assoc /mult /= !eq_refl.
Qed.

Lemma Cr_scal_one (u : complexR) :
  Cr_scal 1 u = u.
Proof.
rewrite /Cr_scal /=; apply/eqP.
by rewrite eq_complex /= !scal_one !eq_refl.
Qed.

Lemma Cr_scal_distr_l (x : R) (u v : complexR) :
  Cr_scal x (u + v) = (Cr_scal x u) + (Cr_scal x v).
Proof.
rewrite /Cr_scal /=; apply/eqP.
by rewrite eq_complex /= !raddfD /= !scal_distr_l !/plus /= !eq_refl.
Qed.

Lemma Cr_scal_distr_r (x y : R) (u : complexR) :
  Cr_scal (x + y) u = (Cr_scal x u) + (Cr_scal y u).
Proof.
rewrite /Cr_scal /=; apply/eqP.
by rewrite eq_complex /= !scal_distr_r !/plus /= !eq_refl.
Qed.

Definition Cr_R_ModuleSpace_mixin :=
  ModuleSpace.Mixin R_Ring _ _ Cr_scal_assoc Cr_scal_one Cr_scal_distr_l 
     Cr_scal_distr_r.

Canonical Cr_R_ModuleSpace :=
  ModuleSpace.Pack R_Ring complexR (ModuleSpace.Class _ _ _ Cr_R_ModuleSpace_mixin) complexR. *)

Lemma Cr_scal_assoc (x y : R) (u : complexR) :
  x *: (y *: u) = (x * y) *: u.
Proof. by rewrite scalerA. Qed.

Lemma Cr_scal_one (u : complexR) :
  1 *: u = u.
Proof. by rewrite scale1r. Qed.

Lemma Cr_scal_distr_l (x : R) (u v : complexR) :
  x *: (u + v) = (x *: u) + (x *: v).
Proof. by rewrite scalerDr. Qed.

Lemma Cr_scal_distr_r (x y : R) (u : complexR) :
  (x + y) *: u = (x *: u) + (y *: u).
Proof. by rewrite -scalerDl. Qed.

Definition Cr_R_ModuleSpace_mixin :=
  ModuleSpace.Mixin R_Ring _ _ Cr_scal_assoc Cr_scal_one Cr_scal_distr_l 
     Cr_scal_distr_r.

Canonical Cr_R_ModuleSpace :=
  ModuleSpace.Pack R_Ring complexR (ModuleSpace.Class _ _ _ Cr_R_ModuleSpace_mixin) complexR.

(* R - NormedModuleAux *)
Canonical Cr_R_NormedModuleAux :=
  NormedModuleAux.Pack R_AbsRing complexR 
    (NormedModuleAux.Class R_AbsRing _ (ModuleSpace.class _ Cr_R_ModuleSpace) 
      (UniformSpace.class _)) complexR.

Lemma Cr_scalE (x : R) (u : complexR) :
   x *: u = RtoC x * u.
Proof. by rewrite CscaleE. Qed.

(* R - NormedModule *)
(* TODO : move to Rstruct *)
Lemma norm_sqr (x : R) : pow (Hierarchy.norm x) 2 = pow x 2.
Proof.
rewrite /norm /= /abs /= !Rmult_1_r -Rabs_mult Rabs_right //.
by apply/Rle_ge/RleP/sqr_ge0.
Qed.

Lemma Cr_norm_triangle (x y : Cr_R_NormedModuleAux) :
  Rle (norm_R (x + y)) ((norm_R x) + (norm_R y))%R.
Proof. by apply/RleP; have /andP[_]:= (complex.ComplexField.lec_normD x y). Qed.

Lemma Cr_norm_scal (l : R) (x : complexR) :
  Rle (norm_R (l *: x)) (abs l * norm_R x)%R.
Proof.
move: x => [xr xi]; apply/RleP.
rewrite /GRing.scale [_ _ _%C]/= /abs /= -sqrt_Rsqr_abs !RsqrtE ?sqr_ge0 //=.
by rewrite Rsqr_pow2 RpowE -sqrtrM ?sqr_ge0 //= !exprMn mulrDr.
Qed.

Lemma Cr_norm_compat1 (x y : complexR) (eps : R) :
  Rlt (norm_R (y - x)) eps -> ball x eps y.
Proof.
case: x => [xr xi]; case: y => [yr yi] /=; rewrite -RsqrtE; last first.
  by apply/addr_ge0/sqr_ge0/sqr_ge0.
move=> H.
rewrite /ball /= /Cr_ball /=.
move: (prod_norm_compat1 (xr, xi) (yr, yi) eps).
rewrite {1}/ball /= /prod_ball /=; apply.
rewrite /minus /plus /opp /= /prod_plus /=. 
rewrite /plus /= /opp /= !RoppE !RplusE /prod_norm.
by rewrite !norm_sqr /= !RmultE !mulr1 -!expr2.
Qed.

Lemma Cr_norm_compat2 :  forall (x y : complexR) (eps : posreal),
    ball x eps y -> 
  Rlt (norm_R (y - x)) ( (Num.sqrt 2%:R) * eps). 
Proof.
move=> [xr xi] [yr yi] eps.
move: (C_NormedModule_mixin_compat2 (xr, xi) (yr, yi) eps)=>  /= H [ Hr Hi].
move: H; rewrite /ball /= /prod_ball /= => H; move: (H (conj Hr Hi)) =>{H}.
set u := _ ^+ 2 + _ ^+ 2.
have u_ge0 : 0 <= u by rewrite /u addr_ge0 ?sqr_ge0.
rewrite /Cmod /minus /plus /opp /= !RoppE !RplusE !RmultE !mulr1 -!expr2 -/u.
by rewrite -!RsqrtE // ler0n.
Qed.

Lemma  CRmod_eq_0: 
forall x : Cr_R_NormedModuleAux, norm_R x = 0 -> x = zero.
Proof. by move=> x ; apply: complex.ComplexField.eq0_normc. Qed.

Definition Cr_R_NormedModule_mixin :=
  NormedModule.Mixin R_AbsRing _ _ _ Cr_norm_triangle
  Cr_norm_scal Cr_norm_compat1 Cr_norm_compat2 CRmod_eq_0.

Canonical Cr_R_NormedModule :=
  NormedModule.Pack R_AbsRing complexR 
    (NormedModule.Class R_AbsRing complexR _ Cr_R_NormedModule_mixin) complexR.

(* TODO : utility ? 
Lemma normM (z1 z2 : complexR) : norm (z1 * z2) = norm z1 * norm z2.
Proof. by rewrite /norm /= complex.ComplexField.normcM. Qed. *)

(* inequalities on norms *)

Lemma norm_Re (x : complexR) : (norm (Re x)) <= (norm x).
Proof.
rewrite /norm /=; case x => xr xi /=.
move: (sqrt_plus_sqr (Rabs xr) (Rabs xi)).
rewrite !RPow_abs !RpowE !Rabs_Rabsolu.
rewrite !(Rabs_right (_ ^+ 2)); try by apply/Rle_ge/RleP/sqr_ge0.
rewrite RplusE -RsqrtE; first move => /= [/RleP H _].
  by apply: ler_trans H; apply/RleP/Rmax_l.
by apply:addr_ge0; apply: sqr_ge0.
Qed.

Lemma norm_Im (x : complexR) : (norm (Im x)) <= (norm x).
Proof.
rewrite /norm /=; case x => xr xi /=.
move: (sqrt_plus_sqr (Rabs xr) (Rabs xi)).
rewrite !RPow_abs !RpowE !Rabs_Rabsolu.
rewrite !(Rabs_right (_ ^+ 2)); try by apply/Rle_ge/RleP/sqr_ge0.
rewrite RplusE -RsqrtE; first move => /= [/RleP H _].
  by apply: ler_trans H; apply/RleP/Rmax_r.
by apply:addr_ge0; apply: sqr_ge0.
Qed.

Lemma norm_ReIm (x : complexR) :
    (norm x) <= (norm (Re x)) + (norm (Im x)).
Proof.
rewrite /norm /=; case x => xr xi /=.
move: (Cmod_triangle (Rabs xr,0) (0,Rabs xi)).
rewrite /Cmod /= !RmultE !RplusE !mulr1 mulr0 !addr0 !add0r => /RleP.
rewrite !sqrt_Rsqr_abs !Rabs_Rabsolu; apply: ler_trans.
have h : forall x , Rmult x x = x ^+ 2.
  by move => x'; rewrite RmultE !exprS expr0 mulr1.
  rewrite -!RmultE -!Rabs_mult !Rabs_right ?h; try apply/Rle_ge/RleP/sqr_ge0.
by rewrite RsqrtE ?lerr // addr_ge0 // sqr_ge0.
Qed.

Lemma normM (x y : complexR) :
  norm (x * y) = norm x * norm y.
Proof.
by rewrite /norm /= complex.ComplexField.normcM.
Qed.

Lemma norm_morph : {morph (norm : complexR -> R) : x y / x * y >-> x * y}.
Proof. by move=> x y; rewrite normM. Qed.


End Cstruct.

(**** * Functions R -> complexR * ****)

Section Ccont.

(**** * Limits * ****)

Definition is_Crlim (f : R -> complexR) (z : R ) (l : complexR) :=
  filterlim f (locally' z) (locally l).

Definition is_Crlim_C (f : R -> complexR) (z : R ) (l : complexR) :=
  filterlim (fun x => Re (f x)) (locally' z) (locally (Re l)) /\
  filterlim (fun x => Im (f x)) (locally' z) (locally (Im l)).

Lemma is_Crlim_C_eq f z l :
  is_Crlim f z l <-> is_Crlim_C f z l.
Proof.
rewrite /is_Crlim /is_Crlim_C !filterlim_locally.
rewrite /locally' /locally /within; split.
  by move=> H; split; move=> eps; move: (H eps) => {H} [del H]; 
    exists del => y Hball Hneq; move: (H y Hball Hneq) => [H1 H2].
move=> [Hr Hi] eps. 
move: (Hr eps) => {Hr} [epsR Hr]; move: (Hi eps) => {Hi} [epsI Hi].
move: (Rmin_l epsR epsI) (Rmin_r epsR epsI); set mm:= Rmin epsR epsI.
set m:= (mkposreal mm (Rmin_stable_in_posreal epsR epsI)) => minre minim.
exists m; move=> y Hball Hneq; rewrite /ball /= /Cr_ball; split.
  by apply: Hr => //; apply: (ball_le _ _ _ minre).
by apply: Hi => //; apply: (ball_le _ _ _ minim).
Qed.

Definition ex_Crlim (f : R -> complexR) (z : R) :=
  exists (l : complexR), is_Crlim f z l.

Definition Cr_limseq (u : nat -> complexR) : complexR :=
  RtoC (real (Lim_seq (fun n => Re (u n)))) + 'i *
  RtoC (real (Lim_seq (fun n => Im (u n)))).

Definition Cr_lim (f : R -> complexR) (z : R) : complexR :=
  RtoC (real (Lim (fun x => Re (f x)) z)) + 'i *
  RtoC (real (Lim (fun x => Im (f x)) z)).

Lemma is_Crlim_C_unique (f : R -> complexR) (z : R) (l : complexR) :
  is_Crlim_C f z l -> Cr_lim f z = l.
Proof.
rewrite /is_Crlim_C /Cr_lim; move=> [Hre Him].
have -> : Lim (fun x : R => Re (f x)) z = Re l by apply: is_lim_unique.
have -> : Lim (fun x : R => Im (f x)) z = Im l by apply: is_lim_unique.
by rewrite /= complex.complexRe complex.complexIm -Crect.
Qed.

Lemma is_Crlim_unique (f : R -> complexR) (z : R) (l : complexR) :
  is_Crlim f z l -> Cr_lim f z = l.
Proof.
by rewrite is_Crlim_C_eq; apply: is_Crlim_C_unique.
Qed.

Lemma Lim_add f a (x : R) :
  Lim (fun y => f (a + y)) x = Lim f (a + x).
Proof.
rewrite /Lim; apply: Lim_seq_ext; move=> n.
have -> // :  (a + Rbar_loc_seq x n) =  (Rbar_loc_seq (a + x) n).
by rewrite /Rbar_loc_seq !RplusE addrA.
Qed.

Lemma Lim_bis f g (x : R) :
  (forall y, y != x -> f y = g y) -> 
  Lim f x = Lim g x.
Proof.
move=> Heq; rewrite /Lim; apply: Lim_seq_ext; move=> n.
apply: Heq; rewrite /Rbar_loc_seq RplusE eq_sym addrC.
rewrite -subr_eq subrr eq_sym; apply: (introN eqP).
apply: Rinv_neq_0_compat; rewrite -S_INR.
by apply: not_0_INR; apply: (elimN eqP); rewrite -lt0n; apply: ltn0Sn.
Qed.

(**** * Continuity * ****)

Definition Crcontinuity_pt (f : R -> complexR) (x : R) :=
  is_Crlim f x (f x).

Lemma Crcontinuity_pt_filterlim' f x :
  Crcontinuity_pt f x <-> filterlim f (locally' x) (locally (f x)).
Proof. by rewrite/Crcontinuity_pt /is_Crlim. Qed.

Lemma is_Crlim_continuity (f : R -> complexR) (x : R) :
  Crcontinuity_pt f x -> is_Crlim f x (f x).
Proof. by done. Qed.

Lemma ex_Crlim_continuity (f : R -> complexR) (x : R) :
  Crcontinuity_pt f x -> ex_Crlim f x.
Proof. by move=> H; exists (f x). Qed.

Lemma Lim_continuity (f : R -> complexR) (x : R) :
  Crcontinuity_pt f x -> Cr_lim f x = f x.
Proof. by move/is_Crlim_continuity => H; apply: is_Crlim_unique. Qed.

Lemma Crcontinuity_pt_ReIm (f : R -> complexR) (x : R) :
  Crcontinuity_pt f x ->
    continuity_pt (fun y => Re (f y)) x /\
    continuity_pt (fun y => Im (f y)) x.
Proof. by move/is_Crlim_C_eq; rewrite !continuity_pt_filterlim'. Qed.

Lemma Crcontinuity_pt_R (f : R -> complexR) (x : R) :
    continuity_pt (fun y => Re (f y)) x /\
    continuity_pt (fun y => Im (f y)) x ->
    Crcontinuity_pt f x.
Proof. by rewrite !continuity_pt_filterlim' /Crcontinuity_pt is_Crlim_C_eq. Qed.

Lemma Crcontinuity_pt_filterlim f x :
  Crcontinuity_pt f x -> filterlim f (locally x) (locally (f x)).
Proof.
move/Crcontinuity_pt_ReIm => [].
move/continuity_pt_filterlim => Hr; move/continuity_pt_filterlim => Hi.
move: Hr Hi; rewrite !filterlim_locally /locally; move=> Hr Hi eps.
move: (Hr eps) => {Hr} [epsR Hr]; move: (Hi eps) => {Hi} [epsI Hi].
move: (Rmin_l epsR epsI) (Rmin_r epsR epsI); set mm:= Rmin epsR epsI.
set m:= (mkposreal mm (Rmin_stable_in_posreal epsR epsI)) => minre minim.
exists m; move=> y Hball; rewrite /ball /= /Cr_ball; split.
  by apply: Hr => //; apply: (ball_le _ _ _ minre).
by apply: Hi => //; apply: (ball_le _ _ _ minim).
Qed.

(**** * Properties of Crcontinuity_pt * ****)

Lemma Crcontinuity_pt_ext f g (x : R) :
  (forall x0 : R, f x0 = g x0) -> 
  Crcontinuity_pt f x -> Crcontinuity_pt g x.
Proof.
move=> Heq /Crcontinuity_pt_ReIm [Hfr Hfi].
apply: Crcontinuity_pt_R; split.
  apply: (continuity_pt_ext _ _ _ _ Hfr).
  by move=> u; rewrite Heq.
apply: (continuity_pt_ext _ _ _ _ Hfi).
by move=> u; rewrite (Heq u).
Qed.

Lemma Crcontinuity_pt_idR (x : R) :
  Crcontinuity_pt (fun y => RtoC y) x.
Proof.
apply: Crcontinuity_pt_R; split.
  apply: (continuity_pt_ext (fun y : R => y) _ x _ (continuity_pt_id x)).
  by move=> y.
apply: (continuity_pt_ext (fun y : R => 0) _ x); first by move=> y.
by apply: continuity_pt_const; move=> u v.
Qed.

Lemma Crcontinuity_pt_const a (x : R) :
  Crcontinuity_pt (fun y => a) x.
Proof.
case: a => r i; apply: Crcontinuity_pt_R; split.
  by apply: continuity_pt_const; move=> u v.
by apply: continuity_pt_const; move=> u v.
Qed.

Lemma Crcontinuity_pt_complex f g (x : R) :
  continuity_pt f x -> continuity_pt g x ->
  Crcontinuity_pt (fun y => RtoC (f y) + 'i * RtoC (g y)) x.
Proof.
move=> Hr Hi; apply: Crcontinuity_pt_R; split.
  apply: (continuity_pt_ext _ _ _ _ Hr).
  by move=> u /=; rewrite mulr0 mul0r subr0 addr0.
apply: (continuity_pt_ext _ _ _ _ Hi).
by move=> u /=; rewrite mul0r !add0r mul1r.
Qed.

(* Maybe add Crcontinuity_pt (fun y => (f y)%:C) and the same for 0+i*(f y),
  but can be proved in one line *)

Lemma Crcontinuity_pt_add f g (x : R) :
  Crcontinuity_pt f x -> Crcontinuity_pt g x ->
  Crcontinuity_pt (fun y => f y + g y) x.
Proof.
move=> /Crcontinuity_pt_ReIm [Hfr Hfi] /Crcontinuity_pt_ReIm [Hgr Hgi].
apply: Crcontinuity_pt_R; split.
  apply: (continuity_pt_ext (plus_fct (fun y => Re (f y)) (fun y => Re (g y)))).
    by move=> u; rewrite /plus_fct RplusE raddfD /=.
  by apply: continuity_pt_plus.
apply: (continuity_pt_ext (plus_fct (fun y => Im (f y)) (fun y => Im (g y)))).
  by move=> u; rewrite /plus_fct RplusE raddfD.
by apply: continuity_pt_plus.
Qed.

Lemma Crcontinuity_pt_opp f (x : R) :
  Crcontinuity_pt f x -> 
  Crcontinuity_pt (fun y => - f y) x.
Proof.
move=> /Crcontinuity_pt_ReIm [Hfr Hfi].
apply: Crcontinuity_pt_R; split.
  apply: (continuity_pt_ext (opp_fct (fun y => Re (f y)))).
    by move=> u; rewrite raddfN.
  by apply: continuity_pt_opp.
apply: (continuity_pt_ext (opp_fct (fun y => Im (f y)))).
  by move=> u; rewrite raddfN.
by apply: continuity_pt_opp.
Qed.

Lemma Crcontinuity_pt_mul f g (x : R) :
  Crcontinuity_pt f x -> Crcontinuity_pt g x ->
  Crcontinuity_pt (fun y => (f y) * (g y)) x.
Proof.
move=> /Crcontinuity_pt_ReIm [Hfr Hfi] /Crcontinuity_pt_ReIm [Hgr Hgi].
apply: (@Crcontinuity_pt_ext (fun y =>   
    ((RtoC (Re (f y) * Re (g y)) + 'i * RtoC (Re (f y) * Im (g y))) +
    (RtoC ((- Im (f y)) * Im (g y)) + 'i * RtoC (Im (f y) * Re (g y)))))).
  move=> u /=; rewrite !rmorphM rmorphN /= !complexRe !complexIm.
  rewrite [(f u) in RHS]Crect [(g u) in RHS]Crect mulC_rect /= mulrDr.
  rewrite addrACA addrA addrA.
  by congr (_ + _ + _); rewrite ?mulNr // (mulrC ('Im (f u))).
apply/Crcontinuity_pt_add.
  by apply/Crcontinuity_pt_complex; apply: continuity_pt_mult.
apply: Crcontinuity_pt_complex; last by apply: continuity_pt_mult.   
apply: (continuity_pt_ext (mult_fct
      (opp_fct (fun y => Im (f y))) (fun y => Im (g y)))) => //.
by apply: continuity_pt_mult => //; apply: continuity_pt_opp.  
Qed. 

Lemma Crcontinuity_pt_poly (P : {poly complexR}) (a : complexR) x :
  Crcontinuity_pt (fun y => P.[y *: a]) x.
Proof.
elim/poly_ind: P => [|Q c ihQ].
  apply: (@Crcontinuity_pt_ext (fun y => RtoC 0)).
    by move=> u /=; rewrite horner0.
  by apply: Crcontinuity_pt_const.
apply: (@Crcontinuity_pt_ext (fun y => (Q.[y *: a] * (RtoC y * a)) + c)).
  by move=> u /=; rewrite hornerMXaddC Cr_scalE.
apply: Crcontinuity_pt_add; last by apply/Crcontinuity_pt_const.
apply: Crcontinuity_pt_mul; first exact ihQ.
apply: Crcontinuity_pt_mul; first by apply: Crcontinuity_pt_idR.
by apply: Crcontinuity_pt_const.
Qed.

Lemma Crcontinuity_pt_exp (a : complexR) (x : R) :
  Crcontinuity_pt (fun y => Cexp(y *: a)) x.
Proof.
apply: (@Crcontinuity_pt_ext (fun y => (RtoC (exp ((Re a) * y))) 
          * (RtoC (cos((Im a)*y)) + 'i * RtoC(sin((Im a)*y)) ))).
  move=> u; rewrite /Cexp /= ![_ * RtoC _]mulrC -!Cr_scalE !scalarZ /=.
  by rewrite [_ * Im _]mulrC [_ * Re _]mulrC.
apply/Crcontinuity_pt_mul; last first.
  apply/Crcontinuity_pt_complex; apply/continuity_pt_comp. 
  + apply/continuity_pt_mult; first by apply/continuity_pt_const.    
    by apply/continuity_pt_id.   
  + by apply/derivable_continuous_pt/derivable_pt_cos.
  + apply/continuity_pt_mult; first by apply/continuity_pt_const.    
    by apply/continuity_pt_id.   
  + by apply/derivable_continuous_pt/derivable_pt_sin.
apply/Crcontinuity_pt_R; split. 
  apply/continuity_pt_comp.
  + apply/continuity_pt_mult; first by apply/continuity_pt_const.
    by apply: continuity_pt_id.
  + by apply/derivable_continuous_pt/derivable_pt_exp.
by apply/(continuity_pt_ext (fun y : R => 0) _ x _ (continuity_pt_const _ x _)).
Qed.

End Ccont.

Section Cderiv.

(**** * Derivability * ****)

Definition is_Crderive_C (f : R -> complexR) (z : R) (l : complexR) :=
  is_derive (fun x => Re (f x)) z (Re l) /\
  is_derive (fun x => Im (f x)) z (Im l).

Lemma is_Crderive_C_eq (f : R_NormedModule -> Cr_R_NormedModule) z l :
  is_derive f z l <-> is_Crderive_C f z l.
Proof.
have Hr_Re x y : (minus (minus (Re (f y)) (Re (f x))) (scal (minus y x) (Re l))) 
  = Re ( (minus (minus (f y) (f x)) (scal (minus y x) l) ) ).    
  rewrite /minus /plus /opp /= !raddfB /= !RplusE !RoppE.
  by congr (_ - _ - _); rewrite /scal /= scalarZ.
have Hr_Im x y : (minus (minus (Im (f y)) (Im (f x))) (scal (minus y x) (Im l))) 
  = Im ( (minus (minus (f y) (f x)) (scal (minus y x) l) ) ).    
  rewrite /minus /plus /opp /= !raddfB /= !RplusE !RoppE.
  by congr (_ - _ - _); rewrite /scal /= scalarZ.
rewrite /is_Crderive_C /is_derive /filterdiff; split.
  move=> [Ha Hb]; split; split; try apply: is_linear_scal_l; move=> x Hx;
    rewrite /Equiv.is_domin /locally => eps;
    move: (Hb x Hx eps) => {Hb} [delta Hb]; exists delta => y Hball;
    move: (Hb y Hball) => /= {Hb} /RleP Hb.
    by rewrite Hr_Re; apply/RleP; apply: (ler_trans (norm_Re _) Hb).
  by rewrite Hr_Im; apply/RleP; apply: (ler_trans (norm_Im _) Hb).
move=> [[Hlre Hre] [Hlim Him]]; split; first by apply: is_linear_scal_l.
move=> x Hx {Hlre} {Hlim}.
rewrite /Equiv.is_domin /locally => eps.
set mu := (mkposreal (Rdiv eps 2) (is_pos_div_2 eps)).
move: (Hre x Hx mu) => {Hre} [deltare Hre].
move: (Him x Hx mu) => {Him} [deltaim Him].
move: (Rmin_l deltare deltaim) (Rmin_r deltare deltaim).
set mm:= Rmin deltare deltaim.
set m:= (mkposreal mm (Rmin_stable_in_posreal deltare deltaim)) => minre minim.
exists m; move=> y Hball.
have Hr : ball z deltare y by apply: (ball_le _ m).
have Hi : ball z deltaim y by apply: (ball_le _ m).
move: (Hre y Hr) => /= {Hr}; rewrite Hr_Re.
move: (Him y Hi) => /= {Hi}; rewrite Hr_Im.
move=> /RleP Hr /RleP Hi; apply/RleP.
apply: (ler_trans (norm_ReIm _)).
suff -> :  (Rmult (pos eps)  (norm (minus y x))) =
     (Rmult ((pos eps)/2) (norm (minus y x))) + 
     (Rmult ((pos eps)/2) (norm (minus y x))) by apply: (ler_add Hi Hr).
by rewrite !RmultE -mulrDl -RplusE -double_var.
Qed.

Definition ex_Crderive_C (f : R -> complexR) (z : R) :=
  exists l : complexR, is_Crderive_C f z l.

Lemma ex_Crderive_C_eq (f : R_NormedModule -> Cr_R_NormedModule) z :
  ex_derive f z <-> ex_Crderive_C f z.
Proof. by split; move=> [l H]; exists l; apply/is_Crderive_C_eq. Qed.

Lemma ex_Crderive_ReIm (f : R_NormedModule -> Cr_R_NormedModule) z :
  ex_derive f z ->
    ex_derive (fun x => Re (f x)) z /\
    ex_derive (fun x => Im (f x)) z.
Proof.
rewrite ex_Crderive_C_eq /ex_Crderive_C /is_Crderive_C.
move=> [l [Hr Hi]]; split.
  by exists (Re l).
by exists (Im l).
Qed.


(**** * Derived function * ****)

Definition Crderive (f : R -> complexR) (z : R) := 
  Cr_lim (fun x =>  (f x - f z) / RtoC (x - z)) z.

Definition Crderive_C (f : R -> complexR) (z : R) : complexR :=
  RtoC (Derive (fun x => Re (f x)) z) + 'i *
  RtoC (Derive (fun x => Im (f x)) z).

Lemma Crderive_C_eq f z :
  Crderive f z = Crderive_C f z.
Proof.
rewrite /Crderive /Crderive_C /Cr_lim.
apply/eqP; rewrite eq_complex /=; apply/andP; split; 
apply/eqP; rewrite /Derive.
  rewrite (@Lim_bis _ (fun h : R => 
     Re (    (f (z + h) - (f z) ) / (RtoC (z + h - z))  ))  (Finite 0)).
    by rewrite !mul0r mulr0 subrr !addr0 -{3}[z]addr0 -Lim_add.
  move=> y Hy.
  rewrite {2}[z + y]addrC -addrA subrr addr0.
  rewrite /Rminus !RplusE !RoppE RdivE // -raddfB/=.
  case:  (f (z + y) - f z) => r i.
  rewrite /= expr0n /= addr0 mul0r mulrN mulr0 opprK addr0.
  by rewrite expr2 mulrA -mulf_div divrr // mulr1.
rewrite (@Lim_bis _ (fun h : R => 
     Im (    (f (z + h) - (f z) ) / (RtoC (z + h - z))  ))  (Finite 0)).
  by rewrite -{3}[z]addr0 -Lim_add.
move=> y Hy.
rewrite {2}[z + y]addrC -addrA subrr addr0.
rewrite /Rminus !RplusE !RoppE RdivE // -raddfB/=.
case:  (f (z + y) - f z) => r i.
rewrite /= expr0n /= addr0 mul0r mulrN mulr0 oppr0 add0r.
by rewrite expr2 mulrA -mulf_div divrr // mulr1.
Qed.

Lemma is_Crderive_C_unique 
   (f : R_NormedModule -> Cr_R_NormedModule) (z : R) (l : complexR) :
  is_Crderive_C f z l -> Crderive_C f z = l.
Proof.
rewrite /Crderive_C; move => [Hre Him]; apply/eqP; rewrite eq_complex.
apply/andP; split; apply/eqP; rewrite /= !mul0r mul1r !add0r ?subr0. 
  by apply: is_derive_unique.
by apply: is_derive_unique.
Qed.

Lemma is_Crderive_unique 
   (f : R_NormedModule -> Cr_R_NormedModule) (z : R) (l : complexR) :
  is_derive f z l -> Crderive f z = l.
Proof.
rewrite is_Crderive_C_eq; move/is_Crderive_C_unique => <-.
by apply: Crderive_C_eq.
Qed.

Lemma Crderive_correct (f : R_NormedModule -> Cr_R_NormedModule) x :
  ex_derive f x -> is_derive f x (Crderive f x).
Proof.
move=> [l H].
by have -> : (Crderive f x = l) by apply is_Crderive_unique.
Qed.

(**** * Properties of derivative * ****)

Lemma Crderive_ext f g (x : R) :
  (forall x0 : R, f x0 = g x0) -> 
  Crderive f x = Crderive g x.
Proof.
move=> Heq; rewrite /Crderive /Cr_lim.
apply/eqP; rewrite eq_complex /= !mul0r mulr0 subr0 !addr0 !add0r !mul1r.
apply/andP; split; apply/eqP.
  move: (Lim_ext   (fun x0 : R => Re ((g x0 - g x) / RtoC (x0 - x)))
  (fun x0 : R => Re ((f x0 - f x) / RtoC (x0 - x))) x) => H.
  by rewrite H //; move=> y; rewrite !Heq.
move: (Lim_ext   (fun x0 : R => Im ((g x0 - g x) / RtoC (x0 - x)))
  (fun x0 : R => Im ((f x0 - f x) / RtoC (x0 - x))) x) => H.
by rewrite H //; move=> y; rewrite !Heq.
Qed.

Lemma is_Crderive_RtoC f l (x : R) :
  is_derive f x l -> 
  is_derive (fun y => RtoC (f y) : Cr_R_NormedModule) x (RtoC l).
Proof.
move=> Hf; rewrite is_Crderive_C_eq /is_Crderive_C /=; split; first by [].
by apply/is_derive_const.
Qed.

Lemma ex_Crderive_RtoC f (x : R) :
  ex_derive f x -> 
  ex_derive (fun y => RtoC (f y) : Cr_R_NormedModule) x.
Proof.
move=> [l Hl]; rewrite ex_Crderive_C_eq /ex_Crderive_C.
exists (RtoC l); rewrite -is_Crderive_C_eq.
by apply: is_Crderive_RtoC.
Qed.

Lemma Crderive_RtoC f (x : R) :
  ex_derive f x ->
  Crderive (fun y => RtoC (f y)) x = (RtoC (Derive f x)).
Proof.
move=> Hf.
rewrite Crderive_C_eq /Crderive_C -[RHS]addr0 -[in RHS](mulr0 'i) -RtoCE.
by congr (_ + 'i * RtoC _); rewrite (Derive_ext _ (fun y => 0)) // Derive_const.
Qed.

(*
Lemma is_Crderive_complex f g lr li (x : R) :
  is_derive f x lr -> is_derive g x li ->
  is_derive (fun y => (RtoC (f y) + 'i * RtoC (g y)) : Cr_R_NormedModule) 
     x (RtoC lr + 'i * RtoC li) .
Proof.
move=> Hr Hi; rewrite is_Crderive_C_eq /is_Crderive_C /=.
  rewrite !mulr0 !mul0r !subr0 !add0r mul1r addr0; split.
  by apply: (is_derive_ext _ _ _ _ _ Hr) => y; rewrite mul0r subr0 addr0.
by apply: (is_derive_ext _ _ _ _ _ Hi) => y; rewrite mul1r !add0r.
Qed.

Lemma ex_Crderive_complex f g (x : R) :
  ex_derive f x -> ex_derive g x ->
  ex_derive (fun y => (f y +i* g y) : Cr_R_NormedModule) x.
Proof.
move=> [lr Hr] [li Hi]; rewrite ex_Crderive_C_eq /ex_Crderive_C.
exists (lr +i* li); rewrite -is_Crderive_C_eq.
by apply: is_Crderive_complex.
Qed.

Lemma Crderive_complexb f g lr li (x : R) :
  Derive f x = lr -> Derive g x = li ->
  Crderive (fun y => f y +i* g y) x = lr+i*li.
Proof.
move=> Hr Hi.
by rewrite Crderive_C_eq /Crderive_C Hr Hi.
Qed.

Lemma Crderive_complex f g x :
  Crderive (fun y => f y +i* g y) x = Derive f x +i* Derive g x .
Proof. by apply: Crderive_complexb. Qed.*)

Lemma Crderive_const a x:
  Crderive (fun _ => a) x = 0.
Proof. by apply: is_Crderive_unique; apply: is_derive_const. Qed.

Lemma is_Crderive_idR x :
  is_derive (RtoC : R_NormedModule -> Cr_R_NormedModule) x 1.
Proof.
rewrite is_Crderive_C_eq /is_Crderive_C; split.
  by apply: (is_derive_ext (fun t => t)); try apply: is_derive_id.
by apply: (is_derive_ext (fun _ => R0)); try apply: is_derive_const.
Qed.

Lemma ex_Crderive_idR x :
  ex_derive (RtoC : R_NormedModule -> Cr_R_NormedModule) x.
Proof. by exists 1; apply: (is_Crderive_idR x). Qed.

Lemma Crderive_idR x:
  Crderive RtoC x = 1.
Proof. by apply: is_Crderive_unique; apply: is_Crderive_idR. Qed.

(* The results on opp/add are not really important, 
   but thanks to them the rewriting of Ropp/Radd is done *)

Lemma is_CrderiveN (f : R_NormedModule -> Cr_R_NormedModule) x l :
  is_derive f x l ->
  is_derive (fun x => GRing.opp (f x) : Cr_R_NormedModule) x (- l).
Proof. exact: is_derive_opp. Qed.

Lemma ex_CrderiveN (f : R_NormedModule -> Cr_R_NormedModule) x :
  ex_derive f x ->
  ex_derive (fun x => GRing.opp (f x) : Cr_R_NormedModule) x.
Proof. by apply: ex_derive_opp. Qed.

Lemma CrderiveN (f : R_NormedModule -> Cr_R_NormedModule) x :
  ex_derive f x ->
  Crderive (fun x => GRing.opp (f x)) x = - Crderive f x.
Proof.
move=> H; apply: is_Crderive_unique.
by apply: is_CrderiveN; apply: Crderive_correct.
Qed.

Lemma is_CrderiveD (f : R_NormedModule -> Cr_R_NormedModule) 
  (g : R_NormedModule -> Cr_R_NormedModule) x lf lg :
  is_derive f x lf -> is_derive g x lg ->
  is_derive (fun x => GRing.add (f x) (g x) : Cr_R_NormedModule) x (lf + lg).
Proof. exact: is_derive_plus. Qed.

Lemma ex_CrderiveD (f : R_NormedModule -> Cr_R_NormedModule) 
  (g : R_NormedModule -> Cr_R_NormedModule) x :
  ex_derive f x -> ex_derive g x ->
  ex_derive (fun x => GRing.add (f x) (g x) : Cr_R_NormedModule) x.
Proof. exact: ex_derive_plus. Qed.

Lemma CrderiveD (f : R_NormedModule -> Cr_R_NormedModule) 
  (g : R_NormedModule -> Cr_R_NormedModule) x :
  ex_derive f x -> ex_derive g x ->
  Crderive (fun x => (f x) + (g x)) x = Crderive f x + Crderive g x.
Proof.
move=> ex_f ex_g; apply: is_Crderive_unique.
by apply: is_CrderiveD; apply: Crderive_correct.
Qed.  

Lemma is_CrderiveB (f : R_NormedModule -> Cr_R_NormedModule) 
  (g : R_NormedModule -> Cr_R_NormedModule) x lf lg :
  is_derive f x lf -> is_derive g x lg ->
  is_derive (fun x => (f x) - (g x) : Cr_R_NormedModule) x (lf - lg).
Proof. exact: is_derive_minus. Qed.

Lemma ex_CrderiveB  (f : R_NormedModule -> Cr_R_NormedModule) 
  (g : R_NormedModule -> Cr_R_NormedModule) x :
  ex_derive f x -> ex_derive g x ->
  ex_derive (fun x => (f x) - (g x) : Cr_R_NormedModule) x.
Proof. exact: ex_derive_minus. Qed.

Lemma CrderiveB (f : R_NormedModule -> Cr_R_NormedModule) 
  (g : R_NormedModule -> Cr_R_NormedModule) x :
  ex_derive f x -> ex_derive g x ->
  Crderive (fun x => (f x) - (g x)) x = Crderive f x - Crderive g x.
Proof.
move=> ex_f ex_g; apply: is_Crderive_unique.
by apply: is_CrderiveB; apply: Crderive_correct.
Qed.  

(* scal is here seen as k * x with k a complexR instead of R *)
Lemma is_CrderiveZ (f : R_NormedModule -> Cr_R_NormedModule) x k l :
  is_derive f x l ->
  is_derive (fun x => k * (f x) : Cr_R_NormedModule) x (k * l).
Proof.
rewrite !is_Crderive_C_eq /is_Crderive_C. 
move=> [Hr Hi]; rewrite [k]complexE /= mulrDl !raddfD ['i * _]mulrC /=.
rewrite -!Cr_scalE -scalerAl !linearZ /= -['i * _]mulrC ImiRe ReiNIm; split.
  apply: (is_derive_ext (fun x : R_NormedModule => (Rmult (Re k) (Re (f x))) -
       (Rmult (Im k) (Im (f x))) : R_NormedModule)).
    move=> t; rewrite [(f t)]complexE /= mulrDl !mulr0 !mul0r !subr0 !add0r.
    by rewrite !mul1r !mulr1 !addr0 !RmultE.
  by rewrite mulrN -RmultE; apply/is_derive_minus; apply/is_derive_scal.
apply: (is_derive_ext (fun x : R_NormedModule => (Rmult (Re k) (Im (f x))) +
       (Rmult (Im k) (Re (f x))) : R_NormedModule)).
  move=> t; rewrite [(f t)]complexE /= mulrDl !mulr0 !mul0r !subr0 !add0r.
  by rewrite !mul1r !mulr1 !addr0 !RmultE.
by rewrite -RmultE; apply/is_derive_plus; apply/is_derive_scal.
Qed.

Lemma ex_CrderiveZ (f : R_NormedModule -> Cr_R_NormedModule) x k :
  ex_derive f x ->
  ex_derive (fun x => k * (f x) : Cr_R_NormedModule) x.
Proof. by move=> [lf Hf]; exists (k * lf); apply: is_CrderiveZ. Qed.

Lemma CrderiveZ (f : R_NormedModule -> Cr_R_NormedModule) x k :
  ex_derive f x ->
  Crderive (fun x => k * (f x)) x = k * Crderive f x.
Proof.
move=> ex_f; apply: is_Crderive_unique.
by apply: is_CrderiveZ; apply: Crderive_correct.
Qed.

Lemma is_CrderiveM (f : R_NormedModule -> Cr_R_NormedModule) 
  (g : R_NormedModule -> Cr_R_NormedModule) x lf lg :
  is_derive f x lf -> is_derive g x lg ->
  is_derive (fun x => (f x) * (g x) : Cr_R_NormedModule) x 
         (lf * (g x) + (f x) * lg).
Proof.
rewrite !is_Crderive_C_eq /is_Crderive_C. move=> [/= Hfr Hfi] [/= Hgr Hgi].
rewrite !raddfD /= [lf]complexE [lg]complexE /= !mulrDr !mulrDl !raddfD /=. 
rewrite ![_ * (RtoC _)]mulrC /= -!Cr_scalE -scalerAl -scalerAr !linearZ /=. 
rewrite -['i * _]mulrC !ImiRe !ReiNIm !mulrN. 
rewrite ![(Im lg) * _]mulrC [(Re lg)* _]mulrC ; split.
  apply: (is_derive_ext (fun x : R_NormedModule => (Rmult (Re (f x)) (Re (g x))) 
     - (Rmult (Im (f x)) (Im (g x)))  : R_NormedModule)).
    move=> t; rewrite [(f t)]complexE /= mulrDl !mulr0 !mul0r !subr0 !add0r.
    rewrite !mul1r !addr0 !RmultE /= ['i * _]mulrC -!Cr_scalE raddfD /=.
    by rewrite -scalerAl !linearZ /= ['i * _]mulrC ReiNIm mulrN.
  rewrite addrACA -opprD -!RmultE -RplusE.
  by apply/is_derive_minus; apply/Derive.is_derive_mult.
apply: (is_derive_ext (fun x : R_NormedModule => (Rmult (Re (f x)) (Im (g x))) 
     + (Rmult (Im (f x)) (Re (g x)))  : R_NormedModule)).
  move=> t; rewrite [(f t)]complexE /= mulrDl !mulr0 !mul0r !subr0 !add0r.
  rewrite !mul1r !addr0 !RmultE /= ['i * _]mulrC -!Cr_scalE raddfD /=.
  by rewrite -scalerAl !linearZ /= ['i * _]mulrC ImiRe.
rewrite addrAC !addrA -addrA addrACA -!RmultE -RplusE.
apply/is_derive_plus; first by apply/Derive.is_derive_mult.
rewrite RmultE mulrC -RmultE addrC -RplusE.
by apply/Derive.is_derive_mult.
Qed.

Lemma ex_CrderiveM (f : R_NormedModule -> Cr_R_NormedModule) 
  (g : R_NormedModule -> Cr_R_NormedModule) x :
  ex_derive f x -> ex_derive g x ->
  ex_derive (fun x => (f x) * (g x) : Cr_R_NormedModule) x.
Proof.
move=> [lf Hf] [lg Hg]; exists (lf * (g x) + (f x) * lg).
by apply: is_CrderiveM.
Qed.

Lemma CrderiveM (f : R_NormedModule -> Cr_R_NormedModule) 
  (g : R_NormedModule -> Cr_R_NormedModule) x :
  ex_derive f x -> ex_derive g x ->
  Crderive (fun y => (f y) * (g y)) x = 
  (Crderive f x) * (g x) + (f x) * (Crderive g x).
Proof.
move=> Hf Hg; apply: is_Crderive_unique.
by apply: is_CrderiveM; apply: Crderive_correct.
Qed.

Lemma is_CrderiveX (f : R_NormedModule -> Cr_R_NormedModule) x n l :
  is_derive f x l ->
  is_derive (fun x => (f x)^+ n) x 
           (l * (f x)^+ n.-1 *+ n).
Proof.
move=> Hf.
case: n => [|n].
  apply: (is_derive_ext (fun x => 1 : Cr_R_NormedModule)).
    by move=> y; rewrite expr0.
  rewrite mulr0n.
  by apply: is_derive_const.
apply: (is_derive_ext (fun y => (f y)^+n * (f y))).
  by move=> y; rewrite exprS mulrC.
rewrite -pred_Sn.
elim: n => [|n Ihn].
  apply: (is_derive_ext f).
    by move=> y; rewrite expr0 mul1r.
  by rewrite expr0 mulr1 mulr1n.
apply: (is_derive_ext (fun y => (f y)^+n * (f y) * (f y))).
  by move=> y; rewrite exprS mulrC mulrA.
have -> : (l * f x ^+ n.+1 *+ n.+2) =
  ((l * f x ^+ n *+ n.+1) * (f x) + ((f x)^+n * (f x) * l)).
  rewrite [X in _ = _ + X]mulrC.
  by rewrite mulrnAl -mulrA -exprSr mulrS addrC.
by apply: is_CrderiveM.
Qed.

Lemma ex_CrderiveX (f : R_NormedModule -> Cr_R_NormedModule) x n :
  ex_derive f x ->
  ex_derive (fun x => (f x)^+ n) x.
move=> [lf Hf]; exists  (lf * (f x)^+ n.-1 *+ n).
by apply: is_CrderiveX.
Qed.

Lemma CrderiveX (f : R_NormedModule -> Cr_R_NormedModule) x n :
  ex_derive f x -> 
  Crderive (fun y => (f y)^+n ) x = 
  (Crderive f x) * (f x)^+n.-1 *+ n.
Proof.
move=> Hf; apply: is_Crderive_unique.
by apply: is_CrderiveX; apply: Crderive_correct.
Qed.

Lemma ex_Crderive_poly (P : {poly complexR}) (a : complexR) (x : R) :
  ex_derive (fun y : R_NormedModule => P.[y *: a] : Cr_R_NormedModule) x.
Proof.
apply: (@poly_ind _ (fun Q => ex_derive 
  (fun y : R_NormedModule => Q.[y *: a]) x)) => [|Q c IhQ].
  apply: (ex_derive_ext (fun y => 0 : Cr_R_NormedModule)).
    by move=> y; rewrite horner0.
  by apply: ex_derive_const.
apply: (ex_derive_ext 
   (fun y : R_NormedModule =>  Q.[y *: a] * (RtoC y * a) + c : Cr_R_NormedModule)).
  by move=> y; rewrite hornerMXaddC Cr_scalE.
apply: ex_CrderiveD; last by apply: ex_derive_const.
by apply/ex_CrderiveM => //; apply/ex_CrderiveM/ex_derive_const/ex_Crderive_idR.
Qed.

Lemma Crderive_poly (P : {poly complexR}) a (x : R) :
  Crderive (fun y => P.[y *: a]) x = a * P^`().[x *: a].
Proof.
apply: (@poly_ind _ (fun Q =>
 Crderive (fun y : R => Q.[y *: a]) x = a * Q^`().[x *: a]
   )) => [|Q c IhQ].
  rewrite (@Crderive_ext _ (fun _ => 0)).
    by rewrite (Crderive_const) deriv0 horner0 mulr0.
  by move=> y; rewrite horner0.
rewrite (@Crderive_ext _ (fun y =>  Q.[y *: a] * ((RtoC y) * a) + c)).
  rewrite (CrderiveD) ?CrderiveM ?IhQ ?Crderive_const ?Crderive_idR; first last.
  + by apply: ex_derive_const.
  + apply/ex_CrderiveM/ex_CrderiveM/ex_derive_const/ex_Crderive_idR.
    by apply/ex_Crderive_poly.
  + by apply/ex_CrderiveM/ex_derive_const/ex_Crderive_idR.
  + by apply/ex_Crderive_poly.
  + by apply/ex_derive_const.
  + by apply/ex_Crderive_idR.
  rewrite derivMXaddC mul1r mulr0 !addr0 hornerD hornerMX -Cr_scalE.
  by rewrite [_ * a]mulrC mulrDr addrC mulrA.
by move=>y; rewrite hornerMXaddC -Cr_scalE.
Qed.

Lemma ex_Crderive_Cexp (a : complexR) (x : R) :
  ex_derive (fun y : R_NormedModule => Cexp(y *: a) : Cr_R_NormedModule) x.
Proof.
apply: (ex_derive_ext (fun y => (RtoC (exp ((Re a) * y))) 
 * (RtoC (cos((Im a)*y)) + 'i * RtoC(sin((Im a)*y)) ) : Cr_R_NormedModule)).
  move=> u; rewrite /Cexp /= ![_ * RtoC _]mulrC -!Cr_scalE !linearZ /=.
  by rewrite [_ * Im _]mulrC [_ * Re _]mulrC.
apply/ex_CrderiveM.
  apply/ex_Crderive_RtoC/ex_derive_comp.
    by apply: ex_derive_Reals_1; apply: derivable_pt_exp.     
  apply/ex_derive_mult; last by apply/ex_derive_id.
  by apply: ex_derive_const.
apply/ex_CrderiveD; last (apply/ex_CrderiveM; first apply: ex_derive_const);
apply/ex_Crderive_RtoC; apply/ex_derive_comp.
+ by apply: ex_derive_Reals_1; apply: derivable_pt_cos.
+ apply/ex_derive_mult; last by apply/ex_derive_id.
  by apply: ex_derive_const.
+ by apply: ex_derive_Reals_1; apply: derivable_pt_sin.
+ apply/ex_derive_mult; last by apply/ex_derive_id.
  by apply: ex_derive_const.
Qed.

Lemma Crderive_Cexp (a : complexR) (x : R) :
  Crderive (fun y => Cexp(y *: a)) x =
    a * Cexp(x *: a).
Proof.
rewrite (@Crderive_ext _ (fun y => (RtoC (exp ((Re a) * y))) 
 * (RtoC (cos((Im a)*y)) + 'i * RtoC(sin((Im a)*y)) )));
  last first.
  move=> u; rewrite /Cexp /= ![_ * RtoC _]mulrC -!Cr_scalE !linearZ /=.
  by rewrite [_ * Im _]mulrC [_ * Re _]mulrC.
rewrite CrderiveM; first last.
    apply/ex_CrderiveD.
      apply/ex_Crderive_RtoC/ex_derive_comp.
      + by apply: ex_derive_Reals_1; apply: derivable_pt_cos.
      + apply/ex_derive_mult; last by apply/ex_derive_id.
        by apply: ex_derive_const.
    apply/ex_CrderiveM; first apply/ex_derive_const.
    apply/ex_Crderive_RtoC/ex_derive_comp.
    + by apply: ex_derive_Reals_1; apply: derivable_pt_sin.
    + apply/ex_derive_mult; last by apply/ex_derive_id.
      by apply: ex_derive_const.
  apply/ex_Crderive_RtoC/ex_derive_comp.
  + by apply: ex_derive_Reals_1; apply: derivable_pt_exp.     
  + apply/ex_derive_mult; last by apply/ex_derive_id.
    by apply: ex_derive_const.
rewrite CrderiveD ?CrderiveM ?Crderive_RtoC ?Crderive_const; first last.
+ apply/ex_CrderiveM; first apply/ex_derive_const.
  apply/ex_Crderive_RtoC/ex_derive_comp.
  + by apply: ex_derive_Reals_1; apply: derivable_pt_sin.
  + apply/ex_derive_mult; last by apply/ex_derive_id.
    by apply: ex_derive_const.
+ apply/ex_Crderive_RtoC/ex_derive_comp.
  + by apply: ex_derive_Reals_1; apply: derivable_pt_cos.
  + apply/ex_derive_mult; last by apply/ex_derive_id.
    by apply: ex_derive_const.
+ apply/ex_Crderive_RtoC/ex_derive_comp.
  + by apply: ex_derive_Reals_1; apply: derivable_pt_sin.
  + apply/ex_derive_mult; last by apply/ex_derive_id.
    by apply: ex_derive_const.
+ by apply: ex_derive_const.
+ apply/ex_derive_comp.
  + by apply: ex_derive_Reals_1; apply: derivable_pt_exp.
  + apply/ex_derive_mult; last by apply/ex_derive_id.
    by apply: ex_derive_const.
+ apply/ex_derive_comp.
  + by apply: ex_derive_Reals_1; apply: derivable_pt_cos.
  + apply/ex_derive_mult; last by apply/ex_derive_id.
    by apply: ex_derive_const.
+ apply/ex_derive_comp.
  + by apply: ex_derive_Reals_1; apply: derivable_pt_sin.
  + apply/ex_derive_mult; last by apply/ex_derive_id.
    by apply: ex_derive_const.    
rewrite Derive_comp; first last.
    apply: ex_derive_mult.
      by apply: ex_derive_const.
    by apply: ex_derive_id.
  by apply: ex_derive_Reals_1; apply: derivable_pt_exp.
rewrite Derive_mult; first last.
    by apply: ex_derive_id.
  by apply: ex_derive_const.
rewrite Derive_const Derive_id.
rewrite -(Derive_Reals exp _ (derivable_pt_exp (Re a * x))).
rewrite derive_pt_exp Derive_comp; first last.
    apply: ex_derive_mult.
      by apply: ex_derive_const.
    by apply: ex_derive_id.
  by apply: ex_derive_Reals_1; apply: derivable_pt_cos.
rewrite Derive_mult; first last.
    by apply: ex_derive_id.
  by apply: ex_derive_const.
rewrite Derive_const Derive_id.
rewrite -(Derive_Reals cos _ (derivable_pt_cos (Im a * x))).
rewrite derive_pt_cos Derive_comp; first last.
    apply: ex_derive_mult.
      by apply: ex_derive_const.
    by apply: ex_derive_id.
  by apply: ex_derive_Reals_1; apply: derivable_pt_sin.
rewrite Derive_mult; first last.
    by apply: ex_derive_id.
  by apply: ex_derive_const.
rewrite Derive_const Derive_id.
rewrite -(Derive_Reals sin _ (derivable_pt_sin (Im a * x))).
rewrite derive_pt_sin !RmultE !RplusE /Cexp !RtoCE /=; simpc.
rewrite !linearZ ![_ *(Im a * _)]mulrCA -!mulrA /= ![(x * _)%R]mulrC /=.
by move: a (exp _ * _) (exp _ * _) => [aR aI] u v /=; simpc.
Qed.

End Cderiv.

Open Scope R_scope.
Lemma fact_factorial : forall p, fact p = p`!.
Proof. by elim => [|p Ip] //; rewrite factS fact_simpl multE Ip. Qed.

Lemma INR_expn x l : INR (x ^ l) = INR x ^ l.
Proof. by elim: l => [|l Il] //=; rewrite expnS -Il -mult_INR. Qed.

Lemma p_prop1 (a b : nat) : exists M, forall n, (M <= n -> a * b ^ n < n`!)%N.
Proof.
have : is_lim_seq (fun n => INR a * (INR b ^ n / INR (fact n))) 0.
  rewrite [_ 0](_ : _ = Rbar_mult (INR a) 0); last by rewrite /= Rmult_0_r.
  apply/is_lim_seq_scal_l/ex_series_lim_0; exists (exp (INR b)).
  by apply/is_pseries_Reals; apply:svalP.
rewrite -is_lim_seq_spec => ils; case: (ils (mkposreal _ Rlt_0_1)) => M'.
rewrite /pos => PM'; exists M' => m /leP M'm; move: (PM' _ M'm).
have fn0 : 0 < INR (fact m) by exact: INR_fact_lt_0.
rewrite /Rminus Ropp_0 Rplus_0_r Rabs_right; last first.
  apply/Rle_ge; repeat apply Rmult_le_pos; auto using pow_le, pos_INR.
  by apply/Rlt_le/Rinv_0_lt_compat.
move => il1; move:(Rmult_lt_compat_r _ _ _ fn0 il1).
rewrite /Rdiv !Rmult_assoc Rinv_l ?Rmult_1_r; last by apply/Rgt_not_eq/fn0.
by rewrite -INR_expn Rmult_1_l -mult_INR fact_factorial;move/INR_lt/ltP.
Qed.

Close Scope R_scope.

Section Cinte.

Lemma Riemann_sum_Re (f : R -> Cr_R_NormedModule) (ptd : SF_seq) :
  Re (Riemann_sum f ptd) = Riemann_sum (fun x => Re (f x)) ptd.
Proof.
apply (SF_cons_ind (fun y => 
   Re (Riemann_sum f y) = Riemann_sum (fun x : R => Re (f x)) y) )
     => [x0 //| [x1 y0] y IH].
by rewrite !Riemann_sum_cons -IH raddfD /scal /= linearZ /=.
Qed.

Lemma Riemann_sum_Im (f : R -> Cr_R_NormedModule) (ptd : SF_seq) :
  Im (Riemann_sum f ptd) = Riemann_sum (fun x => Im (f x)) ptd.
apply (SF_cons_ind (fun y => 
   Im (Riemann_sum f y) = Riemann_sum (fun x : R => Im (f x)) y) )
     => [x0 //| [x1 y0] y IH].
by rewrite !Riemann_sum_cons -IH raddfD /scal /= linearZ.
Qed.

Lemma Riemann_sum_ReIm (f : R -> Cr_R_NormedModule) (ptd : SF_seq) :
  Riemann_sum f ptd =
  RtoC (Riemann_sum (fun x => Re (f x)) ptd) + 'i *
  RtoC (Riemann_sum (fun x => Im (f x)) ptd).
apply/eqP; rewrite eq_complex /=. simpc.
by rewrite Riemann_sum_Re eq_refl andTb Riemann_sum_Im.
Qed.

Definition is_CrInt (f : R -> complexR) (a b : R) (If : complexR):=
  (is_RInt (fun x => Re (f x)) a b (Re If)) /\
  (is_RInt (fun x => Im (f x)) a b (Im If)).

Definition ex_CrInt (f : R -> Cr_R_NormedModule) (a b : R) :=
  exists If : complexR, is_CrInt f a b If.

Lemma is_CrInt_C_eq (f : R -> Cr_R_NormedModule) a b If :
  is_RInt f a b If <-> is_CrInt f a b If.
Proof.
split.
  rewrite /is_CrInt; move=> Hint; split; move=> P [eP HP].
    move: (Hint (fun x => P (Re x))) => [| ef Hf'].
      exists eP => y; rewrite /ball /= /Cr_ball.
      by move=> [Br Bi]; apply: HP.
    exists ef => y H1 H2; rewrite -Riemann_sum_Re.
    by have := (Hf' _ H1 H2); rewrite /scal /= linearZ.
  move: (Hint (fun x => P (Im x))) => [| ef Hf'].
    exists eP => y; rewrite /ball /= /Cr_ball.
    by move=> [Br Bi]; apply: HP.
  exists ef => y H1 H2; rewrite -Riemann_sum_Im.
  by have := (Hf' _ H1 H2); rewrite /scal /= linearZ.
move=> [Hr Hi].
rewrite /is_RInt filterlim_locally => eps.
generalize (proj1 (filterlim_locally _ _) Hr eps) => {Hr}.
generalize (proj1 (filterlim_locally _ _) Hi eps) => {Hi}.
move=> [di /= Hi] [dr /= Hr].
exists (mkposreal _ (Rmin_stable_in_posreal dr di)) => /= ptd Hstep Hptd.
rewrite (Riemann_sum_ReIm f ptd) /=.
split; rewrite /scal /= mul0r; simpc.
  by apply: Hr => //; apply Rlt_le_trans with (2 := Rmin_l dr di).
by apply: Hi => //; apply Rlt_le_trans with (2 := Rmin_r dr di).
Qed.

Lemma ex_CrInt_C_eq (f : R -> Cr_R_NormedModule) a b :
  ex_RInt f a b <-> ex_CrInt f a b.
Proof.
rewrite /ex_CrInt /ex_RInt; split; move=> [e H]; exists e.  
  by rewrite -is_CrInt_C_eq.
by rewrite is_CrInt_C_eq.
Qed.

Lemma ex_RInt_C_eq (f : R -> Cr_R_NormedModule) a b :
  ex_RInt f a b <->
  ex_RInt (fun y => Re (f y)) a b /\ 
  ex_RInt (fun y => Im (f y)) a b.
Proof.
split.
  rewrite ex_CrInt_C_eq /ex_CrInt /is_CrInt.
  move=> [If [is_R is_I]]; split.
    by exists (Re If).
  by exists (Im If).
move => [[lr is_R] [li is_I]]; rewrite ex_CrInt_C_eq.
by exists (RtoC lr + 'i * RtoC li); rewrite /is_CrInt /=; simpc; split.
Qed.

Definition CrInt f a b : complexR :=
  RtoC (RInt (fun x => Re (f x)) a b) + 'i *
  RtoC (RInt (fun x => Im (f x)) a b).
(*
About RInt.

Lemma CrInt_C_eq (f : R -> complexR) a b :
     RInt f a b = CrInt_C f a b.
Proof.
rewrite /CrInt /CrInt_C /RInt /Cr_limseq.
case: (Rle_dec a b) => H.
  apply/eqP; rewrite eq_complex /=; apply/andP; split; apply/eqP; simpc.
    rewrite (Lim_seq_ext _ (RInt_val (fun x : R => Re (f x)) a b)) //.
    by move=> n; rewrite /RInt_val Riemann_sum_Re.
  rewrite (Lim_seq_ext _ (RInt_val (fun x : R => Im (f x)) a b)) //=.
  by move=> n; rewrite /RInt_val Riemann_sum_Im.
apply/eqP; rewrite eq_complex /=; apply/andP; split; apply/eqP; simpc.
  rewrite (Lim_seq_ext _ (RInt_val (fun x : R => Re (f x)) b a)) //=.
  by move=> n; rewrite /RInt_val Riemann_sum_Re.
rewrite (Lim_seq_ext _ (RInt_val (fun x : R => Im (f x)) b a)) //=.
by move=> n; rewrite /RInt_val Riemann_sum_Im. 
Qed.
*)
Lemma CrInt_C_unique f a b If :
  is_CrInt f a b If -> CrInt f a b = If.
Proof.
move=> [Hr Hi].
rewrite /CrInt.
apply/eqP; rewrite eq_complex /=.
by rewrite (is_RInt_unique _ _ _ _ Hr) (is_RInt_unique _ _ _ _ Hi); simpc.
Qed.

Lemma CrInt_unique (f : R -> complexR) a b If :
  is_RInt f a b If -> CrInt f a b = If.
Proof. by rewrite is_CrInt_C_eq; apply: CrInt_C_unique. Qed.

Lemma CrInt_correct (f : R -> complexR) a b :
  ex_RInt f a b ->
  is_RInt f a b (CrInt f a b).
Proof. by move=> [l H]; have ->: (CrInt f a b = l) by apply CrInt_unique. Qed.

(* Theorems to have RInt (Crderive )= ... *)

Lemma CrInt_DeriveAux f a b :
  (forall x, Rmin a b <= x <= Rmax a b -> ex_derive f x) ->
  (forall x, Rmin a b <= x <= Rmax a b -> 
         Crcontinuity_pt (Crderive_C f) x) ->
  CrInt (Crderive_C f) a b = f b - f a.
Proof.
move=> ex_H Hcont; rewrite /Crderive_C /CrInt; simpc.
rewrite (RInt_ext _ (Derive (fun y => Re ( f y)))); last first.
  by move=> x Hx /=; simpc.
rewrite [X in (_ +i* X)%C](RInt_ext _ (Derive (fun y => Im ( f y)))); last first.
  by move=> x Hx /=; simpc.
apply/eqP; rewrite eq_complex /=; simpc.
apply/andP; split; rewrite raddfB /=; simpc; apply/eqP.
apply: (RInt_Derive); move=> x [/RleP Hmin /RleP Hmax];
  have Hineq : (  Rmin a b <= x <= Rmax a b ) by apply/andP; split.
+ by move/ex_Crderive_ReIm: (ex_H x Hineq) => [H _].
+ rewrite /continuous; apply/continuity_pt_filterlim.
  move/Crcontinuity_pt_ReIm: (Hcont x Hineq) => [Hr _].
  apply: (continuity_pt_ext _ _ _ _ Hr) => t; rewrite /Crderive_C raddfD /=.
  by rewrite mul0r mulr0 subr0 addr0.
apply: (RInt_Derive); move=> x [/RleP Hmin /RleP Hmax];
  have Hineq : (  Rmin a b <= x <= Rmax a b ) by apply/andP; split.
+ by move/ex_Crderive_ReIm : (ex_H x Hineq) => [_].
+ rewrite /continuous; apply/continuity_pt_filterlim.
  move/Crcontinuity_pt_ReIm: (Hcont x Hineq) => [_ Hi].
  apply: (continuity_pt_ext _ _ _ _ Hi) => t; rewrite /Crderive_C raddfD /=.
  by rewrite mulr0 mul1r !add0r.
Qed.

Lemma ex_CrInt_cont f a b :
(forall x : R, (Rmin a b <= x <= Rmax a b) -> Crcontinuity_pt f x) ->
ex_CrInt f a b.
move=> H; rewrite /ex_CrInt /is_CrInt.
have H_re :  forall x : R, and (Rle (Rmin a b) x) (Rle x (Rmax a b)) ->
  (Rmin a b) <= x <= (Rmax a b).
  by move=> x [/RleP Hr /RleP Hi]; apply/andP; split.  
have Hr :  forall x : R,  and (Rle (Rmin a b) x) (Rle x (Rmax a b)) -> 
  continuity_pt (fun x => Re ( f x)) x.
  move=> x; move/H_re => Hineq.
  by move/Crcontinuity_pt_ReIm: (H x Hineq) => [Hr _].
have Hi :  forall x : R,  and (Rle (Rmin a b) x) (Rle x (Rmax a b)) -> 
  continuity_pt (fun x => Im ( f x)) x.
  move=> x; move/H_re => Hineq.
  by move/Crcontinuity_pt_ReIm: (H x Hineq) => [_].
case:(ex_RInt_continuous (fun x0 : R => Re (f x0)) a b ).
  move=> z  Hz.
  by rewrite /continuous; apply continuity_pt_filterlim; apply Hr.
move=>Ifr {Hr} Hr.
case:(ex_RInt_continuous (fun x0 : R => Im (f x0)) a b ).
  move=> z  Hz.
  by rewrite /continuous; apply continuity_pt_filterlim; apply Hi.
move=>Ifi {Hi} Hi.
by exists (RtoC Ifr + 'i * RtoC Ifi); rewrite /= !mulr0 mul0r !add0r mul1r subr0.
Qed.  

Lemma is_CrInt_DeriveAux f a b :
  (forall x, Rmin a b  <= x <= Rmax a b  -> ex_derive f x) ->
  (forall x, Rmin a b  <= x <= Rmax a b  -> 
         Crcontinuity_pt (Crderive_C f) x) ->
  is_CrInt (Crderive_C f) a b (f b - f a).
Proof.
move => Df Cdf.
rewrite -(CrInt_DeriveAux Df Cdf).
suff: (ex_CrInt (Crderive_C f) a b).
  by case => l H; rewrite (CrInt_C_unique H).
by apply ex_CrInt_cont; move => x Hx; apply Cdf.
Qed.

Lemma CrInt_C_ext f g a b :
  (forall x : R, (Rmin a b <= x <= Rmax a b) -> f x = g x) ->
  CrInt f a b = CrInt g a b.
Proof.
move=> H; rewrite /CrInt.
rewrite (RInt_ext  (fun x : R => Re (f x)) (fun x : R => Re (g x))).
  rewrite (RInt_ext  (fun x : R => Im (f x)) (fun x : R => Im (g x))) //.
  move=> x [/RltP Hfr /RltP Hfi].
  have Hineq: Rmin a b <= x <= Rmax a b.
    by apply/andP; split; apply/ltrW.
  by move/eqP: (H x Hineq); rewrite eq_complex; move=> /andP [_ /eqP].
move=> x [/RltP Hfr /RltP Hfi].
have Hineq: Rmin a b <= x <= Rmax a b.
  by apply/andP; split; apply/ltrW.
by move/eqP: (H x Hineq); rewrite eq_complex; move=> /andP [/eqP Piou _].
Qed.

Lemma CrInt_ext f g a b :
  (forall x : R, (Rmin a b <= x <= Rmax a b) -> f x = g x) ->
  CrInt f a b = CrInt g a b.
Proof.
by move=> H; apply: (CrInt_C_ext H).
Qed.

Lemma RInt_CrderiveAux f a b :
  ex_RInt (Crderive f) a b ->
    (forall x, Rmin a b <= x <= Rmax a b -> ex_derive f x) ->
    (forall x, Rmin a b <= x <= Rmax a b -> 
         Crcontinuity_pt (Crderive f) x) ->
  CrInt (Crderive f) a b = f b - f a.
Proof.
move=> [l H] Hex Hcont.
rewrite (@CrInt_C_ext _ (Crderive_C f)); first last.
  by move=> x Hineq; rewrite Crderive_C_eq.
rewrite CrInt_DeriveAux //=; move=> x Hineq.
apply: (@Crcontinuity_pt_ext (Crderive f)).
  by move=> u; rewrite Crderive_C_eq.
by apply: (Hcont x Hineq).
Qed.

Lemma ex_RInt_cont_C f a b :
   (forall x : R, (Rmin a b <= x <= Rmax a b) -> Crcontinuity_pt f x) ->
   ex_RInt f a b.
Proof.
move=> Hcont; rewrite ex_CrInt_C_eq /ex_CrInt /is_CrInt.
have Hcontr : (forall x : R, and (Rle (Rmin a b) x) (Rle x (Rmax a b))
   -> continuity_pt  (fun x : R => Re (f x)) x ).
  move=> x [/RleP Hmin /RleP Hmax].
  have Hineq: Rmin a b <= x <= Rmax a b.
    by apply/andP; split.
  by move/Crcontinuity_pt_ReIm: (Hcont x Hineq) => [H _].
have Hconti : (forall x : R, and (Rle (Rmin a b) x) (Rle x (Rmax a b))
   -> continuity_pt  (fun x : R => Im (f x)) x ).
  move=> x [/RleP Hmin /RleP Hmax].
  have Hineq: Rmin a b <= x <= Rmax a b.
    by apply/andP; split.
  by move/Crcontinuity_pt_ReIm: (Hcont x Hineq) => [_].
case: (ex_RInt_continuous (fun x0 : R => Re (f x0)) a b).
   by move=> z Hz ; apply continuity_pt_filterlim; apply Hcontr.
move=> lr Hr.
case: (ex_RInt_continuous (fun x0 : R => Im (f x0)) a b).
   by move=> z Hz ; apply continuity_pt_filterlim; apply Hconti.
move=> li Hi.
by exists (RtoC lr + 'i * RtoC li); rewrite /= !mulr0 mul0r !add0r mul1r subr0.
Qed.

Lemma RInt_Crderive f a b:
  (forall x, Rmin a b <= x <= Rmax a b -> ex_derive f x) ->
  (forall x, Rmin a b <= x <= Rmax a b -> 
         Crcontinuity_pt (Crderive f) x) ->
  CrInt (Crderive f) a b = f b - f a.
Proof.
move=> ex_de cont_de; apply: RInt_CrderiveAux => //=.
by apply: ex_RInt_cont_C.
Qed.

Lemma ex_CrInt_norm f a b :
  (forall x, Rmin a b <= x <= Rmax a b -> Crcontinuity_pt f x) ->
  ex_RInt (fun x => norm (f x)) a b.
Proof.
move=> H.
have Hcr : (forall x, Rmin a b <= x <= Rmax a b -> continuity_pt 
   (fun y => Re (f y)) x ).
  move=> x Hineq.
  by move/Crcontinuity_pt_ReIm: (H x Hineq) => [Y _].
have Hci : (forall x, Rmin a b <= x <= Rmax a b -> continuity_pt 
   (fun y => Im (f y)) x ).
  move=> x Hineq.
  by move/Crcontinuity_pt_ReIm: (H x Hineq) => [_].
apply: (ex_RInt_ext
          (fun y => sqrt (Rplus (Rmult (Re (f y)) (Re (f y)))
                            (Rmult (Im (f y)) (Im (f y)))))).
  move=> x Heq; case xeq: (f x) => [fr fi].
  have h z : Rmult z z = z ^+ 2 by rewrite RmultE !exprS expr0 mulr1.
  by rewrite !h /norm /= RsqrtE RplusE ?addr_ge0 // sqr_ge0.
apply: ex_RInt_continuous=> x [/RleP Hmin /RleP Hmax].
have Hineq : (Rmin a b <= x <= Rmax a b) by apply/andP; split.
move: (Hcr x Hineq) => {Hcr} Hcr; move: (Hci x Hineq) => {Hci} Hci.
apply continuity_pt_filterlim; apply: continuity_pt_comp.
  apply: continuity_pt_plus; by apply: continuity_pt_mult.
apply: continuity_pt_sqrt.
by apply/RleP; rewrite RplusE !RmultE -!expr2 addr_ge0 ?sqr_ge0.
Qed.

Lemma CrInt_norm f a b :
  a <= b -> 
  (forall x, Rmin a b <= x <= Rmax a b -> Crcontinuity_pt f x) ->
  norm (CrInt f a b) <= RInt (fun t => norm (f t)) a b.
Proof.
move=> Hab Hcont; apply/RleP.
apply: (norm_RInt_le (f : R -> Cr_R_NormedModule) (fun t => norm (f t)) a b).
      by apply/RleP.
    by move=> x Hineq; apply/RleP.
  by apply: CrInt_correct; rewrite ex_CrInt_C_eq; apply: ex_CrInt_cont.
apply: RInt_correct.
by apply: ex_CrInt_norm.
Qed.

End Cinte.
