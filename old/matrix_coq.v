From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Open Scope ring_scope.

Section CPGE.
(**

*)
Section ex_6_12.
(** -------------------------------------------- *)
(** #<div class='slide'>#

* Exercices de mathÃ©matiques oraux X-ens Algebre 1

* Exercise 6.12: Endomorphisms u such that Ker u = Im u.

Let E be a vector space (any dimension, but in Coq we reason in finite
dimension).

*)
Variables (F : fieldType) (n' : nat).
Let n := n'.+1.

Section Q1.
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** Question 1.

Let u be an endomorphism of E, such that Ker u = Im u and S be a
complement of Im u ("supplÃ©mentaire" in french), so that E is the
direct sum of S and Im u.

*)
Variable (u : 'M[F]_n) (S : 'M[F]_n).
Hypothesis eq_keru_imu : (kermx u :=: u)%MS.
Hypothesis S_u_direct : (S :&: u)%MS = 0.
Hypothesis S_u_eq1 : (S + u :=: 1)%MS.

Implicit Types (x y z : 'rV[F]_n).
Check matrixP.

(**

*** Question 1.a.

Show that for all x in E, there is a unique pair (y, z) in SÂ² such
that x = y + u (z), and pose v and z so that y = v(x) and z = w(x).

Instead of defining y and z for each x, we now define explicitly the
matrix that computes y and z from x.

 - A direct consequence of this is that v and w will be morphisms by
  construction, you can thus skip the part of the paper proof that
  deals with this.

 - Every morphism induces an ismorphism between a complement of its
   kernel and its image.  The function #<code>pinvmx</code># is the
   inverse of this isomporhism, but since the complement of the kernel
   that was used to produce #<code>pinvmx</code># is arbitrary, we
   must project the result of #<code>pinvmx</code># on S in order to
   get the specific inverse with image S.
*)
Definition w := locked (proj_mx S u).
Definition v := locked (proj_mx u S * pinvmx u * proj_mx S u).
(**

Note that we used locking in order to protect w and v from expanding
unexpectedly during proofs.

</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

**** Question 1.a.i.

Prove the following lemmas.

*)
Lemma wS x : (x *m w <= S)%MS.
Proof. 
by unlock w; rewrite /proj_mx mulmx_sub // mulmx_sub // col_mx_sub submx_refl sub0mx.
(*by unlock w; apply: proj_mx_sub.*)
Qed.

Lemma vS x : (x *m v <= S)%MS.
Proof. by unlock v; rewrite mulmx_sub // proj_mx_sub. Qed.

Lemma w_id x : (x <= S)%MS -> x *m w = x.
Proof. by unlock w => xS; rewrite proj_mx_id.
Qed.


(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#


**** Question 1.a.ii.

Reuse and adapt and the proof in the course.

- (hint: use mulmxKpV)

*)

Lemma Su_rect x : x = x *m w + (x *m v) *m u.
Proof.
unlock v w.
have x_in : (x <= S + u)%MS by rewrite S_u_eq1 submx1.
have {1}<- := (add_proj_mx S_u_direct x_in).
have /submxP [y eq_y] := (proj_mx_sub u S x).
congr (_ + _).
rewrite eq_y -[X in x *m X]mulmxA [x *m _]mulmxA eq_y mulmxA.
set z := _ *m pinvmx u.
have <- : z *m u = y *m u by rewrite mulmxKpV ?submxMl.
apply/eqP; rewrite -subr_eq0 -mulmxBl.
by apply/eqP/sub_kermxP; rewrite eq_keru_imu proj_mx_compl_sub ?S_u_eq1 ?submx1.
Qed.

(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

**** Question 1.a.iii.

From the proof

*)
Lemma Su_dec_eq0 y z : (y <= S)%MS -> (z <= S)%MS ->
  (y + z *m u == 0) = (y == 0) && (z == 0).
Proof.
move=> yS zS; apply/idP/idP; last first.
  by move=> /andP[/eqP -> /eqP ->]; rewrite add0r mul0mx.
rewrite addr_eq0 -mulNmx => /eqP eq_y_Nzu.
have : (y <= S :&: u)%MS by rewrite sub_capmx yS eq_y_Nzu submxMl.
rewrite S_u_direct // submx0 => /eqP y_eq0.
move/eqP: eq_y_Nzu; rewrite y_eq0 eq_sym mulNmx oppr_eq0 eqxx /= => /eqP.
move=> /sub_kermxP; rewrite eq_keru_imu => z_keru.
have : (z <= S :&: u)%MS by rewrite sub_capmx zS.
by rewrite S_u_direct // submx0.
Qed.
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

deduce

*)
Lemma Su_dec_uniq y y' z z' : (y <= S)%MS -> (z <= S)%MS ->
                              (y' <= S)%MS -> (z' <= S)%MS ->
  (y + z *m u == y' + z' *m u) = (y == y') && (z == z').
Proof.
move=> yS zS /submxP[y'S eqy'] /submxP [z'S eqz'].
rewrite -subr_eq0 opprD addrACA -mulmxBl Su_dec_eq0 ?subr_eq0 // ?addmx_sub //.
  by apply/submxP; exists (- y'S); rewrite mulNmx eqy'.
by apply/submxP; exists (- z'S); rewrite mulNmx eqz'.
Qed.  


(**
**** Question 1.a.iii.

Show some simplification lemmas
- the two first are direct
- the two last use Su_dec_uniq.

*)

Lemma u2_eq0 : u *m u = 0.
Proof. by apply/sub_kermxP; rewrite eq_keru_imu. Qed.

Lemma u2K m (a : 'M_(m,n)) : a *m u *m u = 0.
Proof. by rewrite -mulmxA u2_eq0 mulmx0. Qed.

Lemma v_id x : (x <= S)%MS -> (x *m u) *m v = x.
Proof.
move=> xS. 
have /eqP := (Su_rect (x *m u)).
rewrite -{1}[x *m u]add0r -[0](mul0mx _ w).
by rewrite Su_dec_uniq ?mul0mx ?sub0mx ?vS ?wS // => /andP[ _ /eqP].
Qed.

Lemma w0 x : (x <= S)%MS -> (x *m u) *m w = 0.
Proof.
move=> xS.
have /eqP := (Su_rect (x *m u)).
rewrite -{1}[x *m u]add0r -[0](mul0mx _ w).
by rewrite Su_dec_uniq ?mul0mx ?sub0mx ?vS ?wS // => /andP[/eqP -> _].
Qed.

(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

*** Question 1.b.

- Show that v is linear.
- Show that u o v + v o u = 1.

*)

Lemma add_uv_vu : v *m u + u *m v = 1.
Proof.
apply/row_matrixP => i.
rewrite rowE row1 mulmxDr. set x:= delta_mx _ _.
rewrite !mulmxA.
set y := x *m w; set z := x *m v.
by rewrite (Su_rect x) mulmxDl u2K addr0 -/y -/z addrC v_id // wS.
Qed.

(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

*** Question 1.c.

- Show that w is linear.
- Show that u o w + w o u = u.

*)
Lemma add_wu_uw : w *m u + u *m w = u.
Proof.
apply/row_matrixP => i.
rewrite rowE rowE mulmxDr mulmxA. set x := delta_mx _ _.
set y := x *m w.
have -> : x *m (u *m w) = y *m u *m w.
  by rewrite (Su_rect x) mulmxDl mulmxA mulmxA u2K mul0mx addr0 /y.
rewrite w0 ?wS // addr0.
have -> : y = x - x *m v *m u.
  by apply/eqP; rewrite eq_sym subr_eq /y {1}(Su_rect x). 
by rewrite mulmxBl u2K subr0.
Qed.

End Q1.
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** State and prove question 2, and then 3...

*)

End ex_6_12.
End CPGE.
