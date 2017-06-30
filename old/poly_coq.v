From mathcomp Require Import all_ssreflect all_algebra.
(** *** Exercices on polynomials
- Formalisation of the algebraic  part of  a                          
 simple proof that PI is irrational  described in:                   
- http://projecteuclid.org/download/pdf_1/euclid.bams/1183510788    
*)  

Section Algebraic_part.

Open Scope ring_scope.
Import GRing.Theory Num.Theory.

(** *** Parameters definitions:
- Let n na nb be  natural numbers
- Suppose nb is a non zero nat: nb != 0
- Define the corresponding rationals a , b 
- Define pi as a/b.
*)
(* to complete  for na nb*)
Variables n na nb : nat.

Hypothesis nbne0: nb != 0%N.

Definition a:rat := (Posz na)%:~R.
Definition b:rat := (Posz nb)%:~R.

Definition pi := a / b.

(** *** Definition of the polynomials:
-  Look at the f definition: the factorial, the coercion nat :> R (as a Ring), etc...
- Define F:{poly rat} using bigop.
*)
Definition f :{poly rat} := 
  (n`!)%:R^-1 *: ('X^n * (a%:P -  b*:'X)^+n).

Definition F : \sum_(i < n.+1) f^`(2 * i) * ((-1) ^+ i)%:~R.


(** *** Prove that:
- b is non zero rational.
*)
(* Some intermediary simple theorems *)
Lemma bne0: b != 0.
Proof. by rewrite intq_eq0. Qed.


(** *** Prove that:
-  (a -  bX) has a size of 2
*)
Lemma P1_size: size (a%:P -  b*:'X) = 2.
Proof.
rewrite addrC size_addl ?size_opp ?size_scale ?bne0 ?size_polyX // size_polyC.
by move: (a == 0); case.
Qed.


(** *** Prove that:
-  the lead_coef of (a -  bX) is -b.
*)
Lemma P1_lead_coef: lead_coef (a%:P -  b*:'X) = -b.
Proof.
by rewrite lead_coefE P1_size coefD coefN coefZ coefX eq_refl mulr1 coefC sub0r.
Qed.

(** *** Prove that:
-  the size of (a-X)^n is n.+1
*)
Lemma P_size : size ((a%:P -  b*:'X)^+n)  = n.+1.
Proof.
elim: n => [/= | n0 ihn].
  by rewrite expr0 size_poly1.
by rewrite exprS size_mul -?size_poly_eq0 ?ihn ?P1_size.
Qed.


(* 2 useful lemmas for the  Qint predicat. *)
Lemma int_Qint (z:int) : z%:~R \is a Qint.
Proof. by apply/QintP; exists z. Qed.

Lemma nat_Qint (m:nat) : m%:R \is a Qint.
Proof. by apply/QintP; exists m. Qed.

(** *** Prove that:
- Exponent and composition of polynomials combine:
*)
Lemma comp_poly_exprn: 
   forall (p q: {poly rat}) i, p ^+ i \Po q = (p \Po q) ^+ i.
Proof.
move=> p q; elim  => [ | i ihn].
  by rewrite !expr0 comp_polyC.
by rewrite !exprS -ihn comp_polyM.
Qed.


(** *** Prove that:
- f's small coefficients are zero
*)
(* Let's begin the Niven proof *)
Lemma f_small_coef0 i: (i < n)%N -> f`_i = 0.
Proof. by move=> ord_i; rewrite /f scalerAr coefXnM ord_i.
Qed.

(** *** Prove that:
- f/n! as integral coefficients 
*)

Lemma f_int i: (n`!)%:R * f`_i \is a Qint.
Proof.
rewrite /f coefZ mulrA mulfV ?mul1r.
  apply/polyOverP; rewrite rpredM ?rpredX ?polyOverX ?rpredB ?polyOverC ?polyOverZ;
  rewrite ?polyOverX ?int_Qint //.
by rewrite pnatr_eq0 -lt0n fact_gt0.
Qed.

(** *** Prove that:
the f^`(i) (x) have integral values for x = 0
*)
Lemma derive_f_0_int: forall i, f^`(i).[0] \is a Qint.
Proof.
move=> i; have [i_gen | i_ltn] := (leqP n i).
  rewrite horner_coef0 coef_derivn !addn0 ffactnn -(bin_fact i_gen) -mulr_natl.
  rewrite mulnCA mulnC natrM -mulrA rpredM ?nat_Qint ?f_int //.
rewrite horner_coef0 nderivn_def coefMn rpredMn ?nat_Qint // coef_nderivn addn0.
by rewrite rpredMn // (f_small_coef0 _ i_ltn).
Qed.


(** *** Deduce that:
F (0) has an integral value
*)

Lemma F0_int : F.[0] \is a Qint.
Proof.
Qed.

(** *** Then prove 
- the symmetry argument f(x) = f(pi -x).
*)
Lemma pf_sym:  f \Po (pi%:P -'X) = f.
Proof.
Qed.

(** *** Prove 
- the symmetry for the derivative 
*)

Lemma  derivn_fpix i :
      (f^`(i)\Po(pi%:P -'X))= (-1)^+i *: f^`(i).
Proof.
Qed.

(** *** Deduce that
- F(pi) is an integer 
*)
Lemma FPi_int : F.[pi] \is a Qint.
Proof.
Qed.


(** *** if you have time
- you can prove the  equality  F^`(2) + F = f 
- that is  needed by the analytic part of the Niven proof
*)

Lemma D2FDF : F^`(2) + F = f.
Proof.
Qed.

End Algebraic_part.


