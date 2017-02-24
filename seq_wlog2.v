From mathcomp Require Import all_ssreflect.
From mathcomp
Require Import ssralg ssrnum mxpoly rat poly ssrint polyorder polydiv perm.
From mathcomp
Require Import finfun fingroup.
From structs
Require Import Cstruct Rstruct.
From SsrMultinomials
Require Import finmap order mpoly.
From Lind
Require Import ajouts wlog3.

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


Section Wlog2.

(* Hypothèses de base : changer le pre_l en l.+1 *)
Variable l : nat.
Variable alpha : complexR ^ l.+1.
Hypothesis alpha_inj : injective alpha.
Hypothesis alpha_algebraic : forall i : 'I_l.+1, alpha i is_algebraic.
Variable a : complexR ^ l.+1.
Hypothesis a_neq0 : forall i : 'I_l.+1, a i != 0.
Hypothesis a_Cint : forall i : 'I_l.+1, a i \is a Cint.
Hypothesis Lindemann_false : Cexp_span a alpha == 0.

(* Polynômes associés *)

(* polynôme separable des alpha *)
Definition poly_gamma := sval (polyMinseq alpha_algebraic).

Lemma poly_gamma_neq0 : poly_gamma != 0.
Proof. by have /and5P[_ _ H _ _] := svalP (polyMinseq alpha_algebraic). Qed.

Lemma poly_gamma_Cint : poly_gamma \is a polyOver Cint.
Proof. by have /and5P[_ _ _ H _] := svalP (polyMinseq alpha_algebraic). Qed.

Lemma poly_gamma_root i : root poly_gamma (alpha i).
Proof. by have /andP[/forallP H _] := svalP (polyMinseq alpha_algebraic). Qed.

Definition c := lead_coef poly_gamma.

Lemma c_Cint : c \is a Cint.
Proof. by apply/polyOverP; apply: poly_gamma_Cint. Qed.

Lemma c_neq0 : c != 0.
Proof. by rewrite lead_coef_eq0; apply: poly_gamma_neq0. Qed.


(* on récupère l'ensemble des racines 
en séquence pour l'instant, on doit attendre pour la vraie notation 
et qu'on transforme en L.-tuple : b *)
Definition L := (size (seqroots poly_gamma)).-1.
Lemma size_gamma : size (seqroots poly_gamma) == L.+1.
Proof.
have := (seqrootsP _ poly_gamma_neq0 (poly_gamma_root ord0)); rewrite /L.
by move/perm_to_rem /perm_eq_size => -> /=.
Qed.

Definition gamma := finfun (tnth (Tuple size_gamma)).

Lemma gamma_inj : injective gamma.
Proof.
have /and3P[_ /seqroots_separable H _] := svalP (polyMinseq alpha_algebraic).
move=> x y; rewrite /gamma !ffunE !(tnth_nth 0) /=.
move/eqP; rewrite nth_uniq ?(elimT eqP size_gamma) //.
by move/eqP /ord_inj.
Qed.

Lemma alpha_in_gamma : 
  {f : 'I_L.+1 ^ l.+1 | injectiveb f & alpha =1 (gamma \o f)}.
Proof.
have alpha_in i : alpha i \in Tuple size_gamma.
  by apply/(seqrootsP _ poly_gamma_neq0) /poly_gamma_root.
pose f := (fun i => sval (sig_eqW (elimT (tnthP _ _) (alpha_in i)))). 
have H_f i : gamma (f i) = alpha i.
  move: (svalP (sig_eqW (elimT (tnthP _ _) (alpha_in i)))) => ->.
  by rewrite /gamma /f [LHS]ffunE.
exists (finfun f).
  apply/injectiveP; move=> x y /=; rewrite !ffunE => eq_f.
  by apply: alpha_inj; rewrite -!H_f eq_f.
by move=> i /=; rewrite (ffunE f) H_f.
Qed.

Lemma leq_l_L : (l.+1 <= L.+1)%N.
Proof.
move: alpha_in_gamma => [] f /injectiveP inj_f eq_f.
rewrite -[l.+1]card_ord -[L.+1]card_ord -(card_codom inj_f).
apply: subset_leq_card; rewrite /codom; apply/subsetP => i.
by move/mapP=> [] j _ ->.
Qed.

Lemma gamma_set_roots : [fset gamma i | i : 'I_L.+1]%fset \is a setZroots c.
Proof. 
rewrite set_rootsE big_fset /= ?/gamma; last by apply: gamma_inj.
rewrite (big_ffun_ord _ _ (tnth (Tuple size_gamma)) _ (fun x => ('X  - x%:P))).
rewrite -(big_tuple _ _ (Tuple size_gamma) xpredT (fun x => ('X - x%:P))) /=.
by rewrite -seqroots_poly poly_gamma_Cint.
Qed.

(* produit sur toutes les fonctions injectives de l dans L *)
Definition prod_Cexp_span_gamma :=
  \prod_(f : 'I_L.+1 ^ l.+1 | injectiveb f) 
    Cexp_span a (finfun (gamma \o f)).

(* on retrouve le eq0 *)
Lemma prod_Cexp_span_gamma_eq0 : prod_Cexp_span_gamma == 0.
Proof.
move: (svalP alpha_in_gamma); set f := sval alpha_in_gamma. 
move=> [] inj_f eq_alphagamma.
rewrite /prod_Cexp_span_gamma (bigD1 _ inj_f) mulf_eq0 /=; apply/orP; left.
move/eqP: Lindemann_false => <-; apply/eqP; congr Cexp_span.
by apply/ffunP => i; rewrite eq_alphagamma ffunE.
Qed.

(* on le reconnait en tant que poly pour faire du th sym *)
Definition R : {mpoly complexR[L.+1]} :=
  \prod_(f : 'I_L.+1 ^ l.+1 | injectiveb f) 
     \sum_(i : 'I_l.+1) (a i) *: 'X_(f i).

(* egalité valeurs/horner *)
(* TODO : nom et = / == *)
Lemma R_Cexp_span_eq0 :
  (R.@[finfun (Cexp \o gamma)]) = prod_Cexp_span_gamma.
Proof.
rewrite /R /prod_Cexp_span_gamma !rmorph_prod.
apply: eq_bigr => f inj_f /=.
rewrite !(rmorph_sum _ (index_enum (ordinal_finType l.+1))) /=.
by apply: eq_bigr => i _; rewrite mevalZ mevalX !ffunE.
Qed.

(* coefficients entiers pour th sym *)
Lemma R_overCint : 
  R \is a (mpolyOver L.+1 Cint).
Proof.
apply: rpred_prod => f _ /=; apply: rpred_sum => i _ /=; rewrite -mul_mpolyC.
by apply: rpredM => /=; rewrite ?mpolyOverX ?mpolyOverC ?a_Cint.
Qed.

(* le poly est sym *)
Lemma R_sym :
  R \is symmetric.
Proof.
apply/issymP => s; rewrite rmorph_prod /R /=.
(* préparation pour un big_map *)
pose h := (fun (f : {ffun 'I_l.+1 -> 'I_L.+1}) => finfun (s \o f)).
pose F := (fun (f : {ffun 'I_l.+1 -> 'I_L.+1}) =>
      (\sum_(i < l.+1) (a i) *: 'X_(f i)) : {mpoly complexR[L.+1]}).            
have H_eqF (f : {ffun 'I_l.+1 -> 'I_L.+1}) : injectiveb f -> 
    msym s (\sum_(i < l.+1) (a i) *: 'X_(f i)) = F (h f).
  move=> _; rewrite rmorph_sum /=; apply: eq_bigr => i _.
  rewrite msymZ msymX; congr ((a i) *: @mpolyX _ _ _).
  apply/mnmP => j; rewrite mnmE mnmE mnm1E /h ffunE /=.
  by rewrite -(inj_eq (@perm_inj _ s)) permKV.
have H_eqP : forall f : {ffun 'I_l.+1 -> 'I_L.+1}, 
       injectiveb f = injectiveb (h f). 
  move=> f; rewrite /h /=; apply/injectiveP/injectiveP.
    by move/(inj_comp (@perm_inj _ s)) => Hinj x y; rewrite !ffunE; move/Hinj.
  by move=> H_inj x y eq_fxy; apply: H_inj; rewrite !ffunE /= eq_fxy.
rewrite (eq_bigr (fun f => F(h f)) H_eqF) (eq_bigl _ _ (H_eqP)).
rewrite [RHS](eq_bigr (fun f => F f)) // -(big_map h (fun f => injectiveb f) F).
apply: eq_big_perm; set r := index_enum _.
have r_uniq : uniq r by rewrite /r /index_enum -enumT enum_uniq.  
apply: (uniq_perm_eq _ r_uniq).
  rewrite map_inj_uniq // => f g; rewrite /h; move/ffunP => H_eq.
  by apply/ffunP => i; apply: (@perm_inj _ s); move: (H_eq i); rewrite !ffunE /=.
move=> f; rewrite mem_index_enum /h; apply/mapP.
exists (finfun ((fingroup.invg s) \o f)); rewrite ?mem_index_enum //.
by apply/ffunP => i; rewrite ffunE /= ffunE /= permKV.
Qed.

Lemma R_neq0 : R != 0.
Proof.
apply/prodf_neq0 => f /injectiveP f_inj; rewrite -msupp_eq0.
apply/negP => /eqP msupp_eqnil.
have : (U_(f ord0)%MM \in msupp (\sum_(i < l.+1) a i *: 'X_(f i))).
  rewrite (perm_eq_mem (msupp_sum _ _ _)); first last.
  + move=> i j _ _ /negbTE i_neqj m /=.
    rewrite ?(perm_eq_mem (msuppZ _ _)) ?a_neq0 // !msuppX !inE.
    by apply/negP => /andP[/eqP -> /eqP /mnm1_inj /f_inj /eqP]; rewrite i_neqj.
  + by rewrite /index_enum -enumT enum_uniq.
  apply/flatten_mapP; exists ord0; first by apply/map_f; rewrite mem_index_enum.
  by rewrite (perm_eq_mem (msuppZ _ _)) ?a_neq0 // msuppX inE.
by rewrite msupp_eqnil.
Qed.

Definition mpoly_gamma : 'X_{1..L.+1} -> complexR :=
   (fun (m : 'X_{1..L.+1}) => \sum_(i < L.+1) (gamma i) *+ (m i)).

Definition R_pair := [seq (m, (R@_m, mpoly_gamma m)) | m <- msupp R].


Search _ (_ \is symmetric).
Search _ "issym_".
issym_symmE:
  forall (n : nat) (R : ringType) (p : {mpoly R[n]}),
  p \is symmetric -> p = \sum_(m <- msupp p | sorted leq m) p@_m *: mmsym R m

Lemma R_pair_R :
  \sum_((R.@[finfun (Cexp \o gamma)]).
Proof.


(* on commence par partitionner suivant les coeffs *)


(* on partitionne suivant les degrés puis les coeff *)

Definition m_ord := finfun (fun i => 
    tnth (in_tuple (filter (fun m : 'X_{1..L.+1} => R@_m != 0) (msupp R))) i).

(* fonction de partition *)
Definition fpart := finfun ((@msort L.+1) \o m_ord).

Local Notation l_part := (size (filter (fun m : 'X_{1..L.+1} => R@_m != 0) (msupp R))).
Local Notation "''m_' md" := (mmsym _ md)
  (at level 8, md at level 2, format "''m_' md").

Definition morph_m : 'X_{1..L.+1} -> {mpoly complexR[L.+1]} :=
   (fun (m : 'X_{1..L.+1}) => \sum_(i < L.+1) 'X_i *+ (m i)).
Local Notation "''e_' md" := (morph_m md)
  (at level 8, md at level 2, format "''e_' md").

Lemma morph_m_neq0 m : m != 0%MM -> 'e_m != 0.
Proof.
move/eqP/mnmP => m_neq0; rewrite /morph_m; apply/eqP/mpolyP => eq_p.
apply: m_neq0 => i; move: eq_p; move/(_ U_( i)%MM).
rewrite linear_sum mcoeff0 /= (bigD1 i) //= mcoeffMn mcoeffX eq_refl /= mulr1n.
rewrite big1; [by move/eqP; rewrite addr0 pnatr_eq0 mnmE; move/eqP=> ->|].
move=> j /negbTE j_neq_i; rewrite mcoeffMn mcoeffX; case: eqP.
  by move=> /mnmP /(_ i); rewrite !mnmE j_neq_i eq_refl.
by move=> _; rewrite /= mul0rn.
Qed.

(* But : Lemma wlog3 l c (alpha : complexR ^ l.+1) (part : {set {set 'I_l.+1}}) 
  (a : complexR ^ l.+1) :
  c != 0 -> c \is a Cint -> injective alpha -> 
  partition part [set: 'I_l.+1] -> {in part, forall P : {set 'I_l.+1},
  [fset (alpha i) | i in P]%fset \is a setZroots c} ->
  (forall i : 'I_l.+1, a i != 0) -> (forall i : 'I_l.+1, a i \is a Cint) ->
  {in part, forall P : {set 'I_l.+1}, constant [seq a i | i in P]} -> 
  Cexp_span a alpha != 0. *)