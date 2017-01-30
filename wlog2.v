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
Require Import ajouts.

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
Variable pre_l : nat.
Hypothesis pre_l_gt0 : (0%N < pre_l)%N.
Variable pre_alpha : complexR ^ pre_l.
Hypothesis pre_alpha_inj : injective pre_alpha.
Hypothesis pre_alpha_algebraic : forall i : 'I_pre_l, pre_alpha i is_algebraic.
Variable pre_a : complexR ^ pre_l.
Hypothesis pre_a_neq0 : forall i : 'I_pre_l, pre_a i != 0.
Hypothesis pre_a_Cint : forall i : 'I_pre_l, pre_a i \is a Cint.
Hypothesis pre_Lindemann_false : Cexp_span pre_a pre_alpha == 0.

(* changement avec l.+1 *)
Definition l := pre_l.-1.


Definition alpha := 
  finfun (tnth [tuple pre_alpha (cast_ord (prednK pre_l_gt0) i) | i < l.+1]).

Lemma alpha_inj : injective alpha.
Proof.
move=> i j; rewrite !ffunE !tnth_map.
by move/pre_alpha_inj /cast_ord_inj; rewrite !tnth_ord_tuple.
Qed.

Lemma alpha_algebraic : forall i : 'I_l.+1, alpha i is_algebraic.
Proof. by move=> i; rewrite ffunE tnth_map; apply: pre_alpha_algebraic. Qed.

Definition a := 
  finfun (tnth [tuple pre_a (cast_ord (prednK pre_l_gt0) i) | i < l.+1]).

Lemma a_neq0 : forall i : 'I_l.+1, a i != 0.
Proof. by move=> i; rewrite ffunE tnth_map; apply: pre_a_neq0. Qed.

Lemma a_Cint : forall i : 'I_l.+1, a i \is a Cint.
Proof. by move=> i; rewrite ffunE tnth_map; apply: pre_a_Cint. Qed.

Lemma Lindemann_false : Cexp_span a alpha == 0.
Proof. 
apply/eqP; move/eqP : pre_Lindemann_false => <-; rewrite /Cexp_span.
rewrite (big_ord_widen_leq pre_l) ?(prednK pre_l_gt0) //.
apply: eq_big => i; first by rewrite /= -ltnS (prednK pre_l_gt0) ltn_ord.
move=> _; rewrite !ffunE !tnth_map. 
congr (pre_a _ * Cexp (pre_alpha _)); rewrite tnth_ord_tuple /=.
  by apply: ord_inj => /=; rewrite inordK ?(prednK pre_l_gt0) //.
by apply: ord_inj => /=; rewrite inordK ?(prednK pre_l_gt0) //.
Qed.

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

Lemma gamma_set_roots : [fset gamma i | i : 'I_L.+1]%fset  \is a setZroots c.
Proof. 
suff -> : [fset gamma i | i : 'I_L.+1]%fset = seq_fset (seqroots poly_gamma).
  apply: set_roots_seqroots; last by apply: poly_gamma_Cint.
  by have /and3P[_ H _] := svalP (polyMinseq alpha_algebraic).
apply/fsetP => x; rewrite seq_fsetE -[seqroots _]/(tval (Tuple size_gamma)).
apply/imfsetP/idP => [[] i _ -> | ]; first by rewrite /gamma ffunE mem_tnth.
by move/tnthP => [i ->]; exists i => //=; rewrite /gamma ffunE.
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
  (R.@[finfun (Cexp \o gamma)]) == 0.
Proof.
apply/eqP; rewrite /R -[RHS](elimT eqP prod_Cexp_span_gamma_eq0).
rewrite /prod_Cexp_span_gamma !rmorph_prod; apply: eq_bigr => f inj_f /=.
rewrite !(rmorph_sum _ (index_enum (ordinal_finType l.+1))) /=.
by apply: eq_bigr => i _; rewrite mevalZ mevalX !ffunE.
Qed.

(* coefficients entiers pour th sym *)
Lemma R_overCint : 
  R \is a (mpolyOver L.+1 Cint).
Proof.
apply: rpred_prod => f _ /=.
apply: rpred_sum => i _ /=; rewrite -mul_mpolyC.
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

(* on partitionne suivant les degrés puis les coeff *)

Definition mfun_t := finfun (fun i => 
    tnth (in_tuple (filter (fun m : 'X_{1..L.+1} => sorted leq m) (msupp R))) i).
Local Notation t := (size (filter (fun m : 'X_{1..L.+1} => sorted leq m) (msupp R))).

Local Notation "''m_' md" := (mmsym _ md)
  (at level 8, md at level 2, format "''m_' md").

Definition mpoly_gamma : 'X_{1..L.+1} -> {mpoly complexR[L.+1]} :=
   (fun (m : 'X_{1..L.+1}) => \sum_(i < L.+1) 'X_i *+ (m i)).

Lemma mpoly_gamma_neq0 m : m != 0%MM -> mpoly_gamma m != 0.
Proof.
move/eqP/mnmP => m_neq0; rewrite /mpoly_gamma; apply/eqP/mpolyP => eq_p.
apply: m_neq0 => i; move: eq_p; move/(_ U_( i)%MM).
rewrite linear_sum mcoeff0 /= (bigD1 i) //= mcoeffMn mcoeffX eq_refl /= mulr1n.
rewrite big1; [by move/eqP; rewrite addr0 pnatr_eq0 mnmE; move/eqP=> ->|].
move=> j /negbTE j_neq_i; rewrite mcoeffMn mcoeffX; case: eqP.
  by move=> /mnmP /(_ i); rewrite !mnmE j_neq_i eq_refl.
by move=> _; rewrite /= mul0rn.
Qed.

Definition ta := finfun 
   ((fun m => (size (msupp ('m_m : {mpoly complexR[L.+1]}))).-1) \o mfun_t).

Lemma tuple_ta i : 
   size (msupp ('m_(mfun_t i) : {mpoly complexR[L.+1]})) == (ta i).+1.
Proof. by rewrite /ta ffunE /= prednK // lt0n size_eq0 msupp_eq0 mmsym_neq0. Qed.


(* ne peut pas être une finfun, puisque le type renvoyé dépend de la valeur de j :
  la taille de sum_gamma j est ta j, et change ... *)
(* solution moisie : des seq de seq *)
Definition sum_gamma := (fun j : 'I_t  => 
   (finfun ((meval gamma) \o mpoly_gamma \o (tnth (Tuple (tuple_ta j)))))).

Local Notation "''s_' ( n , k )" := (@mesym n _ k).

Lemma blabla im : 
  [seq ((sum_gamma im) j) | j : 'I_(ta im).+1] 
  \is a seqZroots (c ^+ ((msize (mpoly_gamma (mfun_t im))).-1 * (ta im).+1).+1).
Proof.
set m := mfun_t im.
have m_in : m \in msupp R. 
  move: (mem_tnth im (in_tuple (filter (fun m : 'X_{1..L.+1} => sorted leq m) (msupp R)))).
  by rewrite mem_filter /m /mfun_t ffunE => /andP[_].
rewrite set_rootsE.
apply/polyOverP => i; rewrite coefZ. 
have [|] := (ltnP i (ta im).+2).
  rewrite ltnS leq_eqVlt => /orP [/eqP i_nn | ordi].
    rewrite rpredM ?rpredX ?c_Cint // i_nn.
    set P := \prod_(_ <- _ | _) _.
    have H_P : ((size P).-1 <= (ta im).+1)%N.
      rewrite size_prod_XsubC -card_fsetE. 

Search _ (imfset _ _) in finmap.

card_imfset ?card_finset ?card_ord //.
      move=> x y; rewrite /sum_gamma !ffunE /=.

Search _ card in finmap.

/index_enum -enumT size_enum_ord ffunE /=.
    have -> : P`_(size P).-1 = lead_coef P by [].
    by rewrite (monicP _) ?Cint1 ?/P ?rpred_prod // => j _; rewrite monicXsubC.
  have ordinn1 : (i < (ta im).+2)%N by apply: (leq_trans ordi (leqnSn _)).
  rewrite (ordnat ordinn1) mroots_coeff_proper -mulrCA rpredM //=.
    by rewrite rpredX ?rpredN ?Cint1.
  have -> : sum_gamma im = finfun (tnth (map_tuple (meval gamma) 
              (map_tuple mpoly_gamma (Tuple (tuple_ta im))))).
    by apply/ffunP => x; rewrite /sum_gamma !ffunE /= !tnth_map.
  rewrite (eq_meval _ (ffunE _)) -meval_comp_mpoly.
  move P_eq : (_ \mPo _) => P.
  have P_Over : P \is a mpolyOver L.+1 Cint.
    rewrite -P_eq comp_mpolyE rpred_sum // => m' _.
    rewrite mpolyOverZ ?mcoeff_mesym ?Cint_Cnat ?Cnat_nat //.
    rewrite rpred_prod // => j _; rewrite tnth_map rpredX // /mpoly_gamma.
    by rewrite rpred_sum // => k _; rewrite rpredMn // mpolyOverX.
  have msym_mpoly_gamma s : (msym s \o mpoly_gamma) =1 (mpoly_gamma \o (mperm (s^-1)%g)).
    move=> m1 /=; rewrite /mpoly_gamma linear_sum /=; symmetry.
    rewrite (reindex_inj (@perm_inj _ s)) /=; apply: eq_bigr => j _.
    rewrite rmorphMn /= msymX; congr ('X_[ _ ] *+ _). 
      rewrite /=; apply/mnmP => k; rewrite mnmE !mnm1E /=.
      case: (boolP (s j == k)) => [/eqP <- | ]; first by rewrite permK eq_refl.
      move/negP => H; symmetry; congr nat_of_bool; apply/negP => /eqP eq_j.        
      by apply: H; rewrite eq_j permKV.
    by rewrite /mperm mnmE permK.
  have P_sym : P \is symmetric.
    rewrite -P_eq msym_comp_poly ?mesym_sym // => s.
    set t := map_tuple _ _.
    have -> /= : [tuple msym s t`_i0 | i0 < (ta im).+1] = map_tuple (msym s) t.
      apply/eq_from_tnth => x.
      by rewrite tnth_map -tnth_nth tnth_ord_tuple [in RHS]tnth_map.
    rewrite -map_comp (eq_map (msym_mpoly_gamma _)).
    rewrite [X in perm_eq _ X]map_comp; apply: perm_map; apply: uniq_perm_eq.
    + by apply: msupp_uniq.
    + rewrite map_inj_uniq ?msupp_uniq // => m1 m2.
      rewrite /mperm => /mnmP /= eq_ms; apply/mnmP => j; rewrite -(permK s j).
      by move: (eq_ms (s j)); rewrite !mnmE.
    move=> m1; apply/idP/mapP => [ | [m2 m2_in] /esym H].
      rewrite msupp_mmsymP bla1 => /existsP [s' /eqP eq_s'].
      exists (mperm (s * s'^-1)%g m); rewrite ?msupp_mmsymP ?bla1. 
        apply/existsP; exists (s' * s^-1)%g.
        by rewrite /mperm !mpermM mpermKV mpermK.
      by rewrite /m -eq_s' /mperm; apply/mnmP => j; rewrite !mnmE permM /= !permKV.
    rewrite msupp_mmsymP perm_eq_sym bla1 -H; apply/existsP. 
    move: m2_in; rewrite msupp_mmsymP bla1 => /existsP[s' /eqP eq_s'].
    exists (s^-1 * (s' ^-1))%g; rewrite -eq_s' /mperm; apply/eqP/mnmP => j.
    by rewrite !mnmE permM permKV.
  have H := (sym_fundamental_set_roots gamma_set_roots P_Over P_sym).
  suff Hle : (msize P <= ((msize (mpoly_gamma m)).-1 * (ta im).+1).+1)%N.
    by rewrite -(subnK Hle) exprD -mulrA rpredM ?rpredX ?c_Cint.
  rewrite -P_eq comp_mpolyE; apply: (leq_trans (msize_sum _ _ _)).
  rewrite -[msupp 's_( _ , _)]/(tval (in_tuple (msupp _))) big_tuple.
  apply/bigmax_leqP => j _; rewrite msizeZ; last first.
    by rewrite -mcoeff_msupp (tnth_nth 0%MM) in_tupleE mem_nth.
  move eq_m': (tnth _ j) => m'.
  have : m' \in (in_tuple (msupp ('s_((ta im).+1, ((ta im).+1 - i)) : {mpoly complexR[(ta im).+1]}))).
    by rewrite -eq_m' mem_tnth.
  rewrite mem_msupp_mesym /mechar => /andP[/eqP m'_mdeg /forallP m'_i].
  rewrite -[X in (_ * X)%N](subn0 (ta im).+1) mulnC -sum_nat_const_nat big_mkord.
  rewrite (eq_bigr (fun k => if (m' k != 0%N) 
     then (mpoly_gamma (tnth (Tuple (tuple_ta im)) k)) else 1)); last first.
    move=> k _; move: (m'_i k); move: (m' k) => x; case: x; [| case]; rewrite //.
    by move=> _; rewrite expr1 /= tnth_map.
  apply: (@leq_trans (\sum_(i0 < (ta im).+1 | m' i0 != 0) (msize (mpoly_gamma m)).-1).+1%N).
    rewrite -big_mkcond /= -big_filter -(big_filter (index_enum _)).
    move r_eq: (filter _ (index_enum _)) => r.      
    apply: (big_ind2 (fun x y => (msize x <= y.+1)%N)).
    + by rewrite msize1.
    + move=> u su v sv Hu Hv.
      have [->|nz_p ] := eqVneq u 0; first by rewrite mul0r msize0.
      have [->|nz_q ] := eqVneq v 0; first by rewrite mulr0 msize0.
      have [->|nz_pq] := eqVneq (u * v) 0; first by rewrite msize0.
      by rewrite msizeM // -subn1 leq_subLR add1n -addnS -addSn leq_add.
    + move=> k _; rewrite [X in (_ <= X)%N]prednK; last first.
        rewrite lt0n msize_poly_eq0 mpoly_gamma_neq0 //.
        apply/negP => /eqP m_eq0. 
        suff : 0%MM \notin msupp R by move/negP; apply; rewrite -m_eq0.
        rewrite -mcoeff_eq0 /R rmorph_prod /=; apply/prodf_eq0.
        exists (sval alpha_in_gamma); first by move: (svalP alpha_in_gamma) =>[].
        apply/eqP; rewrite rmorph_sum /= big1 // => x _.
        by rewrite mcoeffZ mcoeffX /= mnm1_eq0 /= mulr0.
      move=> {i ordi ordinn1 P P_eq P_Over P_sym H j m' eq_m' m'_mdeg m'_i r r_eq}.
      move m0_eq : (tnth _ _) => m0 /=.
      have : m0 \in msupp (('m_m) : {mpoly complexR[L.+1]}). 
        by rewrite -m0_eq (tnth_nth 0%MM) /= mem_nth ?(elimT eqP (tuple_ta im)).
      rewrite msupp_mmsymP => /tuple_perm_eqP [s /val_inj /= eq_ms].
      have -> : m = mperm s m0.      
        have -> : m = Multinom (multinom_val m) by apply/mnmP => i.
        by apply/mnmP => i; rewrite eq_ms mnmE.
      move: (msym_mpoly_gamma (s^-1)%g m0); rewrite /= invgK => <-.
      move: (mpoly_gamma _) => P; move: (s^-1)%g => {s eq_ms m0 m0_eq m k m_in} s.
      elim/mpolyind: P => [ | c m P m_in c_neq0 ihp].
        by rewrite msym0 leqnn.
      rewrite msymD msymZ msymX !msizeE !(eq_big_perm _ (msuppD _)) /=; last first.
        + move=> m' /=; rewrite (perm_eq_mem (msuppZ _ c_neq0)) msuppX inE.
          by apply/andP => [] [/eqP ->]; apply/negP.
        + move=> m' /=; rewrite (perm_eq_mem (msuppZ _ c_neq0)) msuppX inE.
          apply/andP => [] [/eqP ->]; rewrite mcoeff_msupp mcoeff_sym mpermK.
          by rewrite -mcoeff_msupp; apply/negP.
      rewrite !big_cat -!msizeE !msizeZ // !msizeX mdeg_mperm geq_max leq_maxl.
      by rewrite /=; apply: (leq_trans ihp); rewrite leq_maxr.
  rewrite big_mkcond /= ltnS; apply: (big_ind2 leq) => //. 
    by move=> u1 u2 v1 v2; apply: leq_add.
  by move=> k _; case: ifP => _.
move=> i_gt.
rewrite rpredM ?rpredX ?c_Cint //.
have /leq_sizeP -> := i_gt; first by apply: Cint0.
by rewrite size_prod_XsubC /index_enum -enumT size_enum_ord.
Qed.


(* Récupérer els coeffs *)
Definition b := finfun ((fun m => mcoeff m R) \o mfun_t).

(* Virer les coeffs nuls *)
Definition reindex_seq :=   
  filter (fun i => b i != 0) (enum 'I_t).

Lemma final_l_gt0 : (0 < size reindex_seq)%N.
Proof.
rewrite lt0n; apply/negP => /eqP; rewrite /reindex_seq size_filter.
set a := (fun i => b _ != 0); set r := filter _ _; set s := enum _ => Hcount.
move: (count_predC a s); rewrite Hcount add0n.
move/eqP; rewrite -all_count.
have /eq_all -> : predC a =1 (fun i => b i == 0).
  by move => i; rewrite /a /=; apply/negPn/idP.
rewrite -/r; move=> /allP H {Hcount} {a}.
have {H r s} : R == 0.
  rewrite (issym_symmE R_sym) -/r big_seq_cond big1 // => m /andP[m_in m_sort].
  apply/eqP; rewrite scaler_eq0; apply/orP; left.
  have ordm : (index m r < size r)%N by rewrite index_mem mem_filter m_in m_sort.
  have -> : R@_m = b (Ordinal ordm).
    rewrite /b ffunE /= /mfun_t ffunE (tnth_nth 0%MM) /= -/r nth_index //. 
    by rewrite -index_mem.
  by apply: H; rewrite mem_enum.
rewrite -mleadc_eq0 /R mleadc_prod_proper.
  move/prodf_eq0 => [] f /injectiveP f_inj; rewrite mleadc_eq0 -msupp_eq0 => /eqP H.
  suff : (U_( f ord0))%MM \in [::] by [].
  rewrite -H mcoeff_msupp linear_sum /= (bigD1 ord0) /= ?big1 //.
    by rewrite addr0 mcoeffZ mcoeffX eq_refl mulr1 a_neq0.
  move=> i /negbTE i_neq0; rewrite mcoeffZ mcoeffX (inj_eq (@mnm1_inj _)). 
  by rewrite (inj_eq f_inj) i_neq0 mulr0.
move=> f f_in /injectiveP f_inj.
apply: mulrI0_lreg => x; move/eqP; rewrite mulf_eq0 => /orP[ | /eqP -> //].
rewrite mleadc_eq0 -msupp_eq0 => /eqP H.
suff : (U_( f ord0))%MM \in [::] by [].
rewrite -H mcoeff_msupp linear_sum /= (bigD1 ord0) /= ?big1 //.
  by rewrite addr0 mcoeffZ mcoeffX eq_refl mulr1 a_neq0.
move=> i /negbTE i_neq0; rewrite mcoeffZ mcoeffX (inj_eq (@mnm1_inj _)). 
by rewrite (inj_eq f_inj) i_neq0 mulr0.
Qed.

(* Eliminer les coeffs nuls *)
Definition final_b := finfun (b \o (tnth (in_tuple reindex_seq))).

Definition final_t := finfun ((fun i => (ta i).+1) \o (tnth (in_tuple reindex_seq))). 

Definition final_l := (\sum_(i < size reindex_seq) final_t i)%N.

Definition pre_fta := ([seq tval (Tuple (tuple_ta 
       (tnth (in_tuple reindex_seq) i))) | i <- enum 'I_(size reindex_seq)]).
Definition flatten_ta := flatten pre_fta.

Lemma shape_ta : shape pre_fta = 
     tval [tuple final_t i | i < size reindex_seq].
Proof.
rewrite /shape -map_comp -val_ord_tuple -[map _ (tval _)]/(tval (map_tuple _ _)).
congr tval; apply/eq_from_tnth => i.
rewrite /final_t !tnth_map !tnth_ord_tuple ffunE /=; set j := tnth _ _.
by rewrite /ta ffunE /= prednK // lt0n size_eq0 msupp_eq0 mmsym_neq0.
Qed.

Definition final_alpha := finfun ((meval gamma) \o mpoly_gamma \o (tnth (in_tuple flatten_ta))).

Lemma final_alpha_algebraic : 
    forall i : 'I_(size flatten_ta), final_alpha i is_algebraic.
Proof.
move=> i; rewrite ffunE /= ; move: (tnth _ _) => j {i}.
rewrite mevalE; apply: big_ind.
+ by apply: algebraic0.
+ by move=> u v; apply: algebraic_add.
move=> m _; apply: algebraic_mul.
  rewrite /mpoly_gamma linear_sum /=; apply: big_ind.
  + by apply: algebraic0.
  + by move=> u v; apply: algebraic_add.
  move=> i _; rewrite mcoeffMn mcoeffX; case: eqP => _.
    by rewrite mulr1n integral_algebraic; apply: integral_nat.
  by rewrite mul0rn; apply: algebraic0.
apply: big_ind.
+ by apply: algebraic1.
+ by move=> u v; apply: algebraic_mul.
move=> i _; move: (m i); elim => [ | n ihn].
  by rewrite expr0; apply: algebraic1.
rewrite exprS; apply: algebraic_mul => //.
rewrite ffunE /= (tnth_nth 0) /= integral_algebraic.
apply: (integral_root poly_gamma_neq0).
  apply/seqrootsP; first by apply: poly_gamma_neq0.
  by apply: mem_nth; rewrite (elimT eqP size_gamma).
move=> x /(nthP 0) [k ordk <-].
have /polyOverP /(_ k) /CintP [y] := poly_gamma_Cint.
by rewrite -ratr_int => ->; apply: integral_id.
Qed.

Lemma final_b_neq0 : 
    forall i : 'I_(size reindex_seq), final_b i != 0.
Proof.
move=> i; rewrite ffunE /=; move: (mem_tnth i (in_tuple reindex_seq)).
by set j := tnth _ _; rewrite memtE /= /reindex_seq mem_filter => /andP[].
Qed.

Lemma final_b_Cint : 
    forall i : 'I_(size reindex_seq), final_b i \is a Cint.
Proof.
move=> i; rewrite ffunE /=; move: (tnth _ _) => j {i}; rewrite ffunE /=.
by have /mpolyOverP /(_ (mfun_t j)) := R_overCint.
Qed.

Lemma ord_final (i : 'I_(size reindex_seq)) (j : ('I_(final_t i))) :
  (sumn (shape (take i pre_fta)) + j < size flatten_ta)%N.
(*  ((\sum_(k < size reindex_seq | k < i) (final_t k)) + j < size flatten_ta)%N.
  (sumn (shape (take i pre_fta)) + index x s) *)
Proof.
rewrite size_flatten /shape -!ssrcomplements.bignat_sumn -/size.
rewrite -{2}(cat_take_drop i pre_fta) big_cat /= ltn_add2l.
rewrite (drop_nth [::0%MM]) ?size_tuple ?card_ord //= big_cons.
rewrite -[X in (X < _)%N]addn0 -addSn leq_add //.
have -> // : size (nth [:: 0%MM] pre_fta i) = (final_t i).
rewrite /pre_fta /final_t ffunE /= /ta ffunE /= prednK; last first.
  by rewrite lt0n size_eq0 msupp_eq0 mmsym_neq0.
rewrite -val_ord_tuple -[map _ _]/(tval (map_tuple _ _)) -tnth_nth tnth_map.
by rewrite tnth_ord_tuple.
Qed.

Lemma final_alpha_setZroots : forall (i : 'I_(size reindex_seq)),
  (finfun (fun j : 'I_(final_t i) => final_alpha (Ordinal (ord_final j)))) 
  \is a setZroots (c ^+ ((msize (mpoly_gamma 
          (mfun_t (tnth (in_tuple reindex_seq) i)))).-1 * (final_t i)).+1).
Proof.
move=> i0; set f := finfun _; move eq_i : (tnth _ _) => i.
have H1 : (ta i).+1 = (final_t i0) by rewrite /final_t ffunE /= -eq_i.
have := (blabla i); rewrite !set_rootsE.
congr (c ^+ (_ * _).+1 *: _ \is a polyOver Cint); first by rewrite H1.
rewrite /index_enum -!enumT -!val_ord_tuple.
set r1 := ord_tuple _; set r2 := ord_tuple _.
have -> : r2 =  tcast H1 (map_tuple (cast_ord H1) r1).
  apply: (eq_from_tnth _) => j; rewrite tcastE tnth_map /r2 /r1 !tnth_ord_tuple.
  by rewrite cast_ordKV.
apply: esym; rewrite [X in X = _]/= ssrcomplements.tval_tcast big_map.
apply: big_ind2 => //; first by move => x1 x2 y1 y2 -> ->.
move=> j _; congr ('X - (_)%:P); rewrite /f /sum_gamma /final_alpha /= !ffunE /=.
congr (mpoly_gamma _).@[gamma]; rewrite !(tnth_nth 0%MM) [LHS]/= /flatten_ta. 
apply: (@nth_flatten_proper _ [::0%MM] 0%MM); last first.
+ by rewrite size_tuple.
+ rewrite /pre_fta -val_ord_tuple -[map _ _]/(tval (map_tuple _ _)) -tnth_nth.
  by rewrite tnth_map tnth_ord_tuple eq_i.
by rewrite /pre_fta size_map size_enum_ord.
Qed.


Lemma final_wlog1_false : 
  \sum_(i < size reindex_seq) 
  (Cexp_span (finfun (fun j : 'I_(final_t i) => final_b i)) 
  (finfun (fun j : 'I_(final_t i) => final_alpha (Ordinal (ord_final j))))) == 0.
Proof.
rewrite -[X in _ == X](elimT eqP R_Cexp_span_eq0) /Cexp_span. 
apply/eqP; apply: esym; rewrite {1}(issym_symmE R_sym) linear_sum /=.
rewrite -[X in X = _]big_filter -[filter _ _]/(tval (in_tuple (filter _ _))).
rewrite big_tuple.
rewrite (eq_bigr (fun i => if (b i != 0) then (R@_(mfun_t i) * (('m_(mfun_t i)).@[finfun (Cexp \o gamma)])) else 0)); last first.
  move=> i _; rewrite /mfun_t /= ffunE mevalZ; case: ifP => [_ // | /eqP].
  by rewrite /b ffunE /mfun_t /= ffunE /= => ->; rewrite mul0r.
rewrite -big_mkcond /= -big_filter /= {1}/index_enum -enumT -/reindex_seq.
rewrite big_tnth /=; apply: eq_bigr => i _.
rewrite (eq_bigr (fun j => R@_(mfun_t (tnth (in_tuple reindex_seq) i)) * Cexp (final_alpha (Ordinal (ord_final j))))); last first.
  by move=> j _; rewrite !ffunE /= /b ffunE /=.
rewrite -big_distrr /=; congr (_ * _).
rewrite /=; set j := tnth _ _.
rewrite mevalE -[msupp _]/(tval (Tuple (tuple_ta j))).
rewrite big_tuple.
have Heq : (ta j).+1 = final_t i by rewrite /j /final_t ffunE /= ffunE.  
have -> : index_enum (ordinal_finType (final_t i)) =
   map (cast_ord Heq) (index_enum (ordinal_finType ((ta j).+1))).
  apply: (@eq_from_nth _ (cast_ord Heq ord0)).
    by rewrite size_map /index_enum -!enumT !size_enum_ord Heq.
  move => k; rewrite /index_enum -!enumT size_enum_ord => ordk.
  rewrite (nth_map ord0) ?Heq // {1}(ordnat ordk) ?size_enum_ord //.
  rewrite ?nth_ord_enum /=.
  have ordk2: (k < (ta j).+1)%N by rewrite Heq.
  rewrite {2}(ordnat ordk2) nth_ord_enum.
  by apply/ord_inj.
rewrite big_map /=; apply: eq_bigr => k _.
set md := tnth _ _.
have -> : ('m_(mfun_t j) : {mpoly complexR[ _ ]})@_md = 1.
  rewrite mcoeff_mmsym -{2}[1]/((nat_of_bool true)%:R).
  congr ((nat_of_bool _)%:R).
  rewrite /md (tnth_nth 0%MM) /= -(msupp_mmsymP complexR_ringType).
  apply: mem_nth; move: (ltn_ord k). 
  rewrite [in X in (_ < X)%N]ffunE /= prednK //.
  by rewrite lt0n size_eq0 msupp_eq0 mmsym_neq0.
rewrite mul1r /final_alpha ffunE /= /mpoly_gamma linear_sum. 
rewrite (big_morph _ Cexp_morph Cexp0) /=.
apply: eq_bigr => l _.
rewrite ffunE /= CexpRX rmorphMn /= mevalX.
congr (Cexp (_ *+ (_ _))).
rewrite /md !(tnth_nth 0%MM) [RHS]/= /flatten_ta. 
apply: esym.
rewrite (@nth_flatten_proper _ [::0%MM] 0%MM pre_fta (Tuple (tuple_ta j)) i k) //.
    by rewrite size_map size_enum_ord.
  rewrite (nth_map i) ?size_enum_ord //= /j. 
  congr (msupp 'm_(mfun_t (tnth _ _))).
  by apply/ord_inj; rewrite nth_enum_ord.
by rewrite size_tuple.
Qed.

Search _ "part".
Print preim_partition.

About partition.


(* Theoreme wlog2 *)
Lemma wlog2 : 
  exists (f_l : nat) (f_alpha : complexR ^ f_l) (f_a : complexR ^ f_l), 
  (0%N < f_l)%N /\ injective f_alpha /\ 
  (forall i : 'I_f_l, f_alpha i is_algebraic) /\
  (forall i : 'I_f_l, f_a i != 0) /\ (forall i : 'I_f_l, f_a i \is a Cint) /\
  (Cexp_span f_a f_alpha == 0).
Proof.
exists (size reindex_seq); exists final_alpha; exists final_b.
split; first by apply: final_l_gt0.
split; first by apply: final_alpha_inj.
split; first by apply: final_alpha_algebraic.
split; first by apply: final_b_neq0.
split; first by apply: final_b_Cint.
by apply: final_Lindemann_false.
Qed.

End Wlog2. 



Theorem wlog2_wlog1 :
  (forall (l : nat) (alpha : complexR ^ l) (a : complexR ^ l),
  (0%N < l)%N -> injective alpha -> (forall i : 'I_l, alpha i is_algebraic) ->
  (forall i : 'I_l, a i != 0) -> (forall i : 'I_l, a i \in Cint) ->
  (Cexp_span a alpha != 0)) ->
  forall (l : nat) (alpha : complexR ^ l) (a : complexR ^ l),
  (0%N < l)%N -> injective alpha -> (forall i : 'I_l, alpha i is_algebraic) ->
  (forall i : 'I_l, a i != 0) -> (forall i : 'I_l, a i is_algebraic) ->
  (Cexp_span a alpha != 0).
Proof. 
move=> ih l alpha a l_gt0 alpha_inj alpha_alg a_neq0 a_alg; apply/negP => Hspan.
move: (wlog1 l_gt0 alpha_inj alpha_alg a_neq0 a_alg Hspan) => [fl [falpha [fa]]].
move=> [] fl_gt0 [] falpha_inj [] falpha_alg [] fa_neq0 [] fa_Cint Hspan_eq0.
move: (ih fl falpha fa fl_gt0 falpha_inj falpha_alg fa_neq0 fa_Cint).
by rewrite Hspan_eq0.
Qed.


(*
Lemma tuple_msuppU m : size (msupp (U m)) == (size (msupp (U m))).-1.+1.
Proof. by rewrite prednK // /U lt0n size_eq0 msupp_eq0 mmsym_neq0. Qed.


Definition sum_gamma m := 
   map_tuple (meval gamma) (map_tuple mpoly_gamma 
   (Tuple (tuple_msuppU m))).

Local Notation "''s_' ( n , k )" := (@mesym n _ k).

Lemma blabla m :
  m \in msupp R -> 
  (finfun (tnth (sum_gamma m))) \is a setZroots 
      (c ^+ ((msize (mpoly_gamma m)).-1 * (size (msupp (U m))).-1.+1).+1).
Proof.
move=> m_in; rewrite set_rootsE.
apply/polyOverP => i; rewrite coefZ. 
set nn := (size _).-1.+1.
have [|] := (ltnP i nn.+1).
  rewrite ltnS leq_eqVlt => /orP [/eqP i_nn | ordi].
    rewrite rpredM ?rpredX ?c_Cint // i_nn.
    set P := \prod_ _ _.
    have <- : (size P).-1 = nn.
      by rewrite size_prod_XsubC /index_enum -enumT size_enum_ord.
    have -> : P`_(size P).-1 = lead_coef P by [].
    by rewrite (monicP _) ?Cint1 ?/P ?rpred_prod // => j _; rewrite monicXsubC.
  have ordinn1 : (i < nn.+1)%N by apply: (leq_trans ordi (leqnSn _)).
  rewrite (ordnat ordinn1) mroots_coeff_proper -mulrCA rpredM //=.
    by rewrite rpredX ?rpredN ?Cint1.
  rewrite (eq_meval _ (ffunE _)) -meval_comp_mpoly.
  move P_eq : (_ \mPo _) => P.
  have P_Over : P \is a mpolyOver L.+1 Cint.
    rewrite -P_eq comp_mpolyE rpred_sum // => m' _.
    rewrite mpolyOverZ ?mcoeff_mesym ?Cint_Cnat ?Cnat_nat //.
    rewrite rpred_prod // => j _; rewrite tnth_map rpredX // /mpoly_gamma.
    by rewrite rpred_sum // => k _; rewrite rpredMn // mpolyOverX.
  have msym_mpoly_gamma s : (msym s \o mpoly_gamma) =1 (mpoly_gamma \o (mperm (s^-1)%g)).
    move=> m1 /=; rewrite /mpoly_gamma linear_sum /=; symmetry.
    rewrite (reindex_inj (@perm_inj _ s)) /=; apply: eq_bigr => j _.
    rewrite rmorphMn /= msymX; congr ('X_[ _ ] *+ _). 
      rewrite /=; apply/mnmP => k; rewrite mnmE !mnm1E /=.
      case: (boolP (s j == k)) => [/eqP <- | ]; first by rewrite permK eq_refl.
      move/negP => H; symmetry; congr nat_of_bool; apply/negP => /eqP eq_j.        
      by apply: H; rewrite eq_j permKV.
    by rewrite /mperm mnmE permK.
  have P_sym : P \is symmetric.
    rewrite -P_eq msym_comp_poly ?mesym_sym // => s.
    set t := map_tuple _ _.
    have -> /= : [tuple msym s t`_i0 | i0 < nn] = map_tuple (msym s) t.
      apply/eq_from_tnth => x.
      by rewrite tnth_map -tnth_nth tnth_ord_tuple [in RHS]tnth_map.
    rewrite -map_comp (eq_map (msym_mpoly_gamma _)).
    rewrite [X in perm_eq _ X]map_comp; apply: perm_map; apply: uniq_perm_eq.
    + by apply: msupp_uniq.
    + rewrite map_inj_uniq ?msupp_uniq // => m1 m2.
      rewrite /mperm => /mnmP /= eq_ms; apply/mnmP => j; rewrite -(permK s j).
      by move: (eq_ms (s j)); rewrite !mnmE.
    rewrite /U; move=> m1; apply/idP/mapP => [ | [m2 m2_in] /esym H].
      rewrite msupp_mmsymP bla1 => /existsP [s' /eqP eq_s'].
      exists (mperm (s * s'^-1)%g m); rewrite /U ?msupp_mmsymP ?bla1. 
        apply/existsP; exists (s' * s^-1)%g.
        by rewrite /mperm !mpermM mpermKV mpermK.
      by rewrite -eq_s' /mperm; apply/mnmP => j; rewrite !mnmE permM /= !permKV.
    rewrite msupp_mmsymP perm_eq_sym bla1 -H; apply/existsP. 
    move: m2_in; rewrite msupp_mmsymP bla1 => /existsP[s' /eqP eq_s'].
    exists (s^-1 * (s' ^-1))%g; rewrite -eq_s' /mperm; apply/eqP/mnmP => j.
    by rewrite !mnmE permM permKV.
  have H := (sym_fundamental_set_roots gamma_set_roots P_Over P_sym).
  suff Hle : (msize P <= ((msize (mpoly_gamma m)).-1 * nn).+1)%N.
    by rewrite -(subnK Hle) exprD -mulrA rpredM ?rpredX ?c_Cint.
  rewrite -P_eq comp_mpolyE; apply: (leq_trans (msize_sum _ _ _)).
  rewrite -[msupp _]/(tval (in_tuple (msupp _))) big_tuple.
  apply/bigmax_leqP => j _; rewrite msizeZ; last first.
    by rewrite -mcoeff_msupp (tnth_nth 0%MM) in_tupleE mem_nth.
  move eq_m': (tnth _ j) => m'.
  have : m' \in (in_tuple (msupp ('s_(nn, (nn - i)) : {mpoly complexR[nn]}))).
    by rewrite -eq_m' mem_tnth.
  rewrite mem_msupp_mesym /mechar => /andP[/eqP m'_mdeg /forallP m'_i].
  rewrite -[X in (_ * X)%N](subn0 nn) mulnC -sum_nat_const_nat big_mkord.
  rewrite (eq_bigr (fun k => if (m' k != 0%N) 
     then (mpoly_gamma (tnth (Tuple (tuple_msuppU m)) k)) else 1)); last first.
    move=> k _; move: (m'_i k); move: (m' k) => x; case: x; [| case]; rewrite //.
    by move=> _; rewrite expr1 /= tnth_map.
  apply: (@leq_trans (\sum_(i0 < nn | m' i0 != 0) (msize (mpoly_gamma m)).-1).+1%N).
    rewrite -big_mkcond /= -big_filter -(big_filter (index_enum _)).
    move r_eq: (filter _ _) => r.      
    apply: (big_ind2 (fun x y => (msize x <= y.+1)%N)).
    + by rewrite msize1.
    + move=> u su v sv Hu Hv.
      have [->|nz_p ] := eqVneq u 0; first by rewrite mul0r msize0.
      have [->|nz_q ] := eqVneq v 0; first by rewrite mulr0 msize0.
      have [->|nz_pq] := eqVneq (u * v) 0; first by rewrite msize0.
      by rewrite msizeM // -subn1 leq_subLR add1n -addnS -addSn leq_add.
    + move=> k _; rewrite [X in (_ <= X)%N]prednK; last first.
        rewrite lt0n msize_poly_eq0 mpoly_gamma_neq0 //.
        apply/negP => /eqP m_eq0. 
        suff : 0%MM \notin msupp R by move/negP; apply; rewrite -m_eq0.
        rewrite -mcoeff_eq0 /R rmorph_prod /=; apply/prodf_eq0.
        exists (sval alpha_in_gamma); first by move: (svalP alpha_in_gamma) =>[].
        apply/eqP; rewrite rmorph_sum /= big1 // => x _.
        by rewrite mcoeffZ mcoeffX /= mnm1_eq0 /= mulr0.
      move=> {i ordi ordinn1 P P_eq P_Over P_sym H j m' eq_m' m'_mdeg m'_i r r_eq}.
      move m0_eq : (tnth _ _) => m0 /=.
      have : m0 \in msupp (U m) by rewrite -m0_eq mem_tnth.
      rewrite /U msupp_mmsymP => /tuple_perm_eqP [s /val_inj /= eq_ms].
      have -> : m = mperm s m0.      
        have -> : m = Multinom (multinom_val m) by apply/mnmP => i.
        by apply/mnmP => i; rewrite eq_ms mnmE.
      move: (msym_mpoly_gamma (s^-1)%g m0); rewrite /= invgK => <-.
      move: (mpoly_gamma _) => P; move: (s^-1)%g => {s eq_ms m0 m0_eq m nn k m_in} s.
      elim/mpolyind: P => [ | c m P m_in c_neq0 ihp].
        by rewrite msym0 leqnn.
      rewrite msymD msymZ msymX !msizeE !(eq_big_perm _ (msuppD _)) /=; last first.
        + move=> m' /=; rewrite (perm_eq_mem (msuppZ _ c_neq0)) msuppX inE.
          by apply/andP => [] [/eqP ->]; apply/negP.
        + move=> m' /=; rewrite (perm_eq_mem (msuppZ _ c_neq0)) msuppX inE.
          apply/andP => [] [/eqP ->]; rewrite mcoeff_msupp mcoeff_sym mpermK.
          by rewrite -mcoeff_msupp; apply/negP.
      rewrite !big_cat -!msizeE !msizeZ // !msizeX mdeg_mperm geq_max leq_maxl.
      by rewrite /=; apply: (leq_trans ihp); rewrite leq_maxr.
  rewrite big_mkcond /= ltnS; apply: (big_ind2 leq) => //. 
    by move=> u1 u2 v1 v2; apply: leq_add.
  by move=> k _; case: ifP => _.
rewrite /nn => i_gt.
rewrite rpredM ?rpredX ?c_Cint //.
have /leq_sizeP -> := i_gt; first by apply: Cint0.
by rewrite size_prod_XsubC /index_enum -enumT size_enum_ord.
Qed. *)