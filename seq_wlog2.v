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
Require Import seq_ajouts seq_wlog3.

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

Definition mpoly_gamma : 'X_{1..L.+1} -> {mpoly complexR[L.+1]} :=
   (fun (m : 'X_{1..L.+1}) => \sum_(i < L.+1) ('X_i) *+ (m i)).

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

(* Regroupement par monome *)
Definition regr_gamma := (fun m : 'X_{1..L.+1} =>
    [seq (mpoly_gamma m).@[gamma] | m <- (msupp (mmsym complexR_ringType m))]).

Local Notation "''s_' ( n , k )" := (@mesym n _ k).

Lemma regr_gamma_conj m : m \in msupp R ->
  c ^+ (((msize (mpoly_gamma m)).-1  * size (regr_gamma m))) *: 
      \prod_(x <- regr_gamma m) ('X - x%:P) \is a polyOver Cint. 
Proof.
move=> m_in; apply/polyOverP => i; rewrite coefZ. 
set ta := (fun m => size (regr_gamma m)).
have [|] := (ltnP i (ta m).+1).
  rewrite ltnS leq_eqVlt => /orP [/eqP i_nn | ordi].
    rewrite rpredM ?rpredX ?c_Cint // i_nn.
    set P := \prod_(_ <- _) _.
    have <- : (size P).-1 = (ta m) by rewrite size_prod_XsubC /ta.
    have -> : P`_(size P).-1 = lead_coef P by [].
    by rewrite (monicP _) ?Cint1 ?/P ?rpred_prod // => j _; rewrite monicXsubC.
  have ordinn1 : (i < (ta m).+1)%N by apply: (leq_trans ordi (leqnSn _)).
  pose cs := finfun (fun j : 'I_(ta m) => nth 0 (regr_gamma m) j).
  rewrite -/(ta m).
  have eq_sumA : regr_gamma m = [seq cs i | i <- enum 'I_(ta m)].
    apply/(@eq_from_nth _ 0); first by rewrite [RHS]size_map size_enum_ord.
    move=> j; rewrite -/(ta m) => ord_j; rewrite [RHS](nth_map (Ordinal ordi)).
      by rewrite ffunE /= nth_enum_ord.
    by rewrite size_enum_ord.
  rewrite eq_sumA big_map enumT (ordnat ordinn1) mroots_coeff_proper -mulrCA.
  apply/rpredM; first by rewrite rpredX ?rpredN ?Cint1.
  (*have -> : sum_gamma im = finfun (tnth (map_tuple (meval gamma) 
              (map_tuple mpoly_gamma (Tuple (tuple_ta im))))).
    by apply/ffunP => x; rewrite /sum_gamma !ffunE /= !tnth_map.*)
  rewrite (eq_meval _ (ffunE _)) /regr_gamma.
  have tuple_ta : size (msupp (mmsym complexR_ringType m)) == ta m.
    by apply/eqP; rewrite /ta [RHS]size_map.
  rewrite (@eq_meval _ _ _ (fun j : 'I_(ta m) => tnth (map_tuple (meval gamma) 
                      (map_tuple mpoly_gamma (Tuple tuple_ta))) j)); last first.
    move=> j; rewrite !tnth_map -/(tval (Tuple tuple_ta)).
    rewrite -[X in X`_j]/(tval 
            (map_tuple (fun m0 => (mpoly_gamma m0).@[gamma]) (Tuple tuple_ta))).
    by rewrite -tnth_nth !tnth_map.
  rewrite -meval_comp_mpoly.
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
    have -> /= : [tuple msym s t`_i0 | i0 < (ta m)] = map_tuple (msym s) t.
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
      by rewrite -eq_s' /mperm; apply/mnmP => j; rewrite !mnmE permM /= !permKV.
    rewrite msupp_mmsymP perm_eq_sym bla1 -H; apply/existsP. 
    move: m2_in; rewrite msupp_mmsymP bla1 => /existsP[s' /eqP eq_s'].
    exists (s^-1 * (s' ^-1))%g; rewrite -eq_s' /mperm; apply/eqP/mnmP => j.
    by rewrite !mnmE permM permKV.
  have H := (sym_fundamental_set_roots_proper_wfset _ P_Over P_sym).
  move: gamma_set_roots; rewrite set_rootsE big_fset; last by apply/gamma_inj.
  move/H => {H} H //=.
  suff : (msize P <= ((msize (mpoly_gamma m)).-1 * (ta m)).+1)%N.
    rewrite -[X in (_ <= X)%N]add1n -leq_subLR subn1.
    by move/subnK => <-; rewrite exprD -mulrA rpredM ?rpredX ?c_Cint.
  rewrite -P_eq comp_mpolyE; apply: (leq_trans (msize_sum _ _ _)).
  rewrite -[msupp 's_( _ , _)]/(tval (in_tuple (msupp _))) big_tuple.
  apply/bigmax_leqP => j _; rewrite msizeZ; last first.
    by rewrite -mcoeff_msupp (tnth_nth 0%MM) in_tupleE mem_nth.
  move eq_m': (tnth _ j) => m'.
  have : m' \in (in_tuple (msupp ('s_((ta m), ((ta m) - i)) : {mpoly complexR[(ta m)]}))).
    by rewrite -eq_m' mem_tnth.
  rewrite mem_msupp_mesym /mechar => /andP[/eqP m'_mdeg /forallP m'_i].
  rewrite -[X in (_ * X)%N](subn0 (ta m)) mulnC -sum_nat_const_nat big_mkord.
  rewrite (eq_bigr (fun k => if (m' k != 0%N) 
     then (mpoly_gamma (tnth (Tuple tuple_ta) k)) else 1)); last first.
    move=> k _; move: (m'_i k); move: (m' k) => x; case: x; [| case]; rewrite //.
    by move=> _; rewrite expr1 /= tnth_map.
  apply: (@leq_trans (\sum_(i0 < (ta m) | m' i0 != 0) (msize (mpoly_gamma m)).-1).+1%N).
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
      have : m0 \in msupp ((mmsym _ m) : {mpoly complexR[L.+1]}). 
        rewrite -m0_eq (tnth_nth 0%MM) /= mem_nth ?(elimT eqP (tuple_ta im)) //.
        by move: (ltn_ord k); rewrite /ta /regr_gamma [X in (k < X)%N]size_map.
      rewrite msupp_mmsymP => /tuple_perm_eqP [s /val_inj /= eq_ms].
      have -> : m = mperm s m0.      
        have -> : m = Multinom (multinom_val m) by apply/mnmP => i.
        by apply/mnmP => i; rewrite eq_ms mnmE.
      move: (msym_mpoly_gamma (s^-1)%g m0); rewrite /= invgK => <-.
      move: (mpoly_gamma _) => P. move: (s^-1)%g => {s eq_ms m0 m0_eq k} s.
      elim/mpolyind: P => [ | c m0 P m0_in c_neq0 ihp].
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
by rewrite size_prod_XsubC /ta size_map.
Qed.

(* Les exp associés à un meme monome sont des conjugués. *)
(* Les coeff sont les mêmes sur un monome par le th ci-dessous *)
(* issym_symmE:*)
(* forall (n : nat) (R : ringType) (p : {mpoly R[n]}),*)
(* p \is symmetric -> p = \sum_(m <- msupp p | sorted leq m) p@_m *: mmsym R m *)
(* Aucun des coeff ne vaut 0 *)

(* Faire les sommes de coeff, et undup la liste des gamma de façon simultanée *)
(* A check 1 : il y a un coeff non nul *)
(* A check 2 : *)

(* Condition pas assez forte pour avoir un polyMin !
On pourrait le sortir tel quel !
Lemma seqroots_decomp_polyMin (a : seq complexR) (c : complexR) :
  c != 0 -> c *: \prod_(x <- a) ('X - x%:P) \is a polyOver Cint -> 
  uniq a -> {s : seq ({fset complexR} * complexR) | 
    (perm_eq (flatten (map ((@enum_fset complexR_choiceType) \o fst) s)) a) &
    (all (fun x => x.1 \is a setZconj x.2) s)}. *)

Definition dzeta := undup (flatten [seq regr_gamma m | m <- 
   [seq m1 <- msupp R | sorted leq (m1 : 'X_{1..L.+1})]]).



Definition sum_b := 




Definition R_pair := [seq (m, R@_m) | m <- [seq m1 <- msupp R | sorted leq m1]].
(filter (sorted leq) (msupp R))].


Definition R_pair := [seq (m, (R@_m, mpoly_gamma m)) | m <- msupp R].


Search _ (_ \is symmetric).
Search _ "issym_".

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