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
Require Import seq_ajouts.

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



(* Hypothesis from wlog1 *)
Variable l : nat.
Variable alpha : complexR ^ l.+1.
Hypothesis alpha_inj : injective alpha.
Hypothesis alpha_algebraic : forall i : 'I_l.+1, alpha i is_algebraic.
Variable a : complexR ^ l.+1.
Hypothesis a_neq0 : forall i : 'I_l.+1, a i != 0.
Hypothesis a_Cint : forall i : 'I_l.+1, a i \is a Cint.
Hypothesis Lindemann_false : Cexp_span a alpha == 0.



(* Separable polynomial for alphas *)
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


(* set of roots of poly_gamma : gamma *)
Definition L := (size ((seqroots poly_gamma))).-1. 
Lemma size_gamma : size ((seqroots poly_gamma)) == L.+1. 
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

(* product *)
Definition prod_Cexp_span_gamma :=
  \prod_(f : 'I_L.+1 ^ l.+1 | injectiveb f) 
    Cexp_span a (finfun (gamma \o f)).

Lemma prod_Cexp_span_gamma_eq0 : prod_Cexp_span_gamma == 0.
Proof.
move: (svalP alpha_in_gamma); set f := sval alpha_in_gamma. 
move=> [] inj_f eq_alphagamma.
rewrite /prod_Cexp_span_gamma (bigD1 _ inj_f) mulf_eq0 /=; apply/orP; left.
move/eqP: Lindemann_false => <-; apply/eqP; congr Cexp_span.
by apply/ffunP => i; rewrite eq_alphagamma ffunE.
Qed.

Definition R : {mpoly complexR[L.+1]} :=
  \prod_(f : 'I_L.+1 ^ l.+1 | injectiveb f) 
     \sum_(i : 'I_l.+1) (a i) *: 'X_(f i).

Lemma R_Cexp_span_eq0 :
  (R.@[finfun (Cexp \o gamma)]) = prod_Cexp_span_gamma.
Proof.
rewrite /R /prod_Cexp_span_gamma !rmorph_prod.
apply: eq_bigr => f inj_f /=.
rewrite !(rmorph_sum _ (index_enum (ordinal_finType l.+1))) /=.
by apply: eq_bigr => i _; rewrite mevalZ mevalX !ffunE.
Qed.

Lemma R_overCint : 
  R \is a (mpolyOver L.+1 Cint).
Proof.
apply: rpred_prod => f _ /=; apply: rpred_sum => i _ /=; rewrite -mul_mpolyC.
by apply: rpredM => /=; rewrite ?mpolyOverX ?mpolyOverC ?a_Cint.
Qed.

Lemma R_sym :
  R \is symmetric.
Proof.
apply/issymP => s; rewrite rmorph_prod /R /=.
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

Lemma R_msupp : perm_eq (msupp R) (flatten [seq (msupp (mmsym complexR_ringType 
           m)) | m <- [seq m0 <- msupp R | sorted leq (m0 : 'X_{1..L.+1})]]).
Proof.
have {1}-> : R = \sum_(m <- flatten [seq msupp (mmsym complexR_ringType m)
   | m <- [seq m0 <- msupp R | sorted leq (m0 : 'X_{1..L.+1})]]) R@_m *: 'X_[m].
  rewrite [LHS](issym_symmE R_sym) big_flatten /= big_map big_filter.
  apply/eq_bigr => m m_sorted; rewrite [X in _ *: X = _]mpolyE scaler_sumr.
  rewrite big_seq_cond [RHS]big_seq_cond.
  apply/eq_bigr => m'; rewrite msupp_mmsymP => /andP[m'_perm _].
  rewrite mcoeff_mmsym m'_perm /= scale1r.
  congr (_ *: _); move: m'_perm; rewrite bla1 => /existsP [s /eqP <-].
  by rewrite /mperm msym_coeff ?R_sym.
apply/(@msupp_sumX _ _ _ (fun m => R@_m) _ _); first last.
  move=> m1 /flatten_mapP[m2]; rewrite mem_filter => /andP[m2_s m2_in].
  rewrite msupp_mmsymP perm_eq_sym bla1 => /existsP[s /eqP <-].
  by rewrite /mperm msym_coeff ?R_sym // mcoeff_eq0 m2_in.
move: (msupp_uniq R); elim: (msupp R) => [_ // | x s ihs /= /andP[x_in uniq_s]].
case: (boolP (sorted leq x)) => [Hsorted | _ ]; last by apply: (ihs uniq_s).
rewrite /= cat_uniq; apply/and3P; split; rewrite ?(ihs uniq_s) //.
apply/hasPn => m /flatten_mapP[m0]; rewrite mem_filter => /andP[m0_s m0_in].
rewrite msupp_mmsymP perm_eq_sym => m_in.
apply/negP; rewrite /= msupp_mmsymP => Hperm.
move: x_in; have := (perm_eq_trans Hperm m_in).
have Hasym : antisymmetric leq by move=> u v; rewrite -eqn_leq; move/eqP.
have Htrans : transitive leq by move=> u v w; apply: leq_trans.
move/(eq_sorted Htrans Hasym Hsorted m0_s).
by move/(val_inj)/(val_inj) => ->; rewrite m0_in.
Qed.

Lemma R_dhomog : R \is (L.+1 ^_ l.+1).-homog.
Proof.
rewrite /R -big_filter; set r := filter _ _.
rewrite -(big_map (fun i : 'I_L.+1 ^ l.+1 => (\sum_(i0 < l.+1) a i0 *: 'X_(i i0))) xpredT id).
set r1 := map _ _; set t := in_tuple r1; rewrite -[r1]/(tval t).
have -> : (L.+1 ^_ l.+1 = \sum_(i <- Tuple (nseq_tupleP (size r1) 1%N)) i)%N.
  rewrite /= big_nseq iter_addn_0 mul1n.
  rewrite size_map -sum1_size big_filter.
  by rewrite sum1dep_card card_inj_ffuns !cardT !size_enum_ord.
apply/dhomog_prod => i. 
rewrite (tnth_nth 0) (tnth_nth 0%N) /= /r1.
rewrite (nth_map (finfun (fun i => ord0))); last first.
  by move: (ltn_ord i); rewrite /r1 [X in (_ < X)%N]size_map.
rewrite nth_nseq -/r1 (ltn_ord i) rpred_sum // => j _.
by rewrite rpredZ // dhomogX /= mdeg1.
Qed.

(* Decomposition on monomial symmetric polynomials *)

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

Definition regr_gamma := (fun m : 'X_{1..L.+1} =>
    [seq (mpoly_gamma m).@[gamma] | m <- (msupp (mmsym complexR_ringType m))]).

Local Notation "''s_' ( n , k )" := (@mesym n _ k).

Lemma regr_gamma_R : 
  (R.@[finfun (Cexp \o gamma)]) = \sum_(m <- msupp R | sorted leq m) 
  (R@_m * \sum_(i <- regr_gamma m) (Cexp i)).
Proof.
rewrite {1}[R](issym_symmE R_sym) rmorph_sum /=.
apply/eq_bigr => m m_sorted; rewrite mevalZ /regr_gamma big_map.
congr (_ * _); rewrite [X in X.@[ _ ] = _]mpolyE rmorph_sum /=.
rewrite big_seq_cond [RHS]big_seq_cond.
apply/eq_bigr => m0 /andP[m0_in _]; rewrite mcoeff_mmsym.
rewrite -(msupp_mmsymP complexR_ringType) m0_in /= scale1r /mpoly_gamma.
rewrite rmorph_sum /= [RHS](big_morph _ Cexp_morph Cexp0) mpolyXE_id.
rewrite rmorph_prod /=.
by apply/eq_bigr => i _; rewrite rmorphX /= mevalMn !mevalX ffunE /= CexpRX.
Qed.

Lemma regr_gamma_alg (m : 'X_{1..L.+1}) (x : complexR) : 
  x \in regr_gamma m -> x is_algebraic.
Proof.
move/mapP => [m1 m1_in] ->; rewrite /mpoly_gamma rmorph_sum /=.
apply/(big_ind (fun y => y is_algebraic)); first by apply/algebraic0.
+ by move=> u v; apply: algebraic_add.
move=> i _; rewrite mevalMn -mulr_natr.
apply/algebraic_mul => /=; first last.
  by rewrite integral_algebraic; apply/integral_nat.
have := gamma_set_roots; rewrite set_rootsE mevalX.
apply: poly_algebraic.
  rewrite -lead_coef_eq0 lead_coefZ mulf_eq0 negb_or c_neq0 andTb.
  rewrite (monicP _) ?oner_neq0 //.
  by apply/monic_prod_XsubC.
rewrite rootZ ?c_neq0 // root_prod_XsubC.
by apply/imfsetP; exists i.
Qed.

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

Lemma conj_gamma m x y (Hx : x \in regr_gamma m) : m \in msupp R ->
  y \is a conjOf (regr_gamma_alg Hx) -> y \in regr_gamma m.
Proof.  
move=> m_in /conjOfP y_root.
have := (regr_gamma_conj m_in); set d := c ^+ _. 
have d_neq0 : d != 0 by rewrite expf_neq0 ?c_neq0.
move/(polyMin_dvdp (regr_gamma_alg Hx)).
rewrite rootZ // root_prod_XsubC Hx.
move/eqP; rewrite eq_sym; move/eqP => /dvdpP [q H].
suff : root (d *: \prod_(z <- regr_gamma m) ('X - z%:P)) y.
  by rewrite rootZ // root_prod_XsubC.
by rewrite H rootM y_root orbT.
Qed.

Lemma conj_gamma_count m x y (Hx : x \in regr_gamma m) : 
  m \in msupp R -> y \is a conjOf (regr_gamma_alg Hx) -> 
  (count_mem x) (regr_gamma m) = (count_mem y) (regr_gamma m).
Proof.
move=> m_in y_conj.
have := (regr_gamma_conj m_in); set d := c ^+ _ => Hover.
have d_neq0 : d != 0 by rewrite expf_neq0 // c_neq0.
have [s /perm_eqP Hperm /allP Hall]:= (seqroots_decomp_polyMin d_neq0 Hover).
rewrite -!Hperm !ssrcomplements.count_flatten !(big_seq _ _ s).
apply/eq_bigr => [[]] f /= b fb_in; rewrite !count_uniq_mem ?enum_fset_uniq //.
have /= f_conj := (Hall _ fb_in); congr nat_of_bool.
apply/idP/idP => [x_in | y_in].
  rewrite (setZconj_seqroots_proper x_in f_conj) seq_fsetE /polyMin.
  by rewrite -(polyMinZ_pi (regr_gamma_alg Hx)) -/(polyMin _) -conjOfE.
rewrite (setZconj_seqroots_proper y_in f_conj) seq_fsetE -conjOfE. 
by rewrite -(conjOf_sym (regr_gamma_alg Hx)).
Qed.

(* All the new alphas *)
Definition dzeta := seq_fset (flatten [seq regr_gamma m | m <- 
   [seq m1 <- msupp R | sorted leq (m1 : 'X_{1..L.+1})]]).

Lemma perm_dzeta : perm_eq (enum_fset dzeta) (undup (flatten [seq regr_gamma m | m <- 
   [seq m1 <- msupp R | sorted leq (m1 : 'X_{1..L.+1})]])).
Proof.
rewrite /dzeta; set s := flatten _.
apply: uniq_perm_eq.
+ by apply: enum_fset_uniq.
+ by apply: undup_uniq.
by move=> x; rewrite seq_fsetE mem_undup.
Qed.

Definition sum_b := 
   (fun x => (\sum_(m <- msupp R | (mpoly_gamma m).@[gamma] == x) R@_m)).

Lemma R_re (T : comRingType) (f : 'X_{1..L.+1} -> T) :
  \sum_(m <- msupp R) f m =
  \sum_(i <- enum_fset dzeta) \sum_(m <- msupp R | (mpoly_gamma m).@[gamma] == i) f m.
Proof.
rewrite /dzeta (eq_big_perm _ perm_dzeta) /=.
set r1 := undup _; rewrite (big_tnth _ _ (msupp R)).
set t := in_tuple _.
set g := (fun i => f (tnth t i)); rewrite (eq_bigr g); last by move=> i _.
have p j : (mpoly_gamma (tnth t j)).@[gamma] \in r1. 
  rewrite /r1 mem_undup.
  have := (perm_eq_msort (tnth t j)); rewrite bla1 => /existsP[s /eqP Hs].
  apply/flatten_mapP; exists (msort (tnth t j)).
    rewrite mem_filter msort_sorted andTb.
    by rewrite -Hs /mperm issym_msupp ?R_sym // mem_tnth.
  rewrite -Hs /regr_gamma.
  apply/mapP; exists (tnth t j) => //; rewrite msupp_mmsymP bla1 /mperm.
  by apply/existsP; exists s.
set P := (fun j : 'I_(size (msupp R)) => sval (seq_tnthP (p j))).
rewrite (eq_bigr (fun i => \sum_(j < size (msupp R) | 
                   (mpoly_gamma (tnth t j)).@[gamma] == i) g j)); last first.
  by move=> i _; rewrite big_tnth -/t; apply/eq_bigr => j _.
rewrite [RHS]big_tnth. 
rewrite (eq_bigr (fun i => \sum_(j < size (msupp R) | P j == i) g j)).
  by rewrite -(@partition_big _ _ _ _ _ xpredT _ xpredT).
move=> i _; apply/eq_bigl => j; rewrite /P.
move: (svalP (seq_tnthP (p j))) => {1}->; rewrite !(tnth_nth 0) /=.
by apply: nth_uniq => //; rewrite undup_uniq.
Qed.

Lemma dzeta_regr_gamma_eq0 :
  \sum_(m <- msupp R | sorted leq m) (R@_m * \sum_(i <- regr_gamma m) (Cexp i))
  = \sum_(i <- enum_fset dzeta) ((sum_b i) * (Cexp i)).
Proof.
rewrite /sum_b /dzeta [in LHS]big_seq_cond big_mkcondl -big_filter.
set r := [seq m <- msupp R | sorted leq (m : 'X_{1..L.+1})].
rewrite /= {1}/regr_gamma -big_mkcond /=.
set f := (fun m : 'X_{1..L.+1} => R@_m * Cexp (mpoly_gamma m).@[gamma]).
rewrite (eq_bigr (fun i => (\sum_(m <- msupp (mmsym complexR_ringType i)) 
                            f m))); last first.
  move=> m m_in; rewrite big_map big_distrr /= big_seq_cond [RHS]big_seq_cond.
  apply/eq_bigr => m0 /andP[]; rewrite msupp_mmsymP bla1 => /existsP[s /eqP <-].
  by move=> _; congr (_ * _); rewrite /mperm msym_coeff ?R_sym.
rewrite big_mkcond big_filter -big_mkcondl -big_seq_cond /=.
rewrite -big_filter -/r.
rewrite -(@big_map _ _ _ _ _ (fun i : 'X_{1..L.+1} => msupp (mmsym complexR_ringType i)) 
  r xpredT (fun x => \sum_(m <- x) f m)) -big_flatten /=.
rewrite -(eq_big_perm _ R_msupp) /=.
apply/eqP; rewrite eq_sym; apply/eqP.    
rewrite (eq_bigr (fun i => (\sum_(m <- msupp R | (mpoly_gamma m).@[gamma] == i) 
  f m))); last first.
  move=> x _; rewrite big_distrl /=.
  by apply/eq_bigr => m /eqP <-.
by rewrite -R_re.
Qed.

Lemma dzeta_alg (x : complexR) : x \in dzeta -> x is_algebraic.
Proof. 
by rewrite seq_fsetE => /flattenP [s /mapP[m m_in]] -> /regr_gamma_alg.
Qed.

Lemma conj_dzeta x y (Hx : x \in dzeta) :
  y \is a conjOf (dzeta_alg Hx) -> y \in dzeta.
Proof.
have := Hx; rewrite seq_fsetE.
move/flatten_mapP => [m]; rewrite mem_filter => /andP[m_sorted m_in x_in].
rewrite -(conjOf_pi _ (regr_gamma_alg x_in)).
move/(conj_gamma m_in) => H; rewrite seq_fsetE.
by apply/flatten_mapP; exists m => //; rewrite mem_filter m_sorted m_in.
Qed.

Lemma conj_dzeta_sum_b x y (Hx : x \in dzeta) :
  y \is a conjOf (dzeta_alg Hx) -> sum_b x = sum_b y.
Proof.
move=> y_conj; rewrite /sum_b.
rewrite !(eq_big_perm _ R_msupp) /= !big_flatten /= !big_map !big_filter.
rewrite big_seq_cond [RHS]big_seq_cond.
apply/eq_bigr => m /andP[m_in m_sorted]; rewrite big_seq_cond [RHS]big_seq_cond.
rewrite (eq_bigr (fun i => R@_m * 1%N%:R)); last first.
  move=> m0 /andP[]; rewrite msupp_mmsymP bla1 => /existsP[s /eqP <- _].
  by rewrite /mperm (msym_coeff _ _ R_sym) mulr1.
rewrite [RHS](eq_bigr (fun i => R@_m * 1%N%:R)); last first.
  move=> m0 /andP[]; rewrite msupp_mmsymP bla1 => /existsP[s /eqP <- _].
  by rewrite /mperm (msym_coeff _ _ R_sym) mulr1.
rewrite -!big_distrr /= -!natr_sum -!big_seq_cond !sum1_count.
congr (_ * _ %:R).
pose f := (fun j : _ => (mpoly_gamma j).@[gamma]).
rewrite (@eq_count _ _ (preim f (pred1 x))); last by move=> u /=; rewrite /f.
rewrite [RHS](@eq_count _ _ (preim f (pred1 y))); last first.
  by move=> u /=; rewrite /f.
rewrite -!count_map /f -/(regr_gamma m).
case: (boolP (x \in regr_gamma m)) => [Hxg | H].
  apply: (conj_gamma_count m_in).
  by rewrite (conjOf_pi _ _ (dzeta_alg Hx)).
rewrite (count_memPn H); apply/eqP; rewrite eq_sym.
apply/eqP/count_memPn/negP => y_in; move/negP: H; apply.
by apply: (@conj_gamma _ _ _ y_in m_in _); rewrite -(conjOf_sym (dzeta_alg Hx)).
Qed.

Definition dzeta_n0 := [fset i in dzeta | sum_b i != 0]%fset.

Lemma dzeta_n0_alg (x : complexR) : x \in dzeta_n0 -> x is_algebraic.
Proof.
by rewrite inE /= => /andP[]; move/dzeta_alg.
Qed.

Lemma conj_dzeta_n0 x y (Hx : x \in dzeta_n0) :
  y \is a conjOf (dzeta_n0_alg Hx) -> y \in dzeta_n0.
Proof.
have := Hx; rewrite inE /= => /andP[Hxd bx].
rewrite -(conjOf_pi _ (dzeta_alg Hxd)) => y_conj.
have/conj_dzeta := y_conj => y_in; rewrite inE /= y_in andTb.
by rewrite -(conj_dzeta_sum_b y_conj).
Qed.

Lemma conj_dzeta_n0_sum_b x y (Hx : x \in dzeta_n0) :
  y \is a conjOf (dzeta_n0_alg Hx) -> sum_b x = sum_b y.
Proof.
have := Hx; rewrite inE /= => /andP[Hxd bx].
rewrite -(conjOf_pi _ (dzeta_alg Hxd)) => y_conj.
by apply: (conj_dzeta_sum_b y_conj).
Qed.


Lemma dzeta_n0_conj :
    exists2 d, d *: \prod_(x <- enum_fset dzeta_n0) ('X - x%:P) \is a polyOver Cint & d != 0. 
Proof.
have Hsubset x (H : x \in dzeta_n0) :
  {subset (seq_fset (seqroots (polyMin (dzeta_n0_alg H)))) <= dzeta_n0}.
  by move=> y; rewrite seq_fsetE -conjOfE; apply: conj_dzeta_n0.
pose S_def := map (fun x => 
                 match (eqVneq (x \in dzeta_n0) true) with
                 |left x_in => seq_fset (seqroots (polyMin (dzeta_n0_alg x_in)))
                 |right x_nin => fset0 end)  (enum_fset dzeta_n0).
pose S_undup := undup S_def.
pose S := flatten (map (@enum_fset _ : {fset complexR} -> seq complexR) S_undup).
have S_eqi : S =i dzeta_n0.
  move=> x; apply/flattenP/idP => [[t] | x_in].
    move/mapP => [f]; rewrite mem_undup => /mapP[y y_in].
    case: (eqVneq _ _) => H -> -> //.
    by rewrite /= seq_fsetE -conjOfE => /conj_dzeta_n0.
  have x_sr : x \in seqroots (polyMin (dzeta_n0_alg x_in)).
    by apply/seqrootsP/polyMin_root/polyMin_neq0.
  exists (enum_fset (seq_fset (seqroots (polyMin (dzeta_n0_alg x_in))))). 
    apply/mapP; exists (seq_fset (seqroots (polyMin (dzeta_n0_alg x_in))))=> //.
    rewrite mem_undup; apply/mapP; exists x => //.
    case: (eqVneq _ _) => [H | ]; last by rewrite x_in.
    rewrite /polyMin.
    by congr (_ (seqroots (map_poly _ _))); apply: polyMinZ_pi.
  by rewrite seq_fsetE.
have Hperm : perm_eq S (enum_fset dzeta_n0).
  apply: uniq_perm_eq => //; last by apply/enum_fset_uniq.
  apply: count_mem_uniq => y; rewrite ssrcomplements.count_flatten /=.
  case: (boolP (y \in S)) => [y_in | ].
    have := y_in => /flatten_mapP[f].
    move=> f_in; have := f_in.
    rewrite mem_undup => /mapP[z z_in].
    case: (eqVneq _ _) => [z_inb f_eq y_ina | ]; last by rewrite z_in.
    rewrite /= (bigD1_seq f) ?undup_uniq //=.
    rewrite /= count_uniq_mem; last first.
      by rewrite f_eq /= /seq_fset /= unlock /= sort_keys_uniq.
    rewrite f_eq {1}/seq_fset unlock sort_keysE big_seq_cond big1.
      by move: y_ina; rewrite ?addn0 f_eq seq_fsetE => ->.
    move=> g /andP[g_in /negP g_neq_f].
    have := g_in; rewrite mem_undup => /mapP[u u_in].
    case: (eqVneq _ _) => [u_inb g_eq | ]; last by rewrite u_in.
    apply/count_memPn; rewrite g_eq /seq_fset unlock sort_keysE -seq_fsetE -g_eq.
    apply/negP => y_ing; apply: g_neq_f; apply/eqP; rewrite g_eq /polyMin.
    congr (seq_fset (seqroots (map_poly _ _))); apply/conjOf_polyMinZ.
    move: y_in; rewrite S_eqi => y_in.
    have : z \is a conjOf (dzeta_n0_alg y_in).
      by rewrite -(conjOf_sym (dzeta_n0_alg z_inb)) conjOfE -seq_fsetE -f_eq.
    by move/conjOf_trans_conj; apply; rewrite conjOfE -seq_fsetE -g_eq.
  rewrite S_eqi => /negP y_nin /=; rewrite big_seq_cond big1 //.
  move=> f /andP[]; rewrite mem_undup => /mapP[x x_in].
  case: (eqVneq _ _) => [x_inb f_eq _ | ]; last by rewrite x_in.
  apply/count_memPn; rewrite f_eq /seq_fset unlock sort_keysE.  
  apply/negP; rewrite -conjOfE => y_conj; apply: y_nin.
  by exact: (conj_dzeta_n0 y_conj).
rewrite -(eq_big_perm _ Hperm) /= big_flatten /= big_map.
have /memPn Hneq0 : fset0 \notin S_undup.
  apply/negP; rewrite mem_undup => /mapP[x x_in].
  case: (eqVneq _ _) => [x_inb eq_x | ]; last by rewrite x_in.
  by have // : x \in fset0 by rewrite eq_x seq_fsetE -conjOfE conjOf_refl.
have Hex f (H : f \in S_undup) : {x | x \in dzeta_n0 & x \in f}.
  exists (sval (sigW (fset0Pn f (Hneq0 f H)))). 
    rewrite -S_eqi.
    by apply/flatten_mapP; exists f => //; apply: (svalP (sigW _)).
  by apply:(svalP (sigW ((fset0Pn f) (Hneq0 f H)))).
have Hconj f (H : f \in S_undup) : f \is a setZconj 
                        (lead_coef (polyMin (dzeta_n0_alg (s2valP (Hex f H))))).
  set P := polyMin _.
  suff -> : f = seq_fset (seqroots P) by apply: setZconj_polyMin.
  have := H; rewrite mem_undup => /mapP[x x_in].
  case: (eqVneq _ _) => [x_inb eq_f | ]; last by rewrite x_in.
  rewrite eq_f /P /polyMin.
  congr (seq_fset (seqroots (map_poly _ _))); apply: conjOf_polyMinZ.
  have := (s2valP' (Hex f H)); set y := s2val _.
  by rewrite eq_f seq_fsetE -conjOfE.
pose d := \prod_(j <- S_undup) 
   (fun j => match (eqVneq (j \in S_undup) true) with
    |left j_in => (lead_coef (polyMin (dzeta_n0_alg (s2valP (Hex j j_in)))))
    |right _ => 1 end) j.
exists d. 
  rewrite -scaler_prod big_seq_cond.
  apply/rpred_prod => f /andP[f_in _].
  case: (eqVneq (f \in S_undup) true) => [f_inb | ]; last by rewrite f_in.
  rewrite -set_rootsE /=.
  by apply/setZconj_over/Hconj.
rewrite prodf_seq_neq0.
apply/allP => x x_in; apply/implyP => _.
case: (eqVneq _ _) => [x_inb | ]; last by rewrite x_in.
by rewrite lead_coef_eq0 polyMin_neq0.
Qed.


(* final definitions for wlog2 *)
Definition final_l := (size (enum {: dzeta_n0})).-1.

Lemma final_l_gt0 : size (enum {: dzeta_n0}) == final_l.+1.
Proof.
apply/eqP; rewrite /final_l prednK // -cardE card_fsetE.
have -> : size (enum_fset dzeta_n0) = size (filter (fun i => sum_b i != 0) (enum_fset dzeta)).
  apply/eqP; rewrite -uniq_size_uniq ?enum_fset_uniq //.
    by rewrite filter_uniq ?enum_fset_uniq.
  by move=> x; rewrite mem_filter inE /= andbC.
rewrite size_filter.
have /perm_eqP -> := perm_dzeta; rewrite -has_count.
set f := fun _ => _.
suff : has f (flatten [seq regr_gamma m | m <- [seq m0 <- msupp R |
  sorted leq (m0 : 'X_{1..L.+1})]]).
  by move/hasP=> [x x_in x_f]; apply/hasP; exists x; rewrite ?mem_undup.
set r := flatten _; rewrite has_count lt0n.
apply/negP => /eqP Hcount.
move: (count_predC f r); rewrite Hcount add0n.
move/eqP; rewrite -all_count.
have /eq_all {f Hcount} -> : predC f =1 (fun i => sum_b i == 0).
  by move=> i; rewrite /=; apply/negPn/idP.
set g := (fun i => _ == 0) => /allP Hflat.
pose m_of := (fun (h : {ffun ('I_L.+1 ^ l.+1) -> 'I_l.+1}) => 
   (\sum_(f : 'I_L.+1 ^ l.+1 | injectiveb f) U_(f (h f)))%MM).
pose D := (fun i0 : @finfun_of (exp_finIndexType (S l)) (ordinal (S L))
           (Phant (forall _ : ordinal (S l), ordinal (S L))) =>
           @injectiveb (exp_finIndexType (S l)) (ordinal_eqType (S L))
           (@FunFinfun.fun_of_fin (exp_finIndexType (S l)) (ordinal (S L)) i0)).
set Rt := (fun _ : ordinal (S l) => true).
have H_in_f m : m \in msupp R -> 
                   exists h, (m_of h == m) && (h \in pffun_on ord0 D Rt).
  move=> m_in. 
  have /dhomogP := R_dhomog; move/(_ m m_in) => /= mdeg_m.
  move: m_in; rewrite /R (big_distr_big ord0) /= mcoeff_msupp.
  rewrite (big_morph _ (mcoeffD _) (mcoeff0 _ _)) => H.
  have : [exists f, (f \in pffun_on ord0 D Rt) && 
     ((\prod_(i0 : 'I_L.+1^l.+1| injectiveb i0) 
                  (a (f i0) *: 'X_(i0 (f i0))))@_m != 0)].
    rewrite -[[exists _, _]]Bool.negb_involutive negb_exists.
    apply/negP => /forallP Hforall; move/negP: H; apply.
    rewrite big1 // => f f_in; apply/eqP.
    by move: (Hforall f); rewrite negb_and f_in /= Bool.negb_involutive.
  move=> /existsP[f /andP[f_on f_neq0]].
  exists f; rewrite /m_of f_on andbT.
  move: f_neq0; rewrite scaler_prod mcoeffZ mulf_eq0 negb_or => /andP[_].
  by rewrite mprodXE mcoeffX pnatr_eq0 eqb0 Bool.negb_involutive.
have Hsum_b m : sum_b (mpoly_gamma m).@[gamma] =
  \sum_(i : 'X_{1..L.+1 < (L.+1 ^_ l.+1).+1} | (mpoly_gamma i).@[gamma] ==
   (mpoly_gamma m).@[gamma]) R@_i.
  rewrite /sum_b; set s := index_enum _. 
  pose P := (fun (i : 'X_{1..L.+1 < (L.+1 ^_ l.+1).+1}) => val i \in msupp R).
  have Hperm : perm_eq s ((filter P s) ++ (filter (predC P) s)).
    by rewrite perm_eq_sym (perm_eqlE (perm_filterC _ _)).
  rewrite (eq_big_perm _ Hperm) /= big_cat /=.
  rewrite [X in _ + X]big_filter_cond [X in _ + X]big1 /P; last first.
    by move=> i /= /andP[] /memN_msupp_eq0 ->.
  have {Hperm} Hperm : perm_eq (msupp R) (map val [seq i <- s | val i \in msupp R]).
    apply: uniq_perm_eq.
    + by apply/msupp_uniq.
    + rewrite map_inj_uniq ?filter_uniq /s //.
        by rewrite /index_enum -enumT enum_uniq.
      by apply: val_inj.
    move=> i.
    apply/idP/mapP => [i_in | [] bm].
      have Hmi : (mdeg i < (L.+1 ^_ l.+1).+1)%N.
        by have /dhomogP := R_dhomog; move/(_ i i_in) => /= ->.
      pose bmi := BMultinom Hmi; exists bmi => //; rewrite mem_filter /= i_in /=.
      by rewrite mem_index_enum.
    by rewrite mem_filter => /andP[H _ ->].
  by rewrite (eq_big_perm _ Hperm) /= big_map addr0. 
have H_g : forall (m : 'X_{1..L.+1}), sum_b (mpoly_gamma m).@[gamma] == 0.
  move=> m; case: (boolP [exists m0 : 'X_{1..L.+1 < (L.+1 ^_ l.+1).+1}, 
            ((val m0 \in msupp R) && 
                 ((mpoly_gamma m0).@[gamma] == (mpoly_gamma m).@[gamma]))]).
    move=> /existsP[bm /andP[bm_in /eqP <-]].
    apply/Hflat/flatten_mapP; exists (msort (val bm)).
      rewrite mem_filter msort_sorted /=.
      have := (perm_eq_msort (val bm)); rewrite bla1 => /existsP[s /eqP <-].
      by rewrite /mperm issym_msupp ?R_sym ?m_in.
    by apply/mapP; exists (val bm) => //; rewrite msupp_mmsymP perm_eq_msort.
  rewrite negb_exists => /forallP H; rewrite /sum_b big_seq_cond big1 //.
  move=> m0 /andP[m0_in m0_eq].
  have Hm0 : (mdeg m0 < (L.+1 ^_ l.+1).+1)%N.
    by have /dhomogP := R_dhomog; move/(_ m0 m0_in) => /= ->.
  pose bm0 := BMultinom Hm0.
  by move: (H bm0); rewrite negb_and /= m0_in /= m0_eq.
pose mf := (fun (f : 'I_L.+1 ^ l.+1) => U_(f (index_bmaxf (finfun (gamma \o f))))%MM).
pose Pf (f : 'I_L.+1 ^ l.+1) := (\sum_(i < l.+1) a i *: 'X_(f i)).
have Pf_homog f : (Pf f) \is 1.-homog.
  by apply/rpred_sum => i _; apply/rpredZ; rewrite dhomogX /= mdeg1.
have Pf_msupp (f : 'I_L.+1 ^ l.+1) : injective f -> perm_eq (msupp (Pf f)) 
    [seq U_(f i)%MM | i <- index_enum (ordinal_finType l.+1)].
  move=> inj_f; rewrite /Pf.
  apply/(perm_eq_trans (msupp_sum _ _ _)).
  + by rewrite /index_enum -enumT enum_uniq.
  + move=> i j _ _ /negbTE i_neqj m /=; apply/negP.
    rewrite !(perm_eq_mem (msuppZ _ _)) // !msuppX !inE => /andP[/eqP ->] /eqP.
    by move/(mnm1_inj)/inj_f/eqP; rewrite i_neqj.
  rewrite filter_xpredT -(@eq_map _ _ (fun i : 'I_l.+1 => [:: U_( f i)%MM]));
          last first.
    by move=> i; rewrite msuppMCX ?a_neq0.
  by rewrite -[X in perm_eq _ X]ssrcomplements.flatten_seq1 -map_comp.
have Hf (f : 'I_L.+1 ^ l.+1) i : injective f -> 
  i \in codom f ->
  letcif ((mpoly_gamma U_(i)%MM).@[gamma]) 
  (mpoly_gamma (mf f)).@[gamma]
  (U_(i)%MM == (mf f)).
  move=> inj_f /codomP[j ->].
  have HU_mg k : (mpoly_gamma U_( f k)%MM).@[gamma] = (finfun (gamma \o f)) k.
    rewrite ffunE /mpoly_gamma rmorph_sum /= (bigD1 (f k)) //= big1; last first.
      by move=> u /negbTE u_neqk; rewrite mnm1E eq_sym u_neqk /= mulr0n meval0.
    by rewrite mnm1E eq_refl mulr1n mevalX addr0.
  rewrite !HU_mg eq_index_bmaxf (inj_eq (@mnm1_inj L.+1)) (inj_eq inj_f).
  by apply: bmaxf_letcif => u v; rewrite !ffunE; move/gamma_inj/inj_f.
pose mm := (\sum_(f : 'I_L.+1 ^ l.+1 | injectiveb f) (mf f))%MM.
have mpoly_gammaD u v : mpoly_gamma (u + v) = mpoly_gamma u + mpoly_gamma v.
  rewrite /mpoly_gamma -big_split /=.
  by apply/eq_bigr => i _; rewrite mnmDE mulrnDr.
have Hprod (h : {ffun ('I_L.+1 ^ l.+1) -> 'I_l.+1}) : 
  h \in pffun_on ord0 D Rt ->
  letcif (mpoly_gamma (m_of h)).@[gamma] (mpoly_gamma mm).@[gamma] (m_of h == mm). 
  rewrite /Rt /mm /m_of; set s := index_enum _; elim: s h => [h Hh | f s ihs h].
    rewrite !big_nil eq_refl.
    by apply/letcif_refl.
  rewrite !big_cons; case: (boolP (injectiveb f)) => [ | _]; last by exact: ihs.
  move=> /injectiveP inj_f Hh.
  rewrite !mpoly_gammaD.
  have /letcifP := (ihs h Hh).
  case: (boolP (_ == _)) => [/eqP -> _| ].
    rewrite eqm_add2r.
    apply/letcifP; move/letcifP: (Hf f (f (h f)) inj_f (codom_f f (h f))).
    by case: ifP => [/eqP -> // | _ H]; rewrite !mevalD lttc_add2r.
  move=> m_prod_neq Hlttc_prod.
  have /letcifP := (Hf f (f (h f)) inj_f (codom_f f (h f))).
  case: (boolP (_ == _)) => [/eqP -> _ | ].
    rewrite eqm_add2l (negbTE m_prod_neq) !mevalD.
    by apply/letcifP; rewrite lttc_add2l.
  move=> m_sumf_neq Hlttc_sumf; apply/letcifP; case: ifP => [/eqP H | ].
    by rewrite -!mpoly_gammaD H eq_refl.
  by move=> _; rewrite !mevalD; apply: lttc_add.
pose fmm := (finfun (fun f : 'I_L.+1 ^ l.+1 => if injectiveb f then 
    index_bmaxf (finfun (gamma \o f)) else ord0 )).
have Hfmm : fmm \in pffun_on ord0 D Rt.
  apply/pffun_onP; split; last by move=> h.
  apply/supportP => f; rewrite /fmm ffunE => /negP H /=.
  by have -> : injectiveb f = false by apply/negP => f_inj.
suff : sum_b (mpoly_gamma (m_of fmm)).@[gamma] != 0.
  by move/negP; apply; apply: H_g.
rewrite Hsum_b.
have Hmm_mof : m_of fmm = mm.
  rewrite /m_of /fmm /mm /mf.
  by apply/eq_bigr => f f_inj; congr (mnm1 (f _)); rewrite ffunE f_inj.
rewrite Hmm_mof. 
have Hbmm : (mdeg mm < (L.+1 ^_ l.+1).+1)%N.
  rewrite /mm mdeg_sum (eq_bigr (fun i => 1%N)); last first.
    by move=> i _; rewrite mdeg1.
  by rewrite sum1dep_card card_inj_ffuns !cardT !size_enum_ord.
pose bmm := BMultinom Hbmm.
rewrite (bigD1 bmm) //= big1 ?addr0; last first.
  move=> i /andP[H] Hi_neqm.
  have /negbTE i_neqm : val i != mm.
    rewrite -[mm]/(val bmm).
    by apply/negP; move/eqP/val_inj => Hi; rewrite Hi eq_refl in Hi_neqm.
  case: (boolP [exists f, (f \in pffun_on ord0 D Rt) && (m_of f == i)]).
    move=> /existsP[f /andP[f_in /eqP eq_f]].
    have /letcifP := (Hprod f f_in); rewrite eq_f i_neqm.
    by move/lttc_eqF; rewrite H.
  rewrite negb_exists => /forallP Hi.
  apply/memN_msupp_eq0/negP => i_in.
  have := (H_in_f i i_in) => [[fi /andP[H1 H2]]].
  by move: (Hi fi); rewrite H1 H2.
rewrite /R (big_distr_big ord0) /=.
rewrite (big_morph _ (mcoeffD _) (mcoeff0 _ _)).
rewrite (bigD1 fmm) //= /mm [X in _ + X]big1 ?addr0.
  rewrite scaler_prod mcoeffZ mulf_neq0 //.
    by apply/prodf_neq0 => i _; apply: a_neq0.
  rewrite mprodXE mcoeffX (eq_bigr (fun f => mf f)) ?eq_refl ?oner_neq0 //.
  by move=> f inj_f; rewrite /fmm ffunE inj_f.
move=> h /andP[h_in] h_neq; apply/eqP; rewrite scaler_prod mcoeffZ mulf_eq0.
apply/orP; right; rewrite mprodXE mcoeffX -[0]/((nat_of_bool false)%:R).
apply/eqP; congr (nat_of_bool _)%:R; apply/negP; rewrite -/(m_of h).
move/eqP/(congr1 (fun m => (mpoly_gamma m).@[gamma])); rewrite -/mm => eqmpg.
have /letcifP := (Hprod h h_in).
case: (boolP (m_of h == mm)) => [hm_eq _ | _]; last first.
  by rewrite lttc_neqAle eqmpg eq_refl.
move/negP: h_neq; apply; apply/eqP; rewrite -ffunP.
apply/eqfunP/negPn; rewrite negb_forall; apply/negP => /existsP[f h_neqf].
move=> {Hbmm bmm Pf_homog Pf_msupp r g Hflat H_g Hsum_b}.
case: (boolP (injectiveb f)) => [ inj_f | /negbTE inj_f]; last first.
  case: (boolP (h f == ord0)) => [/eqP h_ok | /negbTE h_ok]; last first.
    have /pffun_onP[/supportP /=] := h_in; move/(_ f) => Hatt.
    have : f \notin D.
      apply/negP => f_in; move/injectiveP: inj_f; apply; apply/injectiveP.
      by move: f_in; rewrite /D.
    by move/Hatt/eqP; rewrite h_ok.
  move: h_neqf; rewrite h_ok eq_sym => /negbTE f_ok.
  have /pffun_onP[/supportP /=] := Hfmm; move/(_ f) => Hatt.
  have : f \notin D.
    apply/negP => f_in; move/injectiveP: inj_f; apply; apply/injectiveP.
    by move: f_in; rewrite /D.
  by move/Hatt/eqP; rewrite f_ok.
suff : lttc (mpoly_gamma (m_of h)).@[gamma] (mpoly_gamma mm).@[gamma].
  by move/eqP: hm_eq => ->; move/lttc_eqF; rewrite eq_refl.
rewrite /m_of /mm (bigD1 f) //= [X in lttc _ (_ X).@[gamma]](bigD1 f) //=.
rewrite !mpoly_gammaD !mevalD.
apply/(@letc_lt_trans ((mpoly_gamma U_( (f (h f)))).@[gamma] + 
    (mpoly_gamma (\sum_(i : 'I_L.+1 ^l.+1| injectiveb i && (i != f)) mf i)).@[gamma])); first last.
  move: inj_f => /injectiveP inj_f.
  rewrite lttc_add2r (lttc_letcif (Hf f _ _ _)) //.
    rewrite /mf; apply/negP; move/eqP/mnm1_inj/inj_f => eq_h.
    move/negP: h_neqf; apply; apply/eqP; rewrite eq_h /fmm ffunE.
    by move/injectiveP : inj_f => ->.
  by apply: codom_f.  
apply: letc_add; first by rewrite letcc.
apply/(big_rec2 (fun x y => letc (mpoly_gamma x).@[gamma] (mpoly_gamma y).@[gamma])).
  rewrite /mpoly_gamma (eq_bigr (fun i => 0)); last first.
    by move=> i _; rewrite mnmE mulr0n.
  by rewrite big1 // letcc.
move=> z x1 x2 /andP[inj_z z_neqf] H; rewrite !mpoly_gammaD !mevalD.
apply: letc_add => //.
apply: (letc_of_leif (Hf z (z (h z)) _ _)).
  by apply/injectiveP.
by apply: codom_f.
Qed.

(* creating the partition of the indexes instead of the set *)
Definition f_oa := finfun (tnth (Tuple final_l_gt0)).

Lemma f_oa_inj : injective f_oa. 
Proof.
move=> x y; rewrite /f_oa !ffunE /= !(tnth_nth (f_oa ord0)) /=.
move/eqP; rewrite nth_uniq ?(elimT eqP final_l_gt0) ?enum_uniq //.
by move/eqP/ord_inj.
Qed.

Lemma f_oa_bij : bijective f_oa.
Proof.
apply: (inj_card_bij f_oa_inj).
by rewrite !cardT size_enum_ord (elimT eqP final_l_gt0).
Qed.

Lemma eq_oa : #|{: dzeta_n0}| = #|'I_final_l.+1|.
Proof. by rewrite cardT (elimT eqP final_l_gt0) card_ord. Qed.

Definition A := (@enum_val _ 'I_final_l.+1 : _ -> 'I_final_l.+1).
Definition B := (@enum_rank (fset_sub_finType dzeta_n0)).
Definition fi_oa := (finfun (A \o (cast_ord eq_oa) \o B) : {ffun {: dzeta_n0} -> 'I_final_l.+1}).

Lemma eq_f_oa : finfun ((@enum_val _ {: dzeta_n0}) \o
  (cast_ord (esym eq_oa)) \o (@enum_rank (ordinal_finType final_l.+1))) = f_oa.
Proof.
apply/ffunP => i; rewrite !ffunE /=.
rewrite enum_rank_ord cast_ord_comp (enum_val_nth (f_oa ord0)).
by rewrite (tnth_nth (f_oa ord0)) /=.
Qed.

Lemma f_oaK : cancel f_oa fi_oa.
Proof.
move=> i; rewrite -eq_f_oa /fi_oa !ffunE /= /A /B.
by rewrite enum_valK cast_ordKV enum_rankK.
Qed.

Lemma fi_oaK : cancel fi_oa f_oa.
Proof.
move=> i; rewrite -eq_f_oa /fi_oa /A /B !ffunE /=.
by rewrite enum_valK cast_ordK enum_rankK.
Qed.

Definition final_alpha := finfun (val \o f_oa).

Lemma final_alpha_injective : injective final_alpha.
Proof.
move=> x y; rewrite /final_alpha !ffunE /=.
by move/val_inj/f_oa_inj.
Qed.

Lemma perm_eq_map_inj (T : eqType) (T' : eqType) (u : seq T) v (g : T -> T') (x : T) : 
       injective g -> perm_eq (map g u) (map g v) -> perm_eq u v.
Proof.
move=> inj_g; move/perm_eq_iotaP; move/(_ (g x)) => [p].
set q := seq.iota _ _; move => Hpq Heq.
apply/(@perm_eq_iotaP _ u v x); exists p.
  by have -> // : seq.iota 0 (size v) = q by rewrite /q size_map.
apply/(@eq_from_nth _ x); first rewrite size_map.
  by move/(congr1 size): Heq; rewrite !size_map.
move=> i i_ord; apply/inj_g; rewrite -!(nth_map _ (g x)) //; last first.
  by rewrite size_map; move/(congr1 size): Heq; rewrite !size_map => <-.
rewrite Heq -map_comp; congr (nth _ _ _).
apply: eq_map => j /=.
case: (boolP (j < size v)%N); first by apply: nth_map.
by rewrite -leqNgt => Hj; rewrite !nth_default ?size_map.
Qed.

Lemma flatten_map (T : eqType) (T' : eqType) (r : seq (seq T)) (g : T -> T') :
    map g (flatten r) = flatten (map (fun x => map g x) r).
Proof. by elim: r => [//= | x r /= <-]; rewrite map_cat. Qed.

Lemma Hl : map val (enum {: dzeta_n0}) = enum_fset dzeta_n0.
Proof.
rewrite -val_fset_sub_enum ?enum_fset_uniq //.
congr (map _ _); rewrite /(enum _) unlock /= /fset_sub_enum filter_undup.
by congr undup; rewrite filter_xpredT.
Qed.

Definition seq_conj := seqroots_decomp_polyMin
  (s2valP' (sig2W dzeta_n0_conj)) (s2valP (sig2W dzeta_n0_conj)).
Notation s := (s2val seq_conj).
Notation Hperm := (s2valP seq_conj).
Notation Hall := (s2valP' seq_conj).
Notation f := (fun (x : {fset complexR}) => [fset y in enum {: dzeta_n0} | val y \in x]%fset).
Definition s_fset := (map (fun x => (f x.1, x.2)) s).
Definition sf := map fst s_fset.

Lemma Hf : perm_eq (flatten [seq (enum_fset (K:=complexR_choiceType) \o fst) i | i <- s])
    (map val (flatten [seq [seq y <- enum {: dzeta_n0} | y \in x.1] | x <- [seq (f x.1, x.2) | x <- s]])).
Proof.
rewrite flatten_map.
move eq_s : s => t.
have {eq_s} : subseq t s by rewrite eq_s.
elim: t => [//= | x t iht /= tx_sub].
have t_sub : subseq t s. 
  by apply/(subseq_trans (subseq_cons _ _) tx_sub).
move: iht; rewrite -(perm_cat2l (enum_fset x.1)).
move/(_ t_sub).
move/perm_eq_trans; apply; rewrite perm_cat2r.
apply/uniq_perm_eq; first by apply/enum_fset_uniq.
  rewrite map_inj_uniq; first by rewrite filter_uniq ?enum_uniq //.
  by move=> u v /val_inj.
move=> i.
apply/idP/mapP => [i_in | [j]]; last first.
  by rewrite mem_filter /f inE /= => /andP[/andP[_ Hj] _ ->].
have : i \in [seq val j | j <- enum {: dzeta_n0}]. 
  rewrite Hl -(perm_eq_mem Hperm).
  apply/flattenP; exists (enum_fset x.1) => //.
  set u := (@enum_fset _ : {fset complexR} -> seq complexR).
  set v := u \o fst.
  have -> : u x.1 = v x by [].
  apply: (map_f v); rewrite -sub1seq.
  by apply: (subseq_trans _ tx_sub) => /=; rewrite eq_refl sub0seq.
move/mapP => [j j_in eq_j]; exists j=> //; rewrite mem_filter j_in /f andbT.
apply/imfsetP => /=; exists j => //=; apply/andP; rewrite j_in; split => //.
by rewrite -eq_j.
Qed.

Lemma perm_eq_sf : (perm_eq (flatten (map (fun x => 
 filter (fun y => y \in x) (enum {: dzeta_n0})) sf)) (enum {: dzeta_n0})).
Proof.
rewrite /sf -map_comp.
rewrite (@eq_map _ _ _ (fun x  => [seq y <- enum {: dzeta_n0} | y \in x.1])).
  apply:(@perm_eq_map_inj _ _ _ _ val (f_oa ord0)); first by apply/val_inj.
  rewrite Hl.
  have Hf := Hf; rewrite perm_eq_sym in Hf.
  by apply/(perm_eq_trans Hf Hperm).
by move=> i /=.
Qed.

Lemma perm_eq_sf_proper : perm_eq (flatten (map (@enum_fset _) sf)) (enum {: dzeta_n0}).
Proof.
apply/(perm_eq_trans _ perm_eq_sf).
elim: sf => [//= | x lx /=].
rewrite -(perm_cat2l (enum_fset x)).
move/perm_eq_trans; apply; rewrite perm_cat2r.
apply: uniq_perm_eq; first by apply/enum_fset_uniq.
  by apply/filter_uniq/enum_uniq.
move=> y; rewrite mem_filter.
by apply/idP/idP => [-> /= | /andP[-> _] //]; rewrite mem_enum.
Qed.

Lemma all_s_fset : all (fun (x : {fset (fset_sub_eqType dzeta_n0)} * complexR_eqType)
      => [fset val i | i in x.1]%fset \is a setZconj x.2) s_fset.
Proof.
apply/allP => x x_in.
have /allP := Hall; move/(_ ([fsetval i in x.1]%fset,x.2)) => /=; apply.
move/mapP: x_in => [[y1 y2] y_in -> /=].
suff -> : [fset (fsval i) | i in f y1]%fset = y1 by [].
apply/fsetP => z.
apply/imfsetP/idP => [[u /=] | z_in].
  by rewrite /f; rewrite inE /= => /andP[_ u_in ->].
have : z \in enum_fset dzeta_n0.
  rewrite -(perm_eq_mem Hperm).
  apply/flattenP; exists (enum_fset y1); last by [].
  set u := @enum_fset _.
  have -> : u y1 = (u \o fst) (y1, y2) by [].
  by apply/map_f.
rewrite -val_fset_sub_enum ?enum_fset_uniq // => /mapP[u u_in eq_u /=].
exists u => //; rewrite /f inE /=.
by apply/andP; rewrite -eq_u z_in mem_enum.
Qed.

Definition final_c := \prod_(x <- s2val seq_conj) x.2.


Lemma final_c_neq0 : final_c != 0.
Proof.
rewrite prodf_seq_neq0.
apply/allP.
have := (s2valP seq_conj); have /allP := (s2valP' seq_conj); set s := s2val _.
move=> /= Hall Hperm [f x] /=.
move/(Hall (f, x)) => /=; move/setZconj_neq0; rewrite -lead_coef_eq0.
rewrite lead_coefZ (monicP _) ?mulr1 //.
by apply/monic_prod_XsubC.
Qed.

Lemma final_c_Cint : final_c \is a Cint.
Proof.
rewrite /final_c.
have := (s2valP seq_conj); have /allP := (s2valP' seq_conj); set s := s2val _.
move=> /= Hall Hperm; rewrite big_seq_cond.
apply/rpred_prod => [[f x] /andP[/= x_in] _].
by move: (Hall (f, x) x_in) => /=; move/setZconj_over/set_roots_lead_coef.
Qed.

Lemma all_sf : all (fun x : {fset (fset_sub_eqType dzeta_n0)} =>
    [fset val i | i in x]%fset \is a setZconj final_c) sf.
Proof.
apply/allP => x; rewrite /sf => /mapP[xp xp_in ->].
have /allP := all_s_fset; move/(_ xp xp_in) => {x}.
set fi := [fsetval _ in _]%fset => fi_set.
have /closed_rootP[y] := (setZconj_size fi_set).
rewrite rootZ ?root_prod_XsubC; last first.
  by move/setZconj_neq0 : fi_set; rewrite scaler_eq0 negb_or => /andP[].
move=> y_in; have y_alg := (setZconj_algebraic y_in fi_set).
apply/(@setZconj_find _ _ y y_alg y_in).
+ have /mapP[xs xs_in eq_xs] := xp_in.
  rewrite /final_c.
  have Hrem := (perm_to_rem xs_in).
  rewrite (eq_big_perm _ Hrem) /= big_cons.
  rewrite mulrC -scalerA ( _ : xs.2 = xp.2); last by rewrite eq_xs.
  apply/polyOverZ; last by apply: (setZconj_over fi_set).
  rewrite big_seq_cond; apply/rpred_prod => i /andP[i_in _].
  have i_ins: i \in s by apply/(mem_rem i_in).
  have /allP := (s2valP' seq_conj); move/(_ i i_ins)/setZconj_over.
  rewrite set_rootsE; move/polyOverP => Hover.
  have -> : i.2 = lead_coef (i.2 *: \prod_(x <- enum_fset i.1) ('X - x%:P)).
    by rewrite lead_coefZ (monicP _) ?mulr1 //; apply/monic_prod_XsubC.
  by apply/Hover.
+ have /mapP[xs xs_in eq_xs] := xp_in.
  rewrite /final_c.
  have Hrem := (perm_to_rem xs_in).
  rewrite (eq_big_perm _ Hrem) /= big_cons.
  rewrite mulrC -scalerA ( _ : xs.2 = xp.2); last by rewrite eq_xs.
  rewrite size_scale; last first.
    rewrite prodf_seq_neq0.
    apply/allP => i /mem_rem i_in; apply/implyP => _.
    have -> : i.2 = lead_coef (i.2 *: \prod_(x <- enum_fset i.1) ('X - x%:P)).
      by rewrite lead_coefZ (monicP _) ?mulr1 //; apply/monic_prod_XsubC.
    rewrite lead_coef_eq0.
    by have /allP := (s2valP' seq_conj); move/(_ i i_in)/setZconj_neq0.
  rewrite ltn_neqAle eq_sym lt0n size_poly_eq0.
  have /allP := all_s_fset; move/(_ xp xp_in) => H.
  by rewrite (setZconj_neq0 H) (setZconj_size H).
apply/allP => x x_in.
apply/seqrootsP; first by apply: polyMin_neq0.
rewrite -conjOfE (conjOf_pi _ _ (setZconj_algebraic y_in fi_set)).
by apply: conjOf_setZconj.
Qed.

Definition sf_part : {fset {fset {: dzeta_n0}}} := 
    (\bigcup_(x <- sf) [fset x]%fset)%fset.

Lemma sf_part_eq : seq_fset sf = sf_part.
Proof.
rewrite /sf_part.
elim: sf => [/= | x s]. 
  rewrite big_nil /=.
  by apply/fsetP => i; rewrite seq_fsetE.
by rewrite fset_cons => ->; rewrite big_cons.
Qed.

Lemma sf_mem : sf =i sf_part.
Proof. by move=> i; rewrite -sf_part_eq seq_fsetE. Qed.

Lemma sf_part_cover : [fset x in {: dzeta_n0}]%fset =
   (\big[@fsetU _/fset0]_(i : sf_part) (val i))%fset.
Proof.
apply/fsetP => x.
apply/imfsetP/idP => [[y /= y_in ->] | _]; last by exists x.
move : y_in => {x} ; rewrite -mem_enum -(perm_eq_mem perm_eq_sf_proper).
move=> /flattenP => [[x]].
set u := (@enum_fset _ : {fset {: dzeta_n0}} -> seq {: dzeta_n0}).
move/(@mapP _ _ u sf x) => [z z_in ->]; rewrite /u => y_in.
have : z \in enum_fset sf_part.
  rewrite /sf_part big_tnth.
  apply/bigfcupP; move: z_in; rewrite -{1}[sf]/(tval (in_tuple sf)).
  by move/tnthP => [i eq_z]; exists i => //; rewrite -eq_z inE.
rewrite -val_fset_sub_enum; last by apply/enum_fset_uniq.
set v := @val _ _; move/mapP => [zz zz_in eq_zz].
by apply/bigfcupP; exists zz => //; move: eq_zz; rewrite /v => <-.
Qed.

Definition fis_oa := (fun x : {fset {: dzeta_n0}} =>
   [set (fi_oa i) | i in x] : {set 'I_final_l.+1}).
Definition fs_oa := (fun x : {set 'I_final_l.+1} =>
   [fset (f_oa i) | i in x]%fset : {fset {: dzeta_n0}}).

Lemma fs_oaK : cancel fs_oa fis_oa.
Proof.
move=> x; rewrite /fis_oa /fs_oa.
apply/setP => i.
apply/imsetP/idP => [[y /imfsetP[j /= j_in -> ->]] | i_in].
  by rewrite f_oaK.
exists (f_oa i); last by rewrite f_oaK.
by apply/imfsetP; exists i => //=.
Qed.

Lemma fis_oaK : cancel fis_oa fs_oa.
Proof.
move=> x; rewrite /fis_oa /fs_oa.
apply/fsetP => i.
apply/imfsetP/idP => [[y /imsetP[j /= j_in -> ->]] | i_in].
  by rewrite fi_oaK.
exists (fi_oa i); last by rewrite fi_oaK.
by apply/imsetP; exists i => //=.
Qed.

Definition part : {set {set 'I_final_l.+1}} := 
     \bigcup_(x <- sf) [set (fis_oa x)].

Lemma part_eq : part = [set i | i \in (map fis_oa sf)].
Proof.
rewrite /part.
elim: sf => [/= | x s]. 
  by rewrite big_nil; apply/setP => i.
by rewrite big_cons => -> /=; apply/setP => i; rewrite !inE.
Qed.

Lemma part_sf_mem x : (x \in part) = (fs_oa x \in sf_part).
Proof.
rewrite part_eq /= !inE.
apply/mapP/idP => [[y y_in ->] | ]; first by rewrite fis_oaK -sf_mem.
by rewrite -sf_mem => Hin; exists (fs_oa x) => //; rewrite fs_oaK.
Qed.

Lemma part_cover : [set: 'I_final_l.+1] = \bigcup_(i in part) i.
Proof.
apply/setP => x.
apply/idP/idP => [_ | _ //].
have : f_oa x \in [fset x in {: dzeta_n0}]%fset.
  apply/imfsetP; exists (f_oa x) => //.
rewrite sf_part_cover => /bigfcupP[y _ in_y].
apply/bigcupP.
exists (fis_oa (val y)); last first.
  by rewrite /fis_oa -[x]f_oaK; apply/imsetP; exists (f_oa x).
rewrite /part big_tnth.
apply/bigcupP.
suff : (val y) \in in_tuple sf.
  by move/tnthP => [i ->]; exists i => //; rewrite inE.
have : val y \in enum_fset sf_part.
  rewrite -val_fset_sub_enum; last by apply/enum_fset_uniq.
  by apply/mapP; exists y => //; rewrite mem_fset_sub_enum.
rewrite /sf_part [X in enum_fset X]big_tnth => /bigfcupP[i _].
by rewrite inE => /eqP ->; rewrite mem_tnth.
Qed.

Lemma part_nset0 : set0 \notin part.
Proof.
apply/negP; rewrite part_sf_mem -sf_mem => H.
have /allP := all_sf; move/(_ _ H)/(setZconj_size)/negP; apply.
rewrite size_scale ?final_c_neq0 // size_prod_XsubC.
apply/eqP; congr (_.+1); apply/eqP.
rewrite -card_fsetE card_imfset; last by apply: val_inj.
rewrite cardfs_eq0 /=; apply/eqP/fsetP => i /=.
rewrite in_fset0 /fs_oa.
by apply/negP => /imfsetP[j /=]; rewrite in_set0.
Qed.

Lemma sf_perm_eq : perm_eq sf (enum_fset sf_part).
Proof.
apply: uniq_perm_eq; first last.
+ by move=> i; rewrite sf_mem.
+ by apply/enum_fset_uniq.
apply/count_mem_uniq => x.
case: (boolP (x \in sf)) => [x_in | /count_memPn -> //].
have /perm_eqP -> := (perm_to_rem x_in).
case: (boolP (x \in rem x sf)) => [x_inr |]; last first.
  by move=> /count_memPn /= ->; rewrite eq_refl.
have /allP := all_sf; move/(_ _ x_in)/(setZconj_size)/negP.
rewrite size_scale ?final_c_neq0 // size_prod_XsubC eqSS.
rewrite -card_fsetE card_imfset; last by apply: val_inj.
rewrite cardfs_eq0 [X in X -> _]/=; move/negP/fset0Pn => [y y_in].
have : (count_mem y) (enum {: dzeta_n0}) = 1%N.
  by rewrite count_uniq_mem ?enum_uniq // mem_enum.
have /perm_eqP <- := perm_eq_sf_proper.
rewrite ssrcomplements.count_flatten /=.
rewrite (eq_big_perm _ (perm_to_rem x_in)) /= big_cons /=.
rewrite (eq_big_perm _ (perm_to_rem x_inr)) /= big_cons /=.
set A := (count_mem y) _; rewrite addnA.
set B := (\sum_(_ <- _) _)%N => H.
have HA : (1%N <= A)%N.
  by rewrite /A -has_count; apply/hasP => /=; exists y.
have {HA} := (leq_add HA HA); rewrite addn1 => HA.
by have := (leq_add HA (leq0n B)); rewrite addn0 H.
Qed.

Lemma part_triv : trivIset part.
Proof.
have := (leq_card_cover part).
rewrite /cover -part_cover cardsT card_ord {1}part_eq /=.
rewrite (eq_bigl (fun A => fs_oa A \in sf_part)); last first.
  by move=> i; rewrite -part_sf_mem -part_eq.
rewrite (eq_bigr (fun A => (\sum_(i <-enum_fset (fs_oa A)) 1)%N)); last first.
  move=> i _; move eq_card: (#| i |) => ic.
  elim: ic i eq_card => [i /eqP|].
    rewrite cards_eq0 => /eqP ->.
    rewrite big_seq_cond big1 //.
    move=> x /andP[] H _.
    have: (fs_oa set0) != fset0 by apply/fset0Pn; exists x.
    suff: (fis_oa (fs_oa set0)) != set0 by rewrite fs_oaK eq_refl.
    apply/set0Pn; exists (fi_oa x); rewrite /fis_oa.
    by apply/imsetP; exists x.
  move=> n ihn i card_i.
  have : #|i| != 0%N by rewrite card_i.
  rewrite cards_eq0; move/set0Pn => [x x_in].
  rewrite -(setD1K x_in); set j := i :\ _.
  rewrite (ihn j _); last first.
    by have /eqP := (cardsD1 x i); rewrite card_i x_in add1n eqSS => /eqP ->.
  rewrite -add1n (_ : addn _  _ = (\sum_(i <- (f_oa x) 
                :: (enum_fset (fs_oa j))) 1%N)%N); last by rewrite big_cons.
  have -> : ((fs_oa (x |: j)) = (f_oa x) |` (fs_oa j))%fset.
    apply/fsetP => k; rewrite /fs_oa /= inE /=.
    apply/imfsetP/orP => [[p /=]| [|]].
        rewrite inE => /orP [|p_in ->].
          by rewrite inE => /eqP -> ->; rewrite inE eq_refl; left.
        by right; apply/imfsetP; exists p.
      by rewrite inE => /eqP ->; exists x => //=; rewrite !inE eq_refl.
    by move/imfsetP => [p /= p_in ->]; exists p; rewrite //= inE p_in orbT.
  apply: eq_big_perm; apply: uniq_perm_eq; first last.
  + by move=> k; rewrite !inE.
  + by apply: enum_fset_uniq.
  rewrite /= (enum_fset_uniq _) andbT.
  apply/negP => H.
  have : x \in j.
    rewrite -[x]f_oaK -[j]fs_oaK /fis_oa.
    by apply/imsetP; exists (f_oa x) => //.
  by rewrite /j !inE eq_refl.
rewrite -(big_map fs_oa (fun i => i \in sf_part) (fun i => (\sum_(j <- enum_fset i) 1%N)%N)).
rewrite -big_filter; set s := filter _ _.
have Hs : perm_eq s (enum_fset sf_part).
  apply: uniq_perm_eq.
  + rewrite /s filter_uniq // map_inj_uniq.
      by rewrite /index_enum -enumT enum_uniq.
    by apply: (can_inj fs_oaK).
  + by apply: enum_fset_uniq.
  move=> k; rewrite mem_filter.
  apply/andP/idP => [[] // | k_in].
  rewrite k_in; split; rewrite //.    
  by apply/mapP; exists (fis_oa k); rewrite ?fis_oaK ?mem_index_enum //.
rewrite (eq_big_perm _ Hs) -(eq_big_perm _ sf_perm_eq) /=.
pose rr := [seq enum_fset i | i <- sf].
have /= := (big_flatten addn_monoid rr xpredT (fun i => 1%N)); rewrite /rr.
rewrite big_map => <-.
rewrite (eq_big_perm _ perm_eq_sf_proper) /= sum1_size.
rewrite (elimT eqP final_l_gt0).
move/leqifP; rewrite eq_refl ltnn.
by case: (boolP (trivIset part)).
Qed.

Lemma part_partition : partition part [set: 'I_final_l.+1].
Proof. 
rewrite /partition; apply/and3P; split.
+ by rewrite /cover part_cover eq_refl.
+ by apply: part_triv.
by apply: part_nset0.
Qed.

Lemma part_setZroots :
  {in part, forall P : {set 'I_final_l.+1},
  [fset (final_alpha i) | i in P]%fset \is a setZroots final_c}.
Proof.
move=> f f_in; apply/setZconj_over.
move: f_in; rewrite part_eq inE => /mapP[i i_in ->].
have /allP := all_sf; move/(_ i i_in).
suff -> : [fsetval j in i]%fset = [fset final_alpha j | j in fis_oa i]%fset.
  by [].
apply/fsetP => j; rewrite /=.
apply/imfsetP/imfsetP => [[x /= x_in ->] | [x /= x_in ->]].
  exists (fi_oa x); first by rewrite /fis_oa; apply/imsetP; exists x.
  by rewrite /final_alpha ffunE /= fi_oaK.
exists (f_oa x); last by rewrite /final_alpha ffunE /=.
by rewrite -[i]fis_oaK; apply/imfsetP; exists x.
Qed.

Definition final_b := finfun (sum_b \o final_alpha).

Lemma final_b_neq0 : (forall i : 'I_final_l.+1, final_b i != 0).
Proof.
move=> i; rewrite ffunE /= ffunE /=.
have : val (f_oa i) \in dzeta_n0 by apply/fsvalP.
by rewrite inE /= => /andP[_].
Qed.

Lemma final_b_Cint : (forall i : 'I_final_l.+1, final_b i \is a Cint).
Proof.
move=> i; rewrite ffunE /= ffunE /sum_b.
apply/rpred_sum => m _. 
by have /mpolyOverP := R_overCint; move/(_ m).
Qed.

Lemma final_b_const :
  {in part, forall P : {set 'I_final_l.+1}, constant [seq final_b i | i in P]}.
Proof.
move=> x x_in.
have : x != set0.
  apply/negP=> /eqP Heq.
  by have /negP := part_nset0; rewrite -Heq; apply.
move/set0Pn => [i i_in].
have i_H : (final_alpha i) \in dzeta_n0 by rewrite /final_alpha ffunE /= fsvalP.
apply/(@all_pred1_constant _ (sum_b (final_alpha i)))/allP => p /mapP[j].
rewrite mem_enum => j_in -> /=; rewrite /final_b ffunE /= eq_sym.
apply/eqP/(@conj_dzeta_n0_sum_b _ _ i_H).
set f := fs_oa x.
have f_in : f \in sf by rewrite sf_mem /f -part_sf_mem.
have /allP := all_sf; move/(_ f f_in).
set g := [fset _ in _ ]%fset => g_conj.
have i_inb : final_alpha i \in g.
  rewrite /final_alpha /g ffunE /f /=.
  apply/imfsetP; exists (f_oa i) => //=.
  by rewrite /fs_oa /=; apply/imfsetP; exists i => //=.
rewrite -(conjOf_pi _ (setZconj_algebraic i_inb g_conj)).
apply: conjOf_setZconj.
rewrite /final_alpha /g ffunE /f /=.
apply/imfsetP; exists (f_oa j) => //=.
by rewrite /fs_oa /=; apply/imfsetP; exists j => //=.
Qed.


Lemma wlog2_eq0 :
  Cexp_span final_b final_alpha == 0.
Proof.
have /eqP <- := prod_Cexp_span_gamma_eq0; rewrite -R_Cexp_span_eq0.
rewrite regr_gamma_R dzeta_regr_gamma_eq0 /Cexp_span /final_b /final_alpha /=.
rewrite (eq_bigr (fun i => sum_b (val (f_oa i)) * Cexp (val (f_oa i)))); last first.
  by move=> i _; rewrite /= !ffunE /= !ffunE /= !ffunE /=.
rewrite -(big_map (val \o f_oa) xpredT (fun i => sum_b i * Cexp i)) /=.
rewrite map_comp.
pose P := (fun i => sum_b i != 0). 
have Hperm :  perm_eq (enum_fset dzeta) ((filter P (enum_fset dzeta)) ++
  (filter (predC P) (enum_fset dzeta))).
  by rewrite perm_eq_sym (perm_eqlE (perm_filterC _ _)).
rewrite (eq_big_perm _ Hperm) /= big_cat /=.
rewrite [X in _ + X]big_filter [X in _ + X]big1 ?addr0; last first.
  by move=> x /=; move/negPn/eqP => ->; rewrite mul0r.
apply/eqP/eq_big_perm/uniq_perm_eq; rewrite ?map_inj_uniq.
+ by rewrite /index_enum -enumT enum_uniq.
+ by apply/(can_inj (f_oaK)).
+ by apply/val_inj.
+ by rewrite filter_uniq // enum_fset_uniq.
move => x; rewrite mem_filter /P -map_comp.
apply/mapP/andP => [[i _ -> /=] | [Hb Hin]].
  have : fsval (f_oa i) \in dzeta_n0 by apply/fsvalP.
  by rewrite inE /= => /andP[-> ->].  
have : x \in enum_fset dzeta_n0 by rewrite inE /= Hin Hb.
rewrite -val_fset_sub_enum ?enum_fset_uniq // => /mapP[i i_in ->].
by exists (fi_oa i); rewrite ?mem_index_enum //= fi_oaK.
Qed.

(* Theoreme wlog2 *)
Lemma wlog2 : 
  exists (f_l : nat) (f_c : complexR) (f_alpha : complexR ^ f_l.+1) 
  (f_a : complexR ^ f_l.+1) (f_part : {set {set 'I_f_l.+1}}),
  f_c != 0 /\ f_c \is a Cint /\ injective f_alpha /\ 
  partition f_part [set: 'I_f_l.+1] /\ {in f_part, forall P : {set 'I_f_l.+1},
  [fset (f_alpha i) | i in P]%fset \is a setZroots f_c} /\
  (forall i : 'I_f_l.+1, f_a i != 0) /\ (forall i : 'I_f_l.+1, f_a i \is a Cint) /\
  {in f_part, forall P : {set 'I_f_l.+1}, constant [seq f_a i | i in P]} /\ 
  Cexp_span f_a f_alpha == 0.
Proof.
exists final_l; exists final_c; exists final_alpha; exists final_b; exists part.
split; first by apply: final_c_neq0.
split; first by apply: final_c_Cint.
split; first by apply: final_alpha_injective.
split; first by apply: part_partition.
split; first by apply: part_setZroots.
split; first by apply: final_b_neq0.
split; first by apply: final_b_Cint.
split; first by apply: final_b_const.
by apply: wlog2_eq0.
Qed.

End Wlog2. 



Theorem wlog2_Lindemann :
  (forall (l : nat) (c : complexR) (alpha : complexR ^ l.+1) 
  (part : {set {set 'I_l.+1}}) (a : complexR ^ l.+1),
  c != 0 -> c \is a Cint -> injective alpha -> 
  partition part [set: 'I_l.+1] -> {in part, forall P : {set 'I_l.+1},
  [fset (alpha i) | i in P]%fset \is a setZroots c} ->
  (forall i : 'I_l.+1, a i != 0) -> (forall i : 'I_l.+1, a i \is a Cint) ->
  {in part, forall P : {set 'I_l.+1}, constant [seq a i | i in P]} -> 
  Cexp_span a alpha != 0) ->
  (forall (l : nat) (alpha : complexR ^ l.+1) (a : complexR ^ l.+1),
  injective alpha -> (forall i : 'I_l.+1, alpha i is_algebraic) ->
  (forall i : 'I_l.+1, a i != 0) -> (forall i : 'I_l.+1, a i \is a Cint) ->
  (Cexp_span a alpha != 0)).
Proof. 
move => ih l alpha a alpha_inj alpha_alg a_neq0 a_Cint; apply/negP => Hspan.
move: (wlog2 alpha_inj alpha_alg a_neq0 a_Cint Hspan) => [fl [fc [falpha]]].
move=> [fa [fpart]] [] fc_neq0 [] fc_Cint [] falpha_inj [] fpart_part [].
move=> fpart_conj [] fa_neq0 [] fa_Cint [] fa_const Hspan_eq0.
move: (ih fl fc falpha fpart fa fc_neq0 fc_Cint falpha_inj fpart_part fpart_conj
  fa_neq0 fa_Cint fa_const).
by rewrite Hspan_eq0.
Qed.
