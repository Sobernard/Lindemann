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

Section Wlog3.

(*
Variable pre_l : nat.
Hypothesis pre_l_gt0 : (0%N < pre_l)%N.
*)

Variable l : nat.

Lemma HcC :
  [char mpoly_idomainType l.+1 complexR_idomainType] =i pred0.
Proof. by move=> x; rewrite char_lalg char_num. Qed.

(*
Variable pre_alpha : complexR ^ pre_l.
Hypothesis pre_alpha_inj : injective pre_alpha.
Hypothesis pre_alpha_algebraic : forall i : 'I_pre_l, pre_alpha i is_algebraic.
*)
Variable c : complexR.
Hypothesis c_neq0 : c != 0.
Hypothesis c_Cint : c \is a Cint.

Variable alpha : complexR ^ l.+1.
Hypothesis alpha_inj : injective alpha.
Hypothesis alpha_algebraic : forall i : 'I_l.+1, alpha i is_algebraic.

(*
Variable pre_part : {set {set 'I_pre_l}}.
Hypothesis pre_part_cover : cover pre_part = [set: 'I_pre_l].
*)

Variable part : {set {set 'I_l.+1}}.
Hypothesis part_partition : partition part [set: 'I_l.+1].
Hypothesis alpha_setZroots : {in part, forall P : {set 'I_l.+1},
  [fset (alpha i) | i in P]%fset \is a setZroots c}.

(*
Variable pre_b : {set 'I_pre_l} -> complexR.
Hypothesis pre_b_neq0 : forall P, (P \in pre_part) = (pre_b P != 0).
Hypothesis pre_b_Cint : forall P, pre_b P \is a Cint.
*)

Variable a : complexR ^ l.+1.
Hypothesis a_neq0 : forall i : 'I_l.+1, a i != 0.
Hypothesis a_Cint : forall i : 'I_l.+1, a i \is a Cint.
Hypothesis a_constant : {in part, forall P : {set 'I_l.+1}, 
  constant [seq a i | i in P]}.

(*
Hypothesis pre_a_neq0 : 
  exists i : 'I_pre_l, \sum_(P in pre_part | i \in P) pre_b P != 0.
Hypothesis pre_Lindemann_false : 
  Cexp_span [ffun i => \sum_(P in pre_part | i \in P) pre_b P] pre_alpha == 0.
Definition a := (finfun (fun i : 'I_l.+1 => \sum_(P in part | i \in P) b P)).
Hypothesis a_neq0 : exists i : 'I_l.+1, a i != 0. *)

Hypothesis Lindemann_false : Cexp_span a alpha == 0.

(*
Hypothesis pre_alpha_setZroots : forall (P : {set 'I_pre_l}), P \in pre_part -> 
  (finfun (pre_alpha \o (@enum_val _ (pred_of_set P)))) \is a setZroots c.
*)

Variable p : nat.
Hypothesis p_prime : prime p.

Lemma p_gt0 : (p > 0)%N.
Proof. by apply: (prime_gt0 p_prime). Qed.

(* Hypothesis p > ce qu'on veut *)

Definition T (i : 'I_l.+1) : {poly {mpoly complexR[l.+1]}}:=
  \prod_(j < l.+1 | j != i) ('X - ('X_j)%:P).

Lemma size_T i : size (T i) = l.+1.
Proof.
rewrite /T -big_filter size_prod_XsubC -rem_filter.
  by rewrite size_rem // /index_enum -enumT size_enum_ord prednK.
by rewrite /index_enum -enumT enum_uniq.
Qed.

(* c ^+ (l.+1 * p) *: *)
Definition F (i : 'I_l.+1) : {poly {mpoly complexR[l.+1]}} := 
   ((\prod_(j < l.+1) ('X - ('X_j)%:P)) ^+ p.-1 * (T i)).

Lemma size_F i : size (F i) = (p * l.+1)%N.
Proof.
rewrite size_mul; last first; first by rewrite -size_poly_eq0 size_T.
  by apply/expf_neq0/prodf_neq0 => j _; rewrite polyXsubC_eq0.
rewrite size_T polyrcf.my_size_exp; last first.
  by apply/prodf_neq0 => j _; rewrite polyXsubC_eq0.
rewrite size_prod_XsubC /index_enum -enumT size_enum_ord [in RHS]mulnC /=. 
by rewrite -[in RHS](prednK p_gt0) [in RHS]mulnS addnC.
Qed.

Lemma F_neq0 i : F i != 0.
Proof. by rewrite -size_poly_gt0 size_F muln_gt0 p_gt0 ltn0Sn. Qed.

Lemma mroot_F i :
  mroot (F i) p.-1 ('X_i) /\ forall j,  (j != i)%N -> mroot (F i) p ('X_j).
Proof.
split; first apply/mrootP. 
  exists ((T i) ^+ p); rewrite /F mulrC.
  rewrite -[X in (T i) ^+ X](prednK p_gt0) exprS -mulrA -exprMn. 
  by congr (_ * (_ ^+ _)); rewrite /T mulrC (bigD1 i).
move=> j Hle; have -> : (p = p.-1 + 1)%N by rewrite addn1 prednK ?p_gt0.
rewrite /F.
apply/mrootM; last first.
  apply/root_mroot/rootP; rewrite horner_prod.
  by apply/eqP/prodf_eq0; exists j => //; rewrite hornerXsubC subrr.
apply/mrootX/rootP; rewrite horner_prod.
by apply/eqP/prodf_eq0; exists j => //; rewrite hornerXsubC subrr.
Qed.

Lemma F_over i : F i \is a polyOver (mpolyOver _ Cint).
Proof.
apply/rpredM; first apply/rpredX.
  by apply/rpred_prod=> j _; rewrite polyOverXsubC mpolyOverX.
by apply/rpred_prod=> j _; rewrite polyOverXsubC mpolyOverX.
Qed.

Lemma F_msize (i : 'I_l.+1) (k : 'I_(size (F i))) j : 
  (msize ((F i)^`(k)).['X_j] <= p * l.+1)%N.
Proof.
apply/(leq_trans (msize_horner _ _)) => {j}.
apply/bigmax_leqP => i0 _.
rewrite coef_derivn -scaler_nat.
apply/(leq_trans (leq_add (leqnn _) (msizeZ_le _ _))).
have [Hord|]:= (ltnP (k + i0) (size (F i))); last first.
  rewrite leqNgt => /negbTE Hlt; rewrite -{3}[F i]coefK coef_poly Hlt msize0.
  rewrite addn0 -(size_F i) ltnW //.
  apply/(leq_trans (ltn_ord i0)) => {i0 Hlt}.
  move: (nat_of_ord k) => {k}; elim => [|k ihk]; first by rewrite derivn0 leqnn.
  apply/(leq_trans _ ihk); rewrite derivnS.
  case: (boolP ((F i)^`(k) == 0)) => [/eqP -> |/lt_size_deriv /ltnW //].
  by rewrite linear0.
apply/(leq_trans (leq_addl k _)); rewrite addnA.
move: Hord; move: (k + i0)%N => k1 ord_k1 {k i0}.
rewrite /F /T -[X in _ * X]big_filter.
set x := \prod_(_ < l.+1) _.
have -> : x ^+ p.-1 = \prod_(r <- (nseq p.-1 (index_enum (ordinal_finType l.+1)))) 
   \prod_(k <- r) ('X - ('X_k)%:P).
  by rewrite big_nseq -/x -(card_ord p.-1) -big_const prodr_const.
rewrite -big_flatten /= -big_cat /= big_tnth /=.
set u := _ ++ _.
pose cs := ((finfun (fun i0 => 'X_(tnth (in_tuple u) i0))) : {mpoly complexR[l.+1]} ^ (size u)).
rewrite (eq_bigr (fun i0 => 'X - (cs i0)%:P)); last first.
  by move=> i0 _; rewrite /cs ffunE.
have size_u : (size u = p.-1 * l.+1 + l)%N.
  rewrite /u size_cat size_flatten size_filter.
  rewrite /shape map_nseq {1}/index_enum -enumT size_enum_ord sumn_nseq.
  set s := index_enum _; set P := (fun _ => _).
  suff -> : count P s = l by rewrite mulnC.
  rewrite (@eq_count _ _ (predC (pred1 i))); last by move=> j /=; rewrite /P.
  apply/eqP; rewrite -(eqn_add2l (count (pred1 i) s)) count_predC.
  rewrite /s /index_enum -enumT (count_uniq_mem _ (enum_uniq _)) size_enum_ord.
  by rewrite mem_enum /= add1n.
have ord_k1S : (k1 < (size u).+1)%N.
  by apply/(leq_trans ord_k1); rewrite size_F size_u -addnS -mulSnr (prednK p_gt0).
rewrite -{2}[k1]/(nat_of_ord (Ordinal ord_k1S)). 
rewrite mroots_coeff_proper /=.
have -> : -1 = - 1 *: 1%:MP by move=> t n; rewrite scaleN1r.
rewrite exprZn -rmorphX /= expr1n -scalerAl mul1r.
apply/(leq_trans (leq_add (leqnn _) (msizeZ_le _ _))).
rewrite mesym_tupleE raddf_sum /=.
apply/(leq_trans (leq_add (leqnn _) (msize_sum _ _ _))).
rewrite -ltnS -ltn_subRL subSn; last first.
  by apply/(leq_trans (ltnW ord_k1)); rewrite size_F.
rewrite ltnS.
apply/bigmax_leqP => t _.
rewrite rmorph_prod /=.
rewrite (eq_bigr (fun i0 => 'X_(tnth (in_tuple u) i0))); last first.
  by move=> i0 _; rewrite mevalX /cs ffunE.
rewrite mprodXE msizeX mdeg_sum (eq_bigr (fun i0 => 1%N)); last first.
  by move=> i0 _; rewrite mdeg1.
rewrite sum1_size size_tuple size_u.
apply: ltn_sub2r; first by move: ord_k1; rewrite size_F.
by rewrite -addnS -mulSnr (prednK p_gt0).
Qed.

Definition Sd (aT : ringType) (P : {poly aT}) j0 := 
  \sum_(j0 <= j < (size P)) P^`(j).

Lemma size_Sd (aT : idomainType) (P : {poly aT}) : 
  [char aT] =i pred0 -> size (Sd P 0) = size P.
Proof.
rewrite charf0P => Hnatr_eq0.
case: (boolP (P == 0)) => [/eqP -> |].
  by rewrite /Sd size_poly0 big_nil size_poly0.
move/polySpred ;
move Hs : (size P).-1 => q.
rewrite /Sd.
elim: q P Hs => [P Hs sP | q Ihq P Hs sP].
  by rewrite sP big_nat1 derivn0.
rewrite big_ltn ; last by rewrite sP.
rewrite derivn0 {1}sP size_addl // big_add1 -pred_Sn.
rewrite (@eq_big_nat _ _ _ _ _ _ (fun i : nat => derivn i (deriv  P) ) );
  last by move => i Hi; apply: derivSn.
suff Hp : (size (P^`()) = q.+1).
  rewrite -Hp Ihq //; last by rewrite Hp -pred_Sn.
  by rewrite lt_size_deriv // -size_poly_gt0 sP.
rewrite [q.+1]pred_Sn -sP /deriv size_poly_eq //.
rewrite sP -!pred_Sn -mulr_natr mulf_neq0 ?Hnatr_eq0 //.
by rewrite -[q.+1]/(q.+2.-1) -sP -lead_coefE lead_coef_eq0 -size_poly_gt0 sP.
Qed.

Definition I i j := Cexp (alpha j) * 
   (Sd (F i) 0).[0].@[alpha] - (Sd (F i) 0).['X_j].@[alpha].

Definition Ji i := \sum_(j < l.+1) (a j) * (I i j).

Definition Jip i : {mpoly complexR[l.+1]} :=  
  - \sum_(j < l.+1) (a j) *: (Sd (F i) 0).['X_j].

Lemma msize_Jip i :
  (msize (Jip i) <= (p * l.+1))%N.
Proof.
rewrite /Jip msizeN.
apply/(leq_trans (msize_sum _ _ _) _) /bigmax_leqP => j _.
rewrite msizeZ ?a_neq0 // /Sd horner_sum.
apply/(leq_trans (msize_sum _ _ _) _); rewrite big_mkord.
apply/bigmax_leqP => k _.
apply: F_msize.
Qed.

Lemma Eq_Ji i : 
  Ji i = (Jip i).@[alpha].
Proof.
rewrite /Ji /I /Jip /=.
rewrite (eq_bigr (fun j => (a j * Cexp (alpha j) * (Sd (F i) 0).[0].@[alpha]
 - a j * (Sd (F i) 0).['X_j].@[alpha]))) /=; last first.
  by move=> j _; rewrite mulrBr -mulrA.
rewrite big_split /= -big_distrl /=.
move/eqP : Lindemann_false; rewrite /Cexp_span => ->; rewrite mul0r add0r.
rewrite -(big_endo _ (@opprD _) (oppr0 _)) mevalN rmorph_sum /=.
by congr (- _); apply: eq_bigr => j _; rewrite mevalZ.
Qed.
(* rentrer le a_j en scal dans le poly Sd *)
(*congr (_ .[ _]); rewrite /Sd [in RHS]size_scale ?expf_neq0 ?c_neq0 //.
rewrite -mul_polyC big_distrr /=.
by apply: eq_bigr => n _; rewrite mul_polyC derivnZ.
Qed.*)

Definition G i : {poly {mpoly complexR[l.+1]}} := 
   \sum_(0 <= j < p * l) (F i)^`N(p)^`(j).

Lemma G_sum i : (G i) *+ (p`!) = \sum_(p <= j < size (F i)) (F i)^`(j).
Proof.
rewrite /G -mulr_natr big_distrl /= size_F mulnS addnC -{4}(add0n p).
rewrite big_addn addnK; apply: eq_bigr => j _.
by rewrite mulr_natr -derivnMn -!nderivn_def addnC derivn_add.
Qed.

Lemma size_G i : (size (G i) = p * l)%N.
Proof.
have -> : size (G i) = size ((G i) *+ (p`!)).
  rewrite -scaler_nat size_scale //.  
  by rewrite -mpolyC_nat mpolyC_eq0 pnatr_eq0 -lt0n fact_gt0.
rewrite G_sum (_ : \sum_(p <=j< size (F i)) (F i)^`(j)=(Sd ((F i)^`(p)) 0)); last first.
  rewrite /Sd (size_derivn_char _ _ HcC) // size_F -{1}[p]add0n big_addn.
  by apply: eq_bigr => j _; rewrite addnC derivn_add.
rewrite size_Sd ?size_derivn_char; [|apply: HcC|apply: HcC]. 
by rewrite size_F mulnS -{3}[p]addn0 subnDl subn0.
Qed.

Lemma G_over i : G i \is a polyOver (mpolyOver _ Cint).
Proof.
by apply/rpred_sum => j _; apply/polyOver_derivn/polyOver_nderivn/F_over.
Qed.

Lemma Fdalpha_re i j : 
        (j != i)%N -> (Sd (F i) 0).['X_j] = (G i).['X_j] *+ p`!. 
Proof. 
move: (mroot_F i) => [_ H] Hj; move: (H j Hj)=> {H} /mrootdP H.
rewrite -hornerMn G_sum /Sd size_F mulnS addnC. 
rewrite (@big_cat_nat _ _ _ p) /= ?hornerD ?horner_sum ?leq0n //; first last. 
  by rewrite -{1}[p]add0n leq_add2r leq0n. 
rewrite (@eq_big_nat _ _ _ _ _ _ (fun i => 0));first by rewrite big1_eq add0r.
move=> k /andP [_ C].
by apply/rootP/(mroot_root _ (H (Ordinal C)));rewrite subn_gt0.
Qed. 

Lemma Fd0_re i : 
     (Sd (F i) 0).['X_i] = 
             (F i)^`N(p.-1).['X_i] *+ (p.-1) `! + (G i).['X_i] *+ p`!.
Proof.
move: (mroot_F i) => [/mrootdP H _].
rewrite -!hornerMn G_sum /Sd /G size_F mulnS addnC -nderivn_def.
have plpnp : (p <= p * l + p)%N  by rewrite -{1}[p]add0n leq_add2r leq0n.
rewrite (big_cat_nat _ _ _ (leq0n p.-1)) /=; last first.
    by rewrite (leq_trans (leq_pred p)).
rewrite hornerD horner_sum (@eq_big_nat _ _ _ _ _ _ (fun i : nat => 0%R)).
  by rewrite big1_eq add0r big_ltn_cond ?hornerD ?(prednK p_gt0).
move=> j /andP [_ Hpi].
move: (H (Ordinal Hpi)) => {H} /= H.
by move: Hpi; rewrite -subn_gt0 => Hpi; move: (mroot_root Hpi H) => /rootP.
Qed.

Lemma Eq_JGi i :
   Ji i = - ((\sum_(j < l.+1) (a j) * (G i).['X_j].@[alpha]) *+ p`!
          + a i * (F i)^`N(p.-1).['X_i].@[alpha] *+ (p.-1) `!).
Proof.
rewrite Eq_Ji (bigD1 i) //= addrC mulrnDl addrA -!mulrnAr -mulrDr -!rmorphMn /=.
rewrite -!mevalD /= -Fd0_re /Jip [in LHS](bigD1 i) //= mevalN mevalD mevalZ.
congr (- (_ + _)); rewrite rmorph_sum -sumrMnl /=.
by apply: eq_bigr => j Hj; rewrite mevalZ (Fdalpha_re Hj) rmorphMn /= mulrnAr.
Qed.

Lemma Eq_JGip i :
   Jip i = - ((\sum_(j < l.+1) (a j) *: (G i).['X_j]) *+ p`!
          + a i *: (F i)^`N(p.-1).['X_i] *+ (p.-1) `!).
Proof.
rewrite /Jip (bigD1 i) //= [in RHS](bigD1 i) //= mulrnDl -[in RHS]addrAC.
congr (-(_ + _)); first by rewrite Fd0_re addrC scalerDr !scalerMnr.
rewrite -sumrMnl; apply: eq_bigr => j; move/Fdalpha_re => ->.
by rewrite scalerMnr.
Qed.

Definition J := c ^+ (\sum_(i < l.+1) (p * l.+1)) * \prod_(i < l.+1) Ji i.

Lemma eq_J_mpoly : J = c ^+ (\sum_(i < l.+1) (p * l.+1)) * (\prod_(i < l.+1) (Jip i)).@[alpha].
Proof.
rewrite /J; congr (_ * _); rewrite rmorph_prod /=.
by apply: eq_bigr => i _; rewrite Eq_Ji.
Qed.

Lemma J_msize : 
   (msize (\prod_(i < l.+1) (Jip i)) <= \sum_(i < l.+1) (p * l.+1))%N.
Proof.
apply/(leq_trans (msize_prod _ _) _); rewrite leq_subLR.
have : (\sum_(i < l.+1) msize (Jip i) <= \sum_(i < l.+1) (p * l.+1))%N.
  by apply: leq_sum => i _; apply/msize_Jip.
move/leq_ltn_trans; apply; rewrite -[X in (X < _)%N]add0n ltn_add2r.
by rewrite sum_nat_const muln1 cardT size_enum_ord.
Qed.

Lemma J_msym : {in part, forall Q : {set 'I_l.+1}, 
   (\prod_(i < l.+1) (Jip i)) \is symmetric_for _ Q}.
Proof.
move=> Q Q_in; apply/issym_forP => s s_on.
have := (constantP 0 _ (a_constant Q_in)).
set sa := [seq _ | _ in _]; move => [a_c eq_a_c].
rewrite [RHS](reindex_inj (@perm_inj _ s)) rmorph_prod /=.
apply/eq_bigr => i_prod _; rewrite !Eq_JGip msymN msymD msymMn rmorph_sum /=.
congr (-((_ *+ _) + _)).
  rewrite [RHS](reindex_inj (@perm_inj _ s)) /=.
  apply/eq_bigr => i_a _; rewrite msymZ.
  congr (_ *: _).
    case: (boolP (i_a \in Q)) => [i_a_in|]; last first.
      by move/(out_perm s_on) => ->.
    have i_a_in_seq : a i_a \in sa by apply: map_f; rewrite mem_enum.
    have : a (s i_a) \in sa. 
      by apply: map_f; rewrite mem_enum (perm_closed _ s_on).
    rewrite eq_a_c; move/nseqP => [-> _].
    by move: i_a_in_seq; rewrite eq_a_c; move/nseqP => [ -> _].
  rewrite /G !horner_sum rmorph_sum /=.
  apply/eq_bigr => i_der _; rewrite -horner_map /= msymX /=.
  congr (_ .[ _] ); first rewrite -derivn_map -nderivn_map rmorphM /=.
    congr (((_ * _)^`N(_)) ^`(_)); first rewrite rmorphX /=.
      congr (_ ^+ _); rewrite [RHS](reindex_inj (@perm_inj _ s)) rmorph_prod /=.
      apply/eq_bigr => i_last _; rewrite rmorphB /= map_polyX map_polyC /=.
      congr (_ - _%:P); rewrite msymX; congr mpolyX.
      apply/mnmP => j; rewrite mnmE !mnm1E; congr nat_of_bool.
      by apply/eqP/eqP => [-> | <-]; rewrite ?permKV ?permK.
    rewrite /T rmorph_prod /= [RHS](reindex_inj (@perm_inj _ s)) /=.
    apply/congr_big => //.
      move=> j; apply/negP/negP => H1 /eqP. 
        by move/perm_inj => H2; apply: H1; rewrite H2.
      by move=> H2; apply: H1; rewrite H2.
    move=> i_last _; rewrite rmorphB /= map_polyX map_polyC /=.
    congr (_ - _%:P); rewrite msymX; congr mpolyX.
    apply/mnmP => j; rewrite mnmE !mnm1E; congr nat_of_bool.
    by apply/eqP/eqP => [-> | <-]; rewrite ?permKV ?permK.
  congr mpolyX; apply/mnmP => i_last; rewrite mnmE !mnm1E; congr nat_of_bool.
  by apply/eqP/eqP => [-> | <-]; rewrite ?permKV ?permK.
rewrite msymMn msymZ -horner_map /= msymX -nderivn_map /= /F rmorphM /=.
congr (_ *: _ *+ _).
  case: (boolP (i_prod \in Q)) => [i_a_in|]; last first.
    by move/(out_perm s_on) => ->.
  have i_a_in_seq : a i_prod \in sa by apply: map_f; rewrite mem_enum.
  have : a (s i_prod) \in sa. 
    by apply: map_f; rewrite mem_enum (perm_closed _ s_on).
  rewrite eq_a_c; move/nseqP => [-> _].
  by move: i_a_in_seq; rewrite eq_a_c; move/nseqP => [ -> _].
congr ((_ * _)^`N( _).[ _]).
    rewrite rmorphX rmorph_prod; congr (_ ^+ _). 
    rewrite [RHS](reindex_inj (@perm_inj _ s)) /=.
    apply/eq_bigr => i_last _; rewrite rmorphB /= map_polyX map_polyC /=.
    congr (_ - _%:P); rewrite msymX; congr mpolyX.
    apply/mnmP => j; rewrite mnmE !mnm1E; congr nat_of_bool.
    by apply/eqP/eqP => [-> | <-]; rewrite ?permKV ?permK.
  rewrite /T rmorph_prod /= [RHS](reindex_inj (@perm_inj _ s)) /=.
  apply/congr_big => //.
    move=> j; apply/negP/negP => H1 /eqP. 
      by move/perm_inj => H2; apply: H1; rewrite H2.
    by move=> H2; apply: H1; rewrite H2.
  move=> i_last _; rewrite rmorphB /= map_polyX map_polyC /=.
  congr (_ - _%:P); rewrite msymX; congr mpolyX.
  apply/mnmP => j; rewrite mnmE !mnm1E; congr nat_of_bool.
  by apply/eqP/eqP => [-> | <-]; rewrite ?permKV ?permK.
congr mpolyX; apply/mnmP => i_last; rewrite mnmE !mnm1E; congr nat_of_bool.
by apply/eqP/eqP => [-> | <-]; rewrite ?permKV ?permK.
Qed.


Lemma J_divp1 : J / (p.-1)`!%:R \is a Cint.
Proof.
suff : (J / (\prod_(i < l.+1) (p.-1)`!%:R)) \is a Cint.
  rewrite prodr_const /= card_ord exprS; set pp := _%:R ^+ _ => H.
  have pp_neq0 : pp != 0 by apply:expf_neq0; rewrite pnatr_eq0 -lt0n fact_gt0.
  rewrite -[X in X \is a Cint]mulr1 -[X in _ * X](divff pp_neq0) mulf_div.
  by rewrite (mulrC J) -mulrA rpredM // Cint_Cnat ?rpredX ?Cnat_nat.
rewrite eq_J_mpoly mulrAC -mulrA -mevalZ.
apply: (sym_fundamental_seqroots_for_leq part_partition) => //.
+ rewrite -prodfV -scaler_prod.
  apply/rpred_prod => i_prod _; rewrite Eq_JGip scalerN /= -scaleN1r.
  apply/mpolyOverZ; first rewrite -sub0r; last rewrite scalerDr.
    by apply/rpredB; [apply/Cint0 | apply/Cint1].
  apply/rpredD; rewrite -!scaler_nat !scalerA; last first.
    rewrite mulVf ?mul1r; last by rewrite pnatr_eq0 -lt0n fact_gt0.
    apply/mpolyOverZ => //; apply/rpred_horner; last by rewrite mpolyOverX.
    by apply/polyOver_nderivn/F_over.
  rewrite -[X in (_ * X`!%:R)](prednK p_gt0) factS natrM mulrCA mulVf ?mul1r.
    apply/mpolyOverZ; first by rewrite mulr1 Cint_Cnat ?Cnat_nat.
    apply/rpred_sum => i_sum _; apply/mpolyOverZ => //.
    by apply/rpred_horner; rewrite ?G_over ?mpolyOverX.
  by rewrite pnatr_eq0 -lt0n fact_gt0.
+ by move=> Q Q_in; apply/rpredZ/(J_msym Q_in).
apply/(leq_trans (msizeZ_le _ _) _)/J_msize.
Qed.

Lemma JB_divp : 
   ((J - c ^+ (\sum_(i < l.+1) (p * l.+1)) * (\prod_(i < l.+1) (- ((p.-1)`!%:R * a i) *: 
     (F i)^`N(p.-1).['X_i])).@[alpha]) / p`!%:R) \is a Cint.
Proof.
set x := \prod_(_ | _) _; set y := _ * x.@[alpha].
suff : ((J - y) / (p%:R * \prod_(i < l.+1) (p.-1)`!%:R)) \is a Cint.
  rewrite prodr_const /= card_ord exprS; set pp := _%:R ^+ _.
  rewrite mulrA -[X in X%:R](prednK p_gt0) -natrM -factS (prednK p_gt0) => H.
  have pp_neq0 : pp != 0 by apply:expf_neq0; rewrite pnatr_eq0 -lt0n fact_gt0.
  rewrite -[X in X \is a Cint]mulr1 -[X in _ * X](divff pp_neq0) mulf_div.
  by rewrite (mulrC (J - _)) -mulrA rpredM // Cint_Cnat ?rpredX ?Cnat_nat.
rewrite mulrDl mulNr eq_J_mpoly mulrAC -mulrA -mevalZ /y -mulrA -mulrBr.
rewrite [X in _ - X]mulrC -mevalZ -mevalB.
apply: (sym_fundamental_seqroots_for_leq part_partition) => //; first last.
+ apply/(leq_trans (msizeD_le _ _)); rewrite msizeN geq_max; apply/andP; split.
    by apply/(leq_trans (msizeZ_le _ _))/J_msize.
  apply/(leq_trans (msizeZ_le _ _))/(leq_trans (msize_prod _ _)).
  rewrite leq_subLR.
  have : (\sum_(i < l.+1) msize (- ((p.-1)`!%:R * a i) *: ((F i)^`N(p.-1)).['X_i])
    <= \sum_(i < l.+1) p * l.+1)%N.
    apply: leq_sum => i _; apply/(leq_trans (msizeZ_le _ _)).
    have p_ord : (p.-1 < size (F i))%N.
      by rewrite size_F mulnS (prednK p_gt0) leq_addr.
    have := (F_msize (Ordinal p_ord) i); rewrite nderivn_def.
    by rewrite hornerMn -scaler_nat msizeZ // pnatr_eq0 -lt0n fact_gt0.
  move/leq_ltn_trans; apply; rewrite -[X in (X < _)%N]add0n ltn_add2r.
  by rewrite sum_nat_const muln1 cardT size_enum_ord.
+ move=> Q Q_in; apply/rpredB/rpredZ; first by apply/rpredZ/(J_msym Q_in).
  apply/issym_forP => s s_on.
  have := (constantP 0 _ (a_constant Q_in)).
  set sa := [seq _ | _ in _]; move => [a_c eq_a_c].
  rewrite [RHS](reindex_inj (@perm_inj _ s)) rmorph_prod /=.
  apply/eq_bigr => i_prod _; rewrite msymZ.
  congr (- (_ * _) *: _).
    case: (boolP (i_prod \in Q)) => [i_prod_in|]; last first.
      by move/(out_perm s_on) => ->.
    have i_prod_in_seq : a i_prod \in sa by apply: map_f; rewrite mem_enum.
    have : a (s i_prod) \in sa. 
      by apply: map_f; rewrite mem_enum (perm_closed _ s_on).
    rewrite eq_a_c; move/nseqP => [-> _].
    by move: i_prod_in_seq; rewrite eq_a_c; move/nseqP => [ -> _].
  rewrite -horner_map /= msymX /=.
  congr (_ .[ _] ); first rewrite -nderivn_map rmorphM /=.
    congr (((_ * _)^`N(_))); first rewrite rmorphX /=.
      congr (_ ^+ _); rewrite [RHS](reindex_inj (@perm_inj _ s)) rmorph_prod /=.
      apply/eq_bigr => i_last _; rewrite rmorphB /= map_polyX map_polyC /=.
      congr (_ - _%:P); rewrite msymX; congr mpolyX.
      apply/mnmP => j; rewrite mnmE !mnm1E; congr nat_of_bool.
      by apply/eqP/eqP => [-> | <-]; rewrite ?permKV ?permK.
    rewrite /T rmorph_prod /= [RHS](reindex_inj (@perm_inj _ s)) /=.
    apply/congr_big => //.
      move=> j; apply/negP/negP => H1 /eqP. 
        by move/perm_inj => H2; apply: H1; rewrite H2.
      by move=> H2; apply: H1; rewrite H2.
    move=> i_last _; rewrite rmorphB /= map_polyX map_polyC /=.
    congr (_ - _%:P); rewrite msymX; congr mpolyX.
    apply/mnmP => j; rewrite mnmE !mnm1E; congr nat_of_bool.
    by apply/eqP/eqP => [-> | <-]; rewrite ?permKV ?permK.
  congr mpolyX; apply/mnmP => i_last; rewrite mnmE !mnm1E; congr nat_of_bool.
  by apply/eqP/eqP => [-> | <-]; rewrite ?permKV ?permK.
rewrite invfM -!scalerA -prodfV -scaler_prod -scalerBr.
pose P := (fun i (k : bool) => if k
  then (- (p%:R) *: \sum_(j < l.+1) ((a j) *: (G i).['X_j]))
  else (- a i *: (F i)^`N(p.-1).['X_i])) : 'I_l.+1 -> bool -> {mpoly complexR[l.+1]}.
have -> : \prod_(i < l.+1) ((p.-1)`!%:R^-1 *: Jip i) = 
   \prod_(i < l.+1) \sum_(j : bool) P i j.
  apply/eq_bigr=> i_prod _; rewrite Eq_JGip scalerN scalerDr opprD.
  set v := index_enum bool_finType.
  have -> : v = [:: true; false] by rewrite /v /index_enum unlock.
  rewrite big_cons big_seq1 /P /= !scaleNr.
  congr (- _ - _); rewrite -scaler_nat scalerA; last first.
    by rewrite mulVf ?scale1r // pnatr_eq0 -lt0n fact_gt0.
  rewrite -[X in _ * X`!%:R](prednK p_gt0) factS natrM mulrCA mulVf; last first.
    by rewrite pnatr_eq0 -lt0n fact_gt0.
  by rewrite (prednK p_gt0) mulr1.
rewrite bigA_distr_bigA /=; set z := \prod_(_ | _) _ *: x.
pose f_false := finfun (fun _ : 'I_l.+1 => false).
have -> : z = \prod_(i < l.+1) P i (f_false i).
  rewrite /z /x -scaler_prod.
  apply: eq_bigr => i _; rewrite scaleNr scalerN scalerA mulrA mulVf ?mul1r.
    by rewrite /P /f_false ffunE scaleNr.
  by rewrite pnatr_eq0 -lt0n fact_gt0.
rewrite (bigD1 f_false) //= addrAC subrr add0r scaler_sumr.
apply: rpred_sum => f Hf.
have [i_f] : exists i : 'I_l.+1, f i != f_false i.
  apply/existsP; rewrite -negb_forall.  
  apply/negP => /forallP Hfi; move/negP: Hf; apply; apply/eqP/ffunP => j.
  by move/eqP: (Hfi j).
rewrite /f_false ffunE /= eqbF_neg => /negPn => Hfi.
rewrite (bigD1 i_f) //= scalerAl [X in _ *: X]/P Hfi scalerA mulrN mulVf; last first.
  by rewrite pnatr_eq0 -lt0n p_gt0.
apply/rpredM.
  apply/mpolyOverZ; first by rewrite rpredN Cint1.
  apply/rpred_sum => i _; apply/mpolyOverZ => //; apply/rpred_horner.
    by apply/G_over.
  by apply/mpolyOverX.
apply/rpred_prod => i _; rewrite /P.
case: ifP => _; apply/mpolyOverZ; rewrite ?rpredN //.
+ by apply/Cint_Cnat/Cnat_nat.
+ apply/rpred_sum => j _; apply/mpolyOverZ=> //; apply/rpred_horner.
    by apply/G_over.
  by apply/mpolyOverX.
apply/rpred_horner; last by apply/mpolyOverX.
by apply/polyOver_nderivn/F_over.
Qed.


Lemma JC_ndivp : 

   ~~ (((c ^+ (\sum_(i < l.+1) (p * l.+1)) * 
     (\prod_(i < l.+1) (- ((p.-1)`!%:R * a i) *: 
     (F i)^`N(p.-1).['X_i])).@[alpha]) / p`!%:R) \is a Cint).
Proof.

Search _ deriv.


suff : \prod_(i < l.+1) (- a i * ((F i)^`N(p.-1)).['X_i].@[alpha] *+ (p.-1)`!) 
                 / p%:R \isn't a Cint.
  set x := \prod_(_ | _) _.
  move=> /negP H; apply/negP.
  rewrite -(prednK (p_gt0)) factS (prednK (p_gt0)) mulnC natrM => H1; apply: H.
  have : (x / ((p.-1)`!%:R * p%:R)) * (p.-1)`!%:R \is a Cint.
    by apply: rpredM => //; apply/Cint_Cnat/Cnat_nat.
  rewrite mulrAC invfM -!mulrA [X in _ * X]mulrA divff ?mulrA ?mulr1 //.
  by rewrite pnatr_eq0 -lt0n fact_gt0.
(* vraiment pas cool ce suff *)










Lemma J_ndivp : ~~ ((J / p`!%:R) \is a Cint).

Lemma J_ge : `|J| >= (p.-1)`!%:R.

set_partition_big_cond:
  forall (T : finType) (R : Type) (idx : R) (op : Monoid.com_law idx) (P : {set {set T}})
    (D : {set T}) (K : pred T) (E : T -> R),
  partition P D ->
  \big[op/idx]_(x in D | K x) E x =
  (fun (P0 : {set {set T}}) (K0 : T -> bool) (E0 : T -> R) =>
   \big[op/idx]_(A in P0) \big[op/idx]_(x in A | K0 x) E0 x) P K E
set_partition_big:
  forall (T : finType) (R : Type) (idx : R) (op : Monoid.com_law idx) (P : {set {set T}})
    (D : {set T}) (E : T -> R),
  partition P D ->
  \big[op/idx]_(x in D) E x =
  (fun (P0 : {set {set T}}) (E0 : T -> R) => \big[op/idx]_(A in P0) \big[op/idx]_(x in A) E0 x) P E













End Wlog3.



(*
(* changement avec l.+1 + les notations et th pratiques *)
Definition l := pre_l.-1.

Definition alpha : complexR ^ l.+1 := 
  (finfun (pre_alpha \o (cast_ord (prednK pre_l_gt0)))).

Lemma alpha_inj : injective alpha.
Proof.
move=> i j; rewrite !ffunE /=. 
by move/pre_alpha_inj /cast_ord_inj.
Qed.

Lemma alpha_algebraic : forall i : 'I_l.+1, alpha i is_algebraic.
Proof. by move=> i; rewrite ffunE; apply: pre_alpha_algebraic. Qed.

Definition part : {set {set 'I_l.+1}} := [set (fun P : {set 'I_pre_l} => 
  [set (cast_ord (esym (prednK pre_l_gt0)) i) | i in P]) P | P in pre_part].

Lemma part_cover : cover part = [set: 'I_l.+1].
Proof.
apply/setP => i; rewrite in_setT -[i](cast_ordK (prednK pre_l_gt0)).
set j := cast_ord _ i; rewrite cover_imset; apply/bigcupP.
have := (in_setT j); rewrite -pre_part_cover; move/bigcupP => [I I_in j_in].
by exists I; rewrite ?mem_imset.
Qed.

Definition b : {set 'I_l.+1} -> complexR := (finfun (pre_b \o 
  (fun P : {set 'I_l.+1} => [set (cast_ord (prednK pre_l_gt0) i) | i in P]))).

Lemma b_neq0 : forall P, (P \in part) = (b P != 0).
Proof.
move=> P; rewrite /b ffunE /= -pre_b_neq0.
apply/imsetP/idP => [[] I I_in -> | ].
  rewrite -imset_comp (@eq_imset _ _ _ (fun x => x)) ?imset_id //=.
  by move=> i; rewrite /= cast_ordKV.
set I := [set _ | _ in P]; move => I_in; exists I => //.
rewrite -imset_comp -[LHS]imset_id.
by apply: eq_imset => i; rewrite /= cast_ordK.
Qed.

Lemma b_Cint : forall P, b P \is a Cint.
Proof. by move=> P; rewrite /b ffunE /= pre_b_Cint. Qed.

Definition a := [ffun i => \sum_(P in part | i \in P) b P].

Lemma a_eq_sum i : a (cast_ord (esym (prednK pre_l_gt0)) i) = 
  \sum_(P in pre_part | i \in P) pre_b P.
Proof.
rewrite /a ffunE /= /part big_mkcondr /= big_imset /= ?big_mkcondr /=.
  apply: eq_bigr => I I_in; rewrite /b ffunE /=; congr (if _ then _ else _).
    by rewrite -(mem_imset_inj _ _ (@cast_ord_inj _ _ _)).    
  rewrite -imset_comp (@eq_imset _ _ _ (fun x => x)) ?imset_id //=.
  by move=> j; rewrite /= cast_ordKV.
move=> I J I_in J_in /setP eq_IJ; apply/setP => j.
rewrite (mem_imset_inj _ _ (@cast_ord_inj _ _ (esym (prednK pre_l_gt0)))).
by rewrite eq_IJ -(mem_imset_inj _ _ (@cast_ord_inj _ _ _)).
Qed.

Lemma a_neq0 : exists i : 'I_l.+1, a i != 0.
Proof.
have [i sum_neq0] := pre_a_neq0.
exists (cast_ord (esym (prednK pre_l_gt0)) i). 
by rewrite a_eq_sum.
Qed.
 
Lemma Lindemann_false : Cexp_span a alpha == 0.
Proof.
apply/eqP; rewrite -[RHS](elimT eqP pre_Lindemann_false) /Cexp_span.
rewrite (reindex (cast_ord (esym (prednK pre_l_gt0)))) /=.
  by apply: eq_bigr => i _; rewrite a_eq_sum !ffunE /= cast_ordKV.
apply/onW_bij/(inj_card_bij (@cast_ord_inj _ _ _)).
by rewrite !card_ord prednK.
Qed.

Lemma alpha_setZroots : forall (P : {set 'I_l.+1}), P \in part -> 
  (finfun (alpha \o (@enum_val _ (pred_of_set P)))) \is a setZroots c.
Proof.
move=> P /imsetP [] Q Q_in eq_PQ; rewrite set_rootsE. 
have := (pre_alpha_setZroots Q_in); rewrite !set_rootsE.
move=> H; erewrite congr1; first exact: H. 
congr (c *: _ \is a polyOver _); rewrite /alpha.
rewrite !(big_ffun _ _ _ _ _ (fun i => ('X - i%:P))) /=.
rewrite -(big_map _ xpredT (fun i => 'X - (pre_alpha i)%:P)).
rewrite -(big_map _ xpredT (fun i => 'X - (alpha i)%:P)) /alpha /=.
rewrite (big_ffun _ _ _ _ _ (fun i => ('X - i%:P))) /=.
rewrite -(big_map _ xpredT (fun i => 'X - (pre_alpha i)%:P)).
apply: eq_big_perm; rewrite -!map_comp.
apply: uniq_perm_eq; rewrite ?map_inj_uniq ?/index_enum -?enumT ?enum_uniq //.
+ by apply/inj_comp; first apply/cast_ord_inj; apply/enum_val_inj.
+ by apply/enum_val_inj.
have eq_card : #|pred_of_set P| = #|pred_of_set Q|.
  by rewrite eq_PQ card_imset //; apply/cast_ord_inj.
move => x; apply/mapP/mapP => [[i _ ->] | [i _ ->]].
  exists (cast_ord eq_card i); rewrite ?mem_enum //.
  apply/enum_rank_inj => /=.

Set Printing All.

  apply/ord_inj => /=; rewrite ?eq_PQ.
  erewrite !enum_val_nth.

Search _ enum_val.
  


Search  _ map mem.

Search "congr" in bigop.
Search _ "big" in finset.



move=> /polyOverP => Hpre.
apply/polyOverP => i.
*)


