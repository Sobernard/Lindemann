Require Import Reals.
From coquelicot
Require Import Hierarchy RInt.
From mathcomp Require Import all_ssreflect.
From mathcomp
Require Import ssralg ssrnum mxpoly rat poly ssrint polyorder polydiv perm.
From mathcomp
Require Import finfun intdiv.
From SsrMultinomials
Require Import finmap order mpoly.
From Lind
Require Import seq_ajouts.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.
Import GRing.Theory Num.Theory ArchimedeanTheory.

(* For Cnat/Cint from Cstruct to superseed those from Num.Theory and ArchTh *)
From structs
Require Import Canalysis Cstruct Rstruct.

Import Cstruct.ComplexTotalOrder.

Local Notation setZroots := ((set_roots Cint) : 
    complexR -> qualifier 1 {fset complexR}).









Section Lindemann_last.










(**** * Variables from Lindemann_wlog2 * ****)

Variable l : nat.
Variable c : complexR.
Variable alpha : complexR ^ l.+1.
Variable part : {set {set 'I_l.+1}}.
Variable a : complexR ^ l.+1.


(**** * Hypothesis from Lindemann_wlog2 * ****)

Hypothesis c_neq0 : c != 0.
Hypothesis c_Cint : c \is a Cint.

Hypothesis alpha_inj : injective alpha.

Hypothesis part_partition : partition part [set: 'I_l.+1].
Hypothesis alpha_setZroots : {in part, forall P : {set 'I_l.+1},
  [fset (alpha i) | i in P]%fset \is a setZroots c}.

Hypothesis a_neq0 : forall i : 'I_l.+1, a i != 0.
Hypothesis a_Cint : forall i : 'I_l.+1, a i \is a Cint.
Hypothesis a_constant : {in part, forall P : {set 'I_l.+1}, 
  constant [seq a i | i in P]}.

Hypothesis Lindemann_false : Cexp_span a alpha == 0.












(**** * Variables to choose the prime number p **** *)

Definition T (i : 'I_l.+1) : {poly complexR} :=
  \prod_(j < l.+1 | j != i) ('X - (alpha j)%:P).

Lemma ex_M_T i j :
 {M : R | forall x : R, 0 <= x <= 1 -> norm (T i).[x *: alpha j] < M}.
Proof.
move: (Continuity.bounded_continuity
                                  (fun y => ((T i).[y *: (alpha j)])) 0 1) => H.
have : forall x : R, and (Rle 0 x) (Rle x 1) ->
       filterlim (fun y : R => (T i).[y *: alpha j]) (locally x) 
                                                 (locally (T i).[x *: alpha j]).
  move=> x [/RleP H0 /RleP H1].
  by apply/Crcontinuity_pt_filterlim/Crcontinuity_pt_poly.
move=> Hb; move: (H Hb) => [M M_H].
by exists M; move=> x /andP[H0 H1]; apply/RltP; apply: M_H; split; apply/RleP.
Qed.

Definition Mt i j := sval (ex_M_T i j).

Definition Mal := max_norm alpha.

Definition Ma := max_norm a. 

Definition Me := max_norm (fun i => exp (Rmax 0 (Re_R (-alpha i)))).

Definition Mm := max_norm (fun i => max_norm (fun j => Mt i j)).

Definition MJi1 := Num.bound (Ma * Mal * exp Mal * Me * (norm c) ^+ l.+1 * Mm).

Definition MJip := Num.bound ((norm c) ^+ l.+1 * (Mal *+ 2) * Mm).

Open Scope nat_scope.

Definition MJi := l.+1 * MJi1.

Lemma p_prop2 :
  exists p : nat, prime p && (MJi * MJip ^ p.-1 < (p.-1)`!) && (p > `|floorC c|) &&
      (p >  `|floorC (\prod_(i < l.+1) a i)|) && (p > `|floorC (c ^+ (\sum_(i < l.+1) l) *
           \prod_(i < l.+1) \prod_(j < l.+1 | j != i) (alpha i - alpha j))|).
Proof.
destruct (p_prop1 MJi MJip) as [q Pq].
set u1 := `| _|; set u2 := `| _ |; set u3 := `| _ |.
set q' := maxn q (maxn (maxn u1 u2) u3).
case: (prime_above q') => p Hmax isPrime.
exists p; rewrite isPrime.
move: Hmax; rewrite !gtn_max => /and3P [H1 /andP[-> ->] ->].
by rewrite Pq // -ltnS (ltn_predK H1).
Qed.

Definition p := xchoose p_prop2.

Lemma p_prime : prime p.
Proof. by move: (xchooseP p_prop2) => /andP [/andP [/andP [/andP [->]]]]. Qed.

Lemma p_gt0 : 0 < p.
Proof. by exact: (prime_gt0 p_prime). Qed.
Hint Resolve p_gt0.

Lemma p_gt1 : 1 < p.
Proof. by exact: (prime_gt1 p_prime). Qed.
Hint Resolve p_gt1.

Lemma p_gt_c : p > `| floorC c |.
Proof. by move: (xchooseP p_prop2) => /andP [/andP [/andP [H ->]]]. Qed.

Lemma p_gt_a : p > `|  floorC (\prod_(i < l.+1) a i)|.
Proof. by move: (xchooseP p_prop2) => /andP [/andP [H ->]]. Qed.

Lemma p_gt_alpha : p >  `|floorC (c ^+ (\sum_(i < l.+1) l) *
           \prod_(i < l.+1) \prod_(j < l.+1 | j != i) (alpha i - alpha j))|.
Proof. by move: (xchooseP p_prop2) => /andP [/andP [H H1]] ->. Qed.

Lemma majoration : MJi * MJip ^ p.-1 < (p.-1)`!.
Proof. by move:(xchooseP p_prop2) => /andP [/andP [/andP [/andP [H ->]]]]. Qed.

Open Scope ring_scope.
















(* **** Definitions for both parts **** *)

Definition Tm (i : 'I_l.+1) : {poly {mpoly complexR[l.+1]}} :=
  \prod_(j < l.+1 | j != i) ('X - ('X_j)%:P).

Definition Fm (i : 'I_l.+1) : {poly {mpoly complexR[l.+1]}} := 
   ((\prod_(j < l.+1) ('X - ('X_j)%:P)) ^+ p.-1 * (Tm i)).

Definition I (i j : 'I_l.+1) : complexR :=  
   (Sd (Fm i) 0).[0].@[alpha] - Cexp(- alpha j) * (Sd (Fm i) 0).['X_j].@[alpha].

Definition J (i : 'I_l.+1) : complexR := 
   c ^+ (p * l.+1).-1 * \sum_(j < l.+1) (a j) * Cexp(alpha j) * (I i j).

(* TODO : necessary to have a def here ? maybe for explanations *)
Definition K : complexR := \prod_(i < l.+1) J i.















(* **************** Algebraic Part *************** *)



(* **** Tm : Properties **** *)

Lemma size_Tm i : size (Tm i) = l.+1.
Proof.
rewrite /Tm -big_filter size_prod_XsubC -rem_filter.
  by rewrite size_rem // /index_enum -enumT size_enum_ord prednK.
by rewrite /index_enum -enumT enum_uniq.
Qed.



(* **** Fm : Properties **** *)

Lemma size_Fm i : size (Fm i) = (p * l.+1)%N.
Proof.
rewrite size_mul; last first; first by rewrite -size_poly_eq0 size_Tm.
  by apply/expf_neq0/prodf_neq0 => j _; rewrite polyXsubC_eq0.
rewrite size_Tm polyrcf.my_size_exp; last first.
  by apply/prodf_neq0 => j _; rewrite polyXsubC_eq0.
rewrite size_prod_XsubC /index_enum -enumT size_enum_ord [in RHS]mulnC /=. 
by rewrite -[in RHS](prednK p_gt0) [in RHS]mulnS addnC.
Qed.

Lemma Fm_neq0 i : Fm i != 0.
Proof. by rewrite -size_poly_gt0 size_Fm muln_gt0 p_gt0 ltn0Sn. Qed.

Lemma mroot_Fm i :
  mroot (Fm i) p.-1 ('X_i) /\ forall j,  (j != i)%N -> mroot (Fm i) p ('X_j).
Proof.
split; first apply/mrootP. 
  exists ((Tm i) ^+ p); rewrite /Fm mulrC.
  rewrite -[X in (Tm i) ^+ X](prednK p_gt0) exprS -mulrA -exprMn. 
  by congr (_ * (_ ^+ _)); rewrite mulrC (bigD1 i).
move=> j Hle; have -> : (p = p.-1 + 1)%N by rewrite addn1 prednK ?p_gt0.
apply/mrootM; last first.
  apply/root_mroot/rootP; rewrite horner_prod.
  by apply/eqP/prodf_eq0; exists j => //; rewrite hornerXsubC subrr.
apply/mrootX/rootP; rewrite horner_prod.
by apply/eqP/prodf_eq0; exists j => //; rewrite hornerXsubC subrr.
Qed.

Lemma Fm_over i : Fm i \is a polyOver (mpolyOver _ Cint).
Proof.
apply/rpredM; first apply/rpredX.
  by apply/rpred_prod=> j _; rewrite polyOverXsubC mpolyOverX.
by apply/rpred_prod=> j _; rewrite polyOverXsubC mpolyOverX.
Qed.

Lemma msize_Fm (i : 'I_l.+1) (k : 'I_(size (Fm i))) j : 
  (msize ((Fm i)^`(k)).['X_j] <= p * l.+1)%N.
Proof.
apply/(leq_trans (msize_horner _ _)) => {j}.
apply/bigmax_leqP => i0 _.
rewrite coef_derivn -scaler_nat.
apply/(leq_trans (leq_add (leqnn _) (msizeZ_le _ _))).
have [Hord|]:= (ltnP (k + i0) (size (Fm i))); last first.
  rewrite leqNgt => /negbTE Hlt; rewrite -{3}[Fm i]coefK coef_poly Hlt msize0.
  rewrite addn0 -(size_Fm i) ltnW //.
  apply/(leq_trans (ltn_ord i0)) => {i0 Hlt}.
  move: (nat_of_ord k) => {k}; elim => [|k ihk]; first by rewrite derivn0 leqnn.
  apply/(leq_trans _ ihk); rewrite derivnS.
  case: (boolP ((Fm i)^`(k) == 0)) => [/eqP -> |/lt_size_deriv /ltnW //].
  by rewrite linear0.
apply/(leq_trans (leq_addl k _)); rewrite addnA.
move: Hord; move: (k + i0)%N => k1 ord_k1 {k i0}.
rewrite /Fm /Tm -[X in _ * X]big_filter.
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
  by apply/(leq_trans ord_k1); rewrite size_Fm size_u -addnS -mulSnr (prednK p_gt0).
rewrite -{2}[k1]/(nat_of_ord (Ordinal ord_k1S)). 
rewrite mroots_coeff_proper /=.
have -> : -1 = - 1 *: 1%:MP by move=> t n; rewrite scaleN1r.
rewrite exprZn -rmorphX /= expr1n -scalerAl mul1r.
apply/(leq_trans (leq_add (leqnn _) (msizeZ_le _ _))).
rewrite mesym_tupleE raddf_sum /=.
apply/(leq_trans (leq_add (leqnn _) (msize_sum _ _ _))).
rewrite -ltnS -ltn_subRL subSn; last first.
  by apply/(leq_trans (ltnW ord_k1)); rewrite size_Fm.
rewrite ltnS.
apply/bigmax_leqP => t _.
rewrite rmorph_prod /=.
rewrite (eq_bigr (fun i0 => 'X_(tnth (in_tuple u) i0))); last first.
  by move=> i0 _; rewrite mevalX /cs ffunE.
rewrite mprodXE msizeX mdeg_sum (eq_bigr (fun i0 => 1%N)); last first.
  by move=> i0 _; rewrite mdeg1.
rewrite sum1_size size_tuple size_u.
apply: ltn_sub2r; first by move: ord_k1; rewrite size_Fm.
by rewrite -addnS -mulSnr (prednK p_gt0).
Qed.



(* **** Link between J and mpoly : Jm **** *)

Definition Jm i : {mpoly complexR[l.+1]} :=  
  - \sum_(j < l.+1) (a j) *: (Sd (Fm i) 0).['X_j].


Lemma eq_J_mpoly i : 
  J i = c ^+ (p * l.+1).-1 * (Jm i).@[alpha].
Proof.
rewrite /J /I /Jm /=.
rewrite (eq_bigr (fun j => (a j * Cexp (alpha j) * (Sd (Fm i) 0).[0].@[alpha]
 - a j * (Sd (Fm i) 0).['X_j].@[alpha]))) /=; last first.
  move=> j _; rewrite mulrBr mulrA.
  by congr (_ - (_ * _)); rewrite -mulrA CexpRD subrr Cexp0 mulr1.
rewrite big_split /= -big_distrl /=.
move/eqP : Lindemann_false; rewrite /Cexp_span => ->; rewrite mul0r add0r.
rewrite -(big_endo _ (@opprD _) (oppr0 _)) mevalN rmorph_sum /=.
by congr (_ * - _); apply: eq_bigr => j _; rewrite mevalZ.
Qed.



(* **** Jm : Properties **** *)

Lemma msize_Jm i :
  (msize (Jm i) <= (p * l.+1))%N.
Proof.
rewrite /Jm msizeN.
apply/(leq_trans (msize_sum _ _ _) _) /bigmax_leqP => j _.
rewrite msizeZ ?a_neq0 // /Sd horner_sum.
apply/(leq_trans (msize_sum _ _ _) _); rewrite big_mkord.
by apply/bigmax_leqP => k _; apply: msize_Fm.
Qed.

Lemma Jm_over i : (Jm i) \is a mpolyOver _ Cint.
Proof.
rewrite rpredN.
apply/rpred_sum => j _; apply/mpolyOverZ => //; apply/rpred_horner/mpolyOverX.
by apply/rpred_sum => k _; apply/polyOver_derivn/Fm_over.
Qed.

Definition Gm i : {poly {mpoly complexR[l.+1]}} := 
   \sum_(0 <= j < p * l) (Fm i)^`N(p)^`(j).

Lemma eq_Gm_sum i : (Gm i) *+ (p`!) = \sum_(p <= j < size (Fm i)) (Fm i)^`(j).
Proof.
rewrite /Gm -mulr_natr big_distrl /= size_Fm mulnS addnC -{4}(add0n p).
rewrite big_addn addnK; apply: eq_bigr => j _.
by rewrite mulr_natr -derivnMn -!nderivn_def addnC derivn_add.
Qed.

Lemma size_Gm i : (size (Gm i) = p * l)%N.
Proof.
have -> : size (Gm i) = size ((Gm i) *+ (p`!)).
  rewrite -scaler_nat size_scale //.  
  by rewrite -mpolyC_nat mpolyC_eq0 pnatr_eq0 -lt0n fact_gt0.
rewrite eq_Gm_sum (_ : \sum_(p <=j< size (Fm i)) (Fm i)^`(j)=(Sd ((Fm i)^`(p)) 0)); last first.
  rewrite /Sd (size_derivn_char _ _ (HcC _)) // size_Fm -{1}[p]add0n big_addn.
  by apply: eq_bigr => j _; rewrite addnC derivn_add.
rewrite size_Sd ?size_derivn_char; [|apply: HcC|apply: HcC]. 
by rewrite size_Fm mulnS -{3}[p]addn0 subnDl subn0.
Qed.

Lemma Gm_over i : Gm i \is a polyOver (mpolyOver _ Cint).
Proof.
by apply/rpred_sum => j _; apply/polyOver_derivn/polyOver_nderivn/Fm_over.
Qed.

Lemma SdFm0_neq i j : 
        (j != i)%N -> (Sd (Fm i) 0).['X_j] = (Gm i).['X_j] *+ p`!. 
Proof. 
move: (mroot_Fm i) => [_ H] Hj; move: (H j Hj)=> {H} /mrootdP H.
rewrite -hornerMn eq_Gm_sum /Sd size_Fm mulnS addnC. 
rewrite (@big_cat_nat _ _ _ p) /= ?hornerD ?horner_sum ?leq0n //; first last. 
  by rewrite -{1}[p]add0n leq_add2r leq0n. 
rewrite (@eq_big_nat _ _ _ _ _ _ (fun i => 0));first by rewrite big1_eq add0r.
move=> k /andP [_ C].
by apply/rootP/(mroot_root _ (H (Ordinal C)));rewrite subn_gt0.
Qed. 

Lemma SdFm0_eq i : 
     (Sd (Fm i) 0).['X_i] = 
             (Fm i)^`N(p.-1).['X_i] *+ (p.-1) `! + (Gm i).['X_i] *+ p`!.
Proof.
move: (mroot_Fm i) => [/mrootdP H _].
rewrite -!hornerMn eq_Gm_sum /Sd /Gm size_Fm mulnS addnC -nderivn_def.
have plpnp : (p <= p * l + p)%N  by rewrite -{1}[p]add0n leq_add2r leq0n.
rewrite (big_cat_nat _ _ _ (leq0n p.-1)) /=; last first.
    by rewrite (leq_trans (leq_pred p)).
rewrite hornerD horner_sum (@eq_big_nat _ _ _ _ _ _ (fun i : nat => 0%R)).
  by rewrite big1_eq add0r big_ltn_cond ?hornerD ?(prednK p_gt0).
move=> j /andP [_ Hpi].
move: (H (Ordinal Hpi)) => {H} /= H.
by move: Hpi; rewrite -subn_gt0 => Hpi; move: (mroot_root Hpi H) => /rootP.
Qed.

Lemma eq_Jm_Sd i :
   Jm i = - ((\sum_(j < l.+1) (a j) *: (Gm i).['X_j]) *+ p`!
          + a i *: (Fm i)^`N(p.-1).['X_i] *+ (p.-1) `!).
Proof.
rewrite /Jm (bigD1 i) //= [in RHS](bigD1 i) //= mulrnDl -[in RHS]addrAC.
congr (-(_ + _)); first by rewrite SdFm0_eq addrC scalerDr !scalerMnr.
rewrite -sumrMnl; apply: eq_bigr => j; move/SdFm0_neq => ->.
by rewrite scalerMnr.
Qed.

Lemma eq_J_Sd i :
   J i = - c ^+ (p * l.+1).-1 * ((\sum_(j < l.+1) (a j) * (Gm i).['X_j].@[alpha]) *+ p`!
          + a i * (Fm i)^`N(p.-1).['X_i].@[alpha] *+ (p.-1) `!).
Proof.
rewrite eq_J_mpoly eq_Jm_Sd mevalN mulrN mulNr mevalD !mevalMn rmorph_sum /=.
congr (- (_ * (_*+ _ + _))); last by rewrite -mevalZ.
by apply/eq_bigr => j _; rewrite -mevalZ.
Qed.



(* **** Link between K and mpoly : Km **** *)

Definition Km := \prod_(i < l.+1) (Jm i).

Lemma eq_K_mpoly : 
  K = c ^+ (\sum_(i < l.+1) (p * l.+1).-1) * Km.@[alpha].
Proof.
rewrite -prodrXr rmorph_prod /= -big_split /=.
by apply: eq_bigr => i _; rewrite eq_J_mpoly.
Qed.



(* **** Km : Properties **** *)

Lemma msize_Km : 
   (msize Km <= (\sum_(i < l.+1) (p * l.+1).-1).+1)%N.
Proof.
apply/(leq_trans (msize_prod _ _) _); rewrite leq_subLR addnS ltnS.
apply/(big_ind3 (fun x y z => (x <= y + z)%N)); first by rewrite addn0.
  move=> x1 x2 x3 y1 y2 y3 H1; move/(leq_add H1).
  by rewrite addnAC -!addnA [(_ + x3)%N]addnC.
by move=> i _; apply/(leq_trans (msize_Jm _)); rewrite add1n leqSpred.
Qed.

Lemma KmZ_over :
  (\prod_(i < l.+1) (p.-1)`!%:R)^-1 *: Km \is a mpolyOver _ Cint.
Proof. 
rewrite -prodfV -scaler_prod.
apply/rpred_prod => i_prod _; rewrite eq_Jm_Sd scalerN /= -scaleN1r.
apply/mpolyOverZ; first rewrite -sub0r; last rewrite scalerDr.
  by apply/rpredB; [apply/Cint0 | apply/Cint1].
apply/rpredD; rewrite -!scaler_nat !scalerA !scaler_nat; last first.
  rewrite mulVf ?mul1r; last by rewrite pnatr_eq0 -lt0n fact_gt0.
  apply/mpolyOverZ => //; apply/rpred_horner; last by rewrite mpolyOverX.
  by apply/polyOver_nderivn/Fm_over.
rewrite -[X in (_ * X`!%:R)](prednK p_gt0) factS natrM mulrCA mulVf ?mul1r.
  apply/mpolyOverZ; first by rewrite mulr1 Cint_Cnat ?Cnat_nat.
  apply/rpred_sum => i_sum _; apply/mpolyOverZ => //.
  by apply/rpred_horner; rewrite ?Gm_over ?mpolyOverX.
by rewrite pnatr_eq0 -lt0n fact_gt0.
Qed.

Lemma Km_msym : 
   {in part, forall Q : {set 'I_l.+1}, Km \is symmetric_for _ Q}.
Proof.
move=> Q Q_in; apply/issym_forP => s s_on.
have := (constantP 0 _ (a_constant Q_in)).
set sa := [seq _ | _ in _]; move => [a_c eq_a_c].
rewrite [RHS](reindex_inj (@perm_inj _ s)) rmorph_prod /=.
apply/eq_bigr => i_prod _. rewrite !eq_Jm_Sd msymN msymD msymMn rmorph_sum /=.
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
  rewrite /Gm !horner_sum rmorph_sum /=.
  apply/eq_bigr => i_der _; rewrite -horner_map /= msymX /=.
  congr (_ .[ _] ); first rewrite -derivn_map -nderivn_map rmorphM /=.
    congr (((_ * _)^`N(_)) ^`(_)); first rewrite rmorphX /=.
      congr (_ ^+ _); rewrite [RHS](reindex_inj (@perm_inj _ s)) rmorph_prod /=.
      apply/eq_bigr => i_last _; rewrite rmorphB /= map_polyX map_polyC /=.
      congr (_ - _%:P); rewrite msymX; congr mpolyX.
      apply/mnmP => j; rewrite mnmE !mnm1E; congr nat_of_bool.
      by apply/eqP/eqP => [-> | <-]; rewrite ?permKV ?permK.
    rewrite rmorph_prod /= [RHS](reindex_inj (@perm_inj _ s)) /=.
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
rewrite msymMn msymZ -horner_map /= msymX -nderivn_map /= rmorphM /=.
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
  rewrite rmorph_prod /= [RHS](reindex_inj (@perm_inj _ s)) /=.
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



(* **** W : Only part not divisible by p **** *)

Definition W : complexR := (c ^+ (\sum_(i < l.+1) (p * l.+1).-1) *:
   \prod_(i < l.+1) (-((p.-1)`!%:R * a i) *: (Fm i)^`N(p.-1).['X_i])).@[alpha].

Definition Wm : {mpoly complexR[l.+1]} :=  
   (\prod_(i < l.+1) (-((p.-1)`!%:R * a i) *: (Fm i)^`N(p.-1).['X_i])).

Lemma eq_W_mpoly :
   W = c ^+ (\sum_(i < l.+1) (p * l.+1).-1) * Wm.@[alpha].
Proof. by rewrite /W /Wm mevalZ. Qed.

Lemma msize_Wm :
  (msize Wm <= (\sum_(i < l.+1) (p * l.+1).-1).+1)%N.
Proof.
apply/(leq_trans (msize_prod _ _)); rewrite leq_subLR addnS ltnS.
apply/(big_ind3 (fun u v w => (u <= v + w)%N)); first by rewrite addn0.
  move=> x1 x2 x3 y1 y2 y3 H1; move/(leq_add H1).
  by rewrite addnAC -!addnA [(_ + x3)%N]addnC.
move=> i _; apply/(leq_trans (msizeZ_le _ _)).
have p_ord : (p.-1 < size (Fm i))%N.
  by rewrite size_Fm mulnS (prednK p_gt0) leq_addr.
have := (msize_Fm (Ordinal p_ord) i); rewrite nderivn_def.
rewrite hornerMn -scaler_nat msizeZ ?pnatr_eq0 -?lt0n ?fact_gt0 //=.
by move/leq_trans; apply; rewrite add1n leqSpred. 
Qed.

Lemma Wm_msym : 
   {in part, forall Q : {set 'I_l.+1}, Wm \is symmetric_for _ Q}.
Proof.
move=> Q Q_in; apply/issym_forP => s s_on.
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
Qed.



(* **** Problems of divisibility **** *)

Lemma K_dvd_f : K / (\prod_(i < l.+1) (p.-1)`!%:R) \is a Cint.
Proof.
rewrite eq_K_mpoly mulrAC -mulrA -mevalZ.
apply: (sym_fundamental_seqroots_for_leq part_partition) => //.
+ by apply/KmZ_over.
+ by move=> Q Q_in; apply/rpredZ/(Km_msym Q_in).
by apply/(leq_trans (msizeZ_le _ _) _)/msize_Km.
Qed.

Lemma KW_dvd_pf : 
  ((K - W) / (p%:R * \prod_(i < l.+1) (p.-1)`!%:R)) \is a Cint.
Proof.
set x := \prod_(_ | _) _.
rewrite eq_K_mpoly eq_W_mpoly -mulrBr -mulrA -mevalB [X in _ * X]mulrC -mevalZ.
apply: (sym_fundamental_seqroots_for_leq part_partition) => //; first last.
+ apply/(leq_trans (msizeZ_le _ _)).
  apply/(leq_trans (msizeD_le _ _)); rewrite msizeN geq_max; apply/andP; split.
    by apply/msize_Km.
  by apply/msize_Wm.
+ by move=> Q Q_in; apply/rpredZ/rpredB/(Wm_msym Q_in)/(Km_msym Q_in).
rewrite invfM -!scalerA scalerBr.
pose P := (fun i (k : bool) => if k
  then (- (p%:R) *: \sum_(j < l.+1) ((a j) *: (Gm i).['X_j]))
  else (- a i *: (Fm i)^`N(p.-1).['X_i])) : 'I_l.+1 -> bool -> {mpoly complexR[l.+1]}.
have -> : x^-1 *: Km = \prod_(i < l.+1) \sum_(j : bool) P i j.
  rewrite -prodfV -scaler_prod.
  apply/eq_bigr=> i_prod _; rewrite eq_Jm_Sd scalerN scalerDr opprD.
  set v := index_enum bool_finType.
  have -> : v = [:: true; false] by rewrite /v /index_enum unlock.
  rewrite big_cons big_seq1 /P /= !scaleNr.
  congr (- _ - _); rewrite -!scaler_nat scalerA !scaler_nat; last first.
    by rewrite mulVf ?scale1r // pnatr_eq0 -lt0n fact_gt0.
  rewrite -[X in _ * X`!%:R](prednK p_gt0) factS natrM mulrCA mulVf; last first.
    by rewrite pnatr_eq0 -lt0n fact_gt0.
  by rewrite (prednK p_gt0) mulr1 scaler_nat.
rewrite bigA_distr_bigA /=. 
pose f_false := finfun (fun _ : 'I_l.+1 => false).
have -> : x^-1 *: Wm  = \prod_(i < l.+1) P i (f_false i).
  rewrite -prodfV -scaler_prod.
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
    by apply/Gm_over.
  by apply/mpolyOverX.
apply/rpred_prod => i _; rewrite /P.
case: ifP => _; apply/mpolyOverZ; rewrite ?rpredN //.
+ by apply/Cint_Cnat/Cnat_nat.
+ apply/rpred_sum => j _; apply/mpolyOverZ=> //; apply/rpred_horner.
    by apply/Gm_over.
  by apply/mpolyOverX.
apply/rpred_horner; last by apply/mpolyOverX.
by apply/polyOver_nderivn/Fm_over.
Qed.


Lemma W_ndvd_pf : 
   (W / (p%:R * \prod_(i < l.+1) (p.-1)`!%:R)) \isn't a Cint.
Proof.
rewrite /W mevalZ.
set x := c ^+ _; rewrite -mulrA [X in x * X]mulrC invfM -mulrA -prodfV.
rewrite rmorph_prod /= -big_split /=.
rewrite (eq_bigr (fun i => (- a i) * ((Fm i)^`N(p.-1)).['X_i].@[alpha])); last first.
  move=> i _; rewrite mevalZ mulrA mulrN mulrA mulVf ?mul1r //.
  by rewrite pnatr_eq0 -lt0n fact_gt0.
rewrite big_split /= prodrN /= cardT size_enum_ord /=.
set A := \prod_(_ | _) _; rewrite mulrCA mulrC !mulrA -mulrA mulrC -!mulrA.
rewrite rpredMsign /=.
set y := \prod_(_ | _) _.
have -> : y = ((\prod_(i < l.+1) \prod_(j < l.+1 | j != i) ('X_i - 'X_j)).@[alpha])^+ p.
  rewrite rmorph_prod -prodrXl.
  apply: eq_bigr => i _; rewrite /Fm (bigD1 i) //= exprMn /T -mulrA -exprSr.
  rewrite (prednK p_gt0).
  set P := (\prod_(_ | _) _).
  have := (derivnMXsubX (P ^+ p) ('X_i) p.-1).
  rewrite nderivn_def hornerMn -[RHS]mulr_natr -mulr_natr.
  move/(mulIf _)=> ->; last first.
    by have := (HcC l); rewrite charf0P => ->; rewrite -lt0n fact_gt0.
  rewrite horner_exp rmorphX /= horner_prod rmorph_prod /=.
  congr (_ ^+ p); rewrite rmorph_prod /=.
  by apply: eq_bigr => j _; rewrite hornerXsubC.
rewrite [X in A * X]mulrCA /x /=.
have Hc_le :(\sum_(i < p) \sum_(j < l.+1) l <= \sum_(i < l.+1) (p * l.+1).-1)%N.
  rewrite !sum_nat_const !cardT !size_enum_ord mulnCA leq_mul2l /=.
  by rewrite mulnS -subn1 addnC -addnBA ?p_gt0 // leq_addr.
rewrite -(subnK Hc_le) exprD -prodrXr prodr_const cardT size_enum_ord -mulrA -exprMn.
move=> {x y}; set x := c ^+ _ * _.@[alpha].
have /CintP [AZ HA] : A \is a Cint by apply/rpred_prod => i _.
have /CintP [cZ Hc] := c_Cint.
have /CintP [xZ Hx] : x \is a Cint.
  apply/(sym_fundamental_seqroots_for_leq part_partition) => //=.
  + apply/rpred_prod => i _; apply/rpred_prod => j _. 
    by apply/rpredB/mpolyOverX/mpolyOverX.
  + move=> Q Q_in; apply/issym_forP => s s_on.
    rewrite [RHS](reindex_inj (@perm_inj _ s)) rmorph_prod /=.
    apply/eq_bigr => i _; rewrite rmorph_prod /=.
    rewrite [RHS](reindex_inj (@perm_inj _ s)) /=.
    apply/congr_big => //= j; first by rewrite (inj_eq (@perm_inj _ s)).
    move=> _; rewrite msymB !msymX.
    congr (mpolyX _ _ - mpolyX _ _); apply/mnmP => k; rewrite mnmE !mnm1E /=.
      by congr nat_of_bool; apply/eqP/eqP => [-> | <-]; rewrite ?permK ?permKV.
    by congr nat_of_bool; apply/eqP/eqP => [-> | <-]; rewrite ?permK ?permKV.
  apply/(leq_trans (msize_prod _ _)); rewrite leq_subLR addnS -big_split ltnS /=.
  apply/leq_sum => i _; apply/(leq_trans (msize_prod _ _)).
  rewrite leq_subLR add1n addnS ltnS.
  have H : (l = \sum_(i0 < l.+1 | i0 != i) 1)%N.  
    have := (cardC (pred1 i)); rewrite card1 => /eqP.
    by rewrite sum1_card cardT size_enum_ord add1n eqSS => /eqP ->.
  rewrite [X in (_ <= _ + X)%N]H -big_split /=.
  apply/leq_sum => j j_neqi; apply/(leq_trans (msizeD_le _ _)).
  by rewrite addn1 geq_max msizeN !msizeX !mdeg1.
set nc := (_ - _)%N.
rewrite mulrC; apply/negP; move/CintP => [m]; rewrite mulrA -[_%:~R]mulr1.
rewrite -[X in _%:~R * X](@mulfV _ p%:R); last by rewrite pnatr_eq0 -lt0n p_gt0.
rewrite [RHS]mulrA.
have : (p%:R != 0 :> complexR) by rewrite pnatr_eq0 -lt0n p_gt0 //.
move/divIf => H; move/H => {H}; rewrite HA Hx Hc -!rmorphX /=.
have -> : (p%:R = p%:~R :> complexR) by [].
move/eqP; rewrite -!intrM eqr_int; move/eqP => H.
have : (p %| AZ * (cZ ^+ nc * xZ ^+ p))%Z by apply/dvdzP; exists m.
rewrite dvdzE absz_nat !abszM !abszX (Euclid_dvdM _ _ p_prime).
apply/negP; rewrite negb_or; apply/andP; split.
  rewrite gtnNdvd //.
    have : A != 0 by rewrite /A; apply/prodf_neq0 => i _.
    by rewrite HA intr_eq0 -absz_eq0 -lt0n.
  have -> : AZ = floorC A by rewrite HA intCK.
  by rewrite /A p_gt_a.
rewrite (Euclid_dvdM _ _ p_prime) !(Euclid_dvdX _ _ p_prime) negb_or !negb_and.
have -> : cZ = floorC c by rewrite Hc intCK.
rewrite gtnNdvd /= ?p_gt_c //; last first.
  by rewrite lt0n absz_eq0 -(intr_eq0 complexR_numDomainType) floorCK.
apply/orP; left.
have -> : xZ = floorC x by rewrite Hx intCK.
have H1 : x  = c ^+ (\sum_(i < l.+1) l) *
       (\prod_(i < l.+1) \prod_(j < l.+1 | j != i) (alpha i - alpha j)).
  congr (_ * _); rewrite rmorph_prod /=.
  apply/eq_bigr => i _; rewrite rmorph_prod /=.
  by apply/eq_bigr => j _; rewrite mevalB !mevalX.
rewrite gtnNdvd //; last by rewrite H1 p_gt_alpha.
rewrite lt0n absz_eq0 -(intr_eq0 complexR_numDomainType) floorCK; last first.
  by apply/CintP; exists xZ.
rewrite /x mulf_neq0 // ?expf_neq0 // rmorph_prod.
apply/prodf_neq0 => i _; rewrite rmorph_prod /=.
apply/prodf_neq0 => j i_neqj; rewrite mevalB !mevalX subr_eq0.
by apply/negP => /eqP /alpha_inj /eqP; apply/negP; rewrite eq_sym.
Qed.

Lemma K_ndvd_pf : (K / (p%:R * \prod_(i < l.+1) (p.-1)`!%:R)) \isn't a Cint.
Proof.
rewrite -[K](addr0) -(subrr W) addrCA mulrDl.
set y := (p%:R * _); apply/negP => HK.
have := W_ndvd_pf; rewrite -/y => HW.
have := KW_dvd_pf; rewrite -/y => HKW.
have := (rpredB HK HKW); rewrite -addrA subrr addr0.
by apply/negP=> /=.
Qed.


(* **** K ge **** *)

Lemma K_ge : `|K| >= ((p.-1)`!%:R ^+ l.+1).
Proof.
rewrite -[X in X <= _]mul1r -ler_pdivl_mulr; last first.
  by apply/exprn_gt0; rewrite ltr0n fact_gt0.
rewrite -normr_nat.
have -> : (`|(p.-1)`!%:R| ^+ l.+1 =`|\prod_(i < l.+1) (p.-1)`!%:R| :> complexR).
  by rewrite -normrX prodr_const cardT size_enum_ord.
rewrite -normrV -?normrM; last first.
  by rewrite unitfE; apply/prodf_neq0 => i _; rewrite pnatr_eq0 -lt0n fact_gt0.
apply/(norm_Cint_ge1 K_dvd_f)/negP => /eqP K_eq0.
by have := K_ndvd_pf; rewrite invfM (mulrA K) mulrAC K_eq0 mul0r Cint0.
Qed.













(* **************** Analysis Part *************** *)


Notation rm_alpha := (meval_rmorphism (fun j => alpha j)).
Local Notation cont_poly := Crcontinuity_pt_poly.
Local Notation cont_exp := Crcontinuity_pt_exp.
Local Notation contM := Crcontinuity_pt_mul.
Local Notation contC := Crcontinuity_pt_const.
Ltac Scont := try repeat 
  apply/cont_poly || 
  apply/cont_exp ||
  apply/contM ||
  apply/contC.

(* TODO : move to ajouts ? not sure ... *)


(* **** from {poly {mpoly _}} to {poly _} **** *) 
Definition MPtoP P : {poly complexR} := 
   map_poly rm_alpha P.

Lemma eq_MPtoP P (x : complexR) : 
   (MPtoP P).[x] = P.[x%:MP].@[alpha].
Proof.
rewrite -(coefK P) poly_def /= horner_sum rmorph_sum /= /MPtoP.
rewrite raddf_sum horner_sum /=.
apply/eq_bigr => j _; rewrite map_polyZ /= map_polyXn !hornerZ !hornerXn mevalM.
by rewrite rmorphX /= mevalC.
Qed.

Lemma eq_MPtoP_X P (j : 'I_l.+1) :
   (MPtoP P).[alpha j] = P.['X_j].@[alpha].
Proof.
rewrite eq_MPtoP !horner_coef !rmorph_sum /=.
by apply/eq_bigr => k _; rewrite !mevalM !rmorphX /= mevalC mevalX.
Qed.

Local Notation "'Fp' i" := (MPtoP (Fm i))
   (at level 4, right associativity).
Local Notation "'SFp' i" := (Sd (Fp i) 0)
   (at level 4, right associativity).

Lemma size_Fp i : size (Fp i) = (p * l.+1)%N.
Proof.
rewrite size_map_poly_id0 ?size_Fm //.
have /monicP -> : (Fm i) \is monic.
  by rewrite rpredM /T ?rpredX ?monic_prod_XsubC.
by rewrite rmorph1 oner_neq0.
Qed.

Lemma eq_SdFp0_x (i : 'I_l.+1) (x : complexR) : 
   (SFp i).[x] = (Sd (Fm i) 0).[x%:MP].@[alpha].
Proof.
rewrite /Sd size_Fp size_Fm !horner_sum rmorph_sum /=.
apply: eq_bigr => j _; rewrite -eq_MPtoP.
by congr (_ .[ _]); rewrite (derivn_map rm_alpha).
Qed.

Lemma eq_SdFp0_X (i j : 'I_l.+1) : 
   (SFp i).[alpha j] = (Sd (Fm i) 0).['X_j].@[alpha].
Proof.
rewrite /Sd size_Fp size_Fm !horner_sum rmorph_sum /=.
apply: eq_bigr => k _; rewrite -eq_MPtoP_X.
by congr (_ .[ _]); rewrite (derivn_map rm_alpha).
Qed.



(* **** Link with the integral of Fp * ...  **** *)

Lemma eq_Fp_SFpDerive x i j :
  alpha j * (Fp i).[x *: alpha j] =
  alpha j * (SFp i).[x *: alpha j] -Crderive (fun y=> (SFp i).[y *: alpha j]) x.
Proof.
rewrite Crderive_poly -mulrBr -hornerN -hornerD.
congr (_ * _.[ _]); rewrite big_endo ?deriv0 //; last by apply/derivD.
rewrite /Sd.
move Hs : (size (Fp i)) => m; case: m Hs => [Hs| m Hs].
  rewrite !big_mkord !big_ord0 subrr.
  by apply/eqP; rewrite -size_poly_eq0; apply/eqP.
rewrite big_nat_recl //.
set S :=  \sum_(0 <= i0 < m) (Fp i)^`(i0.+1); rewrite big_nat_recr //= -derivnS.
have -> : ((Fp i)^`(m.+1)) = 0 by apply/eqP; rewrite -derivn_poly0 Hs.
by rewrite addr0 (@eq_big_nat _ _ _ _ _ _ (fun k => (Fp i)^`(k.+1))) ?addrK.
Qed.

Lemma eq_DeriveSFp x i j :
  Crderive (fun y => - (SFp i).[y *: alpha j] * Cexp(y *: - alpha j)) x =
    alpha j * Cexp(x *: - alpha j) * ((Fp i).[x *: alpha j]).
Proof.
rewrite CrderiveM; last by apply: ex_Crderive_Cexp.
  rewrite CrderiveN; last by apply ex_Crderive_poly.
  rewrite Crderive_Cexp mulrA -mulrDl -mulrA (mulrC (Cexp _)) [RHS]mulrA.
  by rewrite addrC mulrNN eq_Fp_SFpDerive [(_.[_] * alpha _)]mulrC.
by apply/ex_CrderiveN/ex_Crderive_poly.
Qed.

Lemma CrInt_Fp i j :
  CrInt (fun x => alpha j * Cexp(x *: -alpha j) * ((Fp i).[x *: alpha j]))
     0 1 = I i j.
Proof.
set f := (fun x => alpha j * Cexp (x *: - alpha i) * (Fp i).[x *: alpha j]).
rewrite (@CrInt_ext _
         (Crderive (fun y => - (SFp i).[y *: alpha j] * Cexp(y *: - alpha j))));
   last first.
  by move=> x Hx; rewrite eq_DeriveSFp.
rewrite RInt_Crderive.
+ rewrite /I !scale1r !scale0r Cexp0 mulr1 opprK addrC mulNr.
  by rewrite mulrC eq_SdFp0_X eq_SdFp0_x.
+ move=> x _; apply: ex_CrderiveM; last by apply: ex_Crderive_Cexp.
  by apply/ex_CrderiveN/ex_Crderive_poly.
move=> x _; apply: (@Crcontinuity_pt_ext
     (fun x =>(alpha j) * Cexp(x *: -alpha j) * ((Fp i).[x *: (alpha j)]))).
  by move=> y; rewrite eq_DeriveSFp.
by Scont.
Qed.   

Lemma ex_RInt_Fp i j :
  ex_RInt (fun x => alpha j * Cexp(x *: -alpha j)*((Fp i).[x *: alpha j])) 0 1.
Proof. by apply: ex_RInt_cont_C => x H; Scont. Qed.



(* **** Majoration of I i j **** *)

Lemma maj_Ia i j :
  norm (I i j) <=
  RInt (fun x => norm (alpha j * Cexp(x *: -alpha j)*((Fp i).[x *: alpha j])))
     0 1.
Proof.
rewrite -CrInt_Fp.
apply: CrInt_norm; first by apply: ler01. 
by move=> x Hineq; Scont.
Qed.

Lemma maj_Ib i j :
  RInt (fun x => norm (alpha j * Cexp(x *: -alpha j)*((Fp i).[x *: alpha j])))
     0 1 =
  norm (alpha j) *
  RInt (fun x => norm (Cexp(x *: -alpha j)*((Fp i).[x *: alpha j]))) 0 1 .
Proof.
rewrite -Rmult_mul -RInt_scal; apply: RInt_ext=> x Hineq.
by rewrite -mulrA normM Rmult_mul.
Qed.

Lemma maj_Ic i j :
  RInt (fun x => norm (Cexp(x *: -alpha j)*((Fp i).[x *: alpha j])))
     0 1 <=
  RInt (fun x => norm ((RtoC (exp(Rmax 0 (Re_R (-alpha j))))) 
        * ((Fp i).[x *: alpha j]) )) 0 1.
Proof.
apply/RleP; apply: RInt_le; first by apply/RleP/ler01.
    by apply: ex_CrInt_norm => x _; Scont.
  by apply: ex_CrInt_norm => x _; Scont.
move=> x [/RltP H0 /RltP H1].
apply/RleP; rewrite normM [X in _ <= X]normM.
apply: ler_wpmul2r; first by apply/RleP; apply: norm_ge_0.
rewrite /Cexp /norm /= !mul0r !subr0 !addr0 !linearZ /=.
rewrite !exprMn -!mulrDr !add0r mulr0 mul1r subr0 expr0n /= addr0.
set im := Im (- alpha i).
have Htrigo y: (cos y) ^+ 2 + (sin y) ^+ 2 = 1.
  rewrite addrC !exprS !expr0 !mulr1 -Rplus_add -!Rmult_mul; exact: sin2_cos2.
rewrite !Htrigo !mulr1 /= !sqrtr_sqr.
rewrite !gtr0_norm; do? apply/RltP/exp_pos.
have : (Re_R (- alpha j) * x) <= (Rmax 0 (Re_R (- alpha j))).
  move: (num_real (Re_R (-alpha j))); rewrite realE.
  move=> /orP [Hpos| Hneg].
    apply: (@ler_trans _ (Re_R (-alpha j))); last by apply/RleP/Rmax_r.
    rewrite -[X in _<=X]mulr1.
    by apply: ler_wpmul2l=>//; apply: ltrW.
  apply/(@ler_trans _ (Re_R (-alpha j) *0)).
    by apply/ler_wnmul2l=> //; apply/ltrW.
  by rewrite mulr0; apply/RleP/Rmax_l.
rewrite ler_eqVlt => /orP [/eqP Heq | Hlt]; first by rewrite mulrC -Heq lerr.
by apply/ltrW/RltP/exp_increasing/RltP; rewrite mulrC.
Qed.

Lemma maj_Id i j :
  RInt (fun x =>
         norm ((RtoC (exp(Rmax 0 (Re_R (-alpha j))))) *
                (Fp i).[x *: alpha j] : complexR)) 0 1 =
  norm (exp(Rmax 0 (Re_R (-alpha j)))) *
  RInt (fun x => norm ((Fp i).[x *: alpha j])) 0 1.
Proof.
rewrite -Rmult_mul -RInt_scal.
apply: RInt_ext => x Hineq; rewrite Rmult_mul normM.
by congr (_ * _); rewrite /norm /= expr0n addr0 sqrtr_sqr.
Qed.

Lemma maj_Ie i j :
  RInt (fun x => norm ((Fp i).[x *: alpha j])) 0 1 <= 
  (Mal *+ 2) ^+ p.-1 
  * RInt (fun x => norm ((T i)^+ p).[x *: alpha j]) 0 1.
Proof.
(* TODO : maybe this lemma should be moved close to normM. *)
have norm_exp : forall y n, norm (y ^+n : complexR) = (norm y)^+n.
  move=> y; elim => [|m Ihm].
    rewrite !expr0 /=.
    by rewrite /norm /= expr1n expr0n /= addr0 sqrtr1.
  by rewrite !exprS normM Ihm.
rewrite -Rmult_mul -RInt_scal.
apply/RleP; apply: RInt_le; first by apply/RleP; apply: ler01.
    apply: (ex_RInt_ext
     (fun x : R => norm (horner (Fp i) (x *: alpha j)))).
      by move=> x Hineq; rewrite /norm /=.
    by apply: ex_CrInt_norm => x _; Scont.
  apply: (ex_RInt_ext (fun x => norm ((RtoC (Mal *+ 2) ^+ p.-1) *
     ((T i) ^+ p).[x *: alpha j]))).
    move=> x Hineq; rewrite Rmult_mul normM norm_exp. 
    congr (_ ^+ _ * _); rewrite /norm /= expr0n /= addr0 sqrtr_sqr ger0_norm //.
    by rewrite pmulrn_lge0 // max_norm_ge0. 
  by apply: ex_CrInt_norm => x Hineq; Scont.
move=> x [/RltP/ltrW H0 /RltP/ltrW  H1]; apply/RleP; rewrite Rmult_mul.
have -> : (Fp i) = ('X - (alpha i)%:P) ^+ p.-1 * (T i) ^+ p.
  rewrite /MPtoP /T /Fm /= /Tm !rmorphM rmorphX !rmorph_prod /=.
  rewrite (bigD1 i) //= exprMn rmorphB /= map_polyX map_polyC /= mevalX.
  rewrite -mulrA -exprSr /= (prednK p_gt0).
  congr (_ * _ ^+ _); apply: eq_bigr => k _.
  by rewrite rmorphB /= map_polyX map_polyC /= mevalX.
rewrite hornerM normM.
apply/ler_pmul => //; first by apply/RleP/norm_ge_0. 
  by apply/RleP/norm_ge_0.
rewrite horner_exp norm_exp ler_expn2r // ?nnegrE ?hornerXsubC.
+ by apply/RleP/norm_ge_0.
+ by rewrite pmulrn_lge0 // max_norm_ge0.
have : norm (x *: alpha j - alpha i) <= (norm (x *: alpha j) + norm (alpha i)).
  rewrite -[X in _ <= _ + X]norm_opp.
  by apply/RleP/norm_triangle.
move/ler_trans; apply; rewrite mulr2n.
apply/ler_add; last by apply/max_norm_ge.
have /RleP := (norm_scal x (alpha j)); move/ler_trans; apply; rewrite Rmult_mul.
apply/(ler_trans _ (max_norm_ge _ j)); rewrite -[X in _ <= X]mul1r.
apply: ler_wpmul2r; first by apply/RleP/norm_ge_0.
by rewrite /abs /= Rabs_right //; apply/Rle_ge/RleP.
Qed.

Lemma maj_If i j M :
  (forall x, 0 <= x <= 1 -> norm (T i).[x *: alpha j] <= M) ->
  RInt (fun x => norm ((T i)^+ p).[x *: alpha j]) 0 1 <= M ^+ p.
Proof.
rewrite -(prednK p_gt0) //; set m := p.-1.
have HM: M = RInt (fun y => M) 0 1.
  rewrite RInt_const Rmult_mul /Rminus Ropp_opp Rplus_add.
  by rewrite subr0 mul1r.
move=> Hineq; elim: m => [| m Ihm].
  rewrite !expr1 HM.
  apply/RleP/RInt_le; first by apply/RleP/ler01.
      by apply: ex_CrInt_norm => x Hine; Scont.
    apply: ex_RInt_const.
  by move=> x [/RltP/ltrW H0 /RltP/ltrW H1]; apply/RleP/Hineq/andP.
rewrite exprS [X in _<=X]exprS.
apply: (@ler_trans _
           (M * (RInt (fun x : R => norm ((T i) ^+ m.+1).[x *: alpha j]) 0 1))).
  rewrite -Rmult_mul -RInt_scal; apply/RleP/RInt_le;first by apply/RleP/ler01.
      by apply: ex_CrInt_norm => x Hine; Scont.
    apply/ex_RInt_scal/ex_CrInt_norm => x Hine; Scont.
  move=> x [/RltP/ltrW H0 /RltP/ltrW H1]; rewrite hornerM normM !Rmult_mul.
  by apply/RleP/ler_wpmul2r/Hineq/andP; first apply/RleP/norm_ge_0.
apply/ler_wpmul2l/Ihm/(ler_trans _ (Hineq 0 _)); last by rewrite lerr ler01.
by apply/RleP/norm_ge_0.
Qed.

Lemma maj_I i j :
  norm (I i j) <= Mal * (Me * (Mm * (Mal *+ 2 * Mm)^+p.-1)) .
Proof.
apply/(ler_trans (maj_Ia i j)); rewrite maj_Ib.
(* TODO : this is probably general enough to be in the main library. *) 
have hnorm : forall (V : NormedModule R_AbsRing) (x : V), `|norm x| = norm x.
  by move=> V x; apply/normr_idP/RleP/norm_ge_0.
set x1 := _ * (_ * _ ^+ _).
apply/(ler_trans _ (@ler_wpmul2r _ x1 _ (norm (alpha j)) _ _)); last first.
    by apply/max_norm_ge.
  rewrite /x1; apply: mulr_ge0; first by apply: max_norm_ge0.
  apply/mulr_ge0/exprn_ge0/mulr_ge0; do ? apply/max_norm_ge0.
  by apply/mulrn_wge0/max_norm_ge0.
rewrite ![norm _ * _]mulrC.
apply: ler_wpmul2r; first by apply/RleP/norm_ge_0.
apply: (ler_trans (maj_Ic i j)); rewrite maj_Id /x1. 
apply: (ler_trans (@ler_wpmul2l _ (norm _) _ _ _ _) (ler_wpmul2r _ _)).
+ by apply/RleP/norm_ge_0.
+ apply/(ler_trans (maj_Ie i j)).
  rewrite exprMn mulrCA ![(_ *+ _) ^+ p.-1 * _]mulrC.
  apply/ler_wpmul2r; first by apply/exprn_ge0/mulrn_wge0/max_norm_ge0.
  rewrite -exprS (prednK p_gt0) //.
  apply: maj_If => x Hx.
  have := ((svalP (ex_M_T i j)) x Hx); rewrite /Mm.
  move/ltrW/ler_trans; apply; apply/(ler_trans (real_ler_norm (num_real _))).
  apply/(ler_trans (max_norm_ge (fun k => Mt i k) j)).
  apply/(ler_trans _ (max_norm_ge (fun k => max_norm (fun k' => Mt k k')) i)).
  by apply/real_ler_norm/num_real.
+ apply/mulr_ge0; first by apply/max_norm_ge0.
  apply/exprn_ge0/mulr_ge0; last by apply/max_norm_ge0.
  by apply/mulrn_wge0/max_norm_ge0.
by apply/max_norm_ge.
Qed.




(* **** Majoration of J i **** *)

Lemma maj_pre_J i j :
  norm (c ^+ (p * l.+1).-1 * (a j) * Cexp (alpha j) * I i j) <=
    (MJi1 * MJip ^ p.-1)%:R.
Proof.
have norm_exp : forall y n, norm (y ^+n : complexR) = (norm y)^+n.
  move=> y; elim => [|m Ihm]; last by rewrite !exprS normM Ihm.
  by rewrite !expr0 /= /norm /= expr1n expr0n /= addr0 sqrtr1.
apply/(@ler_trans _ ((Ma * Mal * exp Mal * Me * (norm c)^+ l.+1 * Mm) *
    ((norm c) ^+ l.+1 * (Mal *+ 2) * Mm)^+p.-1)); first last.
  set Ar := _ * Mm; set Br := _ * Mm; rewrite natrM natrX.
  have HA : 0 <= Ar.
    apply/mulr_ge0/max_norm_ge0/mulr_ge0/exprn_ge0/RleP/norm_ge_0.
    apply/mulr_ge0/max_norm_ge0/mulr_ge0.
      by apply/mulr_ge0/max_norm_ge0/max_norm_ge0.
    by apply/ltrW/RltP/exp_pos.
  have HB : 0 <= Br.
    apply/mulr_ge0/max_norm_ge0/mulr_ge0/mulrn_wge0/max_norm_ge0.
    by apply/exprn_ge0/RleP/norm_ge_0.
  apply/(ler_pmul HA); first by apply/exprn_ge0/HB.
    apply/ltrW/archi_boundP/HA.
  apply/ler_expn2r; rewrite ?nnegrE ?HB ?ler0n //.
  by apply/ltrW/archi_boundP/HB.
do 3 rewrite normM; set xi := norm _; set xs1 := norm _ ^+ _.
rewrite !(mulrAC _ _ xs1) (mulrC _ xs1) -(mulrA xs1) exprMn.
rewrite !(mulrCA _ (xs1 ^+ _)) !mulrA; set xs := _ * xs1.
have Hx : xi <= xs.
  rewrite /xi /xs /xs1 -exprSr -exprM norm_exp prednK //.
  rewrite -(@prednK (l.+1 * p)%N); last by rewrite muln_gt0 /= p_gt0.
  rewrite mulnC exprS ler_pmull; last apply/exprn_gt0/(@ltr_le_trans _ 1) => //.
    rewrite -ler_RtoC [X in X <= _]RtoCE.
    by have := (norm_Cint_ge1 c_Cint c_neq0); rewrite /Num.norm /= /norm /=.
  rewrite -ler_RtoC [X in X <= _]RtoCE.
  by have := (norm_Cint_ge1 c_Cint c_neq0); rewrite /Num.norm /= /norm /=.
set yi := norm _; set ys := Ma.
have Hy : yi <= ys by rewrite /yi /ys; apply: max_norm_ge.
set zi := norm _; set zs := exp _; rewrite (mulrAC _ Mal zs).
have Hz : zi <= zs.
  rewrite /zi /zs /Mal /Cexp /norm /= !mul0r !mul1r !subr0 !addr0 !add0r.
  rewrite !exprMn -mulrDr sqrtrM ?sqrtr_sqr; last first.
    by rewrite exprn_ge0 //; apply/ltrW/RltP/exp_pos.
  set u := complex.Im _.
  have := (sin2_cos2 u); rewrite /Rsqr !Rmult_mul !Rplus_add addrC => -> /=.
  rewrite sqrtr1 mulr1 ger0_norm; last by apply/ltrW/RltP/exp_pos.
  have H1 : (Re_R (alpha j) <= norm (alpha j)).
    move: (alpha j) => [vr vi] /=; rewrite /norm /=.
    apply: (@ler_trans _ `|vr|); first by apply: ler_norm.
    by rewrite -sqrtr_sqr; apply: ler_wsqrtr; rewrite ler_addl sqr_ge0.
  have := (max_norm_ge alpha j).
  move/(ler_trans H1); rewrite ler_eqVlt => /orP[/eqP -> // | /RltP ].
  by move/exp_increasing/RltP/ltrW.
rewrite -!mulrA (mulrA _ xs1) -/xs; set u := Mal * _.
apply/(ler_pmul _ _ Hx); first by apply/RleP/norm_ge_0.
  apply/mulr_ge0; first by apply/RleP/norm_ge_0.
  by apply/mulr_ge0; apply/RleP/norm_ge_0.
apply/(ler_pmul _ _ Hy); first by apply/RleP/norm_ge_0.
  by apply/mulr_ge0; apply/RleP/norm_ge_0.
apply/(ler_pmul _ _ Hz); first by apply/RleP/norm_ge_0.
  by apply/RleP/norm_ge_0.
by apply: maj_I.
Qed.

Lemma maj_J i :
  norm (J i) < (p.-1)`!%:R.
Proof.
rewrite /J big_distrr /=.
move: majoration; rewrite -(ltr_nat R_numDomainType) /MJi -mulnA natrM.
move/(ler_lt_trans _); apply; rewrite mulr_natl.
have -> : ((MJi1 * MJip ^ p.-1)%:R *+ l.+1 : R) = 
       \sum_(j < l.+1) (MJi1 * MJip ^p.-1)%:R.
  by rewrite sumr_const cardT size_enum_ord.
apply: (big_ind2 (fun x y => norm x <= y)).
+ by rewrite norm_zero.
+ move=> x1 y1 x2 y2 H1 H2.
  by have /RleP := (norm_triangle x1 x2); move/ler_trans; apply; apply/ler_add.
move=> j _; rewrite mulrA mulrA.
by apply: maj_pre_J.
Qed.


(* **** K lt **** *)

Lemma K_lt :
 `|K| < ((p.-1)`!%:R ^+ l.+1).
Proof.
have : norm K < ((p.-1)`!%:R ^+ l.+1).
  rewrite /K /= big_ord_recl /= normM exprS.
  set u := norm _; set v := norm _; set P := _ %:R.
  apply/(@ler_lt_trans _ (u * P^+ l)); last first.
    rewrite ltr_pmul2r; first by apply/maj_J.
    by apply/exprn_gt0; rewrite ltr0n fact_gt0.
  apply/ler_wpmul2l; first by apply/RleP/norm_ge_0.
  have -> : (P ^+ l : R) = \prod_(j < l) P.
    by rewrite prodr_const cardT size_enum_ord.
  apply: (big_ind2 (fun x y => norm x <= y)) => //.
      by rewrite /norm /= expr0n /= addr0 expr1n sqrtr1.
    move=> x1 x2 y1 y2 Hx Hy; rewrite normM.
    by apply/ler_pmul => //; apply/RleP/norm_ge_0.
  by move=> i _; apply/ltrW/maj_J.
rewrite -ltr_RtoC /Num.norm /= /norm /=.
by move/ltr_le_trans; apply; rewrite -!RtoCE.
Qed.

End Lindemann_last.



(***************** Last step of the Lindemann theorem **************)


Lemma Lindemann_last l c (alpha : complexR ^ l.+1) (part : {set {set 'I_l.+1}}) 
  (a : complexR ^ l.+1) :
  c != 0 -> 
  c \is a Cint -> 
  injective alpha -> 
  partition part [set: 'I_l.+1] -> 
  {in part, forall P : {set 'I_l.+1},
       [fset (alpha i) | i in P]%fset \is a setZroots c} ->
  (forall i : 'I_l.+1, a i != 0) -> 
  (forall i : 'I_l.+1, a i \is a Cint) ->
  {in part, forall P : {set 'I_l.+1}, constant [seq a i | i in P]} -> 
  Cexp_span a alpha != 0.
Proof.
move=> c_neq0 c_Cint alpha_inj part_partition alpha_setZroots.
move=> a_neq0 a_Cint a_constant; apply/negP => Lindemann_false.
have := (K_ge c_neq0 c_Cint alpha_inj part_partition alpha_setZroots a_neq0 
     a_Cint a_constant Lindemann_false).
by move/(ltr_le_trans (K_lt alpha a c_neq0 c_Cint)); rewrite ltrr.
Qed.

(* Print Assumptions Lindemann_last. *)

(* TODO : constant_on ou card[set a i ] <= 1 *)



