Require Import Reals.
From coquelicot
Require Import Hierarchy RInt.
From mathcomp Require Import all_ssreflect.
From mathcomp
Require Import ssralg ssrnum mxpoly rat poly ssrint polyorder polydiv perm.
From mathcomp
Require Import finfun intdiv.
From structs
Require Import Canalysis Cstruct Rstruct.
From SsrMultinomials
Require Import finmap order mpoly.
From Lind
Require Import ajouts.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.
Import GRing.Theory Num.Theory ArchimedeanTheory Cstruct.ComplexTotalOrder.

Local Notation RtoC := (structs.Cstruct.RtoC : R -> complexR).
Local Notation Cnat := Cstruct.Cnat.
Local Notation Cint := Cstruct.Cint.

Notation "x 'is_algebraic'" := (algebraicOver QtoC x)
  (at level 55).

Local Notation setZroots := ((set_roots Cint) : 
    complexR -> qualifier 1 {fset complexR}).

Section Wlog3.

Variable l : nat.
Variable c : complexR.
Variable alpha : complexR ^ l.+1.
Variable part : {set {set 'I_l.+1}}.
Variable a : complexR ^ l.+1.

Lemma HcC :
  [char mpoly_idomainType l.+1 complexR_idomainType] =i pred0.
Proof. by move=> x; rewrite char_lalg char_num. Qed.

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


Definition T_an (i : 'I_l.+1) : {poly complexR} :=
  \prod_(j < l.+1 | j != i) ('X - (alpha j)%:P).

(**** * Variables to choose the prime number p **** *)

Lemma ex_Mc i j :
 {M : R | forall x : R, 0 <= x <= 1 -> norm (T_an i).[x *: alpha j] < M}.
Proof.
move: (Continuity.bounded_continuity
          (fun y => ((T_an i).[y *: (alpha j)])) 0 1) => H.
have : forall x : R,
       and (Rle 0 x) (Rle x 1) ->
       filterlim (fun y : R => (T_an i).[y *: alpha j]) (locally x)
           (locally (T_an i).[x *: alpha j]).
  move=> x [/RleP H0 /RleP H1].
  apply: Crcontinuity_pt_filterlim.
  apply: (@Crcontinuity_pt_ext (fun y => ((T_an i) \Po ((alpha j) *: 'X )).[RtoC y]) ).
    by move=> z; rewrite horner_comp hornerZ hornerX Cr_scalE mulrC.
  by apply: Crcontinuity_pt_poly.
move=> Hb; move: (H Hb) => [M M_H].
by exists M; move=> x /andP[H0 H1]; apply/RltP; apply: M_H; split; apply/RleP.
Qed.

Definition M i j := sval (ex_Mc i j).

(* TODO : move to ajouts *)
Definition max_norm (K : AbsRing) (V : NormedModule K) (f : 'I_l.+1 -> V) := 
  bmaxrf (finfun (fun (i : 'I_l.+1)  => norm (f i))).

Lemma max_norm_ge (K : AbsRing) (V : NormedModule K) (f : 'I_l.+1 -> V) i : 
  norm (f i) <= (max_norm f).
Proof.
rewrite /max_norm; set g := finfun _.
by have := (bmaxrf_ler g i); rewrite /g ffunE.
Qed.

Lemma max_norm_ge0 (K : AbsRing) (V : NormedModule K) (f : 'I_l.+1 -> V) : 
  0 <= max_norm f.
Proof. by apply/(ler_trans _ (max_norm_ge f ord0))/RleP/norm_ge_0. Qed.

(* majoration de chaque partie *)
Definition Ma := max_norm alpha.

Definition Mb := max_norm a. 

Definition Me := max_norm (fun i => exp (Rmax 0 (Re_R (-alpha i)))).

Definition Mm := max_norm (fun i => max_norm (fun j => M i j)).


(* majoration d'un terme de Jip *)
Definition A := Num.bound (Mb * Ma * exp Ma * Me * (norm c) ^+ l.+1 * Mm).

Definition Bn := Num.bound ((norm c) ^+ l.+1 * (Ma *+ 2) * Mm).

Open Scope nat_scope.

(* majoration de Jip *)
Definition An := l.+1 * A.

Lemma p_prop2 :
  exists p : nat, prime p && (An * Bn ^ p.-1 < (p.-1)`!) && (p > `|floorC c|) &&
      (p >  `|floorC (\prod_(i < l.+1) a i)|) && (p > `|floorC (c ^+ (\sum_(i < l.+1) l) *
           \prod_(i < l.+1) \prod_(j < l.+1 | j != i) (alpha i - alpha j))|).
Proof.
destruct (p_prop1 An Bn) as [q Pq].
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

Lemma majoration : An * Bn ^ p.-1 < (p.-1)`!.
Proof. by move:(xchooseP p_prop2) => /andP [/andP [/andP [/andP [H ->]]]]. Qed.

Open Scope ring_scope.



(* **************** Algebraic Part *************** *)

Definition T (i : 'I_l.+1) : {poly {mpoly complexR[l.+1]}} :=
  \prod_(j < l.+1 | j != i) ('X - ('X_j)%:P).

Lemma size_T i : size (T i) = l.+1.
Proof.
rewrite /T -big_filter size_prod_XsubC -rem_filter.
  by rewrite size_rem // /index_enum -enumT size_enum_ord prednK.
by rewrite /index_enum -enumT enum_uniq.
Qed.

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

Definition I i j :=  
   (Sd (F i) 0).[0].@[alpha] - Cexp (- alpha j) * (Sd (F i) 0).['X_j].@[alpha].

Definition Ji i := \sum_(j < l.+1) (a j) * Cexp (alpha j) * (I i j).

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
  move=> j _; rewrite mulrBr mulrA.
  by congr (_ - (_ * _)); rewrite -mulrA CexpRD subrr Cexp0 mulr1.
rewrite big_split /= -big_distrl /=.
move/eqP : Lindemann_false; rewrite /Cexp_span => ->; rewrite mul0r add0r.
rewrite -(big_endo _ (@opprD _) (oppr0 _)) mevalN rmorph_sum /=.
by congr (- _); apply: eq_bigr => j _; rewrite mevalZ.
Qed.

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

Definition J := c ^+ (\sum_(i < l.+1) (p * l.+1).-1) * \prod_(i < l.+1) Ji i.

Lemma eq_J_mpoly : J = c ^+ (\sum_(i < l.+1) (p * l.+1).-1) * (\prod_(i < l.+1) (Jip i)).@[alpha].
Proof.
rewrite /J; congr (_ * _); rewrite rmorph_prod /=.
by apply: eq_bigr => i _; rewrite Eq_Ji.
Qed.

Lemma J_msize : 
   (msize (\prod_(i < l.+1) (Jip i)) <= (\sum_(i < l.+1) (p * l.+1).-1).+1)%N.
Proof.
apply/(leq_trans (msize_prod _ _) _); rewrite leq_subLR addnS ltnS.
apply/(big_ind3 (fun x y z => (x <= y + z)%N)); first by rewrite addn0.
  move=> x1 x2 x3 y1 y2 y3 H1; move/(leq_add H1).
  by rewrite addnAC -!addnA [(_ + x3)%N]addnC.
by move=> i _; apply/(leq_trans (msize_Jip _)); rewrite add1n leqSpred.
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


Lemma J_divp1 : J / (\prod_(i < l.+1) (p.-1)`!%:R) \is a Cint.
Proof.
rewrite eq_J_mpoly mulrAC -mulrA -mevalZ.
apply: (sym_fundamental_seqroots_for_leq part_partition) => //.
+ rewrite -prodfV -scaler_prod.
  apply/rpred_prod => i_prod _; rewrite Eq_JGip scalerN /= -scaleN1r.
  apply/mpolyOverZ; first rewrite -sub0r; last rewrite scalerDr.
    by apply/rpredB; [apply/Cint0 | apply/Cint1].
  apply/rpredD; rewrite -!scaler_nat !scalerA !scaler_nat; last first.
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
  ((J - c ^+ (\sum_(i < l.+1) (p * l.+1).-1) * (\prod_(i < l.+1) (- ((p.-1)`!%:R * a i) *: 
     (F i)^`N(p.-1).['X_i])).@[alpha]) / (p%:R * \prod_(i < l.+1) (p.-1)`!%:R)) \is a Cint.
Proof.
set x := \prod_(_ | _) _; set y := _ * x.@[alpha].
rewrite mulrDl mulNr eq_J_mpoly mulrAC -mulrA -mevalZ /y -mulrA -mulrBr.
rewrite [X in _ - X]mulrC -mevalZ -mevalB.
apply: (sym_fundamental_seqroots_for_leq part_partition) => //; first last.
+ apply/(leq_trans (msizeD_le _ _)); rewrite msizeN geq_max; apply/andP; split.
    by apply/(leq_trans (msizeZ_le _ _))/J_msize.
  apply/(leq_trans (msizeZ_le _ _))/(leq_trans (msize_prod _ _)).
  rewrite leq_subLR addnS ltnS.
  apply/(big_ind3 (fun u v w => (u <= v + w)%N)); first by rewrite addn0.
    move=> x1 x2 x3 y1 y2 y3 H1; move/(leq_add H1).
    by rewrite addnAC -!addnA [(_ + x3)%N]addnC.
  move=> i _; apply/(leq_trans (msizeZ_le _ _)).
  have p_ord : (p.-1 < size (F i))%N.
    by rewrite size_F mulnS (prednK p_gt0) leq_addr.
  have := (F_msize (Ordinal p_ord) i); rewrite nderivn_def.
  rewrite hornerMn -scaler_nat msizeZ ?pnatr_eq0 -?lt0n ?fact_gt0 //=.
  by move/leq_trans; apply; rewrite add1n leqSpred. 
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
  congr (- _ - _); rewrite -!scaler_nat scalerA !scaler_nat; last first.
    by rewrite mulVf ?scale1r // pnatr_eq0 -lt0n fact_gt0.
  rewrite -[X in _ * X`!%:R](prednK p_gt0) factS natrM mulrCA mulVf; last first.
    by rewrite pnatr_eq0 -lt0n fact_gt0.
  by rewrite (prednK p_gt0) mulr1 scaler_nat.
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
   (((c ^+ (\sum_(i < l.+1) ((p * l.+1).-1)) * 
     (\prod_(i < l.+1) (- ((p.-1)`!%:R * a i) *: 
     (F i)^`N(p.-1).['X_i])).@[alpha]) / (p%:R * \prod_(i < l.+1) (p.-1)`!%:R)) 
       \isn't a Cint).
Proof.
set x := c ^+ _; rewrite -mulrA [X in x * X]mulrC invfM -mulrA -prodfV.
rewrite rmorph_prod /= -big_split /=.
rewrite (eq_bigr (fun i => (- a i) * ((F i)^`N(p.-1)).['X_i].@[alpha])); last first.
  move=> i _; rewrite mevalZ mulrA mulrN mulrA mulVf ?mul1r //.
  by rewrite pnatr_eq0 -lt0n fact_gt0.
rewrite big_split /= prodrN /= cardT size_enum_ord /=.
set A := \prod_(_ | _) _; rewrite mulrCA mulrC !mulrA -mulrA mulrC -!mulrA.
rewrite rpredMsign /=.
set y := \prod_(_ | _) _.
have -> : y = ((\prod_(i < l.+1) \prod_(j < l.+1 | j != i) ('X_i - 'X_j)).@[alpha])^+ p.
  rewrite rmorph_prod -prodrXl.
  apply: eq_bigr => i _; rewrite /F (bigD1 i) //= exprMn /T -mulrA -exprSr.
  rewrite (prednK p_gt0).
  set P := (\prod_(_ | _) _).
  have := (derivnMXsubX (P ^+ p) ('X_i) p.-1).
  rewrite nderivn_def hornerMn -[RHS]mulr_natr -mulr_natr.
  move/(mulIf _)=> ->; last first.
    by have := HcC; rewrite charf0P => ->; rewrite -lt0n fact_gt0.
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

Lemma J_ndivp : ((J / (p%:R * \prod_(i < l.+1) (p.-1)`!%:R)) \isn't a Cint).
Proof.
pose x :=  c ^+ (\sum_(i < l.+1) (p * l.+1).-1) * (\prod_(i < l.+1) (- ((p.-1)`!%:R * a i) *: 
     (F i)^`N(p.-1).['X_i])).@[alpha].
rewrite -[J](addr0) -(subrr x) addrCA mulrDl.
set y := (p%:R * _); apply/negP => HD.
have := JC_ndivp; rewrite -/x -/y => HX.
have := JB_divp; rewrite -/x -/y => HC.
have := (rpredB HD HC); rewrite -addrA subrr addr0.
by apply/negP=> /=.
Qed.


Lemma J_ge : `|J| >= ((p.-1)`!%:R ^+ l.+1).
Proof.
rewrite -[X in X <= _]mul1r -ler_pdivl_mulr; last first.
  by apply/exprn_gt0; rewrite ltr0n fact_gt0.
rewrite -normr_nat.
have -> : (`|(p.-1)`!%:R| ^+ l.+1 =`|\prod_(i < l.+1) (p.-1)`!%:R| :> complexR).
  by rewrite -normrX prodr_const cardT size_enum_ord.
rewrite -normrV -?normrM; last first.
  by rewrite unitfE; apply/prodf_neq0 => i _; rewrite pnatr_eq0 -lt0n fact_gt0.
apply/(norm_Cint_ge1 J_divp1)/negP => /eqP J_eq0.
by have := J_ndivp; rewrite invfM (mulrA J) mulrAC J_eq0 mul0r Cint0.
Qed.



(* **************** Analysis Part *************** *)

Definition MPtoP P : {poly complexR} := 
   map_poly (fun Q => Q.@[alpha]) P.

Notation rm_alpha := (meval_rmorphism (fun j => alpha j)).

Lemma eq_MPtoP P (x : complexR) : 
   (MPtoP P).[x] = P.[x%:MP].@[alpha].
Proof.
rewrite -(coefK P) poly_def /= horner_sum rmorph_sum /= /MPtoP.
rewrite (raddf_sum (map_poly_additive rm_alpha)) horner_sum /=.
apply/eq_bigr => j _; rewrite map_polyZ /= map_polyXn !hornerZ !hornerXn mevalM.
by rewrite rmorphX /= mevalC.
Qed.

Lemma eq_MPtoP_X P (j : 'I_l.+1) :
   (MPtoP P).[alpha j] = P.['X_j].@[alpha].
Proof.
rewrite eq_MPtoP !horner_coef !rmorph_sum /=.
by apply/eq_bigr => k _; rewrite !mevalM !rmorphX /= mevalC mevalX.
Qed.

Local Notation "'Fp' i" := (MPtoP (F i))
   (at level 4, right associativity).

Lemma size_Fp i : size (Fp i) = (p * l.+1)%N.
Proof.
rewrite size_map_poly_id0 ?size_F //.
have /monicP -> : (F i) \is monic.
  by rewrite /F rpredM /T ?rpredX ?monic_prod_XsubC.
by rewrite meval1 oner_neq0.
Qed.

Lemma eq_Sd_Fp_F_x (i : 'I_l.+1) (x : complexR) : 
   (Sd (Fp i) 0).[x] = (Sd (F i) 0).[x%:MP].@[alpha].
Proof.
rewrite /Sd size_Fp size_F !horner_sum rmorph_sum /=.
apply: eq_bigr => j _; rewrite -eq_MPtoP.
by congr (_ .[ _]); rewrite (derivn_map rm_alpha).
Qed.

Lemma eq_Sd_Fp_F_X (i j : 'I_l.+1) : 
   (Sd (Fp i) 0).[alpha j] = (Sd (F i) 0).['X_j].@[alpha].
Proof.
rewrite /Sd size_Fp size_F !horner_sum rmorph_sum /=.
apply: eq_bigr => k _; rewrite -eq_MPtoP_X.
by congr (_ .[ _]); rewrite (derivn_map rm_alpha).
Qed.

Let contFpalpha (i j : 'I_l.+1) x : 
   Crcontinuity_pt (fun y => (Fp i).[y *: alpha j]) x.
Proof.
apply: (@Crcontinuity_pt_ext (fun y => ((Fp i) \Po (alpha j *: 'X)).[RtoC y])).
  by move=> y; rewrite horner_comp hornerZ hornerX Cr_scalE mulrC.
by apply Crcontinuity_pt_poly.
Qed.

Definition Qdalpha (i j : 'I_l.+1) := (Sd (Fp i) 0) \Po ((alpha j) *: 'X).

Lemma Qdalpha_Fpd i j x : (Sd (Fp i) 0).[x *: alpha j] = (Qdalpha i j).[RtoC x].
Proof.
by rewrite /Qdalpha horner_comp hornerZ hornerX Cr_scalE mulrC.
Qed.

Lemma Qderiv_derive x i j :
  alpha j * (Qdalpha i j).[RtoC x] - Crderive (fun y => (Qdalpha i j).[RtoC y]) 
    x = alpha j * (Fp i).[x *: (alpha j)].
Proof.
rewrite Crderive_poly /Qdalpha deriv_comp horner_comp hornerM.
rewrite horner_comp derivZ derivX alg_polyC hornerC mulrC.
rewrite hornerZ hornerX -mulrBr -hornerN -hornerD Cr_scalE [_ * alpha _]mulrC.
have: (Sd (Fp i) 0 - (Sd (Fp i) 0)^`() = Fp i) => [|-> //].
rewrite big_endo; first last.
    by rewrite deriv0.
  by apply: derivD.
rewrite /Sd.
move Hs : (size (Fp i)) => m; case: m Hs => [Hs| m Hs].
  rewrite !big_mkord !big_ord0 subrr.
  by apply/eqP; rewrite eq_sym; rewrite -size_poly_eq0; apply/eqP.
rewrite big_nat_recl //.
set S :=  \sum_(0 <= i0 < m) (Fp i)^`(i0.+1).
rewrite big_nat_recr //= -derivnS.
have: ((Fp i)^`(m.+1)) = 0 => [|->].
  by apply/eqP; rewrite -derivn_poly0 Hs.
rewrite addr0 (@eq_big_nat _ _ _ _ _ _ (fun k => (Fp i)^`(k.+1))).
  by rewrite /S addrK.
by move=> k Hineq; rewrite derivnS.
Qed.

Lemma Fp_Crderive x i j :
  Crderive (fun y => - (Qdalpha i j).[RtoC y] * Cexp(y *: - alpha j)) x =
    alpha j * Cexp(x *: - alpha j) * ((Fp i).[x *: alpha j]).
Proof.
rewrite CrderiveM; last by apply: ex_Crderive_Cexp.
  rewrite CrderiveN; last by apply ex_Crderive_poly.
  rewrite Crderive_Cexp mulrA -mulrDl -mulrA (mulrC (Cexp _)) [RHS]mulrA.
  by rewrite addrC mulrNN -Qderiv_derive [(_.[_] * alpha _)]mulrC.
by apply/ex_CrderiveN/ex_Crderive_poly.
Qed.

Lemma CrInt_Fp i j :
  CrInt (fun x => alpha j * Cexp(x *: -alpha j) * ((Fp i).[x *: alpha j]))
     0 1 = I i j.
Proof.
set f := (fun x => alpha j * Cexp (x *: - alpha i) * (Fp i).[x *: alpha j]).
rewrite (@CrInt_ext _
           (Crderive (fun y => - (Qdalpha i j).[RtoC y] * Cexp(y *: -alpha j))));
   last first.
  by move=> x Hx; rewrite Fp_Crderive.
rewrite RInt_Crderive.
+ rewrite /I -!Qdalpha_Fpd !scale1r !scale0r Cexp0 mulr1 opprK addrC mulNr.
  by rewrite mulrC eq_Sd_Fp_F_X eq_Sd_Fp_F_x.
+ move=> x _; apply: ex_CrderiveM; last by apply: ex_Crderive_Cexp.
  by apply/ex_CrderiveN/ex_Crderive_poly.
move=> x _.
apply: (@Crcontinuity_pt_ext
     (fun x =>(alpha j) * Cexp(x *: -alpha j) * ((Fp i).[x *: (alpha j)]))).
  by move=> y; rewrite -Fp_Crderive Crderive_C_eq.
apply: Crcontinuity_pt_mul; last by [].
apply: Crcontinuity_pt_mul.
  by apply: Crcontinuity_pt_const.
by apply: Crcontinuity_pt_exp.
Qed.   

Lemma ex_RInt_Fp i j :
  ex_RInt (fun x => alpha j * Cexp(x *: -alpha j)*((Fp i).[x *: alpha j])) 0 1.
Proof.
apply: ex_RInt_cont_C => x H.
apply: Crcontinuity_pt_mul; last by [].
apply: Crcontinuity_pt_mul; first by apply: Crcontinuity_pt_const.
by apply: Crcontinuity_pt_exp.
Qed.

Lemma maj_IFpa i j :
  norm (I i j) <=
  RInt (fun x => norm (alpha j * Cexp(x *: -alpha j)*((Fp i).[x *: alpha j])))
     0 1.
Proof.
rewrite -CrInt_Fp.
apply: CrInt_norm; first by apply: ler01.
move=> x Hineq; apply: Crcontinuity_pt_mul => //; apply: Crcontinuity_pt_mul.
  by apply: Crcontinuity_pt_const.
by apply: Crcontinuity_pt_exp.
Qed.

Lemma normM (x y : complexR) :
  norm x * norm y = norm (x * y).
Proof.
by rewrite /norm /= complex.ComplexField.normcM.
Qed.

Lemma norm_morph : {morph (norm : complexR -> R) : x y / x * y >-> x * y}.
Proof. by move=> x y; rewrite normM. Qed.

Lemma maj_IFpb i j :
  RInt (fun x => norm (alpha j * Cexp(x *: -alpha j)*((Fp i).[x *: alpha j])))
     0 1 =
  norm (alpha j) *
  RInt (fun x =>
            norm (Cexp(x *: -alpha j)*((Fp i).[x *: alpha j])))
     0 1 .
Proof.
rewrite -Rmult_mul -RInt_scal; apply: RInt_ext=> x Hineq.
by rewrite -mulrA -normM Rmult_mul.
Qed.

Lemma maj_IFpc i j :
  RInt (fun x => norm (Cexp(x *: -alpha j)*((Fp i).[x *: alpha j])))
     0 1 <=
  RInt (fun x => norm ((RtoC (exp(Rmax 0 (Re_R (-alpha j))))) * ((Fp i).[x *: alpha j])
            : complexR)) 0 1.
Proof.
apply/RleP; apply: RInt_le; first by apply/RleP/ler01.
    apply: ex_CrInt_norm.
    by move=> x _; apply: Crcontinuity_pt_mul=>//; apply: Crcontinuity_pt_exp.
  apply: ex_CrInt_norm.
  move=> x _. apply: Crcontinuity_pt_mul=>//; apply: Crcontinuity_pt_const.
move=> x [/RltP H0 /RltP H1].
apply/RleP; rewrite -normM -[X in _ <= X]normM.
apply: ler_wpmul2r; first by apply/RleP; apply: norm_ge_0.
rewrite /Cexp /norm /= !mul0r !subr0 !addr0 !linearZ /=.
rewrite !exprMn -!mulrDr !add0r mulr0 mul1r subr0 expr0n /= addr0.
set im := Im (- alpha i).
have Htrigo y: (cos y) ^+ 2 + (sin y) ^+ 2 = 1.
  rewrite addrC !exprS !expr0 !mulr1 -Rplus_add -!Rmult_mul; exact: sin2_cos2.
rewrite !Htrigo !mulr1 /= !sqrtr_sqr.
rewrite !gtr0_norm.
    have : (Re_R (- alpha j) * x) <= (Rmax 0 (Re_R (- alpha j))).
      move: (num_real (Re_R (-alpha j))).
      rewrite realE.
      move=> /orP [Hpos| Hneg].
        apply: (@ler_trans _ (Re_R (-alpha j))).
          rewrite -[X in _<=X]mulr1.
          by apply: ler_wpmul2l=>//; apply: ltrW.
        by apply/RleP; apply: Rmax_r.
      apply: (@ler_trans _ (Re_R (-alpha j) *0)).
        by apply: ler_wnmul2l=> // ; apply:ltrW.
      by rewrite mulr0; apply/RleP; apply: Rmax_l.
    rewrite ler_eqVlt => /orP [/eqP Heq | Hlt].
      by rewrite mulrC -Heq lerr.
    by apply: ltrW; apply/RltP; apply: exp_increasing; apply/RltP; rewrite mulrC.
  by apply/RltP; apply: exp_pos.
by apply/RltP; apply: exp_pos.
Qed.

Lemma maj_IFpd i j :
  RInt (fun x =>
         norm (RtoC (exp(Rmax 0 (Re_R (-alpha j)))) *
                (Fp i).[x *: alpha j] : complexR)) 0 1 =
  norm (exp(Rmax 0 (Re_R (-alpha j)))) *
  RInt (fun x => norm ((Fp i).[x *: alpha j])) 0 1.
Proof.
rewrite -Rmult_mul -RInt_scal; apply: RInt_ext => x Hineq.
rewrite Rmult_mul -normM; congr (_ * _).
by rewrite /norm /= expr0n addr0 sqrtr_sqr.
Qed.

Lemma maj_IFpe i j :
  RInt (fun x => norm ((Fp i).[x *: alpha j])) 0 1 <= 
  (Ma *+ 2) ^+ p.-1 
  * RInt (fun x => norm ((T_an i)^+ p).[x *: alpha j]) 0 1.
Proof.
(* TODO : maybe this lemma should be moved close to normM. *)
have norm_exp : forall y n, norm (y ^+n : complexR) = (norm y)^+n.
  move=> y; elim => [|m Ihm].
    rewrite !expr0 /=.
    by rewrite /norm /= expr1n expr0n /= addr0 sqrtr1.
  by rewrite !exprS -normM Ihm.
rewrite -Rmult_mul -RInt_scal.
apply/RleP; apply: RInt_le.
      by apply/RleP; apply: ler01.
    apply: (ex_RInt_ext
     (fun x : R => norm (horner (Fp i) (x *: alpha j)))).
      by move=> x Hineq; rewrite /norm /=.
    by apply: ex_CrInt_norm.
  apply: (ex_RInt_ext (fun x => norm ((RtoC (Ma *+ 2) ^+ p.-1) *
     ((T_an i) ^+ p).[x *: alpha j]))).
    move=> x Hineq; rewrite Rmult_mul -normM norm_exp. 
    congr (_ ^+ _ * _); rewrite /norm /= expr0n /= addr0 sqrtr_sqr ger0_norm //.
    by rewrite pmulrn_lge0 // max_norm_ge0. 
  apply: ex_CrInt_norm.
  move=> x Hineq.
  apply: Crcontinuity_pt_mul.
    by apply: Crcontinuity_pt_const.
  apply: (@Crcontinuity_pt_ext
             (fun y => (((T_an i)^+ p) \Po ((alpha j) *: 'X )).[RtoC y]) ).
    by move=> y; rewrite horner_comp hornerZ hornerX Cr_scalE mulrC.
  apply: Crcontinuity_pt_poly.
move=> x [/RltP/ltrW H0 /RltP/ltrW  H1]; apply/RleP.
rewrite Rmult_mul.
have -> : (Fp i) = ('X - (alpha i)%:P) ^+ p.-1 * (T_an i) ^+ p.
  rewrite /MPtoP /T_an /F /= /T.
  set mp_rm := (map_poly_rmorphism rm_alpha).
  rewrite !(rmorphM mp_rm) (rmorphX mp_rm) !(rmorph_prod mp_rm) /=.
  rewrite (bigD1 i) //= exprMn (rmorphB mp_rm) /= map_polyX map_polyC /= mevalX.
  rewrite -mulrA -exprSr /= (prednK p_gt0).
  congr (_ * _ ^+ _); apply: eq_bigr => k _; rewrite (rmorphB mp_rm) /=.
  by rewrite map_polyX map_polyC /= mevalX.
rewrite hornerM -normM.
apply/ler_pmul => //; first by apply/RleP/norm_ge_0. 
  by apply/RleP/norm_ge_0.
rewrite horner_exp norm_exp ler_expn2r // ?nnegrE.
+ by apply/RleP/norm_ge_0.
+ by rewrite pmulrn_lge0 // max_norm_ge0.
rewrite hornerXsubC.
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

Lemma maj_IFpf i j M :
  (forall x, 0 <= x <= 1 -> norm (T_an i).[x *: alpha j] <= M) ->
  RInt (fun x => norm ((T_an i)^+ p).[x *: alpha j]) 0 1 <= M ^+ p.
Proof.
rewrite -(prednK p_gt0) //; set m := p.-1.
have HM: M = RInt (fun y => M) 0 1.
  rewrite RInt_const Rmult_mul /Rminus Ropp_opp Rplus_add.
  by rewrite subr0 mul1r.
move=> Hineq; elim: m => [| m Ihm].
  rewrite !expr1 HM.
  apply/RleP/RInt_le; first by apply/RleP/ler01.
      apply: ex_CrInt_norm.
      move=> x Hine.
      apply: (@Crcontinuity_pt_ext
                 (fun y => ((T_an i) \Po ((alpha j) *: 'X )).[RtoC y])).
        by move=> y; rewrite horner_comp hornerZ hornerX Cr_scalE mulrC.
      by apply: Crcontinuity_pt_poly.
    apply: ex_RInt_const.
  move=> x [/RltP/ltrW H0 /RltP/ltrW H1].
  by apply/RleP/Hineq/andP.
rewrite exprS [X in _<=X]exprS.
apply: (@ler_trans _
           (M * (RInt (fun x : R => norm ((T_an i) ^+ m.+1).[x *: alpha j]) 0 1))).
  rewrite -Rmult_mul -RInt_scal; apply/RleP/RInt_le;first by apply/RleP/ler01.
      apply: ex_CrInt_norm => x Hine.
      apply: (@Crcontinuity_pt_ext
                 (fun y => (((T_an i) * (T_an i) ^+ m.+1) \Po ((alpha j) *: 'X )).[RtoC y])).
        by move=> y; rewrite horner_comp hornerZ hornerX Cr_scalE mulrC.
      by apply: Crcontinuity_pt_poly.
    apply/ex_RInt_scal/ex_CrInt_norm.
    move=> x Hine.
    apply: (@Crcontinuity_pt_ext
               (fun y => (((T_an i) ^+ m.+1) \Po ((alpha j) *: 'X )).[RtoC y])).
      by move=> y; rewrite horner_comp hornerZ hornerX Cr_scalE mulrC.
    by apply: Crcontinuity_pt_poly.
  move=> x [/RltP/ltrW H0 /RltP/ltrW H1].
  rewrite hornerM -normM !Rmult_mul.
  apply/RleP/ler_wpmul2r; first by apply/RleP; apply: norm_ge_0.
  by apply/Hineq/andP.
apply: ler_wpmul2l; last by apply: Ihm.
apply: (ler_trans _ (Hineq 0 _)); last by rewrite lerr ler01.
by  apply/RleP/norm_ge_0.
Qed.

Lemma maj_IFp i j :
  norm (I i j) <= Ma * (Me * (Mm * (Ma *+ 2 * Mm)^+p.-1)) .
Proof.
apply: (ler_trans (maj_IFpa i j)); rewrite maj_IFpb.
(* TODO : this is probably general enough to be in the main library. *) 
have hnorm : forall (V : NormedModule R_AbsRing) (x : V), `|norm x| = norm x.
  by move=> V x; apply/normr_idP/RleP/norm_ge_0.
set x1 := _ * (_ * _ ^+ _).
apply: (ler_trans _ (@ler_wpmul2r _ x1 _ (norm (alpha j)) _ _)); last first.
    by apply/max_norm_ge.
  rewrite /x1; apply: mulr_ge0; first by apply: max_norm_ge0.
  apply/mulr_ge0/exprn_ge0/mulr_ge0; do ? apply/max_norm_ge0.
  by apply/mulrn_wge0/max_norm_ge0.
rewrite ![norm _ * _]mulrC.
apply: ler_wpmul2r; first by apply/RleP/norm_ge_0.
apply: (ler_trans (maj_IFpc i j)).
rewrite maj_IFpd /x1. 
apply: (ler_trans (@ler_wpmul2l _ (norm _) _ _ _ _) (ler_wpmul2r _ _)).
+ by apply/RleP/norm_ge_0.
+ apply: (ler_trans (maj_IFpe i j)).
  rewrite exprMn mulrCA ![(_ *+ _) ^+ p.-1 * _]mulrC.
  apply: ler_wpmul2r. 
    by apply/exprn_ge0/mulrn_wge0/max_norm_ge0.
  rewrite -exprS (prednK p_gt0) //.
  apply: maj_IFpf => x Hx.
  have := ((svalP (ex_Mc i j)) x Hx); rewrite -/M.
  move/ltrW/ler_trans; apply.
  apply/(ler_trans (real_ler_norm (num_real _))).
  apply/(ler_trans (max_norm_ge (fun k => M i k) j)).
  apply/(ler_trans _ (max_norm_ge (fun k => max_norm (fun k' => M k k')) i)).
  by apply/real_ler_norm/num_real.
+ apply/mulr_ge0; first by apply/max_norm_ge0.
  apply/exprn_ge0/mulr_ge0; last by apply/max_norm_ge0.
  by apply/mulrn_wge0/max_norm_ge0.
by apply/max_norm_ge.
Qed.

Lemma maj_pre_J i j :
  norm (c ^+ (p * l.+1).-1 * (a j) * Cexp (alpha j) * I i j) <=
    (A * Bn ^ p.-1)%:R.
Proof.
have norm_exp : forall y n, norm (y ^+n : complexR) = (norm y)^+n.
  move=> y; elim => [|m Ihm].
    rewrite !expr0 /=.
    by rewrite /norm /= expr1n expr0n /= addr0 sqrtr1.
  by rewrite !exprS -normM Ihm.
apply/(@ler_trans _ ((Mb * Ma * exp Ma * Me * (norm c)^+ l.+1 * Mm) *
    ((norm c) ^+ l.+1 * (Ma *+ 2) * Mm)^+p.-1)); first last.
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
rewrite -normM -normM -normM.
set xi := norm _; set xs1 := norm _ ^+ _.
rewrite !(mulrAC _ _ xs1) (mulrC _ xs1) -(mulrA xs1) exprMn.
rewrite !(mulrCA _ (xs1 ^+ _)) !mulrA.
set xs := _ * xs1.
have Hx : xi <= xs.
  rewrite /xi /xs /xs1 -exprSr -exprM norm_exp prednK //.
  rewrite -(@prednK (l.+1 * p)%N); last first.
    by rewrite muln_gt0 /= p_gt0.
  rewrite mulnC exprS ler_pmull; last apply/exprn_gt0/(@ltr_le_trans _ 1) => //.
    rewrite -ler_RtoC [X in X <= _]RtoCE.
    have := (norm_Cint_ge1 c_Cint c_neq0).
    by rewrite /Num.norm /= /norm /=.
  rewrite -ler_RtoC [X in X <= _]RtoCE.
  have := (norm_Cint_ge1 c_Cint c_neq0).
  by rewrite /Num.norm /= /norm /=.
set yi := norm _; set ys := Mb.
have Hy : yi <= ys by rewrite /yi /ys; apply: max_norm_ge.
set zi := norm _; set zs := exp _; rewrite (mulrAC _ Ma zs).
have Hz : zi <= zs.
  rewrite /zi /zs /Ma /Cexp /norm /= !mul0r !mul1r !subr0 !addr0 !add0r.
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
rewrite -!mulrA (mulrA _ xs1) -/xs; set u := Ma * _.
apply/(ler_pmul _ _ Hx); first by apply/RleP/norm_ge_0.
  apply/mulr_ge0; first by apply/RleP/norm_ge_0.
  by apply/mulr_ge0; apply/RleP/norm_ge_0.
apply/(ler_pmul _ _ Hy); first by apply/RleP/norm_ge_0.
  by apply/mulr_ge0; apply/RleP/norm_ge_0.
apply/(ler_pmul _ _ Hz); first by apply/RleP/norm_ge_0.
  by apply/RleP/norm_ge_0.
by apply: maj_IFp.
Qed.

Lemma maj_Jip i :
  norm (c ^+ (p * l.+1).-1 * Ji i) < (p.-1)`!%:R.
Proof.
rewrite /Ji big_distrr /=.
move: majoration; rewrite -(ltr_nat R_numDomainType) /An -mulnA natrM.
move/(ler_lt_trans _); apply; rewrite mulr_natl.
have -> : ((A * Bn ^ p.-1)%:R *+ l.+1 : R) = \sum_(j < l.+1) (A * Bn ^p.-1)%:R.
  by rewrite sumr_const cardT size_enum_ord.
apply: (big_ind2 (fun x y => norm x <= y)).
+ by rewrite norm_zero.
+ move=> x1 y1 x2 y2 H1 H2.
  have /RleP := (norm_triangle x1 x2); move/ler_trans; apply.
  by apply/ler_add.
move=> j _; rewrite mulrA mulrA.
by apply: maj_pre_J.
Qed.

Lemma J_lt :
 `|J| < ((p.-1)`!%:R ^+ l.+1).
Proof.
have : norm J < ((p.-1)`!%:R ^+ l.+1).
  rewrite /J -prodrXr -big_split /= big_ord_recl /= -normM exprS.
  set u := norm _; set v := norm _; set P := _ %:R.
  apply/(@ler_lt_trans _ (u * P^+ l)); last first.
    rewrite ltr_pmul2r; first by apply/maj_Jip.
    by apply/exprn_gt0; rewrite ltr0n fact_gt0.
  apply/ler_wpmul2l; first by apply/RleP/norm_ge_0.
  have -> : (P ^+ l : R) = \prod_(j < l) P.
    by rewrite prodr_const cardT size_enum_ord.
  apply: (big_ind2 (fun x y => norm x <= y)) => //.
      by rewrite /norm /= expr0n /= addr0 expr1n sqrtr1.
    move=> x1 x2 y1 y2 Hx Hy; rewrite -normM.
    by apply/ler_pmul => //; apply/RleP/norm_ge_0.
  by move=> i _; apply/ltrW/maj_Jip.
rewrite -ltr_RtoC /Num.norm /= /norm /=.
by move/ltr_le_trans; apply; rewrite -!RtoCE.
Qed.

End Wlog3.

Lemma wlog3 l c (alpha : complexR ^ l.+1) (part : {set {set 'I_l.+1}}) 
  (a : complexR ^ l.+1) :
  c != 0 -> c \is a Cint -> injective alpha -> 
  partition part [set: 'I_l.+1] -> {in part, forall P : {set 'I_l.+1},
  [fset (alpha i) | i in P]%fset \is a setZroots c} ->
  (forall i : 'I_l.+1, a i != 0) -> (forall i : 'I_l.+1, a i \is a Cint) ->
  {in part, forall P : {set 'I_l.+1}, constant [seq a i | i in P]} -> 
  Cexp_span a alpha != 0.
Proof.
move=> c_neq0 c_Cint alpha_inj part_partition alpha_setZroots.
move=> a_neq0 a_Cint a_constant; apply/negP => Lindemann_false.
have := (J_ge c_neq0 c_Cint alpha_inj part_partition alpha_setZroots a_neq0 
     a_Cint a_constant Lindemann_false).
by move/(ltr_le_trans (J_lt alpha a c_neq0 c_Cint)); rewrite ltrr.
Qed.

(* Print Assumptions wlog3. *)





