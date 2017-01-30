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
rewrite /F.


have : (msize ((F i)^`(k)).['X_j] <= \max_(j < size (F i)) (j + msize (F i)`_j))%N.
  by apply/(leq_trans (msize_horner_derivn _ _ _)); rewrite leq_subLR leq_addl.
move/leq_trans; apply; apply/bigmax_leqP => x _. 
<rewrite /F /T coefM /= -ltnS.
rewrite -ltn_subRL -[(_ * _).+1]add1n -addnBA; last first.
  by rewrite -(size_F i) ltnW ?ltn_ord.
rewrite add1n ltnS.
apply/(leq_trans (msize_sum _ _ _))/bigmax_leqP => y _.
apply/(leq_trans (msizeM_proper _ _)).
rewrite -subn1 leq_subLR add1n.

Search _ (msize _) in ajouts.


move: (nat_of_ord k) => {k}; elim => [|k ihk].
  rewrite derivn0 /F hornerM horner_prod horner_exp horner_prod.
  rewrite (eq_bigr (fun i0 => ('X_j - 'X_i0))); last first.
    by move=> k _; rewrite hornerXsubC.
  rewrite [X in _ * X](eq_bigr (fun i0 => ('X_j - 'X_i0))); last first.
    by move=> k _; rewrite hornerXsubC.
  apply: (leq_trans (msizeM_le _ _) _). 
  rewrite (bigD1 j) //= subrr mul0r expr0n.
  have := (prime_gt1 (p_prime)); rewrite -{1}(prednK p_gt0) ltnS lt0n.
  move=> /negbTE -> /=; rewrite msize0 add0n.
  case: (boolP (i == j)) => [/eqP ->| i_neqj]; last first.
    rewrite (bigD1 j) /=; last by move: i_neqj; rewrite eq_sym => ->.
    by rewrite subrr mul0r msize0 muln_gt0 p_gt0.
  have H_XB x y : x != y -> ('X_x - 'X_y : {mpoly complexR[l.+1]}) != 0.
    move=> /negbTE x_neqy; rewrite subr_eq0.
    apply/negP => /eqP /mpolyP /(_ (U_( x))%MM); rewrite !mcoeffX eq_refl /=.
    move/esym; rewrite -[1%N]/(nat_of_bool true).
    move/eqP; rewrite eqr_nat eqb1.
    by move/eqP/mnmP/(_ y); rewrite !mnm1E eq_refl x_neqy.
  apply: (leq_ltn_trans (msize_prod _) _).
    by move=> k; rewrite eq_sym; move: (H_XB j k).
  apply/(leq_ltn_trans (leq_subr _ _) _).
  apply/(@leq_trans (2 * l.+1)%N); last first.
    by rewrite leq_pmul2r // (prime_gt1 (p_prime)).
  rewrite (eq_bigr (fun i0 => 2%N)); last first.
    move=> k k_neqj; rewrite msizeE (eq_big_perm _ (msuppD _)); last first.
      move=> x /=; rewrite (perm_eq_mem (msuppN _)) !msuppX !inE.
      apply/negP=> /andP[/eqP ->]; rewrite eq_sym.
      move/eqP/(congr1 (mpolyX complexR_ringType))/eqP; rewrite -subr_eq0.
      by apply/negP/(H_XB k j k_neqj).
    by rewrite big_cat (eq_big_perm _ (msuppN _)) /= !msuppX !big_seq1 !mdeg1.
  rewrite -ssrcomplements.big_set /= sum_nat_dep_const /= cardsE.
  have -> : [set i0 | i0 != j] = [set: 'I_l.+1] :\: [set j].
    by apply/setP => x; rewrite !inE andbT.
  rewrite cardsDS; last by apply/subsetP => x _; rewrite !inE.
  rewrite cards1 cardsT card_ord subn1 /= [X in (_ < X)%N]mulnS.
  by rewrite -[(l * 2).+1%N]addn1 -addnS addnC mulnC.
rewrite derivnS.

Search _ "poly" in poly.
horner_poly:
  forall (R : ringType) (n : nat) (E : nat -> R) (x : R),
  (\poly_(i < n) E i).[x] = \sum_(i < n) E i * x ^+ i

coef_deriv: forall (R : ringType) (p : {poly R}) (i : nat), (p^`())`_i = p`_i.+1 *+ i.+1

Search _ (msize _) in ajouts.

msize_horner:
  forall (R : idomainType) (n : nat) (p : {poly {mpoly R[n]}}) (i : 'I_n),
  (msize p.['X_i] <= \max_(j < size p) (j + msize p`_j))%N
msize_horner_deriv:
  forall (R : idomainType) (n : nat) (p : {poly {mpoly R[n]}}) (i : 'I_n),
  (msize (p^`()).['X_i] <= (\max_(j < size p) (j + msize p`_j)).-1)%N

Search _ (#| _ |) in finset.

Search _ pred1 (#| _ |).
Search _ predC (#| _ |).

Search _ (#| _ |) in finset.
Search _ [set _ | _ _].
sum_nat_dep_const:
  forall (T : finType) (pA : pred T) (n : nat), (\sum_(x | pA x) n)%N = (#|[set x | pA x]| * n)%N


Search _ "const" in bigop.
    
Search _ mdeg mnm1.
 
Search _ (msize _).
Search _ msupp.

msuppD:
  forall (n : nat) (R : ringType) (p1 p2 : {mpoly R[n]}),
  [predI msupp p1 & msupp p2] =1 xpred0 -> perm_eq (msupp (p1 + p2)) (msupp p1 ++ msupp p2)
msizeD_le:
  forall (n : nat) (R : ringType) (p q : {mpoly R[n]}), (msize (p + q) <= maxn (msize p) (msize q))%N

Search _ (_ * _)%N (_ <= _)%N in ssrnat.
   leq_subr: forall m n : nat, (n - m <= n)%N

Search _ mnm1 in mpoly.

Search _ (_ - _) (_ == _) in ssralg.
  
About msizeM.
Search _ (_ * _)%N (0 < _)%N in ssrnat.
Search _ prime.



Search _ (msize _).

rewrite -mul_mpolyC -hornerZ. msizeZ.

Search _ "max" in bigop.

Lemma Eq_Ji i : 
  Ji i = (Jip i).@[alpha].
Proof.
rewrite /Ji /I /Jip /=.
rewrite (eq_bigr (fun j => (a j * Cexp (alpha j) * (Sd (F i) 0).[0].@[alpha]
 - a j * (Sd (F i) 0).['X_j].@[alpha]))) /=; last first.
  by move=> j _; rewrite mulrBr -mulrA.
rewrite big_split /= -big_distrl /=.
move/eqP : Lindemann_false; rewrite /Cexp_span => ->; rewrite mul0r add0r.
rewrite -(big_endo _ (@opprD _) (oppr0 _)).
by congr (- _); apply: eq_bigr => j _; rewrite -hornerZ.
Qed.
(* rentrer le a_j en scal dans le poly Sd *)
(*congr (_ .[ _]); rewrite /Sd [in RHS]size_scale ?expf_neq0 ?c_neq0 //.
rewrite -mul_polyC big_distrr /=.
by apply: eq_bigr => n _; rewrite mul_polyC derivnZ.
Qed.*)

Definition G i : {poly {mpoly complexR[l.+1]}} := 
   \sum_(0 <= j < p * l) (F i)^`N(p)^`(j).

(* TODO : this is very general and should be migrated to poly *)
Lemma derivn_add {R : ringType} (P : {poly R}) i j : P^`(i+j) = P^`(i)^`(j).
Proof. by rewrite addnC [LHS]iter_add. Qed.

Lemma G_sum i : (G i) *+ (p`!) = \sum_(p <= j < size (F i)) (F i)^`(j).
Proof.
rewrite /G -mulr_natr big_distrl /= size_F mulnS addnC -{4}(add0n p).
rewrite big_addn addnK; apply: eq_bigr => j _.
by rewrite mulr_natr -derivnMn -!nderivn_def addnC derivn_add.
Qed.

(* This one already exists in cauchyreals, with name size_derivn
   but it requires a structure that is to strong: realDomainType. *)
Lemma size_deriv_char (aT : idomainType) (P : {poly aT}) :
  [char aT] =i pred0 -> (size (deriv P) = (size P).-1)%N.
Proof.
rewrite charf0P => Hnatr_eq0.
have [lep1|lt1p] := leqP (size P) 1.
  by rewrite {1}[P]size1_polyC // derivC size_poly0 -subn1 (eqnP lep1).
rewrite size_poly_eq //. 
rewrite -mulr_natl mulf_eq0 Hnatr_eq0 -subn2 -subSn // subn2.
by rewrite lead_coef_eq0 -size_poly_eq0 -(subnKC lt1p).
Qed.

Lemma size_derivn_char (aT : idomainType) (P : {poly aT}) j :
  [char aT] =i pred0 -> (size (P^`(j)) = (size P) - j)%N.
Proof.
move=> Hchar.
elim: j => [ | j ihj]; first by rewrite subn0 derivn0.
by rewrite derivnS subnS -ihj size_deriv_char.
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
rewrite Eq_Ji (bigD1 i) //= [in RHS](bigD1 i) //= Fd0_re mevalD mulrDr -addrA addrC.
congr (- (_ + _)); last by rewrite mevalMn mulrnAr.
rewrite mulrnDl mevalMn mulrnAr -sumrMnl.
by congr (_ + _); apply: eq_bigr => j Hj; rewrite (Fdalpha_re Hj) mevalMn mulrnAr.
Qed.

Definition J := c ^+ (    ) * \prod_(i < l.+1) Ji i.

Lemma J_divp1 : J / (p.-1)`!%:R \is a Cint.
Proof.
suff : (J / (\prod_(i < l.+1) (p.-1)`!%:R)) \is a Cint.
  rewrite prodr_const /= card_ord exprS; set pp := _%:R ^+ _ => H.
  have pp_neq0 : pp != 0 by apply:expf_neq0; rewrite pnatr_eq0 -lt0n fact_gt0.
  rewrite -[X in X \is a Cint]mulr1 -[X in _ * X](divff pp_neq0) mulf_div.
  by rewrite (mulrC J) -mulrA rpredM // Cint_Cnat ?rpredX ?Cnat_nat.
rewrite /J /= -prodf_div.
rewrite (eq_bigr (fun i => - ((\sum_(j < l.+1) (a j) * (G i).[alpha j]) *+ p
          + a i * (F i)^`N(p.-1).[alpha i]))); last first.
  move=> i _; rewrite Eq_JGi mulNr mulrDl; congr (- (_ + _)).
    rewrite -mulr_natr -{1}(prednK p_gt0) factS (prednK p_gt0) natrM.
    rewrite mulrA -[in RHS]mulr_natr -[RHS]mulr1 -!mulrA divff //.
    by rewrite pnatr_eq0 -lt0n fact_gt0.
  by rewrite -mulr_natr -!mulrA divff ?mulr1 // pnatr_eq0 -lt0n fact_gt0.
rewrite prodrN rpredMsign ?card_ord /=; set x := \prod_(_ in _) _.
have {x} -> : x = \prod_(Q in part) \prod_(i in Q) ((\sum_(j < l.+1) 
             a j * (G i).[alpha j]) *+ p + a i * ((F i)^`N(p.-1)).[alpha i]).
  rewrite -(set_partition_big _ part_partition) /= /x.
  by apply: eq_bigl => i; rewrite in_setT.





About set_partition_big.
rewrite (@set_partition_big _ _ _ _ part _ (fun i => ((\sum_(j < l.+1) a j * 
                   (G i).[alpha j]) *+ p + a i * ((F i)^`N(p.-1)).[alpha i])

) part_partition).


Lemma JB_divp : 
   ((J - \prod_(i < l.+1) (- a i * (F i)^`N(p.-1).[alpha i] *+ (p.-1) `!)) 
         / p`!%:R) \is a Cint.

Lemma JC_ndivp : 
   ~~ ((\prod_(i < l.+1) (- a i * (F i)^`N(p.-1).[alpha i] *+ (p.-1) `!) 
         / p`!%:R) \is a Cint).

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


