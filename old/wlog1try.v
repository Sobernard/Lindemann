From mathcomp Require Import all_ssreflect.
From mathcomp
Require Import ssralg ssrnum mxpoly rat poly ssrint polyorder polydiv perm.
From mathcomp
Require Import finfun.
From structs
Require Import Cstruct Rstruct.
From SsrMultinomials
Require Import finmap order mpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.
Import GRing.Theory Num.Theory ArchimedeanTheory complex.ComplexTotalOrder.

Local Notation RtoC := Cstruct.RtoC.
Local Notation Cnat := Cstruct.Cnat.
Local Notation Cint := Cstruct.Cint.
Local Notation bigmaxC := (@bigmaxc R_rcfType : complexR -> seq complexR -> complexR).
Local Notation leCt := (@lect R_rcfType : rel complexR).
Local Notation ltCt := (@ltct R_rcfType : rel complexR).
Local Notation maxC := (@maxc R_rcfType : complexR -> complexR -> complexR).

Notation "x 'is_algebraic'" := (algebraicOver QtoC x)
  (at level 55).


Section Def.

(* move to mxpoly ? *)
Lemma poly_caract_root (F E: fieldType) (f:{rmorphism F -> E}) x : 
    algebraicOver f x -> x != 0 -> 
    exists P : {poly F}, [&&  P \is monic, root (map_poly f P) x & P`_0 != 0].
Proof.
move=> /integral_algebraic [P Pmonic Proot] xneq0.
wlog P_0: P Proot Pmonic / P`_0 != 0=> [hwlog|]; last by exists P; apply/and3P.
have Pneq0 : P != 0 by rewrite monic_neq0.
have [n [Q /implyP /(_ Pneq0) rootQN0 P_eq]] := multiplicity_XsubC P 0.
move: Pneq0 Proot Pmonic.
rewrite P_eq rmorphM rootM rmorphX rmorphB rmorph0 /= map_polyX => Pn0 Pr Pm.
have Qmonic : Q \is monic by move:Pm; rewrite monicMr ?monic_exp ?monicXsubC.
have Qn : Q`_0 != 0 by rewrite -horner_coef0.
have Qr : root (map_poly f Q) x.
 move: Pr; case: {P_eq Pn0 Pm} n => [|n] .
    by rewrite expr0 rootC oner_eq0 orbF.
  by rewrite rmorph0 root_exp_XsubC (negPf xneq0) orbF.
exact: (hwlog Q).
Qed.

Lemma ratr_eq0 (x : rat) : ((QtoC x) == (0: complexR)) = (x == 0).
Proof.
by rewrite -numq_eq0 mulf_eq0 invr_eq0 !intr_eq0 (negbTE (denq_neq0 x)) orbF.
Qed.

Lemma poly_caract_int (x : complexR) : x is_algebraic -> x != 0 ->
    exists P : {poly int}, (P != 0) && root (map_poly ZtoC P) x &&
    (P`_0 != 0) && (0 < lead_coef P).
Proof.
move => algebraic_x xn0.
case: (poly_caract_root algebraic_x xn0) => [P /andP [mon /andP [r nc]]].
set P' :=
    \sum_(0 <= i < size P)
       (\prod_(0 <= j < size P | j != i) (denq P`_j) * numq P`_i) *: 'X^i
    : {poly int}.
exists P'.
have Pn0 : P != 0.
  by apply/negP=> /eqP p0; case/negP:nc; rewrite p0 coef0.
have sp_n0 : size P != 0%N.
  by rewrite size_poly_eq0.
have prn0 : forall pr : pred nat,
      \prod_(0 <= j < size P | pr j) denq P`_j != 0.
  move => pr; elim: {1 3} (size P) (leqnn (size P))=> [| n In] ns.
    by rewrite big_nil.
  rewrite big_mkcond big_nat_recr //; case: (pr n).
    by rewrite mulf_eq0 denq_eq0 orbF -big_mkcond In // ltnW.
  by rewrite /= mulr1 -big_mkcond In // ltnW.
have nc' : P'`_0 != 0.
  rewrite /P'; move: sp_n0; case hs:(size P)=>[| k] // _. 
  rewrite big_nat_recl; last by [].
  rewrite expr0 alg_polyC addrC.
  have eqb :forall i, (0 <= i < k)%N -> 
       (\prod_(0<= j < k.+1 |j != i.+1) denq P`_j * numq P`_i.+1) *: 'X^i.+1 =
       (\prod_(0<= j < k.+1 |j != i.+1) denq P`_j * numq P`_i.+1) *: 'X^i * 'X.
    by move => i _; rewrite exprS -scalerAl (mulrC 'X).
  rewrite (eq_big_nat _ _ eqb) -big_distrl -cons_poly_def coef_cons eqxx {eqb}.
  by rewrite mulf_eq0 negb_or numq_eq0 nc andbT -hs; apply: prn0.
have -> : P' != 0.
  by apply/negP=> /eqP p0; case/negP: nc'; rewrite p0 coef0.
rewrite nc' andbT andTb /P' big_mkord.
rewrite -(poly_def _
          (fun i => (\prod_(0 <= j < size P | j != i) denq P`_j * numq P`_i))).
rewrite /root horner_poly.
rewrite size_poly_eq; last first.
  rewrite mulf_eq0 numq_eq0 -lead_coefE lead_coef_eq0 negb_or Pn0 andbT.
  by apply: prn0.
move: r; rewrite /root horner_poly => /eqP r /=.
rewrite [X in X == 0]
               (_ : _ = (\prod_(0 <= j < size P) denq P`_j)%:~R *
                     \sum_(i < size P) ratr P`_i * x ^+ i).
  rewrite r mulr0 eqxx andTb.
  rewrite lead_coef_poly; first last.
    rewrite mulf_eq0 negb_or prn0 numq_eq0 -lead_coefE.
    by move/monicP: mon=> ->.
  by rewrite lt0n.
  rewrite -lead_coefE; move/monicP: (mon) => ->; have -> :numq 1 = 1%N by [].
  rewrite mulr1.
  apply: (big_rec (fun x => 0 < x)) => // i w ci cw.
  by rewrite mulr_gt0 // denq_gt0.
rewrite big_distrr; apply: eq_bigr => i _ /=.
rewrite coef_poly /=; case: i => i ic /=; rewrite ic !mulrA; congr (_ * _).
have := (denq_neq0 P`_i); rewrite -(intr_eq0 complexR_numDomainType) => di.
apply: (mulIf di); rewrite mulfVK // mulrC -!rmorphM /= mulrA.
congr ((_ * _)%:~R); rewrite !big_mkord.
by apply/esym; apply:(@bigD1 _ _ _ _ (Ordinal ic) (fun _ => true)).
Qed.

Lemma polyMin_subproof (x : complexR) : x is_algebraic -> x != 0 -> 
    {P : {poly int} | (P != 0) && root (map_poly ZtoC P) x &&
    (P`_0 != 0) && (0 < lead_coef P)}.
Proof.
move => x_alg x_neq0.
move: (sigW (poly_caract_int x_alg x_neq0)) => [P /andP [] /andP [] /andP [] P_neq0 x_root_P P0_neq0 lcP_gt0].
by exists P; rewrite P_neq0 x_root_P P0_neq0 lcP_gt0.
Qed.

Definition polyMin (x : complexR) (H : x is_algebraic) :=
  match Sumbool.sumbool_of_bool(x != 0) with
  |right _ => 'X
  |left toto => sval(polyMin_subproof H toto) 
  end.

Lemma polyMin_neq0 (x : complexR) (H : x is_algebraic) : (polyMin H) != 0.
Proof.
rewrite /polyMin.
case : ((Sumbool.sumbool_of_bool (x != 0))) => [a | _]; last first.
  by rewrite polyX_eq0.
by move: (svalP (polyMin_subproof H a)) => /andP [ /andP [ /andP [-> _] _] _].
Qed.

Lemma polyMin_root (x : complexR) (H : x is_algebraic) : 
  root (map_poly ZtoC (polyMin H)) x.
Proof.
rewrite /polyMin.
case : ((Sumbool.sumbool_of_bool (x != 0))) => [a | /eqP ->]; last first.
  by rewrite map_polyX rootX.
by move: (svalP (polyMin_subproof H a)) => /andP [ /andP [ /andP [_ ->] _] _].
Qed.

Lemma polyMin_lcoef_gt0 (x : complexR) (H : x is_algebraic) : 
  0 < lead_coef (polyMin H).
Proof.
rewrite /polyMin.
case : ((Sumbool.sumbool_of_bool (x != 0))) => [a | _]; last first.
  by rewrite lead_coefX.
by move: (svalP (polyMin_subproof H a)) => /andP [ /andP [ /andP [_ _] _] ->].
Qed.

Lemma polyMin_coef0_neq0 (x : complexR) (H : x is_algebraic) :
  ((polyMin H)`_0 == 0) = (x == 0).
Proof.
rewrite /polyMin.
case : ((Sumbool.sumbool_of_bool (x != 0))) => [a | /eqP ->]; last first.
  by rewrite coefX eq_refl.
move: (svalP (polyMin_subproof H a)) => /andP[ /andP[_ /negbTE ->] _].
by apply/eqP; rewrite eq_sym; apply/eqP/negbTE; rewrite a.
Qed.

Definition Cexp_span (n : nat) (a : complexR ^ n) (alpha : complexR ^ n) :=
  \sum_(i : 'I_n) (a i) * Cexp (alpha i).

(*
Lemma index_inj (T : eqType) (s : seq T) :
  {in s, injective (index^~ s)}.
Proof.
move=> x x_in y y_in.
elim: s x_in y_in => [//| a l H]. 
case: (boolP (x == a)) => [/eqP <- _ | /negbTE x_eq_a].
  by rewrite /= eq_refl; case: (boolP (x == y)) => [/eqP //| _].
rewrite inE x_eq_a orFb => x_in /=; rewrite eq_sym x_eq_a.
case: (boolP (a == y)) => [/eqP <- // | negbTE y_eq_a].
by apply: (H x_in); apply/eqP; rewrite -eqSS y_eq_a.
Qed.

Lemma tnth_count_mem (T : eqType) (n : nat) (s : n.-tuple T) (i j : 'I_n) :
  (count_mem (tnth s i) s == 1)%N -> (tnth s i == tnth s j) = (i == j).
Proof.
move=> count_i.
case: (boolP (i == j)) => [/eqP | /negbTE i_neq_j]. 
  by move=> <-; rewrite !eq_refl.
apply/negbTE/negP => /eqP H; move/eqP: count_i.
rewrite -sum1_count big_tuple (bigD1 j) /=; last by rewrite H.
move/eqP; rewrite add1n eqSS sum_nat_eq0; apply/negP; rewrite negb_forall.
by apply/existsP; exists i; rewrite H i_neq_j eq_refl andTb /=.
Qed.

Lemma tnth_count_memP (T : eqType) (n : nat) (s : n.+1.-tuple T) (i : 'I_n.+1) :
  reflect (forall j, (tnth s i == tnth s j) = (i == j)) 
    (count_mem (tnth s i) s == 1)%N.
Proof.
apply: (iffP idP); first by move/tnth_count_mem.
move=> H_tnth.
move: (perm_to_rem (mem_tnth i s)).
move/perm_eqP => -> /=; rewrite eq_refl /=.
suff -> : count_mem (tnth s i) (rem (tnth s i) s) = 0%N by rewrite addn0.
apply/count_memPn.
apply/negP; move=> /(nthP (tnth s i)) [j].
rewrite (size_rem (mem_tnth _ _)) size_tuple /= => j_le.
have -> : nth (tnth s i) (rem (tnth s i) s) j = 
          nth (tnth s i) (tnth s i :: rem (tnth s i) s) j.+1 by [].
move: j_le; rewrite -ltnS => j_ord.
rewrite -[j.+1]/(nat_of_ord (Ordinal j_ord)) => H_eq.
move: (perm_to_rem (mem_tnth i s)); rewrite perm_eq_sym.
move/tuple_perm_eqP => [] f H_eq_seq.
have eq_j_ord : (fingroup.invg f) i = Ordinal j_ord.
  move: H_eq; rewrite H_eq_seq -tnth_nth tnth_map tnth_ord_tuple.
  by move/eqP; rewrite eq_sym H_tnth => /eqP ->; rewrite permK.
have eq_i_0 : i = f ord0.
  apply/eqP; rewrite -H_tnth; apply/eqP.
  rewrite -[LHS]/(head (tnth s i) (tnth s i :: rem (tnth s i) s)).   
  rewrite -nth0 H_eq_seq -[X in nth _ _ X]/(nat_of_ord (@ord0 n)).
  by rewrite -tnth_nth tnth_map tnth_ord_tuple.
move: eq_j_ord; rewrite eq_i_0 permK /= => H.
by have: nat_of_ord (@ord0 n) = nat_of_ord (Ordinal j_ord) by rewrite -H.
Qed.

Lemma nth_count_memP (T : eqType) (x0 : T) (s : seq T) (i : nat) :
  (i < size s)%N -> reflect (forall j, (j < size s)%N -> 
      (nth x0 s i == nth x0 s j) = (i == j))
      (count_mem (nth x0 s i) s == 1)%N.
Proof.
case: s => [//= | x s].
have: (size (x :: s) > 0)%N by [].
move: (x :: s) => {x s} s.
rewrite -[s]/(val (in_tuple s)); move: (in_tuple s) => t.
rewrite size_tuple; move/prednK => Hsize.
move: t; rewrite -Hsize => t {Hsize} => ord_i.
rewrite -[i]/(nat_of_ord (Ordinal ord_i)); move: (Ordinal ord_i) => {i ord_i} i.
rewrite -tnth_nth /=.
apply: (iffP idP).
  move/tnth_count_memP => H1 j j_ord.
  by rewrite -[j]/(nat_of_ord (Ordinal j_ord)) -tnth_nth H1.
move=> H; apply/tnth_count_memP => j.
by rewrite [X in _ == X](tnth_nth x0) H.
Qed. *)

End Def.

Section Theory.

Section fintype_ajouts.

Variable n : nat.

Lemma ordnat i (ord_i : (i < n)%N) :
  i = nat_of_ord (Ordinal ord_i).
Proof. by []. Qed.

End fintype_ajouts.

Section ssrcomplements_ajouts.

(*
Lemma uniq_tnth (T : eqType) (n : nat) (t : n.-tuple T) :
  (forall i j : 'I_n, i != j -> tnth t i != tnth t j) -> uniq t.
Proof.
case: n t => [t _ | n t /=].
  by have -> //= : tval t = [::] by apply/eqP; rewrite -size_eq0 size_tuple.
move=> H; apply: (@ssrcomplements.uniq_nth _ (tnth t ord0)) => i j.
rewrite size_tuple => ord_i ord_j.
rewrite (ordnat ord_i) (ordnat ord_j) -!tnth_nth => Hneq.
by apply: H.
Qed.
*)

End ssrcomplements_ajouts.

Section finfun_ajouts.

Variable R : eqType.
Variable n : nat.

Lemma uniq_fgraphP (f : R ^ n.+1) :
  reflect (injective f) (uniq (fgraph f)).
Proof.
apply: (iffP idP) => [uniq_f i j | inj_f].
  rewrite -[RHS](nth_fgraph_ord (f i)) -{1}(nth_fgraph_ord (f i)).
  by move/eqP; rewrite (nth_uniq) ?size_tuple ?card_ord //=; move/eqP /ord_inj.
apply: (@ssrcomplements.uniq_nth _ (f ord0)) => i j.
rewrite size_tuple {2}card_ord {1}card_ord => ord_i ord_j.
rewrite (ordnat ord_i) (ordnat ord_j) => /negP eq_ord.
by rewrite !nth_fgraph_ord; apply/negP => /eqP /inj_f /eqP.
Qed.

End finfun_ajouts.

Section mpoly_ajouts.

Lemma eq_mmap n (R S : ringType) (f : R -> S) (h1 : 'I_n -> S) (h2 : 'I_n -> S) (p : {mpoly R[n]}) :
   h1 =1 h2 -> mmap f h1 p = mmap f h2 p.
Proof.
move=> Heq; rewrite /mmap.
by apply: eq_bigr => i _; rewrite (mmap1_eq _ Heq).
Qed.

Lemma eq_meval (n : nat) (R : ringType) (v1 : 'I_n -> R) (v2 : 'I_n -> R) (p : {mpoly R[n]}) :
   v1 =1 v2 -> p.@[v1] = p.@[v2].
Proof. by move=> Heq; rewrite /meval (eq_mmap _ _ Heq). Qed.



Local Notation "''s_' ( n , k )" := (@mesym n _ k).

(* th poly sym pour des éléments dans un subringPred : move to mpoly ? *)
Lemma sym_fundamental_subring n (R : comRingType) S (ringS : @subringPred R S)
      (kS : keyed_pred ringS) (p : {mpoly R[n]}) :
    p \is a mpolyOver n kS -> p \is symmetric ->
    {q | [&& (p == q \mPo [tuple 's_(n, i.+1) | i < n]),
          ((mweight q) <= msize p)%N  & (q \is a mpolyOver n kS)]}.
Proof.
move=> p_over p_sym.
have symf1_kS1 q : q \is a mpolyOver n kS -> (symf1 q).1 \is a mpolyOver n kS.
  rewrite /symf1 => q_over; case: (ifP _) => [_ | /negbT q_neq0] /=.
    by rewrite rpred0.
  apply: mpolyOverZ.
    by move/mpolyOverP: q_over; move/(_ (mlead q)).
  by apply: mpolyOverX.
have symf1_kS2 q : q \is a mpolyOver n kS -> (symf1 q).2 \is a mpolyOver n kS.
  rewrite /symf1 => q_over; case: (ifP _) => [_ | /negbT q_neq0] /=.  
    by rewrite rpred0.
  apply: rpredB => //=; apply: mpolyOverZ => /=.
    by move/mpolyOverP: q_over; move/(_ (mlead q)).
  rewrite comp_mpolyX; apply: rpred_prod => i _.
  rewrite tnth_map; apply: rpredX.
  rewrite /mesym; apply: rpred_sum => j _; apply: rpred_prod => k _.
  by apply: mpolyOverX.
have symfn_kS k q : q \is a mpolyOver n kS ->
  (symfn k q).1 \is a mpolyOver n kS /\ (symfn k q).2 \is a mpolyOver n kS.
  elim: k q => [q q_over | k ihk q q_over].
    by rewrite /symfn (symf1_kS1 _ q_over); rewrite symf1_kS2.
  move: (ihk (symf1 q).2 (symf1_kS2 _ q_over)) => [] H1 H2.
  split; rewrite /= [symf1 q]surjective_pairing [symfn k (symf1 q).2]surjective_pairing //=.
  by apply: rpredD => //; apply: (symf1_kS1 _ q_over).   
exists (symf p); rewrite (symfn_wgle _ p_sym) {1}(symfP p_sym) eq_refl /symf /=.
by move: (symfn_kS (sval (symfnS p)) p p_over) => [] H _.
Qed.

End mpoly_ajouts.
  
Section ClosedField_ajouts.

Variable T : closedFieldType.

Definition seqroots (P : {poly T}) := if P == 0 then [::] 
                                      else(sval(closed_field_poly_normal P)).

Lemma seqroots_0 : seqroots 0 = [::].
Proof. by rewrite /seqroots eq_refl. Qed.


Lemma seqroots_poly P : P = lead_coef P *: \prod_(x <- (seqroots P)) ('X - x%:P). 
Proof.
case: (boolP (P == 0)) => [/eqP -> | /negbTE P_neq0].
  by rewrite lead_coef0 scale0r.
by rewrite /seqroots P_neq0 {1}(svalP(closed_field_poly_normal P)).
Qed.

Lemma seqrootsP P x : P != 0 -> reflect (x \in seqroots P) (root P x).
Proof.
move=> P_neq0.
have lead_coef_neq0 : lead_coef P != 0; first by rewrite lead_coef_eq0.
move: P_neq0 (svalP(closed_field_poly_normal P)) => /negbTE P_neq0 H; rewrite H.
rewrite (rootZ _ _ lead_coef_neq0) -H root_prod_XsubC /seqroots P_neq0.
by apply: (iffP idP).
Qed.

Lemma seqroots_neq0 P : (P != 0) -> (0 \in (seqroots P)) = (P`_0 == 0).
Proof.
move=> P_neq0; apply/idP/idP.
  by move/(seqrootsP _ P_neq0)/rootP; rewrite horner_coef0 => ->.
by move=> /eqP H; apply/(seqrootsP _ P_neq0)/rootP; rewrite horner_coef0.
Qed.

Lemma seqroots_mu P x : (count_mem x) (seqroots P) = \mu_x P.
Proof.
case: (boolP (P == 0)) =>  [/eqP P_eq0 | P_neq0].
  by rewrite P_eq0 seqroots_0 mu0; apply/count_memPn; rewrite in_nil.
case: (boolP (root P x)) => [x_root | x_not_root]; last first.
  rewrite (muNroot x_not_root); apply/count_memPn.
  by apply/negP; apply: (elimN (seqrootsP x P_neq0) x_not_root).
have [sr_eq] : seqroots P = sval(closed_field_poly_normal P).
  by rewrite /seqroots; move/negbTE: P_neq0 => P_neq0; rewrite ifF.
move: (svalP (closed_field_poly_normal P)); rewrite -sr_eq.
rewrite -prodr_undup_exp_count.
have x_seqroot : x \in undup (seqroots P); first by rewrite mem_undup; apply /seqrootsP.
rewrite (bigD1_seq _ x_seqroot (undup_uniq (seqroots P))) /= scalerAr mulrC => P_eq.
apply/eqP; rewrite -(muP _ _ P_neq0); apply/andP; split.
  by apply/dvdpP; exists (lead_coef P *: 
    \prod_(i <- undup (seqroots P) | i != x) ('X - i%:P) ^+ (count_mem i) (seqroots P)).
rewrite [X in _ %| X]P_eq exprS dvdp_mul2r; last first.
  by rewrite expf_neq0 // polyXsubC_eq0.
rewrite dvdp_XsubCl; move: P_neq0; rewrite -lead_coef_eq0 => lc_P_neq0.
rewrite (rootZ _ _ lc_P_neq0) prodr_undup_exp_count.
by rewrite -big_filter root_prod_XsubC mem_filter eq_refl.
Qed.

Lemma seqroots_size P : size (seqroots P) = if (P == 0) then 0%N else (size P).-1.
Proof.
case: (boolP (P == 0)) => [/eqP ->| H].
  by rewrite seqroots_0.
have Hp : (0 < size P)%N; first by rewrite size_poly_gt0.
rewrite /seqroots; move/negbTE : H => H; rewrite H; move/negbT: H => H.
move: (svalP( closed_field_poly_normal P)); set r := sval _ => ->.
move: H; rewrite -lead_coef_eq0 => H; rewrite (size_scale _ H).
by rewrite size_prod_XsubC.
Qed.

Lemma seqroots_polyC c : seqroots c%:P = [::].
Proof.
apply: size0nil; rewrite seqroots_size.
case: (boolP (c == 0)) => [/eqP -> | /negbTE c_neq0] /=.
  by rewrite eq_refl.
by rewrite polyC_eq0 c_neq0 size_polyC; move/negbT: c_neq0 => -> /=.
Qed.

Lemma seqrootsM P Q : P * Q != 0 ->
  perm_eq (seqroots (P * Q)) ((seqroots P) ++ (seqroots Q)).
Proof.
move => PQ_neq0; rewrite /perm_eq; apply/allP => x.
rewrite !mem_cat => /orP [ H | /orP [H | H]] /=; 
by rewrite count_cat !seqroots_mu (mu_mul _ PQ_neq0).
Qed.

Lemma seqroots_prod (I : Type) P (r : seq I) : all [pred i | P i != 0] r ->
  perm_eq (seqroots (\prod_(i <- r) P i)) (flatten [seq seqroots (P i) | i <- r]).
Proof.
elim: r => [_ | j r Ihr].
  rewrite big_nil /=; have -> : (seqroots 1) = [::]; last by [].
  have -> : (1 = (1%:P : poly_ringType T)); first by [].
  by rewrite seqroots_polyC.
rewrite /= => /andP [Hj Hprod].
rewrite big_cons; apply: (perm_eq_trans (seqrootsM _)).
  apply:mulf_neq0; first by [].
  by rewrite prodf_seq_neq0.
by rewrite perm_cat2l; apply: Ihr.
Qed.

(* la définition fera le lien avec le changement pour plus tard *)
Definition cset_of_roots P := [qualify a s | perm_eq s (seqroots P)]. 


Local Notation "''s_' ( n , k )" := (@mesym n _ k).

(* revoir le state du th *)
Lemma seqroots_pred S (ringS : @subringPred T S)
      (kS : keyed_pred ringS) P m (l : T ^ m) : 
   (codom l) \is a cset_of_roots P ->
   P \is a polyOver kS -> forall i : 'I_m,
  ((lead_coef P) *: 's_(m, i.+1)).@[l] \in kS.
Proof.
move=> /= l_setroots P_over i.
case: (boolP (P == 0)) => [/eqP P_eq0 | /negbTE P_neq0].
  by rewrite [X in lead_coef X]P_eq0 lead_coef0 scale0r meval0; apply: rpred0.
have -> : ((lead_coef P) *: 's_(m, i.+1)) .@[l]
    = (-1) ^+ i.+1 * P`_(m - i.+1).
  rewrite -[_.@[ _]](signrMK i.+1); congr ((-1)^+ i.+1 * _).
  move: (ltn_ord i); rewrite -ltnS => ord_i1.
  rewrite -[i.+1]/(nat_of_ord (Ordinal ord_i1)) /= mevalZ mulrCA.
  rewrite (@eq_meval _ _ _ (tnth [tuple l i | i < m])); last first.
    by move=> j; rewrite tnth_map tnth_ord_tuple.
  rewrite -(mroots_coeff _ (Ordinal ord_i1)) -coefZ.
  rewrite (eq_big_perm (seqroots P)) /= -?seqroots_poly //.
by rewrite rpredMsign; apply/polyOverP.
Qed.

(* codom, perm_eq :
  apply: (perm_eq_trans perm_l); rewrite codom_ffun /=.
  have <- // : [seq l i | i : 'I_m] = fgraph l.
  move: ord_i1; rewrite ltnS => ord_i.
  apply/(@eq_from_nth _ (l (Ordinal ord_i))).
    by rewrite /= size_tuple size_map card_ord size_enum_ord.
  move=> j; rewrite size_map size_enum_ord => ord_j.
  rewrite -[j]/(nat_of_ord (Ordinal ord_j)).
  rewrite nth_fgraph_ord (nth_map (Ordinal ord_j)) ?size_enum_ord //.
  by rewrite (ord_inj (nth_enum_ord _ _)). *)

(* a generaliser et bouger *)
Lemma meval_comp_mpoly (n : nat) (R : comRingType) (k : nat) (lq : n.-tuple {mpoly R[k]})
      (h : R ^ k) (p : {mpoly R[n]}) :
  (p \mPo lq).@[h] = p.@[tnth (map_tuple (meval h) lq)].
Proof.  
rewrite comp_mpolyE rmorph_sum /= mevalE.
apply: eq_bigr => m _; rewrite mevalZ rmorph_prod /=.
by congr (p@_m * _); apply: eq_bigr => i _; rewrite tnth_map rmorphX.
Qed.

(* th fond caché, pour les seqroots *)
Lemma sym_fundamental_seqroots S (ringS : @subringPred T S) 
  (kS : keyed_pred ringS) P m p (l : T ^ m) :
  (codom l) \is a cset_of_roots P ->
  P \is a polyOver kS -> p \is a mpolyOver m kS ->
  p \is symmetric -> (lead_coef P)^+ (msize p) * p.@[l] \in kS.
Proof.
move=> l_setroots P_over p_over p_sym.  
move: (sym_fundamental_subring p_over p_sym) => [q /andP[/eqP eq_qp /andP[size_le q_over]]].
rewrite {2}eq_qp meval_comp_mpoly -mevalZ [q]mpolyE scaler_sumr rmorph_sum /=.
rewrite big_seq; apply: rpred_sum => i i_msupp /=; rewrite !mevalZ mulrCA.
apply: rpredM; rewrite -?mevalZ; first by move/mpolyOverP: q_over; move/(_ i).
rewrite mpolyXE_id.
have -> : (msize p = (msize p - (\sum_(j < m ) i j)) +
                     (\sum_(j < m) (i j)))%N.
  rewrite subnK // -mdegE.
  apply: (leq_trans _ size_le).
  apply: (leq_trans _ (leq_msize_meight q)).
  by apply: (leq_trans _ (msize_mdeg_lt i_msupp)).
rewrite exprD -scalerA mevalZ.
apply: rpredM; first by apply: rpredX; apply/polyOverP.
rewrite -prodrXr -scaler_prod rmorph_prod /=.
apply: rpred_prod => j _; rewrite -exprZn rmorphX /=.
apply: rpredX; rewrite mevalZ mevalX !tnth_map /= -mevalZ.
by apply: seqroots_pred.
Qed.

(* th fond caché, pour les poly de poly : généraliser pour cacher le poly de poly *)
Lemma sym_fundamental_seqroots_empil S (ringS : @subringPred T S) 
  (kS : keyed_pred ringS) P n m p (l : T ^ m) :
  (codom l) \is a cset_of_roots P ->
  P \is a polyOver kS -> p \is a (mpolyOver m (mpolyOver n kS)) ->
  p \is symmetric -> 
  (lead_coef P)^+ (msize p) *: p.@[finfun((@mpolyC n T) \o l)] \is a mpolyOver n kS.
Proof.
move=> l_setroots P_over p_over p_sym.  
move: (sym_fundamental_subring p_over p_sym) => [q /andP[/eqP eq_qp /andP[size_le q_over]]].
rewrite {2}eq_qp meval_comp_mpoly -mul_mpolyC.
set t := tnth _; rewrite -[_%:MP_[n]](mevalC t) -mevalM mul_mpolyC.
rewrite [q]mpolyE scaler_sumr rmorph_sum /=.
rewrite big_seq; apply: rpred_sum => i i_msupp /=; rewrite !mevalZ mulrCA.
apply: rpredM; rewrite -?mevalZ; first by move/mpolyOverP: q_over; move/(_ i).
rewrite mpolyXE_id.
have -> : (msize p = (msize p - (\sum_(j < m) i j)) +
                     (\sum_(j < m) (i j)))%N.
  rewrite subnK // -mdegE.
  apply: (leq_trans _ size_le).
  apply: (leq_trans _ (leq_msize_meight q)).
  by apply: (leq_trans _ (msize_mdeg_lt i_msupp)).
rewrite exprD mpolyCM -scalerA mevalZ.
apply: rpredM; first by rewrite mpolyOverC; apply: rpredX; apply/polyOverP.
rewrite rmorphX /= -prodrXr -scaler_prod rmorph_prod /=.
apply: rpred_prod => j _; rewrite -exprZn rmorphX /=.
apply: rpredX; rewrite mevalZ mevalX /t !tnth_map /= tnth_ord_tuple.
move: (seqroots_pred l_setroots P_over j); set c := lead_coef _.
rewrite -(mpolyOverC n).
suff -> : ((c *: 's_(m, j.+1)).@[l])%:MP_[n] =
          c%:MP_[n] * ('s_(m, j.+1))
          .@[finfun((mpolyC n (R:=T)) \o l)] by [].
rewrite -mul_mpolyC mevalM mpolyCM mevalC; congr (c%:MP_[n] * _).
rewrite !mesym_tupleE [in RHS]rmorph_sum /=.
rewrite [X in X%:MP_[n]]rmorph_sum /= rmorph_sum /=.
apply: eq_bigr => u Hu; rewrite !rmorph_prod /=.
by apply: eq_bigr => k _; rewrite !mevalX ffunE.
Qed.

  
End ClosedField_ajouts.

Section Seq_ajouts.

Variable T : eqType.

(*
Lemma nth_flatten_size s0 (A : seq (seq T)) s x i :
  (x \in s) -> (i < size A)%N -> nth s0 A i = s ->
    ((sumn (shape (take i A)) + (index x s))%N < size (flatten A))%N.
Proof.
move=> x_in_s leq_i_sizeA nth_i_s_A.
have s_in_A : s \in A by apply/(nthP s0); exists i.
have x_in_flatten : x \in flatten A by apply/flattenP; exists s.
have len_ind_size : (index x s < size s)%N; first by rewrite index_mem.
have H2 : (sumn (shape (take i A)) + index x s < sumn (shape (take i.+1 A)))%N.
  rewrite (take_nth s0) ?index_mem // nth_i_s_A.
  by rewrite {2}/shape map_rcons -/shape -cats1 sumn_cat /= addn0 ltn_add2l.
rewrite size_flatten -{2}[A](@cat_take_drop i.+1) /shape map_cat /= sumn_cat.
by apply: (leq_trans H2 _); apply: leq_addr.
Qed.

Lemma nth_flatten (x0 : T) s0 (A : seq (seq T)) s x i :
  (x \in s) -> (i < size A)%N -> nth s0 A i = s ->
  nth x0 (flatten A) (sumn (shape (take i A)) + (index x s))%N = x.
Proof.
move=> x_in_s.
elim/last_ind: A i => [i| A l IhA j]; first by rewrite ltn0.
rewrite size_rcons ltnS leq_eqVlt => /orP [/eqP ->| lt_j_size].
  rewrite nth_rcons ltnn eq_refl => ->.
  rewrite -cats1 take_cat ltnn subnn take0 cats0 -size_flatten flatten_cat.
  rewrite nth_cat -[X in (_ < X)%N]addn0 ltn_add2l ltn0 addKn /=.
  by rewrite nth_cat index_mem x_in_s nth_index.
rewrite nth_rcons lt_j_size => nth_j.
rewrite -{2}(IhA j lt_j_size nth_j).
rewrite -cats1 flatten_cat takel_cat 1?leq_eqVlt ?lt_j_size ?orbT //.
by rewrite nth_cat (nth_flatten_size x_in_s lt_j_size nth_j).
Qed.
*)
End Seq_ajouts.

Section MSym.


End MSym.



Section LeC_ajouts.

Variable n : nat.

(* a generaliser *)
Variable r : complexR ^ n.+1.

Local Notation bigmaxf r := (bigmaxC 0 (fgraph r)).

Hypothesis r_bigmax : bigmaxf r = r ord0.

Notation mnm_to_C := 
  (fun (m : 'X_{1.. n.+1}) => \sum_(i < n.+1) ((r i) *+ m i)).

Lemma mnm_to_CE m : 
  mnm_to_C m = \sum_(i <- m2s m) (r i).
Proof.
rewrite /mnm_to_C /m2s big_flatten /= big_map /=.
rewrite enumT /index_enum; apply: eq_bigr => i _.
by rewrite big_nseq -Monoid.iteropE /=.
Qed.

Lemma mnm_bigmaxc p :
  forall m, mdeg m = p -> leCt (mnm_to_C m) (mnm_to_C (U_( Ordinal n_gt0) *+ p)%MM). 
Proof.
move=> m m_mdeg. 
have tuple_m : size (m2s m) == p by rewrite size_m2s m_mdeg.
set tm := Tuple tuple_m; rewrite mnm_to_CE -[m2s m]/(val tm) big_tuple.
rewrite /mnm_to_C (bigD1 (Ordinal n_gt0)) //= [X in _ + X]big1; last first.
  by move=> i /negbTE i_neq0; rewrite mulmnE mnm1E eq_sym i_neq0 muln0 mulr0n.
rewrite addr0 mulmnE mnm1E eq_refl muln1 /GRing.natmul Monoid.iteropE /=.
rewrite -big_const_ord; apply: lect_sum => i _ /=.
rewrite -r_bigmax -(nth_fgraph_ord 0).
by apply: bigmaxc_lect; rewrite size_tuple card_ord.
Qed.

Lemma mnm_bigmaxc_lt p :
  forall m, mdeg m = p.+1 -> injective r ->
    (ltCt (mnm_to_C m) (mnm_to_C (U_( Ordinal n_gt0) *+ p.+1)%MM)) = 
    (m != U_( Ordinal n_gt0) *+ p.+1)%MM.
Proof.
move=> m m_mdeg uniq_r.
case: (boolP (m == _)) => [/eqP -> /= | H_m].
  by rewrite ltct_neqAle eq_refl.
have tuple_m : size (m2s m) == p.+1 by rewrite size_m2s m_mdeg.
set tm := Tuple tuple_m; rewrite mnm_to_CE -[m2s m]/(val tm) big_tuple.
rewrite /mnm_to_C (bigD1 (Ordinal n_gt0)) //= [X in _ + X]big1; last first.
  by move=> i /negbTE i_neq0; rewrite mulmnE mnm1E eq_sym i_neq0 muln0 mulr0n.
rewrite addr0 mulmnE mnm1E eq_refl muln1 /GRing.natmul Monoid.iteropE.
rewrite -big_const_ord /= big_ord_recr big_ord_recr /=.
apply: (@lect_lt_trans _ (\sum_(i < p) r (Ordinal n_gt0) + r (tnth tm ord_max))).
  rewrite lect_add2r; apply: lect_sum => i _.
  rewrite -(nth_fgraph_ord 0) -r_bigmax.
  by apply: bigmaxc_lect; rewrite size_tuple card_ord.
rewrite ltct_add2l -(nth_fgraph_ord 0) -r_bigmax.
apply: bigmaxc_ltct; rewrite ?size_tuple ?r_bigmax //.

rewrite index_uniq ?size_tuple //.
rewrite (tnth_nth (Ordinal n_gt0)) /=.
apply/negP => /eqP /= eq_last_m.
move/negP: H_m; apply; apply/eqP; apply/mnmP => i.
have: forall s x0, sorted leq s -> forall i, (i < size s)%N -> ((nth x0 s i) <= last x0 s)%N.
  move=> s x0; case: s => [_ j //= | a s /=].
  elim/last_ind : s => [_ j /= | s b ihs].
    by rewrite ltnS leqn0 => /eqP ->.
  rewrite rcons_path => /andP[Hpath le_last j].
  rewrite ltnS leq_eqVlt last_rcons size_rcons => /orP[/eqP -> | j_size].
    by rewrite /= nth_rcons ltnn eq_refl.
  move/ihs : Hpath; move/(_ j j_size) => {ihs} ihs.
  rewrite -rcons_cons nth_rcons /= j_size.
  by apply: (leq_trans ihs le_last).
move/(_ _ 0%N (srt_m2s m)).
rewrite (last_map _ _ (Ordinal n_gt0)) /= -nth_last size_map.
move/eqP : tuple_m {tm} => eq_p; rewrite eq_p /= eq_last_m => H_eq0.
have eq_m2s : m2s m = nseq p.+1 (Ordinal n_gt0).
  apply/(@eq_from_nth _ (Ordinal n_gt0)); first by rewrite eq_p size_nseq.
  rewrite eq_p => j j_size; move: (H_eq0 j j_size). 
  rewrite leqn0 (nth_map (Ordinal n_gt0)); last by rewrite eq_p.
  rewrite -[0%N]/(nat_of_ord (Ordinal n_gt0)); move/eqP /ord_inj => ->.
  by rewrite nth_nseq j_size.
rewrite -[m]s2mK eq_m2s /s2m mulmnE mnm1E.
case: (boolP (Ordinal n_gt0 == i)) => [/eqP <- | /negP neq_i_0].
  rewrite muln1 mnmE; apply/eqP.
  by move: (all_pred1_nseq (Ordinal n_gt0) p.+1); rewrite all_count size_nseq.
rewrite muln0 mnmE; apply/count_memPn /nseqP; rewrite ltn0Sn.
by move=> [H _]; apply neq_i_0; rewrite H.
Qed.

Lemma mnm_bigmaxc_seq p (lm : seq 'X_{1..n})  :
  all (fun m => (mdeg m == p)%N) lm -> ((U_( Ordinal n_gt0) *+ p)%MM \in lm) ->
  bigmaxC 0 (map mnm_to_C lm) = mnm_to_C (U_( Ordinal n_gt0) *+ p)%MM.
Proof.
move=> /allP lm_all_mdeg U_in.
apply: bigmaxcP; split; first by apply: map_f.
move=> i; rewrite size_map => i_size.
rewrite (nth_map 0%MM) //.
apply: mnm_bigmaxc; apply/eqP; apply: lm_all_mdeg.
by apply: mem_nth.
Qed.

Lemma mnm_bigmax_count_mem p (lm : seq 'X_{1..n}) :
  uniq r -> uniq lm ->
  all (fun m => (mdeg m == p.+1)%N) lm -> ((U_( Ordinal n_gt0) *+ p.+1)%MM \in lm) ->
    count_mem (bigmaxC 0 (map mnm_to_C lm)) (map mnm_to_C lm) == 1%N.
Proof.
move=> r_uniq lm_uniq lm_all_mdeg U_in.
move: (mnm_bigmaxc_seq lm_all_mdeg U_in) => H; rewrite H.
move/(nthP 0%MM): U_in => [] i i_size Hu; move: H.
rewrite -Hu -(nth_map 0%MM 0 mnm_to_C i_size).
set s := [seq _ | i <- lm]; move: i_size.
have eq_size : size lm = size s by rewrite size_map. 
rewrite eq_size; move => i_size H.
apply/nth_count_memP => //; rewrite -eq_size; move => j j_size.
move/all_nthP : lm_all_mdeg. move/(_ 0%MM j j_size) /eqP => Hmdeg.
rewrite /s.
move: (@mnm_bigmaxc_lt p (nth 0%MM lm j) Hmdeg r_uniq).
rewrite -Hu -!(nth_map 0%MM 0) -/s // ?eq_size //.
rewrite (nth_uniq _ j_size _ lm_uniq) ?eq_size //.
rewrite ltct_neqAle -{2}H bigmaxc_lect -?eq_size // andbT.
rewrite eq_sym (eq_sym j _).
by case: (boolP (i == j)) => /= _ ; [apply/negbFE | apply/negbTE].
Qed.


End LeC_ajouts.

Section ExtractSeq.

Lemma size_undup_tuple (T : eqType) (n : nat) (t : n.+1.-tuple T) :
  size (undup t) == (size (undup t)).-1.+1.
Proof.
rewrite prednK // lt0n size_eq0; apply/negP => /eqP Heq.
by move: (mem_tnth ord0 t); rewrite -mem_undup Heq in_nil.
Qed.

Lemma index_tnth0 (T : eqType) (n : nat) (t : n.+1.-tuple T) :
  index (tnth t ord0) t = 0%N.
Proof.
rewrite (tnth_nth (tnth t ord0)).
move: (tnth t ord0) => x0; move: (val t) => s {t}.
by case: s => [//= | x s /=]; rewrite eq_refl.
Qed.

Lemma extract_poly (n : nat) (a : n.+1.-tuple complexR) (alpha : n.+1.-tuple complexR) :
  (forall i : 'I_n.+1, tnth a i \is a Cint) ->
  (forall i : 'I_n.+1, tnth a i != 0) -> 
  (forall i : 'I_n.+1, (i != ord0) -> ltCt (tnth alpha i) (tnth alpha ord0)) ->
  let m := (size (undup alpha)).-1 in
  let t_alpha := Tuple (size_undup_tuple alpha) in
  exists (P : {mpoly complexR[m.+1]}), P!= 0 /\ P \is a mpolyOver m.+1 Cint /\
  (P.@[tnth (map_tuple Cexp t_alpha)] = Cexp_span a alpha) /\
  P \is 1.-homog. 
  (*all (fun x : 'X_{1..m.+1} => mdeg x == 1%N) (msupp P)*)
Proof.
move=> a_Cint a_neq0 alpha_bigmax m; rewrite -/m => t_alpha.
have eq_size_m : (size (undup alpha) = m.+1)%N.
  by move/eqP: (size_undup_tuple alpha) => ->.
have ord_c i : (index (tnth alpha i) t_alpha < m.+1)%N.
  by rewrite -[X in (_ < X)%N](size_tuple t_alpha) index_mem mem_undup mem_tnth.
have big_in : tnth alpha ord0 \in t_alpha by rewrite mem_undup mem_tnth.
have ord_c0 : tnth t_alpha ord0 = tnth alpha ord0.
  rewrite !(tnth_nth 0) /= [alpha]tuple_eta /= ifF //= /thead.
  apply/negP; move/tnthP => /= [i]; rewrite tnth_behead; move/eqP; apply/negP.
  rewrite neq_ltct; apply/orP; right; apply: alpha_bigmax.
  apply/negP; move/eqP => Heq.
  have: (nat_of_ord ((inord i.+1) : 'I_n.+1) != (@ord0 n)).
    by rewrite /= inordK -?lt0n ?ltnS.
  by rewrite Heq eq_refl.
pose c := [tuple \sum_(i < n.+1 | Ordinal (ord_c i) == j) (tnth a i) | j < m.+1].
exists (\sum_(j < m.+1) (tnth c j) *: 'X_j); split.
  rewrite -msupp_eq0 -size_eq0 (perm_eq_size (msupp_sum _ _ _)); first last.
  + move=> i j _ _ /negbTE i_neq_j x /=; apply/negP => /andP [].
    move/msuppZ_le; rewrite msuppX inE => /eqP ->.
    move/msuppZ_le; rewrite msuppX inE. 
    by move/eqP; rewrite mnmP; move/(_ j); rewrite !mnm1E eq_refl i_neq_j.  
  + by rewrite /index_enum -enumT enum_uniq.
  rewrite filter_predT size_flatten /shape -map_comp.
  rewrite -ssrcomplements.bignat_sumn sum_nat_eq0 negb_forall /=.
  apply/existsP; exists ord0; rewrite msuppMCX // tnth_map tnth_ord_tuple.
  rewrite (eq_bigl (fun i : 'I_n.+1 => i == ord0)) ?big_pred1_eq //.
  move=> i /=; apply/idP/idP => /eqP H; last first.
    rewrite H; apply/eqP /ord_inj; rewrite [RHS]/=.
    by rewrite -(index_tnth0 t_alpha) ord_c0.
  case: (boolP (i == ord0)) => [// | ].
  move/alpha_bigmax; rewrite -ord_c0 ltct_neqAle => /andP[/negbTE <- _].
  rewrite -H /= [X in _ == X](tnth_nth 0) /= nth_index //.
  by rewrite mem_undup mem_tnth.
split.
  apply: rpred_sum => j _ /=; apply: mpolyOverZ; last by apply: mpolyOverX.
  by rewrite tnth_map; apply: rpred_sum => i _; apply: a_Cint.
split.
  rewrite rmorph_sum /= /Cexp_span.
  set g := (fun (i : 'I_n.+1) => (tnth a i * Cexp (tnth alpha i))).
  rewrite (eq_bigr g); last by move=> i _; rewrite /g.
  rewrite (partition_big (fun i :'I_n.+1 => Ordinal (ord_c i)) predT) /=; last by [].
  apply: eq_bigr => j _; rewrite tnth_map tnth_ord_tuple /= mevalZ mevalX /g.
  rewrite tnth_map big_distrl /=; apply: eq_bigr => i /eqP <- .
  congr (tnth a i * Cexp _) => /=; rewrite (tnth_nth 0) /=.
  by apply: nth_index; rewrite /t_alpha mem_undup mem_tnth.
apply/allP => x /msupp_sum_le.
rewrite filter_predT.
have H_flatten_subset f g (s : seq 'I_m.+1) : (forall x, {subset f x <= [:: g x]}) -> 
    {subset (flatten [seq f x | x <- s]) <= (flatten [seq [:: g x] | x <- s])}.
  move=> H_subset u /flatten_mapP [] su su_in u_in_su; apply/flatten_mapP.
  by exists su => //; apply: H_subset.
move/(H_flatten_subset _ _ (fun i => U_( i)%MM)).
have H_subset : forall x0 : 'I_m.+1, {subset msupp (tnth c x0 *: 'X_x0) <= [:: U_( x0)%MM]}.
  by move=> i u; move/msuppZ_le; rewrite msuppX.
move/(_ H_subset); rewrite (map_comp (fun u => [:: u]) (fun i => U_( i)%MM)).
by rewrite ssrcomplements.flatten_seq1; move/mapP => [] i _ -> /=; rewrite mdeg1.
Qed.

Lemma extract_Cexp_span (n : nat) (P : {mpoly complexR[n.+1]}) (alpha : n.+1.-tuple complexR) l :
  (forall i : 'I_n.+1, algebraic (tnth alpha i)) -> P \is a mpolyOver n.+1 Cint -> 
  P != 0 -> exists m : nat, size (msupp P) = m.+1 /\
  exists (bla : (m.+1.-tuple complexR) * (m.+1.-tuple complexR)),
    (forall i : 'I_m.+1, tnth bla.1 i != 0) /\
    (forall i : 'I_m.+1, tnth bla.1 i \is a Cint) /\
    (forall i : 'I_m.+1, algebraic (tnth bla.2 i)) /\                            
    (P.@[tnth (map_tuple Cexp alpha)] = Cexp_span bla.1 bla.2) /\ 
    (uniq alpha -> P \is 1.-homog -> uniq bla.2) /\
    (uniq alpha -> (U_( ord0) *+ l.+1)%MM \in (msupp P) -> 
      (P \is l.+1.-homog) ->
      (forall i : 'I_n.+1, (i != ord0) -> ltCt (tnth alpha i) (tnth alpha ord0)) ->
      (forall i : 'I_m.+1, (nat_of_ord i != index (U_( ord0) *+ l.+1)%MM (msupp P)) ->
      ltCt (tnth bla.2 i) (nth 0 bla.2 (index (U_( ord0) *+ l.+1)%MM (msupp P))))).
Proof.
move=> alpha_alg P_over P_neq0.
set m := (size (msupp P)).-1; exists m.
have eq_size_m : size (msupp P) = m.+1.
  by rewrite /m prednK // lt0n size_eq0 msupp_eq0.
have def_tsuppP : size (msupp P) == m.+1 by rewrite eq_size_m.
set t_suppP := Tuple def_tsuppP; split; [rewrite eq_size_m // | ].
exists (map_tuple ((@mcoeff n.+1 complexR_ringType)^~ P) t_suppP,
   map_tuple (fun (m : 'X_{1.. n.+1}) => \sum_(i < n.+1) ((tnth alpha i) *+ m i)) t_suppP).
split; first by move=> i /=; rewrite tnth_map -mcoeff_msupp mem_tnth.
split; first by move=> i /=; rewrite tnth_map; move/mpolyOverP: P_over.
split.
  move=> i /=; rewrite tnth_map /algebraic.
  apply: big_ind; first by apply: algebraic0.
    by move=> x y Hx Hy; apply: algebraic_add.
  move=> j _; move: ((tnth t_suppP i) j); elim.
    by rewrite mulr0n; apply: algebraic0.
  by move=> k alg_k; rewrite mulrS; apply: algebraic_add => //; apply: alpha_alg.
split.
  rewrite /= /Cexp_span mevalE -[msupp P]/(val t_suppP) big_tuple.
  apply: eq_bigr => i _ ; rewrite !tnth_map (big_morph _ Cexp_morph Cexp0).
  congr (P@_(tnth _ _) * _); apply: eq_bigr => j _.
  by rewrite tnth_map CexpRX.
split.
  move=> alpha_uniq H.
  have Hmieux x : x \in msupp P -> [exists i, (x == U_( i))%MM].
    by move=> x_msupp; move/allP: H; move/(_ x x_msupp); rewrite /= mdeg_eq1.
  pose t := [seq (tnth alpha i) | i <- [seq j <- index_enum( ordinal_finType n.+1) 
       | (U_( j)%MM \in msupp P)]].
  have t_uniq : uniq t.
    rewrite map_inj_in_uniq.
      by apply: filter_uniq; rewrite /index_enum -enumT enum_uniq.  
    move=> i j _ _; rewrite !(tnth_nth 0) => /eqP.
    by rewrite nth_uniq ?size_tuple //=; move/eqP; apply: ord_inj.
  apply: (@ssrcomplements.uniq_nth _ 0); rewrite size_map.
  set p := size _ => i j pre_ord_i pre_ord_j i_neq_j.
  rewrite !(nth_map (0%MM)) ?/p //.
  set mi := nth _ _ i; set mj := nth _ _ _.
  suff le_pn : (p <= n.+1)%N.
    move/existsP: (Hmieux _ (mem_nth 0%MM pre_ord_i)) => [] ui /eqP; rewrite -/mi => Hi.
    move/existsP: (Hmieux _ (mem_nth 0%MM pre_ord_j)) => [] uj /eqP; rewrite -/mj => Hj.
    rewrite Hi Hj.
    have ord_i:= (leq_trans pre_ord_i le_pn).
    have ord_j:= (leq_trans pre_ord_j le_pn).
    rewrite [X in _ != X](bigD1 uj) // [X in X != _](bigD1 ui) //=.
    rewrite !mnm1E /= !eq_refl /= !mulr1n !big1 ?addr0 ?(tnth_nth 0); first last.
    + by move=> u /negbTE eq_i; rewrite mnm1E eq_sym eq_i /= mulr0n.
    + by move=> u /negbTE eq_j; rewrite mnm1E eq_sym eq_j /= mulr0n.
    rewrite (@nth_uniq _ 0 alpha ui uj  _ _ alpha_uniq) ?size_tuple //=.
    move: i_neq_j.
    rewrite -(@nth_uniq _ 0%MM (in_tuple (msupp P)) i j _ _ _) ?size_tuple //=.
    rewrite -/mi -/mj Hi Hj => /negP Heq; apply/negP => /eqP.
    by move/ord_inj => u_eq; apply: Heq; rewrite u_eq eq_refl.
  pose s := [seq U_( i)%MM  | i <- index_enum (ordinal_finType n.+1)].
  rewrite /p /=.
  have {3}-> : n.+1 = size s.
    by rewrite size_map /index_enum -enumT /= size_enum_ord.
  apply: (@uniq_leq_size _ (msupp P) s (msupp_uniq _)) => m1 m1_in.
  move/Hmieux: m1_in => /existsP [] k /eqP ->; rewrite /s mem_map.
    by rewrite /index_enum -enumT mem_enum.
  move=> u v; move/mnmP; move/(_ v); rewrite !mnm1E eq_refl /=.
  by move/eqP; rewrite eqb1; move/eqP => ->.
move=> uniq_alpha; set n0 := @ord0 n.
move=> U_in P_mdeg H.
have: bigmaxC 0 alpha = tnth alpha n0.
  apply: bigmaxcP => /=; split; first by apply: mem_tnth.
  move=> i; rewrite size_tuple => ord_i; rewrite lect_eqVlt. 
  rewrite -[i]/(nat_of_ord (Ordinal ord_i)) -tnth_nth.
  case: (boolP (Ordinal ord_i == n0)) => [/eqP -> | Heq].
    by rewrite eq_refl orTb.
  by apply/orP; right; apply: H.    
rewrite (tnth_nth 0) => big_alpha i i_neq0 /=; set m1 := tnth t_suppP i.
rewrite -[(fun _ => _)]/(mnm_to_C alpha)  -[msupp P]/(val t_suppP).
have index_ord : (index (U_( n0) *+ l.+1)%MM t_suppP < m.+1)%N.
  by rewrite -[X in (_ < X)%N](size_tuple t_suppP) index_mem.
rewrite tnth_map (nth_map 0%MM) ?size_tuple // nth_index //.
rewrite mnm_bigmaxc_lt //=; last first.
  apply/eqP; rewrite (tnth_nth 0%MM) /=. 
  move/(all_nthP 0%MM): P_mdeg; move/(_ i) => Hap; apply: Hap.
  by rewrite eq_size_m.
rewrite (tnth_nth 0%MM) /= -(nth_index 0%MM U_in).
by rewrite nth_uniq ?eq_size_m //=.
Qed.

(*
Lemma rot_nth (T : eqType) (n : nat) (m : nat) (s : m.+1.-tuple T) (x0 : T) (i : 'I_m.+1) :
  (n < m.+1)%N -> nth x0 (rot n s) i = nth x0 s ((n + i) %% m.+1)%N.
Proof.
move=> Hn.
rewrite /rot.
rewrite nth_cat nth_drop size_drop size_tuple.
case: ifP.
  by rewrite ltn_subRL /=; move/modn_small => ->.
move/negbT; rewrite -leqNgt leq_subLR -leq_subLR.
have -> : (i - (m.+1 - n) = (n + i - m.+1))%N.
  rewrite subnBA; last by rewrite leq_eqVlt Hn orbT.
  by rewrite addnC.
rewrite leq_subLR; move => H.
have Hineq : (n + i - m.+1 < m.+1)%N.
  rewrite -[X in (_ < X)%N](addnK m.+1); apply: ltn_sub2r.
    by rewrite -{1}[m.+1]addn0 ltn_add2l.
  apply: (@ltn_trans (n + m.+1)%N).
    by rewrite ltn_add2l.
  by rewrite ltn_add2r.
rewrite nth_take; last first.
  by rewrite -subn_gt0 subnBA // subnDl subn_gt0.
congr (nth x0 s _).
rewrite -(modn_small Hineq).
apply/eqP; rewrite eq_sym eqn_mod_dvd ?subKn //.
by apply: leq_subr.
Qed.

Lemma rot_tnth (T : eqType) (n : nat) (m : nat) (s : m.+1.-tuple T) (i : 'I_m.+1) :
  (n < m.+1)%N -> tnth (Tuple (rot_tupleP n s)) i = 
    tnth s (Ordinal (ltn_pmod (n + i) (ltn0Sn m))).
Proof.
move=> Hineq.
rewrite (tnth_nth (tnth s ord0)).
rewrite [in RHS](tnth_nth (tnth s ord0)) /=.
by apply: rot_nth.
Qed.

Lemma rot_nth_propre (T : eqType) (n : nat) (m : nat) (s : m.+1.-tuple T) (x0 : T) (i : nat) :
  (n < m.+1)%N -> (i < m.+1)%N -> nth x0 (rot n s) i = nth x0 s ((n + i) %% m.+1)%N.
Proof.
move=> Hn ord_i.
rewrite -[i]/(nat_of_ord (Ordinal ord_i)).
by apply: rot_nth.
Qed.
*) 


Lemma extract_Cexp_span_order (n : nat) (P : {mpoly complexR[n.+1]}) (alpha : n.+1.-tuple complexR) l :
  (forall i : 'I_n.+1, algebraic (tnth alpha i)) -> P \is a mpolyOver n.+1 Cint -> 
  P != 0 -> exists m : nat,
  exists (bla : (m.+1.-tuple complexR) * (m.+1.-tuple complexR)),
    (forall i : 'I_m.+1, tnth bla.1 i != 0) /\
    (forall i : 'I_m.+1, tnth bla.1 i \is a Cint) /\
    (forall i : 'I_m.+1, algebraic (tnth bla.2 i)) /\                            
    (P.@[tnth (map_tuple Cexp alpha)] = Cexp_span bla.1 bla.2) /\ 
    (uniq alpha -> P \is 1.-homog -> uniq bla.2) /\
    (uniq alpha -> (U_( ord0) *+ l.+1)%MM \in (msupp P) -> 
      P \is l.+1.-homog ->
      (forall i : 'I_n.+1, (i != ord0) -> ltCt (tnth alpha i) (tnth alpha ord0)) ->
      (forall i : 'I_m.+1, (i != ord0) ->
      ltCt (tnth bla.2 i) (tnth bla.2 ord0))).
Proof.
move=> alg_alpha P_Cint P_neq0.
move: (extract_Cexp_span l alg_alpha P_Cint P_neq0) => [] m [] eq_m [] [] tcoeff texp /=.
move=> [] tcoeff_neq0 [] tcoeff_Cint [] texp_algebraic [] eq_span [] cond1 cond2.
exists m.
set i_max := index (U_( ord0) *+ l.+1)%MM (msupp P).
case: (boolP (i_max < m.+1)%N).
  move=> ord_imax.
  have size_order_tuple : size (Ordinal ord_imax :: 
      rem (Ordinal ord_imax) (index_enum (ordinal_finType m.+1))) == m.+1.
    rewrite /= size_rem.
      by rewrite /index_enum -enumT size_enum_ord.
    by apply: mem_index_enum.
  pose tuple_order := Tuple size_order_tuple.
  pose Tcoeff := nosimpl (map_tuple (tnth tcoeff) tuple_order).
  pose Texp := nosimpl (map_tuple (tnth texp) tuple_order).
  exists (Tcoeff, Texp); rewrite /=.
  split; first by move=> i; rewrite /Tcoeff tnth_map.
  split; first by move=> i; rewrite /Tcoeff tnth_map.
  split; first by move=> i; rewrite /Texp tnth_map.
  split.
    rewrite eq_span /Texp /Tcoeff /Cexp_span.
    rewrite [RHS](eq_bigr (fun i => tnth tcoeff (tnth tuple_order i) * 
                           Cexp (tnth texp (tnth tuple_order i)))) /=.
    rewrite [LHS](big_rem (Ordinal ord_imax)) ?mem_index_enum //=.
      by rewrite -(big_tuple _ _ tuple_order predT 
        (fun i => tnth tcoeff i * Cexp (tnth texp i))) /= big_cons.
    by move=> i _; rewrite !tnth_map.
  split.
    move/cond1=> H_int; move/H_int => uniq_texp.
    have : uniq Texp.
      rewrite (@perm_eq_uniq _ _ texp) // /Texp {2}[texp]tuple_map_ord.
      apply: perm_map; rewrite /= perm_eq_sym /index_enum -enumT.
      by apply: perm_to_rem; apply: mem_enum.
    by done.
  move=> uniq_alpha U_in all_deg ltct_alpha; move: cond2.
  move/(_ uniq_alpha U_in all_deg ltct_alpha)=> Hmax_texp i /negP i_neq0.
  rewrite !tnth_map; set j := tnth _ i.
  rewrite [tnth tuple_order _](tnth_nth ord0) /=.
  rewrite [X in ltct _ X](tnth_nth 0) /= .
  apply: Hmax_texp; apply/negP=> /eqP; rewrite -/i_max.
  rewrite -[i_max]/(nat_of_ord (Ordinal ord_imax)); move/ord_inj.
  have -> : Ordinal ord_imax = tnth tuple_order (@ord0 m) by [].
  rewrite /j.
  rewrite !(tnth_nth ord0); move/eqP.
  rewrite nth_uniq // ?size_tuple //.
  by rewrite /= mem_remF /= ?rem_uniq // /index_enum -enumT enum_uniq.
rewrite -{1}eq_m /i_max index_mem => /negbTE U_notin.
exists (tcoeff, texp); rewrite /=.
split; first by [].
split; first by [].
split; first by [].
split; first by [].
split; first by [].
by rewrite U_notin.
Qed.

End ExtractSeq.

End Theory.


Section Wlog1.

Variable pre_l : nat.
Hypothesis pre_l_gt0 : (0%N < pre_l)%N.
Variable pre_alpha : pre_l.-tuple complexR.
Hypothesis pre_alpha_uniq : uniq pre_alpha.
Hypothesis pre_alpha_algebraic : forall i : 'I_pre_l, algebraic (tnth pre_alpha i).
Variable pre_a : pre_l.-tuple complexR.
Hypothesis pre_a_neq0 : forall i : 'I_pre_l, (tnth pre_a i) != 0.
Hypothesis pre_a_algebraic : forall i : 'I_pre_l, algebraic (tnth pre_a i).
Hypothesis pre_Lindemann_false : Cexp_span pre_a pre_alpha == 0.

 
(* Un peu d'ordre pour tracker les alpha *)
Definition alpha_max := bigmaxC 0 pre_alpha.

Lemma index_alpha_max : (index alpha_max pre_alpha < pre_l)%N.
Proof.
rewrite -{2}(size_tuple pre_alpha) index_mem.
by apply: bigmaxc_mem; rewrite size_tuple.
Qed.

Definition l := pre_l.-1.

Lemma size_order_tuple : size (Ordinal index_alpha_max :: 
    rem (Ordinal index_alpha_max) (index_enum (ordinal_finType pre_l))) == l.+1.
Proof.
rewrite /= size_rem.
  by rewrite /index_enum -enumT size_enum_ord /l.
by apply: mem_index_enum.
Qed.

Definition tuple_order := Tuple size_order_tuple.

Definition alpha := nosimpl (map_tuple (tnth pre_alpha) tuple_order).

Lemma alpha_uniq : uniq alpha.
Proof. 
rewrite (@perm_eq_uniq _ _ pre_alpha) // /alpha {2}[pre_alpha]tuple_map_ord.
apply: perm_map; rewrite /= perm_eq_sym /index_enum -enumT.
by apply: perm_to_rem; apply: mem_enum.
Qed.

Lemma alpha_algebraic : forall i : 'I_l.+1, algebraic (tnth alpha i).
Proof. by move=> i; rewrite /alpha tnth_map. Qed.

Definition a := nosimpl (map_tuple (tnth pre_a) tuple_order).

Lemma a_neq0 : forall i : 'I_l.+1, (tnth a i) != 0.
Proof. by move=> i; rewrite /a tnth_map. Qed.

Lemma a_algebraic : forall i : 'I_l.+1, algebraic (tnth a i).
Proof. by move=> i; rewrite /a tnth_map. Qed.

Lemma Lindemann_false : Cexp_span a alpha == 0.
Proof.
rewrite /a /alpha; move/eqP: pre_Lindemann_false => <-; rewrite /Cexp_span.
rewrite (eq_bigr (fun i => tnth pre_a (tnth tuple_order i) * 
                           Cexp (tnth pre_alpha (tnth tuple_order i)))) /=.
  rewrite [X in _ == X](big_rem (Ordinal index_alpha_max)) ?mem_index_enum //=.
  by rewrite -(big_tuple _ _ tuple_order predT 
      (fun i => tnth pre_a i * Cexp (tnth pre_alpha i))) /= big_cons.
by move=> i _; rewrite !tnth_map.
Qed.

Lemma alpha_ord0 (i : 'I_l.+1) :
   (i != ord0) -> ltCt (tnth alpha i) (tnth alpha ord0).
Proof.
rewrite !tnth_map !(tnth_nth 0) /= nth_index; last first.
  by rewrite bigmaxc_mem ?size_tuple.
move=> /negP H; apply: (bigmaxc_ltct pre_alpha_uniq); rewrite ?size_tuple => //=.
rewrite -/alpha_max -[index alpha_max pre_alpha]/(nat_of_ord (Ordinal index_alpha_max)).
have -> : Ordinal index_alpha_max = nth (Ordinal pre_l_gt0) tuple_order (@ord0 l.+1) by [].
rewrite (tnth_nth (Ordinal pre_l_gt0)); apply/negP; move/eqP /ord_inj /eqP.
rewrite (@nth_uniq _ (Ordinal pre_l_gt0) tuple_order (nat_of_ord i) (nat_of_ord (@ord0 l.+1))).
+ by move/eqP => i_eq0; apply: H; apply/eqP; apply: ord_inj.
+ by rewrite size_tuple.
+ by rewrite size_tuple.
by rewrite /= mem_remF /= ?rem_uniq // /index_enum -enumT enum_uniq.
Qed.

(* Polynômes associés *)

(* polynôme de chaque a_i *)
Definition poly_a i := polyMin (a_algebraic i).

Lemma poly_a_neq0 i : poly_a i != 0.
Proof.
rewrite /poly_a -lead_coef_eq0.
by move/lt0r_neq0: (polyMin_lcoef_gt0 (a_algebraic i)); rewrite ZtoCE.
Qed.

(* produit de tous les polynomes *)
Definition prod_poly_a := \prod_(i : 'I_l.+1) (poly_a i).

Definition poly_b := (map_poly ZtoC prod_poly_a).

Lemma poly_b_Cint : poly_b \is a polyOver Cint.
Proof. by apply/polyOverP => i; rewrite /poly_b coef_map Cint_int. Qed.

Lemma poly_b_neq0 : poly_b != 0.
Proof.
rewrite /poly_b_Cint.
rewrite -lead_coef_eq0 (lead_coef_map_inj (@intr_inj complexR_numDomainType) 
      (rmorph0 (intmul1_rmorphism complexR_ringType))).
rewrite ZtoCE lead_coef_eq0 /prod_poly_a.
apply/prodf_neq0 => i _; apply: poly_a_neq0.
Qed.

Definition c := lead_coef poly_b.

Lemma c_Cint : c \is a Cint.
Proof. by rewrite /c /lead_coef coef_map Cint_int. Qed.

Lemma c_neq0 : c != 0.
Proof. by rewrite lead_coef_eq0; apply: poly_b_neq0. Qed.

(* on récupère l'ensemble des racines 
en séquence pour l'instant, on doit attendre pour la vraie notation 
et qu'on transforme en L.-tuple : b *)
Definition b_seq := seqroots poly_b.

Lemma perm_eq_b : 
  perm_eq (flatten [seq (seqroots (map_poly ZtoC (poly_a i))) | i : 'I_l.+1]) b_seq.
Proof.
set f := (fun (i : 'I_l.+1) => (map_poly ZtoC (poly_a i))).
set s := (fun (i : 'I_l.+1) => seqroots (f i)).
have a_in_s i : 
  tnth a i \in (s i).
  apply/seqrootsP. 
    rewrite -lead_coef_eq0 (lead_coef_map_inj (@intr_inj complexR_numDomainType) 
      (rmorph0 (intmul1_rmorphism complexR_ringType))).
    by move/lt0r_neq0: (polyMin_lcoef_gt0 (a_algebraic i)); rewrite ZtoCE.
  by apply: (polyMin_root (a_algebraic i)).
have in_a_s i : (index (tnth a i) (s i) < size (s i))%N by rewrite index_mem.
set deg_poly_a := (fun (i : 'I_l.+1) => size (seqroots (f i))).
set seq_s := [seq s i | i : 'I_l.+1].
have i_index_enum (i : 'I_l.+1) : (i < size (enum 'I_l.+1))%N by rewrite size_enum_ord.
have nth_s (i : 'I_l.+1) : nth [::] seq_s i = s i.
  rewrite ?size_map -?enumT //= /seq_s (nth_map ord0) //.
  by congr s; apply: ord_inj; rewrite nth_enum_ord.
have eq_l_size : size seq_s = l.+1 by rewrite size_map size_enum_ord.
have s_in_seq_s i : s i \in seq_s.
  apply/(nthP _); exists i; rewrite ?eq_l_size //.
set A := flatten seq_s.
rewrite /b_seq /=.
have -> : poly_b = \prod_(i : 'I_l.+1) (f i).
  by rewrite /poly_b rmorph_prod.
rewrite perm_eq_sym; apply: (perm_eq_trans (seqroots_prod _) _).   
  apply/allP => i Hi /=; rewrite /f map_poly_eq0_id0.
    by rewrite /poly_a; apply: polyMin_neq0.
  by rewrite intr_eq0 /poly_a lead_coef_eq0; apply: polyMin_neq0.
by rewrite /A /seq_s /s /index_enum -enumT; apply: perm_eq_refl.
Qed.

Definition L := (size b_seq).-1.
Lemma size_b : size b_seq == L.+1.
Proof.
rewrite /L prednK ?eq_refl // /b_seq seqroots_size.
move/negbTE : poly_b_neq0 => ->; rewrite -ltnS. 
move: poly_b_neq0; rewrite -size_poly_gt0; move/prednK => ->.
apply: (@root_size_gt1 _ (tnth a ord0) _ poly_b_neq0).
apply/(seqrootsP); first by apply: poly_b_neq0.
rewrite -(perm_eq_mem perm_eq_b).
apply/flattenP.
exists (seqroots (map_poly ZtoC (poly_a ord0))).
  apply: (map_f (fun i => seqroots( map_poly ZtoC (poly_a i)))).
  by rewrite mem_enum.
apply/seqrootsP.
  rewrite -lead_coef_eq0 (lead_coef_map_inj (@intr_inj complexR_numDomainType) 
      (rmorph0 (intmul1_rmorphism complexR_ringType))).
  by move/lt0r_neq0: (polyMin_lcoef_gt0 (a_algebraic ord0)); rewrite ZtoCE.
by apply: (polyMin_root (a_algebraic ord0)).
Qed.

Definition b := nosimpl (Tuple size_b).

Lemma eq_L_sizeb : L.+1 = size b.
Proof. by move/eqP: size_b => ->. Qed.

Lemma leq_l_L : (l.+1 <= L.+1)%N.
Proof.
rewrite eq_L_sizeb -(perm_eq_size perm_eq_b) size_flatten.
rewrite /shape -ssrcomplements.bignat_sumn /size big_map.
have eq_l : (l.+1 = \sum_(j <- enum 'I_l.+1) 1)%N.
  by rewrite sum1_size size_enum_ord.
rewrite {1}[l.+1]eq_l.
apply: (big_ind2 leq (leqnn 0)).
  by move=> n1 n2 p1 p2; apply: leq_add.
move=> i _; rewrite -/size seqroots_size. 
have : map_poly ZtoC (poly_a i) != 0.
  rewrite -lead_coef_eq0 (lead_coef_map_inj (@intr_inj complexR_numDomainType) 
      (rmorph0 (intmul1_rmorphism complexR_ringType))).
  rewrite ZtoCE lead_coef_eq0; apply/negP/negP; apply: poly_a_neq0.
move/negbTE => Cpoly_a_neq0.
rewrite Cpoly_a_neq0 -ltnS; rewrite prednK; last first.
  by rewrite lt0n size_poly_eq0 Cpoly_a_neq0.
apply: (@root_size_gt1 _ (tnth a i)); first by rewrite Cpoly_a_neq0.
by apply: (polyMin_root (a_algebraic i)).
Qed.


(* passer aux ensembles, et f : l.-tuple 'I_L, avec uniq f. *)
Lemma a_in_b : 
  {f : l.+1.-tuple 'I_L.+1 | uniq f & forall i : 'I_l.+1, (tnth a i) = (tnth b (tnth f i))}.
Proof.
set f := (fun (i : 'I_l.+1) => (map_poly ZtoC (poly_a i))).
set s := (fun (i : 'I_l.+1) => seqroots (f i)).
have a_in_s i : 
  tnth a i \in (s i).
  apply/seqrootsP. 
    rewrite -lead_coef_eq0 (lead_coef_map_inj (@intr_inj complexR_numDomainType) 
      (rmorph0 (intmul1_rmorphism complexR_ringType))).
    by move/lt0r_neq0: (polyMin_lcoef_gt0 (a_algebraic i)); rewrite ZtoCE.
  by apply: (polyMin_root (a_algebraic i)).
have in_a_s i : (index (tnth a i) (s i) < size (s i))%N by rewrite index_mem.
set deg_poly_a := (fun (i : 'I_l.+1) => size (seqroots (f i))).
set seq_s := [seq s i | i : 'I_l.+1].
have i_index_enum (i : 'I_l.+1) : (i < size (enum 'I_l.+1))%N by rewrite size_enum_ord.
have nth_s (i : 'I_l.+1) : nth [::] seq_s i = s i.
  rewrite ?size_map -?enumT //= /seq_s.
  rewrite (nth_map ord0 [::]) //.
  by congr s; apply: ord_inj; rewrite nth_enum_ord.
have eq_l_size : size seq_s = l.+1 by rewrite size_map size_enum_ord.
have s_in_seq_s i : s i \in seq_s.
  apply/(nthP _); exists i; rewrite ?eq_l_size //.
set A := flatten seq_s.
have perm_eq_A_b : perm_eq A b.
  rewrite /b /= /b_seq /=.
  have -> : poly_b = \prod_(i : 'I_l.+1) (f i).
    by rewrite /poly_b rmorph_prod.
  rewrite perm_eq_sym; apply: (perm_eq_trans (seqroots_prod _) _).
    apply/allP => i Hi /=; rewrite /f map_poly_eq0_id0.
      by rewrite /poly_a; apply: polyMin_neq0.
    by rewrite intr_eq0 /poly_a lead_coef_eq0; apply: polyMin_neq0.
  by rewrite /A /seq_s /s /index_enum -enumT; apply: perm_eq_refl.
set g_i := (fun i : 'I_l.+1 => (sumn (shape (take i seq_s))
      + index (tnth a i) (s i))%N).
have g i : ((g_i i) < L.+1)%N.
  have -> : L.+1 = size (flatten seq_s).
    by rewrite -(size_tuple b) -/A (perm_eq_size perm_eq_A_b).
  apply: (@nth_flatten_size _ [::]); rewrite ?eq_l_size //.
move/perm_eq_iotaP: perm_eq_A_b => H; move: (sig2_eqW(H 0)) => [t perm_t_iota eq_A_b].
have eq_L_size : size b = size t by rewrite (perm_eq_size perm_t_iota) size_iota size_tuple.
set h_j := (fun j => nth 0%N t j).
have h j : (j < L.+1)%N -> (h_j j < L.+1)%N.
  rewrite eq_L_sizeb eq_L_size => j_size.
  move: (mem_nth 0%N j_size); rewrite (perm_eq_mem perm_t_iota).
  move/nthP; move/(_ 0%N) => [] x; rewrite /h_j size_iota eq_L_size => x_size <-.
  by rewrite nth_iota ?add0n.
(* exists *)
exists [tuple (Ordinal ( h (g_i i) (g i))) | i < l.+1] => [|i]; last first.
(* égalité*)
  rewrite [X in tnth b X]tnth_map !tnth_ord_tuple /=.
  have -> : tnth b (Ordinal (h (g_i i) (g i))) = nth 0 A (Ordinal (g i)).
    rewrite (tnth_nth 0) eq_A_b /= (nth_map 0%N); first by [].
    by apply: (leq_trans (g i)); rewrite eq_L_sizeb eq_L_size.
  rewrite /A /= (@nth_flatten _ 0 [::]) ?eq_l_size //=.
(* injectivité *)
rewrite map_inj_uniq ?enum_uniq // => n p eq_ord; apply/eqP.
have Heq x : h_j (g_i x) = nat_of_ord (Ordinal (h (g_i x) (g x))); first by [].
have {Heq} : h_j (g_i n) = (h_j (g_i p)); first by rewrite (Heq n) (Heq p) eq_ord.
rewrite /h_j => /eqP; rewrite nth_uniq -?eq_L_size -?eq_L_sizeb => [|//|//|]; first last.
  by rewrite (perm_eq_uniq perm_t_iota); apply iota_uniq.
(* clean *)
move=> /eqP eq_g {H t perm_t_iota eq_A_b eq_L_size h_j h eq_ord}.
(* retour à une inégalité stricte *)
case: (boolP (n == p)) => //.
suff H (u : 'I_l.+1) (v : 'I_l.+1) : (u < v)%N -> (g_i u < g_i v)%N.
  by rewrite neq_ltn => /orP []; move/H; rewrite eq_g ltnn.
(* dem inégalité stricte *)
move=> {eq_g n p} leq_u_v; rewrite /g_i /shape /= !map_take -/shape.
have : (index (tnth a u) (s u) < size (s u))%N by rewrite index_mem.
rewrite -(ltn_add2l (sumn (take u (shape seq_s)))) => H.
apply: (leq_trans H) => {H}.
have -> : (sumn (take u (shape seq_s)) + size (s u)
        = sumn (take u.+1 (shape seq_s)))%N.
  rewrite (take_nth 0%N); last by rewrite size_map eq_l_size.
  rewrite -cats1 sumn_cat /= addn0; apply/eqP; rewrite eqn_add2l; apply/eqP.
  by rewrite (nth_map [::]) ?eq_l_size // nth_s.
apply: (@leq_trans (sumn (take v (shape seq_s)))).
  have -> : (nat_of_ord v = u.+1 + (v - u.+1))%N by rewrite subnKC.
  set w := (v - u.+1)%N.
  elim: w => [| w H]; rewrite ?addn0 ?leqnn //; apply: (leq_trans H) => {H}.
  rewrite addnS. 
  case: (boolP ((u.+1 + w)%N < size (shape seq_s))%N) => [H|].
    by rewrite (take_nth 0%N H) -cats1 sumn_cat -{1}[(sumn _)]addn0 leq_add2l.
  rewrite -leqNgt => H; rewrite (take_oversize H) take_oversize //.
  by apply: (leq_trans H).
by rewrite -[X in (X <= _)%N]addn0 leq_add2l leq0n.
Qed.

Lemma b_neq0 i : tnth b i != 0.
Proof.
have b_inb : (tnth b i) \in b by rewrite mem_tnth.
move: (perm_eq_mem perm_eq_b); move/(_ (tnth b i)); rewrite b_inb.
move/flatten_mapP => [u u_in].
apply/memPn; rewrite seqroots_neq0.
  rewrite coef_map /poly_a ZtoCE polyMin_coef0_neq0.
  by apply: a_neq0.  
rewrite -lead_coef_eq0 (lead_coef_map_inj (@intr_inj complexR_numDomainType) 
      (rmorph0 (intmul1_rmorphism complexR_ringType))) ZtoCE lead_coef_eq0.
by apply: poly_a_neq0.
Qed.


(* produit sur toutes les fonctions injectives de l dans L *)
Definition prod_Cexp_span_b :=
  \prod_(f : l.+1.-tuple 'I_L.+1 | uniq f) 
    Cexp_span [tuple (tnth b (tnth f i)) | i < l.+1] alpha.

(* on retrouve le eq0 *)
Lemma prod_Cexp_span_b_eq0 : prod_Cexp_span_b == 0.
Proof.
move: (svalP a_in_b); set t := sval a_in_b; move=> [] uniq_t val_t.
rewrite /prod_Cexp_span_b (bigD1 _ uniq_t) mulf_eq0 /=; apply/orP; left.
move/eqP: Lindemann_false => <-; apply/eqP; congr Cexp_span.
by apply: eq_from_tnth => i; rewrite tnth_map /= tnth_ord_tuple.
Qed.

(* on le reconnait en tant que poly de poly pour faire du th sym *)
Definition R : {mpoly {mpoly complexR[l.+1]}[L.+1]} :=
  \prod_(f : l.+1.-tuple 'I_L.+1 | uniq f) \sum_(i : 'I_l.+1) 'X_i *: 'X_(tnth f i).

(* egalité valeurs/horner *)
Lemma prod_Cexp_span_b_eq0_horner :
  (R.@[tnth (map_tuple (@mpolyC l.+1 complexR_ringType) b)]).@[tnth (map_tuple Cexp alpha)]
    = prod_Cexp_span_b.
Proof.
rewrite /R /= !rmorph_prod; apply: eq_bigr => t t_uniq /=.

have -> : (\sum_(i < l.+1) 'X_i *: 'X_(tnth t i)).@[tnth (map_tuple 
    (mpolyC l.+1 (R:=complexR_ringType)) b)].@[tnth (map_tuple Cexp alpha)] =
    \sum_(i < l.+1) ('X_i *: 'X_(tnth t i)).@[tnth 
    (map_tuple (mpolyC l.+1 (R:=complexR_ringType)) b)].@[
    tnth (map_tuple Cexp alpha)] by rewrite -!rmorph_sum.
apply: eq_bigr => i _; rewrite mulrC mevalZ mevalX tnth_map.
rewrite [X in _ = _ * X]tnth_map tnth_ord_tuple rmorphM /= mevalX tnth_map.
by congr (Cexp _ *_); rewrite mevalC.
Qed.

(* coefficients entiers pour th sym *)
Lemma R_overCint : 
  R \is a (mpolyOver L.+1 (mpolyOver l.+1 Cint)).
Proof.
apply: rpred_prod => f uniq_f /=.
apply: rpred_sum => i _ /=; rewrite -mul_mpolyC.
by apply: rpredM => /=; rewrite ?mpolyOverC /= mpolyOverX.
Qed.

(* le poly est sym *)
Lemma R_sym :
  R \is symmetric.
Proof.
apply/issymP => s; rewrite rmorph_prod /R /=.
pose h := (fun (f : l.+1.-tuple 'I_L.+1) => [tuple of [seq s i | i <- f]] : l.+1.-tuple 'I_L.+1).
pose F := (fun (f : l.+1.-tuple 'I_L.+1)
     => (\sum_(i < l.+1) 'X_i *: 'X_(tnth f i)) : {mpoly {mpoly complexR[l.+1]}[L.+1]}).            
have H_eqF (f : l.+1.-tuple 'I_L.+1) : uniq f -> msym s (\sum_(i < l.+1) 'X_i *:
    'X_(tnth f i)) = F (h f).
  move=> _; rewrite rmorph_sum /=; apply: eq_bigr => i _.
  rewrite msymZ msymX; congr ('X_i *: @mpolyX _ _ _).
  apply/mnmP => j; rewrite mnmE mnmE mnm1E tnth_map.
  move: (tnth f i) => x /=; rewrite /nat_of_bool.
  case: (ifP _) => [/eqP -> | H]; first by rewrite permKV eq_refl.
  by case: (ifP _) => [/eqP Hr | //]; rewrite -Hr permK eq_refl in H.  
have H_eqP : forall f : l.+1.-tuple 'I_L.+1, uniq f = uniq (h f). 
  by move=> f; rewrite map_inj_uniq //=; apply: perm_inj.
rewrite (eq_bigr (fun f => F(h f)) H_eqF) (eq_bigl _ _ (H_eqP)).
rewrite [RHS](eq_bigr (fun f => F f)) //.
rewrite -(big_map h (fun (f : l.+1.-tuple 'I_L.+1) => uniq f) F).
apply: eq_big_perm.
pose h1 := (fun (f : l.+1.-tuple 'I_L.+1) =>
              [tuple of [seq (fingroup.invg s) i | i <- f]] : l.+1.-tuple 'I_L.+1).
have H_uniq : uniq (index_enum (tuple_finType l.+1 (ordinal_finType L.+1))).
  by rewrite /index_enum -enumT enum_uniq.
apply: (uniq_perm_eq _ H_uniq).
  apply: (@map_uniq _ _ h1) => //=; rewrite mapK //=.
  move => x; rewrite /h /h1 /=; apply: eq_from_tnth => i.
  by rewrite !tnth_map permK.
move=> f; rewrite mem_index_enum; apply/mapP.
exists (h1 f); rewrite ?mem_index_enum //.
rewrite /h /h1 /=; apply: eq_from_tnth => i.
by rewrite !tnth_map permKV.
Qed.

(* on perd un mpoly ! *)
Definition U := (c ^+ (msize R)) *: R.@[tnth (map_tuple (@mpolyC l.+1 complexR_ringType) b)].

Lemma U_overCint : U \is a mpolyOver l.+1 Cint.
Proof.
have eq_l : seqroots poly_b = b by [].
by apply: (sym_fundamental_seqroots_empil eq_l poly_b_Cint R_overCint R_sym).
Qed.

Lemma X1_in_U (t : l.+1.-tuple 'I_L.+1) : 
  U_( ord0)%MM \in msupp
          (((\sum_(i < l.+1) 'X_i *: 'X_(tnth t i))).@[
          tnth (map_tuple (mpolyC l.+1 (R:=complexR_ringType)) b)]).
rewrite rmorph_sum /=.
rewrite (eq_bigr (fun i0 => (tnth b (tnth t i0)) *: 'X_i0)); last first.
  by move=> j _; rewrite mevalZ mevalX tnth_map -mul_mpolyC mulrC.
rewrite (bigD1 ord0) //= (perm_eq_mem (msuppD _)).
  rewrite mem_cat; apply/orP; left; rewrite msuppMCX ?inE ?eq_refl //.
  by apply: b_neq0.
move=> y /=; apply/nandP.
case: (boolP (y == U_( ord0)%MM)) => [/eqP ->| Hx].
  right; apply/negP; move/msupp_sum_le => /=.
  rewrite (@eq_map _ _ _ (fun i : 'I_l.+1 => [:: U_( i)]%MM)).
    have -> : [seq [:: U_( j)%MM] | j <- index_enum (ordinal_finType l.+1) & j != ord0] =
    [seq [:: x] | x <- [seq U_( j)%MM | j <- [seq z <- 
           index_enum (ordinal_finType l.+1) | z != ord0]]].
      by rewrite -map_comp /=; apply: eq_map => j.
    rewrite ssrcomplements.flatten_seq1.
    move/mapP => [] j; rewrite mem_filter => /andP[] /negbTE j_neq0 _.
    by move/mnmP; move/(_ ord0); rewrite !mnm1E eq_refl j_neq0.
  by move=> j; rewrite msuppMCX //; apply: b_neq0.
left; rewrite msuppMCX; last by apply: b_neq0.
by rewrite mem_seq1.
Qed.

Lemma U_neq0 : U != 0.
Proof.
rewrite /U scaler_eq0 expf_eq0.
move/negbTE: c_neq0 => ->; rewrite andbF orFb /R rmorph_prod /=.
apply/prodf_neq0 => i _; apply/negP => /eqP H.
by move: (X1_in_U i); rewrite H msupp0 in_nil.
Qed.

Definition deg_U := (\sum_(f : l.+1.-tuple 'I_L.+1 | uniq f) 1)%N.-1.


Lemma U_in_all : 
     (U_( ord0) *+ deg_U.+1)%MM \in msupp U /\ 
      U \is deg_U.+1.-homog.
Proof.
rewrite /U.
move H : (c^+ msize R) => r.
have r_neq0 : (r != 0) by rewrite -H expf_neq0 // c_neq0.
move=> {H}; rewrite /R /deg_U.
set s := (index_enum (tuple_finType l.+1 (ordinal_finType L.+1))).
have sum_lt0 : (0 < \sum_(f <- s | uniq f) 1)%N.
  rewrite lt0n sum_nat_eq0 negb_forall; apply/existsP.
  exists [tuple (widen_ord leq_l_L i) | i < l.+1].
  rewrite negb_imply /= andbT map_inj_uniq ?enum_uniq //.
  move=> i j H_widen; apply: ord_inj.
  by rewrite -[nat_of_ord _]/(nat_of_ord (widen_ord leq_l_L _)) H_widen.
rewrite (prednK sum_lt0).
have size_s : (0 < size s)%N.
  move: sum_lt0; rewrite sum1_count => lt0.
  by apply: (leq_trans lt0); apply: count_size.
case/lastP: s size_s sum_lt0 => [//= | s x] _.
elim: s => [/= | y s ihs].
  rewrite (perm_eq_mem (msuppZ _ _)) //.
  rewrite big_mkcond big_seq1.
  case: (boolP (uniq x)) => [uniq_x _ | //].
  split.
    rewrite mulm1n big_mkcond big_seq1 uniq_x.
    by apply: X1_in_U.
  apply: rpredZ; rewrite big_mkcond big_seq1 uniq_x.
  rewrite rmorph_sum /=.
  apply: rpred_sum => i _; rewrite mevalZ mevalX mulrC tnth_map mul_mpolyC.
  by apply: rpredZ; rewrite dhomogX /= mdeg1.
rewrite rcons_cons big_cons /=.
case: (boolP (uniq y)) => [uniq_y | /=].
  rewrite add1n ltnS leq_eqVlt => /orP [/eqP H | ].
    have Hvide : (fun i : tuple_eqType l.+1 (ordinal_eqType L.+1) => 
          (i \in rcons s x) && uniq i) =1 xpred0.
      move=> i; apply/negP/negP; rewrite negb_and -implybE; apply/implyP.
      move/(nthP [tuple (@ord0 L) | i < l.+1]) => [j ord_j eq_j].
      move/eqP: H; rewrite eq_sym (big_tnth) sum_nat_eq0.
      move/forallP => /=; move/(_ (Ordinal ord_j)).
      by rewrite -leqn0 ltn0 (tnth_nth [tuple (@ord0 L) | i < l.+1]) eq_j.
    split.
      rewrite (perm_eq_mem (msuppZ _ _)) //.
      rewrite big_cons uniq_y mevalM big_seq_cond big_pred0 // mulm1n.
      rewrite [X in (_ * meval _ X)]big_seq_cond.
      rewrite [X in (_ * meval _ X)]big_pred0 // meval1 mulr1.
      by apply X1_in_U.
    rewrite -H big_cons uniq_y.
    apply: dhomogZ; rewrite mevalM -[X in X.-homog]add1n.
    apply: dhomogM.
      rewrite rmorph_sum /=.
      apply: rpred_sum => i _; rewrite mevalZ mevalX mulrC tnth_map mul_mpolyC.
      by apply: rpredZ; rewrite dhomogX /= mdeg1.
    rewrite big_seq_cond big_pred0 // meval1.
    by apply: dhomog1.
  move/ihs => [] ihs_in _.
  split.
    rewrite mulmS big_cons uniq_y mevalM.
    rewrite rmorph_sum /= mcoeff_msupp big_distrl /= mcoeffZ.
    rewrite (@big_morph _ _ _ 0 _ _ _ (@mcoeffD _ _ _)); last first.
      by rewrite mcoeff0.
    rewrite big_ord_recl /= mulrDr.
    set p := r * \sum_(i < l) _.
    move: ihs_in; set p_ihs := _.@[ _ ]; rewrite mcoeff_msupp; move=> ihs_in.
    suff -> : p = 0.
      rewrite mevalZ mevalX tnth_map [X in X * p_ihs]mulrC -mulrA mcoeffCM addr0.
      rewrite mulrCA; apply: mulf_neq0; first by apply: b_neq0.
      by rewrite -mcoeffZ scalerAr mulrC mcoeffMX.
    rewrite /p big_distrr /=; apply: big1 => i _.
    rewrite mevalZ mevalX tnth_map ['X_ _ * _]mulrC -mulrA mcoeffCM.
    rewrite -mulrCA; apply/eqP; rewrite mulf_eq0; apply/orP; right.
    rewrite -mcoeffZ mcoeff_eq0 mulrC; apply/negP.
    rewrite scalerAl (perm_eq_mem (msuppMX _ _)).
    set u_dhomog := msupp _ => {p ihs}.
    set sm := [seq _ | _ <- _].
    move/(nthP 0%MM) => [] k ord_k.
    apply/mnmP; move/(_ (lift ord0 i)).    
    rewrite (nth_map 0%MM); last by move: ord_k; rewrite /sm size_map.    
    by rewrite !mnmDE mulmnE !mnm1E eq_refl add0n muln0 /=.
  rewrite big_cons uniq_y mevalM -[X in X.-homog]add1n scalerAr.
  apply: dhomogM => //; rewrite rmorph_sum /=.
  apply: rpred_sum=> i _; rewrite mevalZ mevalX mulrC tnth_map mul_mpolyC.
  by apply: rpredZ; rewrite dhomogX /= mdeg1.
move=> /negbTE uniq_y.
move/ihs => [] ihs_in ihs_homog. 
by split; rewrite big_cons uniq_y.
Qed.

(* on repasse au Cexp_span *)
Lemma extract_good_C_span :
  exists n : nat, (0%N < n)%N /\ (exists bla : n.-tuple complexR * n.-tuple complexR,
    (uniq bla.2) /\ (forall i : 'I_n, algebraic (tnth bla.2 i)) /\
    (forall i : 'I_n, (tnth bla.1 i) != 0) /\ 
    (forall i : 'I_n, (tnth bla.1 i) \is a Cint) /\ Cexp_span bla.1 bla.2 == 0).
Proof.
move: (extract_Cexp_span_order deg_U alpha_algebraic U_overCint U_neq0).
move=> [] m_cgamma [] [] c gamma [] /= c_neq0 [] c_Cint [] gamma_algebraic [].
rewrite /U mevalZ prod_Cexp_span_b_eq0_horner.
move/eqP: prod_Cexp_span_b_eq0 => ->; rewrite mulr0;  move => Cexp_eq0 [] _ H.
move: alpha_uniq => /=; move/H => {H}.
move: U_in_all => [] U_in U_mdeg.
move/(_ U_in); move/(_ U_mdeg); move/(_ alpha_ord0) => ltct_gamma.
move: (extract_poly c_Cint c_neq0 ltct_gamma).
set pre_eta := undup gamma; set m_eta := (size pre_eta).-1; set eta := Tuple _.
move=> [P [P_neq0 [P_Cint [P_eq P_deg_all]]]].
have eta_algebraic i : algebraic (tnth eta i).
  rewrite (tnth_nth 0) /=.
  have : eta`_i \in gamma.
    by rewrite -mem_undup -/pre_eta mem_nth ?size_tuple //=.
  move/(nthP 0) => [j]; rewrite (size_tuple gamma) => j_size <-.
  rewrite -[j]/(nat_of_ord (Ordinal j_size)).
  by move: (gamma_algebraic (Ordinal j_size)); rewrite (tnth_nth 0) /=.
move: (extract_Cexp_span_order 0%N eta_algebraic P_Cint P_neq0).
move=> [] m_kkappa [] [] k kappa [] /= k_neq0 [] k_Cint [] kappa_algebraic [] eq_k [] H _.
move:(H (undup_uniq gamma) P_deg_all) => uniq_kappa.
exists m_kkappa.+1; split; first by [].
exists (k, kappa); rewrite /=; split; first by exact uniq_kappa.
split; first by exact: kappa_algebraic.
split; first by exact: k_neq0.
split; first by exact: k_Cint.
by rewrite -eq_k P_eq -Cexp_eq0.
Qed.

  
End Wlog1. 



Theorem wlog1_Lindemann :
  (forall (l : nat) (alpha : l.-tuple complexR) (a : l.-tuple complexR),
  (0%N < l)%N -> uniq alpha -> (forall i : 'I_l, algebraic (tnth alpha i)) ->
  (forall i : 'I_l, (tnth a i) != 0) -> (forall i : 'I_l, (tnth a i) \in Cint) ->
  (Cexp_span a alpha != 0)) ->
  forall (l : nat) (alpha : l.-tuple complexR) (a : l.-tuple complexR),
  (0%N < l)%N -> uniq alpha -> (forall i : 'I_l, algebraic (tnth alpha i)) ->
  (forall i : 'I_l, (tnth a i) != 0) -> (forall i : 'I_l, algebraic (tnth a i)) ->
  (Cexp_span a alpha != 0).
Proof.  
move=> ih l alpha a l_neq0 uniq_alpha alg_alpha a_neq0 alg_a; apply/negP => span_eq0.
move: (extract_good_C_span l_neq0 uniq_alpha alg_alpha a_neq0 alg_a span_eq0).
move=> [] n [] n_neq0 [] [] c gamma /= [] uniq_gamma [] alg_gamma [] c_neq0 [] c_int.
apply/negP.
by apply: (ih n gamma).
Qed.