From mathcomp Require Import all_ssreflect.
From mathcomp
Require Import ssralg ssrnum mxpoly rat poly ssrint polyorder polydiv perm.
From mathcomp
Require Import finfun separable fingroup vector.
From structs
Require Import Cstruct Rstruct.
From SsrMultinomials
Require Import finmap order mpoly ssrcomplements.

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


Section Def.

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

Section separable_ajouts.

Lemma separable_polyZ (R : idomainType) (p : {poly R}) (a : R) : 
    a != 0 -> separable_poly (a *: p) = separable_poly p.
Proof.
by move=> an0; rewrite /separable_poly derivZ coprimep_scalel ?coprimep_scaler.
Qed.





End separable_ajouts.

Section ssrcomplements_ajouts.

Lemma filter_xpredT (T : eqType) (r : seq T) :
  filter xpredT r = r.
Proof. by apply/all_filterP /allP. Qed.


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

Section seq_ajouts.

Lemma mask_size (T : eqType) a (u : seq T) (v : seq T) : 
     size u = size v -> size (mask a u) = size (mask a v).
Proof.
move=> eq_uv; elim: a u v eq_uv => // a l iha u v eq_uv.
case: u eq_uv; case: v=> // u lu v lv /= /eqP; rewrite eqSS => /eqP eq_uv.
by case: a => /=; rewrite (iha _ _ eq_uv).
Qed.

End seq_ajouts.

Section finfun_ajouts.

Variable R : eqType.
Variable n : nat.

(*
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
*)

Lemma uniq_codomP (f : R ^ n.+1) :
  reflect (injective f) (uniq (codom f)).
Proof.
apply: (iffP idP) => [uniq_f i j eq_fij | inj_f].
  apply: ord_inj; apply/eqP.
  rewrite -(nth_uniq (f ord0) _ _ uniq_f) ?size_codom ?card_ord //=.
  rewrite /codom !(nth_map ord0) -?enumT /= ?size_enum_ord //=.
  by rewrite !nth_ord_enum !eq_fij.
apply: (@ssrcomplements.uniq_nth _ (f ord0)) => i j.
rewrite size_codom => ord_i ord_j.
rewrite (ordnat ord_i) (ordnat ord_j) => /negP eq_ord.
by rewrite !nth_codom; apply/negP => /eqP /inj_f /enum_val_inj /eqP.
Qed.

Lemma ffun_tupleE (f : R ^n): f =1 tnth [tuple f i  | i < n].
Proof. by move=> i; rewrite tnth_map tnth_ord_tuple. Qed.

End finfun_ajouts.

Section tuple_ajouts.

Lemma sort_tupleP (n : nat) (T : eqType) (leT : rel T) (t : n.-tuple T) :
  size (sort leT t) == n.
Proof. by rewrite size_sort size_tuple. Qed.

Definition sort_tuple (n : nat) (T : eqType) (leT : rel T) (t : n.-tuple T) :=
  Tuple (sort_tupleP leT t). 

End tuple_ajouts.

Section bigop_ajouts.

Lemma big_enum_val_cond (R : Type) (idx : R) (op : Monoid.com_law idx) (I : finType)
  (A : {set I}) (P : pred I) (F : I -> R) :
  \big[op/idx]_(i in A | P i) (F i) =
  \big[op/idx]_(i < #|A| | P (enum_val i)) (F (enum_val i)).
Proof.
case: (set_0Vmem A) => [-> | [x0 x0_in]].
  rewrite -big_filter_cond filter_index_enum enum_set0 big_nil.
  rewrite -big_map /index_enum -enumT.
  rewrite -[enum (ordinal_finType #|@set0 I|)]/(tval (ord_tuple #|@set0 I|)).
  rewrite -[map enum_val _]/(tval (map_tuple enum_val _)).
  suff -> : tval (map_tuple enum_val (ord_tuple #|set0|)) = ([::] : seq I).
    by rewrite big_nil.
  by apply/eqP; rewrite -size_eq0 size_tuple cards0.
rewrite -big_filter_cond filter_index_enum /= -[enum _]/(enum A).
rewrite -[enum _]/(tval (Tuple (enum_tupleP (mem A)))) -[RHS]big_map.
rewrite /index_enum -enumT.
rewrite -[enum (ordinal_finType #|_|)]/(tval (ord_tuple #|_|)).
rewrite -[map enum_val _]/(tval (map_tuple enum_val _)).
apply: congr_big => //=; apply: (@eq_from_nth _ x0).
  by rewrite size_map -cardE size_enum_ord.
move=> i pre_ordi /=.
have ordi : (i < #|A|)%N by move: pre_ordi; rewrite cardE.
rewrite -[i]/(nat_of_ord (Ordinal ordi)).
rewrite -enum_val_nth (nth_map (enum_rank_in x0_in x0)) ?size_enum_ord //.
by rewrite nth_ord_enum.
Qed.

Lemma big_enum_val (R : Type) (idx : R) (op : Monoid.com_law idx) (I : finType)
  (A : {set I}) (F : I -> R) :
  \big[op/idx]_(i in A) (F i) =
  \big[op/idx]_(i < #|A|) (F (enum_val i)).
Proof.
rewrite -(big_enum_val_cond _ A xpredT F).
by apply: eq_bigl => i //; rewrite andbT.
Qed.

Lemma big_ffun (R : Type) (idx : R) (op : R -> R -> R) (I : Type) (J : finType)
    (f : J -> I) (r : seq J) (P : pred J) (F : I -> R) :
  \big[op/idx]_(i <- r | P i) F ((finfun f) i)
      = \big[op/idx]_(i <- r | P i) F (f i).
Proof. by apply: eq_bigr => i _; rewrite ffunE. Qed.

Lemma big_ffun_ord (R : Type) (idx : R) (op : R -> R -> R) (I : Type) 
    (J : finType) (f : J -> I) (r : seq J) (F : I -> R) :
  \big[op/idx]_(i <- r) F ((finfun f) i)
      = \big[op/idx]_(i <- r) F (f i).
Proof. by rewrite big_ffun. Qed.

Lemma big_fset (R : Type) (idx : R) (op : Monoid.com_law idx) (I : finType) 
  (J : choiceType) (f : I -> J) (P : pred J) (F : J -> R) :
  injective f ->
  \big[op/idx]_(i <- enum_fset [fset f j | j : I]%fset | P i) F i =
  \big[op/idx]_(j : I | P (f j)) F (f j). 
Proof.
move=> inj_f; rewrite -[in RHS]big_map.
apply: eq_big_perm; apply: (uniq_perm_eq (enum_fset_uniq _)).
  by rewrite (map_inj_uniq inj_f) /index_enum -enumT enum_uniq.
by move=> i; apply/imfsetP/mapP => [[x _ ->] | [x _ ->]]; exists x => //.
Qed.

Lemma big_fset_set (R : Type) (idx : R) (op : Monoid.com_law idx) (I : finType)
  (J : choiceType) (f : I -> J) (Q : {set I}) (P : pred J) (F : J -> R) :
injective f ->
  \big[op/idx]_(i <- enum_fset [fset f j | j in Q]%fset | P i) F i =
  \big[op/idx]_(j in Q | P (f j)) F (f j). 
Proof.
move=> inj_f; rewrite -big_filter_cond -[in RHS]big_map.
apply: eq_big_perm; apply: (uniq_perm_eq (enum_fset_uniq _)).
  by rewrite (map_inj_uniq inj_f) /index_enum -enumT filter_uniq ?enum_uniq.
move=> i; apply/imfsetP/mapP => /= [[x x_in ->] | [x x_in ->]]; exists x => //.
  by rewrite mem_filter x_in /= mem_index_enum.
by move: x_in; rewrite mem_filter => /andP[-> _].
Qed.


Lemma big_split_comm (R : Type) (idx : R) (op : Monoid.law idx) (I : finType) 
  (r : seq I) (P : pred I) (F1 : I -> R) F2 :
  (forall x y, op (F2 x) y = op (y) (F2 x)) ->
  \big[op/idx]_(i <- r | P i) (op (F1 i) (F2 i)) =
  op (\big[op/idx]_(i <- r | P i) F1 i)  (\big[op/idx]_(i <- r | P i) F2 i).
Proof.
move=> Hcomm.
elim/big_rec3: _ => [|i x y _ _ ->]; first by rewrite Monoid.mul1m.
rewrite !Monoid.mulmA. 
congr (op _ _).
by rewrite -Monoid.mulmA Hcomm -Monoid.mulmA.
Qed.

Lemma bigID_comm (R : Type) (idx : R) (op : Monoid.law idx) (I : finType)
  (r : seq I) (a P : pred I) (F : I -> R) :
  (forall x y, ~~ a x -> op (F x) y = op y (F x)) ->
  \big[op/idx]_(i <- r | P i) F i =
    op (\big[op/idx]_(i <- r | P i && a i) F i)
    (\big[op/idx]_(i <- r | P i && ~~ a i) F i).
Proof.
move=> Hcomm; rewrite !(big_mkcond _ F) -big_split_comm; first last.
move=> x y.
case: ifP => [/andP[_] not_a| _]; first by apply: Hcomm.
  by rewrite Monoid.mul1m Monoid.mulm1.
by apply: eq_bigr => i; case: (a i) => _; rewrite andbT andbF
  (Monoid.mul1m, Monoid.mulm1).
Qed.

Lemma big_setID_comm (R : Type) (idx : R) (aop : Monoid.law idx) (I : finType) 
  (A B : {set I}) (F : I -> R) :
  (forall x y, x \notin B -> aop (F x) y = aop y (F x)) ->
  \big[aop/idx]_(i in A) F i =
  aop (\big[aop/idx]_(i in A :&: B) F i) (\big[aop/idx]_(i in A :\: B) F i).
Proof.
move=> Hcomm.
rewrite (@bigID_comm _ _ _ _ _ (mem B) (mem A)) // !(eq_bigl _ _ (in_set _)) //.
by congr (aop _); apply: eq_bigl => i; rewrite andbC.
Qed.

End bigop_ajouts.

Section set_ajouts.

Variable T : finType.

Definition cover_rel (P : {set {set T}}) : rel T :=
  fun x y => [forall Q, (Q \in P) ==> ((x \in Q) == (y \in Q))].

Lemma cover_relP (P : {set {set T}}) x y :
  reflect (forall Q, Q \in P -> (x \in Q) = (y \in Q)) (cover_rel P x y).
Proof.
apply: (iffP forallP).
  by move=> H Q Q_in; apply/eqP/(implyP (H Q)).
by move=> H Q; apply/implyP; move/(H Q) => ->.
Qed.

Lemma cover_eqrel (P : {set {set T}}) : (equivalence_rel (cover_rel P)).
Proof.
move=> x y z; split; first by apply/cover_relP. 
move=> /cover_relP Hxy.
by apply/cover_relP/cover_relP => H Q Q_in; rewrite -(H Q Q_in) Hxy.
Qed.

Definition cover_rel_partition (P : {set {set T}}) := 
   (equivalence_partition (cover_rel P) (cover P)).

Lemma cover_rel_partitionP (P : {set {set T}}) : 
  partition (cover_rel_partition P) (cover P).
Proof. by apply/equivalence_partitionP => x y z _ _ _; apply/cover_eqrel. Qed.

(*
Definition pfun (aT : Type) (A : {set T}) (f : forall x : T, x \in A -> aT) 
  (g : T -> aT) (x : T) :=
  match (boolP (x \in A)) with
  |AltTrue x_in => f x x_in
  |AltFalse b => g x end. *)

Definition pfun (aT : Type) (A : {set T}) (f : forall x : T, x \in A -> aT) 
  (g : T -> aT) (x : T) :=
  match (eqVneq (x \in A) (true)) with
  |left x_in => f x x_in
  |right x_nin => g x
  end.

Lemma pfun_eq_in (aT : Type) (A : {set T}) (f1 : forall x : T, x \in A -> aT) 
      (f2 : forall x : T, x \in A -> aT) (g : T -> aT) :
  (forall x : T, forall H : (x \in A), f1 x H = f2 x H) 
      -> pfun f1 g =1 pfun f2 g.
Proof.
move=> Hf x; rewrite /pfun.
by case: (eqVneq (x \in A) true).
Qed.

Lemma pfun_eq_out (aT : Type) (A : {set T}) (f : forall x : T, x \in A -> aT)
      (g1 : T -> aT) (g2 : T -> aT) :
  {in ~:A, g1 =1 g2} -> pfun f g1 =1 pfun f g2.
Proof. 
move=> Hf x; rewrite /pfun.
by case: (eqVneq (x \in A) true) => // /eqP/setCP H_out; apply: Hf.
Qed.

Lemma pfun_out (aT : Type) (A : {set T}) (f : forall x : T, x \in A -> aT) 
  (g : T -> aT) (x : T) :
  x \notin A -> pfun f g x = g x.
Proof.
move=> /negP x_in; rewrite /pfun.
by case: (eqVneq (x \in A) true) => //.
Qed.

End set_ajouts.

Section finset_ajouts.

Lemma mem_imset_inj (aT rT : finType) (f : aT -> rT) (D : pred aT) x :
  injective f -> (x \in D) = (f x \in [set f x | x in D]).
Proof.
move=> f_inj; apply/idP/imsetP => [x_in | [y y_in] /f_inj -> //].
by exists x.
Qed.


End finset_ajouts.

Section perm_ajouts.

Lemma perm_onI (T : finType) (A : {set T}) s :
  perm_on A s -> perm_on A (s^-1)%g.
Proof.
move/subsetP => Asub; apply/subsetP => i. 
rewrite inE -(inj_eq (@perm_inj _ s)) permKV eq_sym => Hi.
by apply/(Asub i); rewrite inE.
Qed.

Lemma pre_map_in_inj (T : finType) (A : {set T}) (s : {perm 'I_(#|A|)}) (x0 : T) (H : x0 \in A) :
  {in A &, injective (enum_val \o s \o (enum_rank_in H))}.
Proof.
have H_A := (enum_tupleP (pred_of_set A)). 
move=> x y; rewrite -mem_enum -[enum A]/(tval (Tuple H_A)) => /tnthP [ix ->].
rewrite -mem_enum -[enum A]/(tval (Tuple H_A)) => /tnthP [iy ->].
move=> /enum_val_inj /perm_inj; rewrite !(tnth_nth x0) /= -!enum_val_nth.
by rewrite !enum_valK_in => ->. 
Qed.

Lemma pre_map_in_sub (T : finType) (A : {set T}) (s : {perm 'I_(#|A|)}) (x0 : T) (H : x0 \in A) :
  [set (enum_val \o s \o (enum_rank_in H)) x | x in A] \subset A.
Proof. by apply/subsetP; move=> x /imsetP[y y_in -> /=]; apply: enum_valP. Qed.


Definition map_in_old (T : finType) (A : {set T}) (s : {perm 'I_(#|A|)}) : {perm T}.
Proof.
move: s; move H_n : #|A| => n.
case: n H_n => [_ _ | n card_A].
  by exists (finfun idfun); apply/injectiveP => x y; rewrite !ffunE /=.
rewrite -card_A.
have H_A := (enum_tupleP (pred_of_set A)).
set x0 := tnth (Tuple H_A) (cast_ord (esym card_A) ord0).
have x0_in : x0 \in A by rewrite -mem_enum -[enum A]/(val (Tuple H_A)) mem_tnth.
move=> s; apply: (automorphism.perm_in (@pre_map_in_inj T A s x0 x0_in)).
apply/subsetP; move=> x /imsetP[y y_in -> /=].
by apply: enum_valP.
Defined.

Definition map_in (T : finType) (A : {set T}) (s : {perm 'I_(#|A|)}) :=
  match (set_0Vmem A) with
  |inl B => (@perm_one T)
  |inr C => let x0 := sval C in
            let x0_in := svalP C in
            (automorphism.perm_in (@pre_map_in_inj T A s x0 x0_in) 
               (@pre_map_in_sub T A s x0 x0_in))
  end.

Lemma map_in_perm_on (T : finType) (A : {set T}) (s : {perm 'I_(#|A|)}) :
  perm_on A (map_in s).
Proof.
rewrite /map_in.
case: (set_0Vmem A) => [-> | [x0 x0_in]].
  by apply/subsetP => x; rewrite inE perm1 eq_refl.
by apply: automorphism.perm_in_on.
Qed.

Lemma pre_map_out (T : finType) (A : {set T}) (s : {perm T}) (H : perm_on A s) : 
  let H_A := (enum_tupleP (pred_of_set A)) in
  perm_eq (map_tuple s (Tuple H_A)) (Tuple H_A).
Proof.
apply: uniq_perm_eq; rewrite ?(map_inj_uniq (@perm_inj _ s)) /= ?enum_uniq //.
move=> i; rewrite mem_enum.
apply/mapP/idP => [[j j_in ->] | i_in]; last first.
  by exists ((s^-1)%g i); rewrite ?mem_enum ?permKV ?perm_closed ?perm_onI.
by rewrite (perm_closed _ H) -mem_enum.
Qed.

Definition map_out (T : finType) (A : {set T}) (s : {perm T}) (H : perm_on A s) :=
  sval(sig_eqW(elimT tuple_perm_eqP (pre_map_out H))).

Lemma map_outK (T : finType) (A : {set T}) (s : {perm T}) (H : perm_on A s) :
  map_in (map_out H) = s.
Proof.
apply/permP => i.
case: (boolP (i \in A)) => [i_in | i_nin]; last first.
  by rewrite (out_perm H i_nin) (out_perm (map_in_perm_on _) i_nin).
rewrite /map_in.
case: (set_0Vmem A) => [A_eq0 | ]; first by move: i_in; rewrite A_eq0 inE.
move=> [x0 x0_in].
rewrite automorphism.perm_inE ?i_in // /map_out.
move: (svalP(sig_eqW(elimT tuple_perm_eqP (pre_map_out H)))).
set H_A := (enum_tupleP (pred_of_set A)).
set t := sval _; move: (svalP _) => y /val_inj eq_A. 
move: i_in; rewrite -mem_enum -[enum A]/(tval (Tuple H_A)).
move=> /tnthP[k eq_k]; rewrite eq_k /= -[RHS]tnth_map.
rewrite -[[tuple of [seq _ | _ <- _]]]/(map_tuple s (Tuple H_A)) eq_A.
rewrite !tnth_map tnth_ord_tuple.
have -> : (tnth (Tuple H_A) k) = nth x0 (enum A) k by rewrite (tnth_nth x0) /=.
by rewrite -enum_val_nth enum_valK_in (tnth_nth x0) -enum_val_nth.
Qed.

Lemma map_inK (T : finType) (A : {set T}) (s : {perm 'I_(#|A|)}) :
  map_out (map_in_perm_on s) = s.
Proof.
apply/permP => i.
rewrite /map_out.
move: (svalP(sig_eqW(elimT tuple_perm_eqP (pre_map_out (map_in_perm_on s))))).
set H_A := (enum_tupleP (pred_of_set A)).
rewrite /map_in.
set t := sval _.
case: (set_0Vmem A) => [A_eq0 | [x0 x0_in]].
  have i_in : tnth (Tuple H_A) i \in (Tuple H_A) by rewrite mem_tnth.
  have : tnth (Tuple H_A) i \in set0 by rewrite -A_eq0 -mem_enum.
  by rewrite in_set0.
move/val_inj=> H.
have H_inj : injective (tnth (Tuple H_A)).
  move=> x y; rewrite !(tnth_nth x0) /= -!enum_val_nth.
  by apply/enum_val_inj.
apply/H_inj.
have -> : tnth (Tuple H_A) (t i) = tnth [tuple (tnth (Tuple H_A) (t i)) | i < #|A|] i.
  by rewrite tnth_map tnth_ord_tuple.
rewrite -H !tnth_map automorphism.perm_inE !(tnth_nth x0) -!enum_val_nth. 
  by rewrite /= enum_valK_in.
by apply/enum_valP.
Qed.

Lemma map_out_val (T : finType) (A : {set T}) (s : {perm T}) (H : perm_on A s) i :
  enum_val ((map_out H) i) = s (enum_val i).
Proof.
rewrite /map_out.
move: (svalP(sig_eqW(elimT tuple_perm_eqP (pre_map_out H)))).
set H_A := (enum_tupleP (pred_of_set A)); set t := sval _ => /val_inj eq_t.
pose x0 := enum_val i.
rewrite (enum_val_nth x0) -[enum A]/(tval (Tuple H_A)) -tnth_nth.
have -> : s (enum_val i) = tnth (map_tuple s (Tuple H_A)) i.
  by rewrite tnth_map (tnth_nth x0) /= -enum_val_nth.
by rewrite eq_t tnth_map tnth_ord_tuple.
Qed.

Lemma map_in_val (T : finType) (A : {set T}) (s : 'S_(#|A|)) i :
  ((map_in s) (enum_val i)) = enum_val (s i).
Proof.
rewrite /map_in.
case: (set_0Vmem A) => [A_eq0 | [x0 x0_in]].
  by move: (enum_valP i); rewrite {2}A_eq0 inE.
by rewrite automorphism.perm_inE ?i_in ?enum_valP /= ?enum_valK_in.
Qed.

End perm_ajouts.

Section mpoly_ajouts.

Lemma mnm1_inj n : injective (@mnm1 n).
Proof.
move => i j /mnmP; move/(_ j); rewrite !mnmE eq_refl.
by move/eqP; rewrite eqb1; move/eqP => ->.
Qed.

Lemma eq_mmap n (R S : ringType) (f : R -> S) (h1 : 'I_n -> S) (h2 : 'I_n -> S) (p : {mpoly R[n]}) :
   h1 =1 h2 -> mmap f h1 p = mmap f h2 p.
Proof.
move=> Heq; rewrite /mmap.
by apply: eq_bigr => i _; rewrite (mmap1_eq _ Heq).
Qed.

Lemma eq_meval (n : nat) (R : ringType) (v1 : 'I_n -> R) (v2 : 'I_n -> R) (p : {mpoly R[n]}) :
   v1 =1 v2 -> p.@[v1] = p.@[v2].
Proof. by move=> Heq; rewrite /meval (eq_mmap _ _ Heq). Qed.

Definition msort n (m : 'X_{1..n}) := Multinom (sort_tuple leq m).

Lemma msort_sorted n (m : 'X_{1..n}) : sorted leq (msort m).
Proof. by rewrite sort_sorted //; apply: leq_total. Qed.

Lemma perm_eq_msort n (m : 'X_{1..n}) : perm_eq (msort m) m.
Proof. by rewrite perm_sort. Qed.

Local Notation "''s_' ( n , k )" := (@mesym n _ k).

(*
Lemma msize_mesym n (R : ringType) k : msize (@mesym n R k) = k.
Proof.
 par mesym_dhomog *)

Lemma dhomog_comp_mpoly n (R : idomainType) (k : nat) (lq : n.-tuple {mpoly R[k]})
      (p : {mpoly R[n]}) (d1 : nat) (d2 : nat) :
  p \is d1.-homog -> (forall i, tnth lq i \is d2.-homog) ->
  p \mPo lq \is (d1 * d2).-homog.
Proof.
move=> p_homog lc_dhomog.
rewrite comp_mpolyE; apply/dhomogP => m /msupp_sum_le; rewrite filter_xpredT.
move/flatten_mapP => [m' m'_in]; rewrite (perm_eq_mem (msuppZ _ _)); last first.
  by rewrite -mcoeff_msupp.
apply/dhomogP.
have /dhomogP /(_ m' m'_in) /= <- := p_homog.
rewrite mdegE big_distrl /= -(big_map _ xpredT (fun x => x)).
rewrite -(big_map (fun i => (m' i * d2)%N) xpredT (fun x => x)).
have -> : index_enum (ordinal_finType n) = ord_tuple n.
  by rewrite /= /index_enum -enumT.
rewrite -![map _ (ord_tuple _)]/(tval (map_tuple _ _)).
by apply: dhomog_prod => i; rewrite !tnth_map !tnth_ord_tuple mulnC dhomogMn.
Qed.

Lemma dhomog_size n (R : ringType) (p : {mpoly R[n]}) (d : nat) :
  p \is d.-homog -> p != 0 -> msize p = d.+1.
Proof.
move=> /allP /= p_homog p_neq0; apply/eqP; rewrite eqn_leq; apply/andP; split.
  rewrite msizeE big_seq_cond; eapply big_ind => //.
    by move=> x y Hx Hy; rewrite geq_max Hx Hy.
  by move=> m /andP[/p_homog /eqP -> _].
have:= p_neq0; rewrite -msupp_eq0 -[msupp _]filter_xpredT -has_filter.
move=> /hasP[m' m'_in _]; move: p_neq0; rewrite -msize_poly_eq0 -lt0n => p0.
by move/eqP: (p_homog m' m'_in) => <-; apply: msize_mdeg_lt.
Qed.



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


(* a generaliser et bouger *)
Lemma meval_comp_mpoly (n : nat) (R : comRingType) (k : nat) (lq : n.-tuple {mpoly R[k]})
      (h : R ^ k) (p : {mpoly R[n]}) :
  (p \mPo lq).@[h] = p.@[tnth (map_tuple (meval h) lq)].
Proof.  
rewrite comp_mpolyE rmorph_sum /= mevalE.
apply: eq_bigr => m _; rewrite mevalZ rmorph_prod /=.
by congr (p@_m * _); apply: eq_bigr => i _; rewrite tnth_map rmorphX.
Qed.

Lemma mroots_coeff_proper (R : idomainType) (n : nat) (cs : R ^ n) (k : 'I_n.+1) :
(\prod_(i < n) ('X - (cs i)%:P))`_k = (-1) ^+ (n - k) * ('s_(n, n - k)).@[cs].
Proof.
set t := [tuple cs i | i < n].
have /eq_meval -> : cs =1 tnth t by move=> i; rewrite tnth_map tnth_ord_tuple.
have ordk : (n - k < n.+1)%N by rewrite ltnS leq_subr.
rewrite -[(n - k)%N]/(nat_of_ord (Ordinal ordk)) -mroots_coeff subKn ?big_tuple.
  by congr ((_ _)`_k); apply: eq_bigr => i _; rewrite tnth_map tnth_ord_tuple.
by rewrite -ltnS.
Qed.

Lemma msize_horner (R : idomainType) (n : nat) (p : {poly {mpoly R[n]}}) (i : 'I_n) :
  (msize (p.['X_i]) <= \max_(j < size p) (j + msize (p`_j)))%N.
Proof.
rewrite horner_coef.
apply/(leq_trans (msize_sum _ _ _) _) => /=.
apply: (big_ind2 (fun x y => (x <= y)%N) (leq0n _)).
  by move=> x x' y y' Hx Hy; rewrite geq_max !leq_max Hx Hy orbT.
move=> j _; case: (boolP (p`_j == 0)) => [/eqP -> | p_neq0].
  by rewrite mul0r msize0 addn0 leq0n.
have HX : (msize ('X_i ^+ j : {mpoly R[n]}) = j.+1)%N.
  by rewrite mpolyXn msizeX mdegMn mdeg1 mul1n.
rewrite (msizeM p_neq0) -?msize_poly_eq0 HX -?lt0n ?ltn0Sn //.
by rewrite -subn1 -addnBA ?ltn0Sn // subn1 /= addnC.
Qed.    

Lemma msize_horner_deriv (R : idomainType) (n : nat) (p : {poly {mpoly R[n]}}) (i : 'I_n) :
  (msize (p^`().['X_i]) <= (\max_(j < size p) (j + msize (p`_j))).-1)%N.
Proof.
case: (boolP (p == 0)) => [/eqP -> | p_neq0].
  by rewrite size_poly0 /= big_ord0 deriv0 horner0 msize0.
apply/(leq_trans (msize_horner _ _) _).
apply/(@leq_trans (\max_(i0 < size p) (i0 + msize (p`_i0 *+ i0)).-1)%N).
  apply/bigmax_leqP => j _; rewrite coef_deriv.
  by apply/(bigmax_sup (Ordinal (leq_ltn_trans (ltn_ord j) (lt_size_deriv p_neq0)))). 
apply: (big_ind2 (fun x y => (x <= y.-1)%N) (leqnn _)).
  move=> x x' y y' Hx Hy; rewrite geq_max /maxn.
  case: ifP => [Hxy | ].
    rewrite Hy andbT; apply/(leq_trans Hx).
    rewrite -subn1 leq_subLR -subn1 addnBA; last first.
      by apply/(leq_trans _ Hxy).
    by rewrite addnC addn1 subn1 /= (ltnW Hxy).
  move/negP/negP; rewrite -leqNgt => Hyx; rewrite Hx /=.
  apply/(leq_trans Hy); rewrite -!subn1.
  by apply: leq_sub2r.
move=> j _.
case: (boolP (j%:R == (0 : R))) => [/eqP j_eq0| j_neq0].
  rewrite -scaler_nat j_eq0 scale0r msize0 addn0 -!subn1.
  apply/(leq_sub2r)/leq_addr.
by rewrite -scaler_nat (msizeZ _ j_neq0).
Qed.

Lemma msize_horner_derivn (R : idomainType) (n : nat) (p : {poly {mpoly R[n]}}) (i : 'I_n) k :
  (msize ((p^`(k)).['X_i]) <= (\max_(j < size p) (j + msize (p`_j))) - k)%N.
Proof.
case: (boolP (p == 0)) => [/eqP -> | p_neq0].
  by rewrite size_poly0 /= big_ord0 linear0 horner0 msize0.
apply/(leq_trans (msize_horner _ _) _).
apply/(@leq_trans (\max_(i0 < size p) (i0 + msize (p`_i0 *+ (i0) ^_k)) - k)%N).
  apply/bigmax_leqP => j _; rewrite coef_derivn.
  have Hj : (nat_of_ord j = k + j - k)%N by rewrite -{4}[k]addn0 subnDl subn0.
  have ord_k : (k + j < size p)%N.  
    apply/(@leq_trans (k + (size p^`(k)))); first by rewrite ltn_add2l.
    have H : (size p^`(k) <= (size p) - k)%N.
      elim: k {j Hj} => [| k ihk]; first by rewrite derivn0 subn0.
      rewrite derivnS subnS.
      case: (boolP (p^`(k) == 0)) => [/eqP -> | p'_neq0].
        by rewrite linear0 size_poly0.
      rewrite -ltnS.
      apply/(leq_trans (lt_size_deriv p'_neq0)).
      apply/(leq_trans ihk); rewrite prednK //.
      by apply/(leq_trans _ ihk); rewrite lt0n size_poly_eq0.
    have := H; rewrite -(leq_add2l k); move/leq_trans; apply.
    rewrite subnKC // ltnW // -subn_gt0.
    by apply/(leq_trans _ H)/(leq_ltn_trans _ (ltn_ord j)).
  rewrite {1}Hj addnC addnBA ?leq_addr //.
  apply: leq_sub2r.
  by apply/(bigmax_sup (Ordinal ord_k)) => //=; rewrite addnC.
apply: leq_sub2r.
apply: (big_ind2 (fun x y => (x <= y)%N) (leqnn _)).
  move=> x x' y y' Hx Hy; rewrite geq_max /maxn.
  case: ifP => [Hxy | ].
    by rewrite Hy andbT; apply/(leq_trans Hx); rewrite ltnW.
  move/negP/negP; rewrite -leqNgt => Hyx; rewrite Hx /=.
  by apply/(leq_trans Hy Hyx).
move=> j _; rewrite leq_add2l -scaler_nat.
case: (boolP ((j ^_ k)%:R == (0 : R))) => [/eqP ->| j_neq0].
  by rewrite scale0r msize0.
by rewrite (msizeZ _ j_neq0).
Qed.

Lemma msizeM_proper (n : nat) (R : idomainType) (p : {mpoly R[n]}) 
  (q : {mpoly R[n]}) :
  (msize (p * q) <= (msize p + msize q).-1)%N.
Proof.
have [->|nz_p ] := eqVneq p 0; first by rewrite mul0r msize0.
have [->|nz_q ] := eqVneq q 0; first by rewrite mulr0 msize0.
have [->|nz_pq] := eqVneq (p * q) 0; first by rewrite msize0.
rewrite -!mlead_deg // !(addSn, addnS) -addn1 -[X in (_ <= X)%N]addn1.
rewrite leq_add2r.
by have /lemc_mdeg := mleadM_le p q; rewrite mdegD.
Qed.

Lemma msize_prod (n : nat) (R : idomainType) (I : finType) (P : pred I) 
     (F : I -> {mpoly R[n]}) :
  (forall i, P i -> F i != 0) -> 
  (msize (\prod_(i | P i) F i) <= 
  (\sum_(i | P i) (msize (F i))).+1 - \sum_(i | P i) 1)%N.
Proof.
move=> H_neq0.
apply: (big_rec3 (fun x y z => (msize x <= y.+1 - z)%N)).
  by rewrite subn0 msize1.
move=> i p x y Hi; rewrite -addn1 subnDA => Hp.
rewrite -addn1 -subnDA.
case: (boolP (p == 0)) => [/eqP -> | p_neq0].
  by rewrite mulr0 msize0.
apply: (leq_trans (msizeM_proper _ _)).
apply/(@leq_trans (msize (F i) + (x + 1 - y)).-1).
  by rewrite -!subn1 leq_sub2r ?leq_add2l.
rewrite -subn1 subnDA [(_ + _ + 1)%N]addn1 !subn1 /= -subn1 leq_subLR add1n addn1.
have leq_yx : (y <= x + 1)%N.
  apply/(@leq_trans (1 + x)); last by rewrite addnC.
  rewrite addnC ltnW // -[y]addn0 -ltn_subRL.
  by apply/(leq_trans _ Hp); rewrite lt0n msize_poly_eq0.
rewrite -[X in (_ <= X)%N]subSn; last first.
  by apply/(leq_trans leq_yx); rewrite addnC leq_add2r lt0n msize_poly_eq0 H_neq0 ?Hi.
by rewrite -addnS addnBA // -addn1.
Qed.

Lemma msupp_msym (R : ringType) (n : nat) (p : {mpoly R[n]}) (s : 'S_n) :
  let mperm s (m : 'X_{1..n}) := [multinom m (s i) | i < n] in
  perm_eq (msupp (msym s p)) 
           [seq (mperm (s^-1)%g m) | m <- (msupp p)].
Proof.
rewrite /= uniq_perm_eq ?(map_inj_uniq (@mperm_inj _ (s^-1)%g)) ?msupp_uniq //. 
move=> i; rewrite mcoeff_msupp mcoeff_sym -mcoeff_msupp -{2}[i](mpermKV s).
by rewrite (mem_map (@mperm_inj _ _)).
Qed.

Lemma msupp_sym (R : ringType) (n : nat) (p : {mpoly R[n]}) (s : 'S_n) :
  p \is symmetric -> perm_eq (msupp (msym s p)) (msupp p).
Proof. 
by move=> /issymP p_sym; rewrite /= uniq_perm_eq ?msupp_uniq ?(p_sym s). 
Qed.

Lemma msym_mevalE (R : comRingType) (n' : nat) (p : {mpoly R[n']}) (s : 'S_n') :
  msym s p = p \mPo [tuple 'X_(s i) | i < n'].
Proof.
rewrite -[LHS]comp_mpoly_id msym_mPo.
congr comp_mpoly; apply/eq_from_tnth => i.
by rewrite !tnth_map !tnth_ord_tuple.
Qed.

(* symétrisé d'un monôme *)
Section MSymOf.

Variable n : nat.
Variable R : ringType.

Implicit Types m md : 'X_{1..n}.

Definition mperm (s : 'S_n) m := [multinom m (s i) | i < n].

Local Notation "m # s" := (mperm s m)
  (at level 40, left associativity, format "m # s").


(* pourquoi un pval ? *)
(* possiblement (s^-1)%g à la place de s
 \sum_(m' : [fset (m # fun_of_perm (s^-1)%g) | s : 'S_n]%fset) 'X_[fsval m'].  *)
(*Definition fns := (@pred_fset (perm_for_choiceType (ordinal_finType n))
              (pred_finpredType (perm_for_finType (ordinal_finType n)))
              (@sort_of_simpl_pred (@perm_of (ordinal_finType n) (Phant (ordinal n)))
                 (pred_of_argType (@perm_of (ordinal_finType n) (Phant (ordinal n)))))).*)

Definition mmsym (md : 'X_{1..n}) : {mpoly R[n]} :=
  \sum_(m <- enum_fset ((mperm^~ md) @` 'S_n)%fset) 'X_[m]. 

Local Notation "''m_' md" := (mmsym md)
  (at level 8, md at level 2, format "''m_' md").

Lemma mmsymE md :
  'm_md = \sum_(m <- enum_fset ((mperm^~ md) @` 'S_n)%fset) 'X_[m].
Proof. by rewrite /mmsym. Qed.

Lemma msupp_mmsym md :  
  perm_eq (msupp 'm_md) (enum_fset ((mperm^~ md) @` 'S_n)%fset).
Proof.
rewrite mmsymE; apply/(perm_eq_trans (msupp_sum _ _ _))=> /=.
+ by apply: enum_fset_uniq.
+ move=> h1 h2 _ _ ne_h1h2 m /=; rewrite !msuppX !mem_seq1.
  by apply/negbTE/negP=> /andP[/eqP->]; apply/negP.
(* trop long à passer *)
rewrite (eq_map (fun h => msuppX _ h)).
by rewrite (map_comp (cons^~ [::])) flatten_seq1 filter_xpredT map_id.
Qed.

Lemma bla1 md m : perm_eq md m = [exists s : 'S_n, mperm s m == md].
Proof.
apply/tuple_perm_eqP/idP => [[s /val_inj /= eq_md] | /existsP[s /eqP eq_md]].
  apply/existsP; exists s; rewrite /mperm; apply/eqP /mnmP => i.
  by rewrite mnmE /fun_of_multinom eq_md tnth_map tnth_ord_tuple.
by exists s; rewrite -eq_md.
Qed.

Lemma msupp_mmsymP md m : (m \in msupp 'm_md) = perm_eq md m.
Proof.
rewrite (perm_eq_mem (msupp_mmsym _)) perm_eq_sym bla1.
apply/idP/existsP => [/imfsetP[s _ ->] | [s /eqP <-]]; first by exists s.
by apply/imfsetP; exists s.
Qed.

(* assure la compatibilité avec ceux de florent *)
Lemma mcoeff_mmsym md m : ('m_md)@_m = (perm_eq md m)%:R.
Proof.
case: (boolP (perm_eq md m)); rewrite -msupp_mmsymP; last first.
  by move/memN_msupp_eq0 => ->.
rewrite linear_sum -(eq_big_perm _ (msupp_mmsym _)) /= => m_in.
rewrite (bigD1_seq _ m_in (msupp_uniq _)) /= mcoeffX eq_refl big1_seq ?addr0 //.
by move=> i /andP[/negbTE i_neqm _]; rewrite mcoeffX i_neqm.
Qed.

Lemma mmsym_sym md : 'm_md \is symmetric.
Proof.
apply/issymP => s; apply/mpolyP => m.
rewrite mcoeff_sym !mcoeff_mmsym !bla1; congr ((nat_of_bool _)%:R).
apply/existsP/existsP => [[t /eqP <-] | [t /eqP <-]].
  by exists (t * s)%g; rewrite /mperm mpermM. 
by exists (t * s^-1)%g; rewrite /mperm mpermM mpermKV.
Qed.

(* calqué sur le issym_symmE dans sympoly de florent *)
Lemma issym_symmE (p : {mpoly R[n]}) :
  p \is symmetric ->
  p = \sum_(m <- msupp p | sorted leq m) p@_m *: mmsym m.
Proof.
move=> Hsym; apply/mpolyP => m.
have := (perm_eq_msort m); rewrite bla1 => /existsP[s /eqP eq_msort].
case: (boolP (m \in msupp p)) => Hm.
- rewrite -big_filter (bigD1_seq (msort m)) /=; first last.
  + by apply filter_uniq; apply msupp_uniq.
  + rewrite mem_filter msort_sorted //= mcoeff_msupp -eq_msort.
    by rewrite /mperm -mcoeff_sym (issymP _ Hsym) -mcoeff_msupp.
  rewrite linearD linearZ /= mcoeff_mmsym perm_eq_msort mulr1.
  rewrite big_filter_cond /= -{1}eq_msort /mperm msym_coeff //.
  rewrite -[LHS]addr0; congr (_ + _); symmetry.
  rewrite linear_sum big1_seq // => i /andP[/andP[i_sorted i_neqm] i_in] /=.
  rewrite mcoeffZ mcoeff_mmsym. 
  suff /negbTE -> : ~~ (perm_eq i m) by rewrite mulr0.
  apply/(perm_sortP _ _ anti_leq).
  + by move=> u v; rewrite leq_total.  
  + by move=> u v; apply: leq_trans.
  rewrite (eq_sorted _ anti_leq (sort_sorted _ _) i_sorted); first last.
  + by apply/perm_eqlP /perm_sort.
  + by move=> u v; rewrite leq_total.
  + by move=> u v; apply: leq_trans.
  by rewrite -[sort _ _]/(tval (msort m)); apply/eqP.
- rewrite (memN_msupp_eq0 Hm); symmetry.
  rewrite !raddf_sum /= big_seq_cond big1 // => /= m' /andP[m'_in m'_sorted].
  rewrite mcoeffZ mcoeff_mmsym.
  case: (boolP (perm_eq _ _)) => [ | Hperm]; last by rewrite mulr0.
  rewrite bla1 => /existsP[s' /eqP]; rewrite /mperm => <-.    
  by rewrite -mcoeff_sym (issymP p Hsym) mulr1 memN_msupp_eq0.
Qed.

Lemma dhomog_mmsym md : 'm_md \is (mdeg md).-homog.
Proof.
apply/dhomogP => m; rewrite msupp_mmsymP bla1 => /existsP[s /eqP <-].
by rewrite /mperm /= mdeg_mperm.
Qed.

Lemma mmsym_neq0 md : 'm_md != 0.
Proof.
apply/eqP/mpolyP; move/(_ md); apply/eqP.
by rewrite mcoeff0 mcoeff_mmsym perm_eq_refl /= oner_neq0.
Qed.


End MSymOf.

Section mpeval.

Variable n : nat.
Variable R : ringType.

Implicit Types m : 'X_{1..n}.
Implicit Types p : {mpoly R[n]}.
Implicit Types A : {set 'I_n}.

Definition mpeval A (v : 'I_n -> R) p :=
   p \mPo [tuple if i \in A then (v i)%:MP_[n] else 'X_i| i < n]. 

Local Notation "p '.@[' v , A ']' " := (mpeval A v p)
  (at level 2, left associativity, format " p .@[ v , A ]").

Lemma mpevalE A v p :
  p.@[v,A] = \sum_(m <- msupp p) (p@_m * (\prod_(i in A) (v i) ^+ (m i))) *: 
                           \prod_(i in ~: A) ('X_i)^+(m i).
Proof. 
rewrite /mpeval comp_mpolyE; apply/eq_bigr=> m _; rewrite -scalerA.
congr (_ *: _); rewrite -mul_mpolyC rmorph_prod. 
pose F := (fun i => (if i \in A then (v i)%:MP_[n] else 'X_i) ^+ (m i)).
rewrite [LHS](eq_bigr F); last by move=> i _; rewrite tnth_map tnth_ord_tuple.
rewrite [in RHS](eq_bigr F); last by move=> i i_in; rewrite rmorphX /F i_in.
rewrite [X in _ * X](eq_bigr F); last first.
  by move=> i /setCP /negP /negbTE i_not; rewrite /F i_not.
rewrite -{1}(setTI A) -setTD -big_setID_comm /=.
  by apply: eq_bigl => i; rewrite inE.
by move=> x y /negbTE x_in; rewrite /F x_in mpolyXn commr_mpolyX.
Qed.

Lemma mpeval_is_additive A v : additive (mpeval A v).
Proof. by move=> p q; rewrite /comp_mpoly -mmapB. Qed.

Canonical mpeval_additive A v := Additive (mpeval_is_additive A v).

Lemma mpeval0 A v : 0.@[v,A] = 0. Proof. exact: raddf0. Qed.
Lemma mpevalN A v : {morph mpeval A v : x / - x}. Proof. exact: raddfN. Qed.
Lemma mpevalD A v : {morph mpeval A v : x y / x + y}. Proof. exact: raddfD. Qed.
Lemma mpevalB A v : {morph mpeval A v : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma mpevalMn A v l : {morph mpeval A v : x / x *+ l} . 
Proof. exact: raddfMn. Qed.
Lemma mpevalMNn A v l : {morph mpeval A v : x / x *- l} . 
Proof. exact: raddfMNn. Qed.

Lemma mpeval_is_linear A v : linear (mpeval A v).
Proof. by move=> c p q; rewrite /mpeval -comp_mpoly_is_linear. Qed.

Canonical mpeval_linear A v := Linear (mpeval_is_linear A v).

Lemma mpeval1 A v : 1.@[v,A] = 1.
Proof. by rewrite /mpeval comp_mpoly1. Qed.

Lemma mpevalC c A v : c%:MP.@[v,A] = c%:MP.
Proof. by rewrite /mpeval comp_mpolyC. Qed.

Lemma mpevalZ c p A v : (c *: p).@[v,A] = c *: (p.@[v,A]).
Proof. by apply/linearZ. Qed.

Lemma mpevalXU i A v : ('X_i).@[v,A] = if i \in A then (v i)%:MP else 'X_i.
Proof. by rewrite /mpeval comp_mpolyXU -tnth_nth tnth_map tnth_ord_tuple. Qed.

Lemma mpevalX m A v :
  'X_[m].@[v,A] = (\prod_(i in A) (v i) ^+ (m i)) *: 
      'X_[[multinom (if i \in A then 0%N else m i) | i < n]].
Proof. 
rewrite mpevalE msuppX big_seq1 mcoeffX eq_refl mul1r mpolyXE_id.
congr (_ *: _); rewrite big_mkcond /=.
apply: eq_bigr => i _; rewrite mnmE in_setC.
by case: (i \in A).
Qed.

Lemma eq_mpeval A (v1 : 'I_n -> R) (v2 : 'I_n -> R) (p : {mpoly R[n]}) :
   v1 =1 v2 -> p.@[v1,A] = p.@[v2,A].
Proof. 
move=> Heq; rewrite /mpeval /comp_mpoly. 
apply: eq_mmap => i; rewrite !tnth_map tnth_ord_tuple.
by case: (i \in A); first rewrite Heq.
Qed.

Lemma eq_mpeval_in A (v1 : 'I_n -> R) (v2 : 'I_n -> R) (p : {mpoly R[n]}) :
  {in A, v1 =1 v2} -> p.@[v1,A] = p.@[v2,A].
Proof.
move=> Heq; rewrite /mpeval /comp_mpoly. 
apply: eq_mmap => i; rewrite !tnth_map tnth_ord_tuple.
by case: (boolP (i \in A)) => H; first rewrite Heq.
Qed.

Lemma mpeval_mpolyOver_in S (ringS : semiringPred S) (kS : keyed_pred ringS) 
          A v p :
  p \is a mpolyOver n kS -> {in A, forall i, v i \in kS} ->
  p.@[v,A] \is a mpolyOver n kS.
Proof.
move=> /mpolyOverP p_over v_over; rewrite mpevalE rpred_sum // => m _.
rewrite -mul_mpolyC rpredM ?mpolyOverC ?rpredM ?p_over ?rpred_prod // => i i_in.
  by rewrite rpredX ?v_over ?i_in.
by rewrite rpredX ?mpolyOverX.
Qed.

Lemma mpeval_mpolyOver S (ringS : semiringPred S) (kS : keyed_pred ringS) 
          A v p :
  p \is a mpolyOver n kS -> (forall i, v i \in kS) ->
  p.@[v,A] \is a mpolyOver n kS.
Proof. by move=> p_over v_in; apply: (mpeval_mpolyOver_in p_over) => x _. Qed.

(* set operations *)
Lemma mpevalsT v p :
  p.@[v,[set: 'I_n]] = p.@[v]%:MP.
Proof.
rewrite mevalE mpevalE rmorph_sum.
apply: eq_bigr => m _; rewrite setCT big_set0 alg_mpolyC /=.
by congr (_ * _)%:MP; apply: eq_bigl => i; rewrite inE.
Qed.

Lemma mpevals0 v p :
  p.@[v,set0] = p.
Proof.
rewrite mpevalE [RHS]mpolyE.
apply: eq_bigr => m _; rewrite setC0 big_set0 mulr1 mpolyXE_id.
by congr (_ *: _); apply: eq_bigl => i; rewrite inE.
Qed.

End mpeval.

Local Notation "p '.@[' v , A ']' " := (mpeval A v p)
  (at level 2, left associativity, format " p .@[ v , A ]").

Section mpeval_comm.

Variable n : nat.
Variable R : comRingType.

Implicit Types m : 'X_{1..n}.
Implicit Types p : {mpoly R[n]}.
Implicit Types A : {set 'I_n}.

Lemma mpeval_is_multiplicative A v : multiplicative (@mpeval n R A v).
Proof. exact: mmap_is_multiplicative. Qed.

Canonical mpeval_rmorphism A v := AddRMorphism (mpeval_is_multiplicative A v).
Canonical mpeval_lrmorphism A v := [lrmorphism of (mpeval A v)].

Lemma mpevalsU v A B p :
  (p.@[v,A]).@[v,B] = p.@[v,(A :|: B)].
Proof.
rewrite /(mpeval A) [RHS]/mpeval !comp_mpolyE rmorph_sum.
apply: eq_bigr => m _; rewrite linearZ /= rmorph_prod.
congr (_ *: _); apply: eq_bigr => i _ /=; rewrite rmorphX /=. 
rewrite !tnth_map tnth_ord_tuple inE.
case: (i \in A) => /=; first by rewrite mpevalC.
by congr (_ ^+ _); rewrite mpevalXU.
Qed.

Lemma mpevalsC v A B p :
  (p.@[v,A]).@[v,B] = (p.@[v,B]).@[v,A].
Proof. by rewrite !mpevalsU setUC. Qed.

End mpeval_comm.

Section MSymFor.

Variable n : nat.
Variable R : ringType.
Variable A : {set 'I_n}.

Implicit Types m : 'X_{1..n}.

Local Notation "m # s" := (mperm s m)
  (at level 40, left associativity, format "m # s").

Definition symmetric_for : qualifier 0 {mpoly R[n]} :=
  [qualify p | [forall s, perm_on A s ==> (msym s p == p)]].

Fact symmetric_for_key : pred_key symmetric_for. Proof. by []. Qed.
Canonical symmetric_for_keyed := KeyedQualifier symmetric_for_key.

Lemma issym_forP p : 
   reflect (forall s, perm_on A s -> msym s p = p) (p \is symmetric_for).
Proof.
apply: (iffP forallP)=> /= h s; first by move/(implyP (h s))/eqP => ->.
by apply/implyP; move/(h s) => ->.
Qed.

Lemma sym_for_zmod : zmod_closed symmetric_for.
Proof.
split=> [|p q /issym_forP sp /issym_forP sq]; apply/issym_forP=> s s_A.
  by rewrite msym0.
by rewrite msymB (sp s s_A) (sq s s_A).
Qed.

Canonical sym_for_opprPred := OpprPred sym_for_zmod.
Canonical sym_for_addrPred := AddrPred sym_for_zmod.
Canonical sym_for_zmodPred := ZmodPred sym_for_zmod.

Lemma sym_for_mulr_closed : mulr_closed symmetric_for.
Proof.
split=> [|p q /issym_forP sp /issym_forP sq]; apply/issym_forP=> s s_A.
  by rewrite msym1.
by rewrite msymM (sp s s_A) (sq s s_A).
Qed.

Canonical sym_for_mulrPred     := MulrPred     sym_for_mulr_closed.
Canonical sym_for_smulrPred    := SmulrPred    sym_for_mulr_closed.
Canonical sym_for_semiringPred := SemiringPred sym_for_mulr_closed.
Canonical sym_for_subringPred  := SubringPred  sym_for_mulr_closed.

Lemma sym_for_submod_closed : submod_closed symmetric_for.
Proof.
split=> [|c p q /issym_forP sp /issym_forP sq]; apply/issym_forP=> s s_A.
  by rewrite msym0.
by rewrite msymD msymZ (sp s s_A) (sq s s_A).
Qed.

Canonical sym_for_submodPred := SubmodPred sym_for_submod_closed.
Canonical sym_for_subalgPred := SubalgPred sym_for_submod_closed.

Lemma issym_for_msupp p (s : 'S_n) m : 
  perm_on A s -> p \is symmetric_for ->
  (m#s \in msupp p) = (m \in msupp p).
Proof. by rewrite !mcoeff_msupp -mcoeff_sym => H /issym_forP /(_ s H) ->. Qed.

Lemma msym_for_coeff (p : {mpoly R[n]}) (m : 'X_{1..n}) (s : 'S_n) :
  perm_on A s -> p \is symmetric_for -> p@_(m#s) = p@_m.
Proof.
move=> /perm_onI H; move/issym_forP=> /(_ (s^-1)%g H) {1}<-; rewrite mcoeff_sym.
by congr (_@__); apply/mnmP=> i /=; rewrite !mnmE permKV.
Qed.

Lemma msupp_sym_for (p : {mpoly R[n]}) (s : 'S_n) :
  perm_on A s -> p \is symmetric_for -> perm_eq (msupp (msym s p)) (msupp p).
Proof. 
by move=> s_on /issym_forP psym; rewrite /= uniq_perm_eq ?msupp_uniq ?(psym s). 
Qed.

End MSymFor.

Section MPolyFor.

Variable n : nat.
Variable R : comRingType.
Implicit Types A : {set 'I_n}.
Implicit Types p : {mpoly R[n]}.

Definition mpoly_for A p :=
  mmap ((@mpolyC #|A| (mpoly_comRingType n R)) \o (@mpolyC n R))
  (pfun  (fun (x : 'I_n) => (fun (H : x \in A) => 'X_(enum_rank_in H x)))
  (fun i : 'I_n => mpolyC #|A| ('X_i))) p.

Lemma mpoly_forE A p :
  mpoly_for A p =
  \sum_(m <- msupp p) 
  (p@_m *: 'X_[[multinom (if i \in A then 0%N else m i) | i < n]]) *:
 'X_[[multinom m (enum_val i) | i < #|A|]].
Proof.
rewrite [p in LHS]mpolyE /mpoly_for raddf_sum /=.
apply: eq_bigr=> m _; rewrite mmapZ /= -(mul_mpolyC (p@_m)) [in LHS]mul_mpolyC.
rewrite -scalerA; congr (_ *: _).
rewrite mmapX /mmap1 !mpolyXE_id -mul_mpolyC rmorph_prod /=.
set f := pfun _ _.
rewrite [in RHS](eq_bigr (fun i => (if i \notin A then (f i ^+ m i) else 1))); last first.
  move=> i _; rewrite mnmE /f /pfun. 
  case: (eqVneq (i \in A)) => [ H | /eqP/negP/negbTE -> /=].
    by rewrite H /= expr0 mpolyC1.
  by rewrite -rmorphX.
rewrite -big_mkcond /=.
rewrite (eq_bigr (fun i => (f (enum_val i)) ^+ m (enum_val i))); last first.
  move=> i _; rewrite /f /pfun mnmE; congr (_ ^+ _).
  case: (eqVneq ((enum_val i) \in A)) => [H | ]; first by rewrite enum_valK_in.
  by rewrite enum_valP.
rewrite -(big_enum_val _ _ (fun i => f i ^+ m i)) /= (bigID (mem A)) /=.
by rewrite mulrC [X in _ = _ * X](eq_bigl (fun i => (i \in A))) //. 
Qed.


Lemma mpoly_for_is_additive A : additive (mpoly_for A).
Proof. by move=> p q; rewrite /mpoly_for -mmapB. Qed.

Canonical mpoly_for_additive A := Additive (mpoly_for_is_additive A).

Lemma mpoly_for0 A : mpoly_for A 0 = 0. Proof. exact: raddf0. Qed.
Lemma mpoly_forN A : {morph mpoly_for A : x / - x}. Proof. exact: raddfN. Qed.
Lemma mpoly_forD A : {morph mpoly_for A : x y / x + y}. 
Proof. exact: raddfD. Qed.
Lemma mpoly_forB A : {morph mpoly_for A : x y / x - y}. 
Proof. exact: raddfB. Qed.
Lemma mpoly_forMn A l : {morph mpoly_for A : x / x *+ l} . 
Proof. exact: raddfMn. Qed.
Lemma mpoly_forMNn A l : {morph mpoly_for A : x / x *- l} . 
Proof. exact: raddfMNn. Qed.

Lemma mpoly_for_is_multiplicative A : multiplicative (mpoly_for A).
Proof. exact: mmap_is_multiplicative. Qed.

Canonical mpoly_for_rmorphism A := AddRMorphism (mpoly_for_is_multiplicative A).

Lemma mpoly_for1 A : mpoly_for A 1 = 1.
Proof. by rewrite rmorph1. Qed.

Lemma mpoly_forC c A : mpoly_for A (c%:MP) = (c%:MP)%:MP.
Proof. by rewrite /mpoly_for mmapC. Qed.

Lemma mpoly_forZ c p A : mpoly_for A (c *: p) = c%:MP *: (mpoly_for A p).
Proof. by rewrite -!mul_mpolyC rmorphM /= mpoly_forC. Qed.

Lemma mpoly_forXU_in i A (H : i \in A): 
  mpoly_for A ('X_i) = 'X_(enum_rank_in H i).
Proof.
rewrite /mpoly_for mmapX /mmap1 (bigD1 i) //= big1 /=; last first.
  by move=> j /negbTE j_neqi; rewrite mnmE eq_sym j_neqi expr0.
rewrite /pfun mulr1 mnm1E eq_refl expr1.
case: (eqVneq (i \in A)) => [H1 | ]; last by rewrite H.
by congr ('X_( _ )); apply/enum_val_inj; rewrite !enum_rankK_in.
Qed.

Lemma mpoly_forXU_out i A :
  i \notin A -> mpoly_for A ('X_i) = ('X_i)%:MP.
Proof. 
move=> /negbTE H.
rewrite /mpoly_for mmapX /mmap1 (bigD1 i) //= big1 /=; last first.
  by move=> j /negbTE j_neqi; rewrite mnmE eq_sym j_neqi expr0.
rewrite /pfun mulr1 mnm1E eq_refl expr1.
by case: (eqVneq (i \in A)) => // H1; rewrite H1 in H.
Qed.

Lemma mpoly_forX m A :
  mpoly_for A 'X_[m] = 'X_[[multinom (if i \in A then 0%N else m i) | i < n]] *:
 'X_[[multinom m (enum_val i) | i < #|A|]].
Proof. by rewrite mpoly_forE msuppX big_seq1 mcoeffX eq_refl scale1r. Qed.

Lemma mpeval_mpoly_for (v : 'I_n -> R) A p :
  p.@[v,A] = (mpoly_for A p) .@[fun i => (v (enum_val i))%:MP_[n]].
Proof.
rewrite mpevalE mpoly_forE raddf_sum /=.
apply: eq_bigr => m _.
rewrite mevalZ /meval mmapX -scalerA -scalerAl mulrC.
congr (_ *: _); rewrite -mul_mpolyC; congr (_ * _); last first.
  rewrite mpolyXE_id /= big_mkcond /=.
  apply: eq_bigr => i _; rewrite in_setC mnmE.
  by case: (i \in A).
rewrite rmorph_prod /= /mmap1.
set F := (fun i => (v i ^+ m i)%:MP_[n]).
rewrite (eq_bigr F); last by move => i _.
rewrite (eq_bigr (fun i => F (enum_val i))); last first.
  by move=> i _; rewrite /F rmorphX /= mnmE.
rewrite -[RHS](big_map (@enum_val _ (mem A)) xpredT).
suff -> : [seq enum_val i | i <- index_enum (ordinal_finType #|A|)] = enum A.
  by rewrite big_filter.
have -> : enum A = Tuple (enum_tupleP (mem A)) by [].
have -> : index_enum (ordinal_finType #|A|) = ord_tuple #|A|.
  by rewrite val_ord_tuple /index_enum -enumT.
rewrite -[map _ _]/(tval (map_tuple _ _)).
congr tval; apply/eq_from_tnth => i; rewrite /= tnth_map tnth_ord_tuple.
by rewrite (tnth_nth (enum_val i)) /= -enum_val_nth.
Qed.

Lemma mpoly_for_mpolyE (A : {set 'I_n}) (p : {mpoly R[n]}) :
  p = (mpoly_for A p).@[fun i => 'X_(enum_val i)].
Proof.
rewrite mpoly_forE raddf_sum /= [LHS]mpolyE.
apply: eq_bigr => m _; rewrite mevalZ -scalerAl.
congr (_ *: _); rewrite !mpolyXE_id !mprodXnE /meval mmapX /mmap1.
rewrite (eq_bigr (fun i => 'X_(enum_val i) ^+ (m (enum_val i)))); last first.
  by move=> i _; congr (_ ^+ _); rewrite -multinomUE_id mnmE.
rewrite mprodXnE -mpolyXD -!multinomUE_id.
rewrite -(big_map (@enum_val _ (mem A)) xpredT (fun i => (U_( i) *+ m i)%MM)).
suff -> : [seq enum_val i | i <- index_enum (ordinal_finType #|A|)] = enum A.
  congr mpolyX; apply/mnmP => i /=; rewrite mnmDE mnmE mnm_sumE.
  case: (boolP (i \in A)) => [i_in | /negbTE i_in].
    rewrite add0n (bigD1_seq i) ?mem_enum ?enum_uniq //= mulmnE mnm1E eq_refl.
    rewrite muln1 big1_seq ?addn0 // => j /andP[/negbTE j_neqi _].
    by rewrite mulmnE mnm1E j_neqi muln0.
  rewrite big_mkcond big1_seq ?addn0 // => j /andP[_].
  rewrite mem_enum => j_in.
  rewrite mulmnE mnm1E.
  suff /negbTE -> : j != i by rewrite muln0.
  apply/negP => /eqP H.
  by suff //= : j \in A by rewrite H i_in.
have -> : enum A = Tuple (enum_tupleP (mem A)) by [].
have -> : index_enum (ordinal_finType #|A|) = ord_tuple #|A|.
  by rewrite val_ord_tuple /index_enum -enumT.
rewrite -[map _ _]/(tval (map_tuple _ _)).
congr tval; apply/eq_from_tnth => i; rewrite /= tnth_map tnth_ord_tuple.
by rewrite (tnth_nth (enum_val i)) /= -enum_val_nth.
Qed.

Lemma mpoly_for_msym (A : {set 'I_n}) (p : {mpoly R[n]}) s :
  msym s (mpoly_for A p) = mpoly_for A (msym (map_in s) p).
Proof.
rewrite rmorph_sum /=.
apply: esym; rewrite msym_mevalE comp_mpolyE rmorph_sum /=.
apply: eq_bigr => m _ /=; rewrite mpoly_forZ mul_mpolyC msymZ rmorph_prod /=.
congr (_ *: _); rewrite /mmap1 rmorph_prod /=.
apply: eq_bigr => i _ /=; rewrite tnth_map tnth_ord_tuple rmorphX rmorphX /=.
congr (_ ^+  m i); rewrite /pfun.
case: (eqVneq (i \in A)) => [H | /eqP/negP H].
  move eq_j : (enum_rank_in H i) => j.
  have/(congr1 enum_val) := eq_j; rewrite (enum_rankK_in _ H) => ->.
  rewrite map_in_val (mpoly_forXU_in (enum_valP _)) enum_valK_in.
  by rewrite /msym mmapX mmap1U.
by rewrite (out_perm (map_in_perm_on _) H) (mpoly_forXU_out H) /msym mmapC.
Qed.

Lemma mpoly_for_sym_for (A : {set 'I_n}) (p : {mpoly R[n]}) s 
  (H : perm_on A s) :
  p \is symmetric_for R A -> 
  msym (map_out H) (mpoly_for A p) = mpoly_for A p.
Proof.
move=> p_sym; rewrite msym_mevalE mpoly_forE raddf_sum /=.
have H_perm : (perm_eq (msupp p) [seq (mperm s m) | m <- msupp p]).
  have -> : s = ((s^-1)^-1)%g by rewrite invgK.
  apply: (perm_eq_trans _ (msupp_msym _ _)); rewrite perm_eq_sym.
  apply: (msupp_sym_for (perm_onI H) p_sym).
rewrite (eq_big_perm _ H_perm) /= big_map.
apply: eq_bigr => m _; rewrite (msym_for_coeff _ H p_sym).
rewrite comp_mpolyZ; congr (_ *: 'X_[ _ ] *: _).
  apply/mnmP => i; rewrite !mnmE.
  by case: ifP => // /negP/negP i_in; rewrite (out_perm H i_in).
rewrite comp_mpolyX (@mpolyXE _ _ (map_out H)).
by apply: eq_bigr => i _; rewrite tnth_map tnth_ord_tuple !mnmE map_out_val. 
Qed.

Lemma msym_for_msym (A : {set 'I_n}) (p : {mpoly R[n]}) :
  (p \is symmetric_for R A) = ((mpoly_for A p) \is symmetric).
Proof.
apply/issym_forP/issymP => [H s | H s s_on].
  have /issym_forP Hsym := H; rewrite -[s]map_inK.
  by apply: (mpoly_for_sym_for (map_in_perm_on s) Hsym).
have /issymP Hsym := H; pose t := map_out s_on.
rewrite [RHS](mpoly_for_mpolyE A) -(H t).
by rewrite mpoly_for_msym -mpoly_for_mpolyE /t map_outK.
Qed.

Lemma mpoly_for_mpolyOver (A : {set 'I_n}) (p : {mpoly R[n]}) 
      S (ringS : semiringPred S) (kS : keyed_pred ringS) :
  (p \is a mpolyOver n kS) = (mpoly_for A p \is a mpolyOver #|A| (mpolyOver n kS)).
Proof.
apply/mpolyOverP/mpolyOverP => [H m | /mpolyOverP H].
  rewrite mpoly_forE raddf_sum /= rpred_sum // => m' _.
  rewrite mcoeffZ rpredM // ?mpolyOverZ ?H ?mpolyOverX //=.
  by rewrite mcoeffX rpred_nat.
apply/mpolyOverP; rewrite [p](mpoly_for_mpolyE A).
apply: rpred_mhorner => //.
by apply/forallP => i; rewrite mpolyOverX.
Qed.



End MPolyFor.

Section MSymForOf.

Variable n : nat.
Variable R : ringType.
Variable A : {set 'I_n}.

Implicit Types m md : 'X_{1..n}.

Local Notation "m # s" := (mperm s m)
  (at level 40, left associativity, format "m # s").


(* pourquoi un pval ? *)
(* possiblement (s^-1)%g à la place de s
 \sum_(m' : [fset (m # fun_of_perm (s^-1)%g) | s : 'S_n]%fset) 'X_[fsval m'].  *)
(*Definition fns := (@pred_fset (perm_for_choiceType (ordinal_finType n))
              (pred_finpredType (perm_for_finType (ordinal_finType n)))
              (@sort_of_simpl_pred (@perm_of (ordinal_finType n) (Phant (ordinal n)))
                 (pred_of_argType (@perm_of (ordinal_finType n) (Phant (ordinal n)))))).*)
(*
About mpeval.
Definition mmsym_for (md : 'X_{1..n}) : {mpoly R[n]} :=



  (mmsym _ ([multinom (if i \in A then md i else 0%N) | i < n]))


  * 'X_[[multinom (if i \in A then 0%N else md i) | i < n]].*)


Definition mmsym_for (md : 'X_{1..n}) : {mpoly R[n]} :=
  \sum_(m <- enum_fset (((@mperm n)^~ md) @` (perm_on A))%fset) 'X_[m]. 


Local Notation "''m_' md" := (mmsym_for md)
  (at level 8, md at level 2, format "''m_' md").
(*
Lemma mmsym_forE md :
  'm_md = (mmsym _ ([multinom (if i \in A then md i else 0%N) | i < n]))
  * 'X_[[multinom (if i \in A then 0%N else md i) | i < n]].
Proof. by []. Qed.
*)
Lemma mmsym_forE md :
  'm_md = \sum_(m <- enum_fset (((@mperm n)^~ md) @` (perm_on A))%fset) 'X_[m].
Proof. (*
rewrite mmsym_forE mmsymE.*)


by []. Qed.

Lemma msupp_mmsym_for md :  
  perm_eq (msupp 'm_md) (enum_fset (((@mperm n)^~ md) @` (perm_on A))%fset).
Proof.
rewrite mmsym_forE; apply/(perm_eq_trans (msupp_sum _ _ _))=> /=.
+ by apply: enum_fset_uniq.
+ move=> h1 h2 _ _ ne_h1h2 m /=; rewrite !msuppX !mem_seq1.
  by apply/negbTE/negP=> /andP[/eqP->]; apply/negP.
(* trop long à passer *)
rewrite (eq_map (fun h => msuppX _ h)).
by rewrite (map_comp (cons^~ [::])) flatten_seq1 filter_xpredT map_id.
Qed.

Definition perm_eq_on md m := [exists s : 'S_n, perm_on A s && (m # s == md)].

Lemma perm_eq_on_sym md m : perm_eq_on md m = perm_eq_on m md.
Proof.
apply/existsP/existsP => [[s /andP[s_on /eqP <-]] | [s /andP[s_on /eqP <-]]].
  by exists (s^-1)%g; rewrite perm_onI /mperm ?mpermKV ?eq_refl.
by exists (s^-1)%g; rewrite perm_onI /mperm ?mpermKV ?eq_refl.
Qed.

(*
Lemma perm_eq_on_mask md m : 
   let maskA := [tuple i \in A | i < n] in
   perm_eq_on md m = ((perm_eq (mask maskA md) (mask maskA m)) &&
     (mask (map negb maskA) md == mask (map negb maskA) m)).
Proof.
move=> maskA.
apply/existsP/andP=> [[s /andP[s_on /eqP <-]] | [Hperm /eqP eq_mask]].
  have -> : tval m = map_tuple m (ord_tuple n).
    congr tval; apply/eq_from_tnth => i.
    by rewrite tnth_map tnth_ord_tuple mnm_tnth.
  have -> : tval (m#s) = map_tuple (m \o s) (ord_tuple n).
    by congr tval; apply/eq_from_tnth => i.
  split.   
    rewrite -!map_mask map_comp perm_map ?uniq_perm_eq //.
    + rewrite map_inj_uniq ?map_id ?mask_uniq -?enumT ?enum_uniq //.
      by apply/perm_inj.
    + by rewrite map_id mask_uniq -?enumT ?enum_uniq.
    + move=> i; rewrite -{1}[i](permKV s) (mem_map (@perm_inj _ _)) map_id.
      rewrite /maskA -enumT -filter_mask mem_filter [RHS]mem_filter /=.
      by rewrite enumT !mem_index_enum !andbT perm_closed ?perm_onI ?s_on.
  apply/eqP; rewrite -!map_mask map_comp [in LHS]map_id.
  congr (map m _); apply/eq_in_map => x.
  rewrite /maskA -map_comp -enumT -filter_mask mem_filter /= => /andP[x_in _].
  by apply: (out_perm s_on x_in).  
have H1 m' : perm_eq (mask maskA m' ++ mask (map negb maskA) m') m'.
About perm_eq_on.

Search _ mask.
Search _ perm_eq (_ ++ _).



Search _ map (_ = _) in seq.
map_mask:
  forall (T1 T2 : Type) (f : T1 -> T2) (m : bitseq) (s : seq T1),
  [seq f i | i <- mask m s] = mask m [seq f i | i <- s]
perm_map:
  forall (T1 T2 : eqType) (f : T1 -> T2) (s t : seq T1),
  perm_eq s t -> perm_eq [seq f i | i <- s] [seq f i | i <- t]
*)

Lemma msupp_mmsym_forP md m : (m \in msupp 'm_md) = perm_eq_on md m.
Proof.
rewrite (perm_eq_mem (msupp_mmsym_for _)).
apply/imfsetP/existsP=>[[s /perm_onI son ->]|[s /andP[/perm_onI son /eqP <-]]].
  by exists (s^-1)%g; rewrite /mperm mpermKV son eq_refl.
by exists (s^-1)%g; rewrite ?/mperm ?mpermKV.
Qed.

(* assure la compatibilité avec ceux de florent *)
Lemma mcoeff_mmsym_for md m : ('m_md)@_m = (perm_eq_on md m)%:R.
Proof.
case: (boolP (perm_eq_on md m)); rewrite -msupp_mmsym_forP; last first.
  by move/memN_msupp_eq0 => ->.
rewrite linear_sum -(eq_big_perm _ (msupp_mmsym_for _)) /= => m_in.
rewrite (bigD1_seq _ m_in (msupp_uniq _)) /= mcoeffX eq_refl big1_seq ?addr0 //.
by move=> i /andP[/negbTE i_neqm _]; rewrite mcoeffX i_neqm.
Qed.

Lemma mmsym_sym_for md : 'm_md \is symmetric_for _ A.
Proof.
apply/issym_forP => s s_on; apply/mpolyP => m.
rewrite mcoeff_sym !mcoeff_mmsym_for; congr ((nat_of_bool _)%:R).
apply/existsP/existsP => [[t /andP[t_on /eqP <-]] | [t /andP[t_on /eqP <-]]].
  by exists (t * s)%g; rewrite /mperm mpermM eq_refl andbT perm_onM.
by exists (t * s^-1)%g; rewrite /mperm mpermM mpermKV perm_onM ?perm_onI /=.
Qed.

End MSymForOf.

Section MSymForOfSuite.

Definition msort_for n (A : {set 'I_n}) (m : 'X_{1..n}) :=
  let tm := [tuple m (enum_val i) | i < #|A|] in
  let tm_s := Tuple (sort_tupleP leq tm) in
  [multinom (pfun (fun (x : 'I_n) => (fun (H : x \in A) => 
      tnth tm_s (enum_rank_in H x))) m) i | i < n].

Lemma perm_eq_msort_for n (A : {set 'I_n}) (m : 'X_{1..n}) : 
    perm_eq_on A (@msort_for n A m) m.
Proof.
case: n A m => [A m | n A m].
  apply/existsP; exists 1%g; rewrite /mperm mperm1 perm_on1 /=.
  by apply/eqP/val_inj; rewrite (tuple0 m) (tuple0 (msort_for A m)).
apply/existsP; rewrite /msort_for.
set tm := [tuple m (enum_val i) | i < #|A|].
set tm_s := Tuple (sort_tupleP leq tm).
have /tuple_perm_eqP[s] : perm_eq tm_s tm by apply/perm_eqlE/perm_sort.
move/val_inj => eq_s.
exists (map_in s); rewrite map_in_perm_on /=.
apply/eqP/mnmP => i; rewrite /mperm !mnmE /pfun.
case: (eqVneq (i \in A)) => [H | /eqP/negP H].
  move eq_j : (enum_rank_in H i) => j.
  move/(congr1 enum_val) : eq_j; rewrite (enum_rankK_in H H) => ->.
  by rewrite map_in_val eq_s tnth_map tnth_ord_tuple tnth_map tnth_ord_tuple.
by rewrite (out_perm (map_in_perm_on _) H).
Qed.

Lemma sorted_msort_for n (A : {set 'I_n}) (m : 'X_{1..n}) :
  sorted leq [seq (msort_for A m) (enum_val i) | i <- enum 'I_#|A|].
Proof.
suff -> : [seq (msort_for A m) (enum_val i) | i <- enum 'I_#|A|] = 
    sort leq [seq m (enum_val i) | i <- enum 'I_#|A|].
  by rewrite sort_sorted // => x y; rewrite leq_total.
rewrite /msort_for.
set tm := [tuple m (enum_val i) | i < #|A|].
set tm_s := Tuple (sort_tupleP leq tm).
apply/(@eq_from_nth _ 0%N); rewrite /= ?size_sort ?size_map // => i.
rewrite -enumT size_enum_ord => ord_i.
have := enum_valP (Ordinal ord_i).
set j := enum_val _ => j_in.
rewrite (nth_map (enum_rank_in j_in j)) ?size_enum_ord // mnmE /pfun.  
case: (eqVneq _) => [H | /eqP/negP]; last by rewrite enum_valP.
by rewrite enum_valK_in /tm_s (tnth_nth 0%N) /j /= nth_enum_ord //.
Qed.

Lemma issym_symm_forE n (R : ringType) (A : {set 'I_n}) (p : {mpoly R[n]}) :
  p \is symmetric_for _ A ->
  p = \sum_(m <- msupp p | sorted leq ([tuple m (enum_val i) | i < #|A|])) 
                        p@_m *: mmsym_for R A m.
Proof.
move=> Hsym; apply/mpolyP => m.
case: (boolP (m \in msupp p)) => Hm; last first.
  rewrite (memN_msupp_eq0 Hm); symmetry.
  rewrite linear_sum /= big_seq_cond big1 // => /= m' /andP[m'_in m'_sorted].
  rewrite mcoeffZ mcoeff_mmsym_for.
  case: (boolP (perm_eq_on _ _ _)) => [/existsP[] | Hperm]; last by rewrite mulr0.
  move=> s /andP[s_on /eqP <-].
  by rewrite (msym_for_coeff _ s_on Hsym) (memN_msupp_eq0 Hm) mul0r.
case: (set_0Vmem A) => [A_eq0 | ].
  congr (_ @_ _); rewrite [in LHS](mpolyE p) A_eq0.
  apply: eq_big => [i /= |i _].
    suff -> : enum ('I_#|set0|) = [::] by [].
    by move=> t; apply/eqP; rewrite -size_eq0 size_enum_ord cards0.
  congr (_ *: _); rewrite mmsym_forE. 
  suff H : perm_eq (enum_fset [fset mperm x i | x in perm_on set0]%fset) [:: i].
    by rewrite (eq_big_perm _ H) /= big_seq1.
  apply: (uniq_perm_eq (enum_fset_uniq _)) => // m'; rewrite inE.
  apply/imfsetP/eqP => [[s /= /out_perm Hs ->] | ->].
    suff ->: s = (1%g : 'S_n) by rewrite /mperm mperm1.
    by apply/permP=> j; rewrite Hs ?in_set0 ?perm1.
  exists (1%g : 'S_n) => /=; last by rewrite /mperm mperm1.
  by have // : perm_on set0 (1%g : 'S_n) by rewrite perm_on1.
move=> [k k_in].
rewrite big_mkcond (bigD1_seq (msort_for A m)) /= ?msupp_uniq //; first last.
  have /existsP[s /andP[s_on /eqP <-]] := perm_eq_msort_for A m.
  by rewrite (issym_for_msupp _ s_on Hsym).
rewrite -big_mkcondr /= raddfD /= [X in _ + X]raddf_sum big1. 
  rewrite addr0 sorted_msort_for.
  have /existsP[s /andP[s_on /eqP <-]] := (perm_eq_msort_for A m).
  rewrite (msym_for_coeff _ s_on Hsym) mcoeffZ mcoeff_mmsym_for.
  suff -> : perm_eq_on A (mperm s m) m by rewrite mulr1.
  by apply/existsP; exists s; rewrite eq_refl s_on.
move=> m' /andP[/negP m'_neq Hsorted]; rewrite /= mcoeffZ.
suff -> : (mmsym_for R A m')@_m = 0 by rewrite mulr0.
rewrite mcoeff_mmsym_for.
suff -> : (perm_eq_on A m' m) = false by rewrite /=.
set tm := [tuple m (enum_val i) | i < #|A|].
set tm_s := Tuple (sort_tupleP leq tm).
have tm_perm : perm_eq tm_s tm by rewrite /= perm_sort.
rewrite /perm_eq_on. 
apply: negbTE; rewrite negb_exists.
apply/forallP => s; rewrite negb_and.
apply/orP; case: (boolP (perm_on _ _)) => [s_on /= | _  //=]; last by left.
right; apply/negP => /eqP eq_m'; apply: m'_neq; apply/eqP.
move: Hsorted; rewrite -eq_m' => Hsorted.
apply/mnmP => i.
case: (boolP (i \in A)) => [H | /negP/negP H]; last first.
  by rewrite /mperm mnmE (out_perm s_on H) /msort_for mnmE (pfun_out _ _ H).
move eq_j : (enum_rank_in H i) => j.
have <- := (enum_rankK_in H H); rewrite eq_j.
have -> : (mperm s m) (enum_val j) = nth 0%N [seq (mperm s m) (enum_val i) | i <- enum 'I_#|A|] j.
  by rewrite (nth_map j) ?nth_ord_enum // size_enum_ord ltn_ord.
have -> : (msort_for A m) (enum_val j) = nth 0%N [seq (msort_for A m) (enum_val i) | i <- enum 'I_#|A|] j.
  by rewrite (nth_map j) ?nth_ord_enum // size_enum_ord ltn_ord.
congr (nth _ _ _).
apply: (@eq_sorted _ leq _ _ _ _ Hsorted (sorted_msort_for _ _)).
+ by move=> y x z; apply: leq_trans.
+ by move=> x y; rewrite -eqn_leq => /eqP ->.
move=> {m' eq_m' i H eq_j k k_in}; rewrite -[enum _]/(tval (ord_tuple #|A|)).
rewrite -![map _ _]/(tval (map_tuple _ _)).
apply/tuple_perm_eqP.
have /tuple_perm_eqP[t1 /val_inj eq_t1] := tm_perm; pose t2 := map_out s_on.
exists (t2 * (t1^-1)%g)%g; congr tval; apply/eq_from_tnth => i.
rewrite !tnth_map !tnth_ord_tuple /mperm mnmE /msort_for mnmE -/tm -/tm_s eq_t1.
rewrite permM /pfun.
case: (eqVneq _) => [H | /eqP/negP]; last by rewrite enum_valP.
by rewrite !tnth_map !tnth_ord_tuple enum_valK_in permKV /t2 map_out_val.
Qed.



(*
Lemma dhomog_mmsym md : 'm_md \is (mdeg md).-homog.
Proof.
apply/dhomogP => m; rewrite msupp_mmsym_forP bla1 => /existsP[s /eqP <-].
by rewrite /mperm /= mdeg_mperm.
Qed.
*)

Lemma mmsym_for_neq0 n (R : ringType) (A : {set 'I_n}) (md : 'X_{1..n}) : 
   mmsym_for R A md != 0.
Proof.
apply/eqP/mpolyP; move/(_ md); apply/eqP.
rewrite mcoeff0 mcoeff_mmsym_for. 
suff -> : perm_eq_on A md md by rewrite oner_neq0.
by apply/existsP; exists (1%g); rewrite perm_on1 /mperm mperm1 eq_refl.
Qed.

Lemma mpoly_for_mmsym_for n (R : comRingType) (A : {set 'I_n}) (m : 'X_{1..n}) :
  mmsym_for R A m = ((mmsym R [multinom m (enum_val i) | i < #|A|]) \mPo 
  [tuple 'X_(enum_val i) | i < #|A|]) *
  'X_[[multinom if i \in A then 0%N else m i | i < n]].
Proof.
rewrite mmsymE rmorph_sum /= big_distrl /= mmsym_forE.
rewrite [RHS](eq_bigr (fun (md : 'X_{1..(#|A|)}) => 'X_[[multinom 
   (pfun (fun (x : 'I_n) => (fun (H : x \in A) => tnth md (enum_rank_in H x))) 
    m) i | i < n]])); last first.
  move=> md _; rewrite mpolyXE_id rmorph_prod /=.
  set m' := [multinom pfun (fun (x : 'I_n) (H : x \in A) => 
                                       tnth md (enum_rank_in H x)) m i | i < n].
  rewrite (eq_bigr (fun i => 'X_(enum_val i) ^+ m' (enum_val i))); last first.
    move=> i _; rewrite rmorphX /= comp_mpolyXU -tnth_nth tnth_map.
    rewrite tnth_ord_tuple.
    congr (_ ^+ _); rewrite /m' mnmE /pfun.
    case: (eqVneq _) => [H | /eqP/negP]; first by rewrite enum_valK_in.
    by rewrite enum_valP.    
  rewrite -(big_enum_val _ _ (fun i => 'X_i ^+ m' i)) /= mpolyXE_id big_mkcond.
  rewrite [X in _ * X](eq_bigr (fun i => if i \in ~: A then 'X_i ^+ m' i else 1)); last first.
    move=> i _; rewrite mnmE in_setC; case: (boolP (i \in A)) => //= H.
    by rewrite /m' mnmE (pfun_out _ _ H).
  by rewrite -!big_mkcond /= -{1}(setTI A) -setTD -big_setID mpolyXE_id big_set.
set f := (fun (i : 'X_{1..(#|A|)}) => [multinom pfun (fun (x : 'I_n) 
                 (H : x \in A) => tnth i (enum_rank_in H x)) m i0 | i0 < n]).
rewrite [RHS](eq_bigr (fun i => 'X_[f i])); last by move=> md _; rewrite /f.
rewrite -[RHS](big_map f xpredT).
apply: eq_big_perm.
apply: uniq_perm_eq.
    by rewrite enum_fset_uniq.
  rewrite map_inj_uniq ?enum_fset_uniq // => x y.
  move/mnmP => eq_f; apply/mnmP => i.
  suff Heq md : (f md) (enum_val i) = md i by rewrite -!Heq eq_f.
  rewrite /f mnmE /pfun.
  case: (eqVneq _) => [H | /eqP/negP]; first by rewrite enum_valK_in.
  by rewrite enum_valP.
move=> i.
rewrite -[i \in enum_fset _]/(_ \in [fset _ | _ in _]%fset) /=.
apply/imfsetP/mapP => [[s /= s_on eq_i] | [j /imfsetP[s /= s_on eq_j] eq_i]].
  exists [multinom ((mperm s m) (enum_val j)) | j < #|A|].
    rewrite -[X in X \in _]mperm1 /mperm.
    rewrite -[_ \in enum_fset _]/(_ \in [fset _ | _ in _]%fset) /=.
    apply/imfsetP; exists (map_out s_on); rewrite //=.
    by apply/mnmP => j; rewrite !mnmE map_out_val perm1.
  apply/mnmP=> j; rewrite eq_i /f mnmE /mperm mnmE /pfun.
  case: (eqVneq _) => [H | /eqP/negP H]; last by rewrite (out_perm s_on H).
  by rewrite tnth_map tnth_ord_tuple (enum_rankK_in H H) mnmE.
exists (map_in s); first by apply: map_in_perm_on.
rewrite eq_i eq_j.
apply/mnmP => k; rewrite /f /mperm !mnmE /pfun.
case: (eqVneq _) => [H | /eqP/negP H].
  by rewrite tnth_map mnmE tnth_ord_tuple -[in RHS](enum_rankK_in H H) map_in_val.
by rewrite (out_perm (map_in_perm_on _) H).
Qed.


End MSymForOfSuite.



End mpoly_ajouts.
  
Notation "p '.@[' v , A ']' " := (mpeval A v p)
  (at level 2, left associativity, format " p .@[ v , A ]").

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

Lemma seqroots_separable P :
  separable_poly P -> uniq (seqroots P).
Proof.
case: (boolP (P == 0)) => [/eqP -> _ | P_neq0].
  by rewrite /seqroots eq_refl.
rewrite [X in separable_poly X]seqroots_poly separable_polyZ ?lead_coef_eq0 //.
by rewrite -separable_prod_XsubC.
Qed.

(*  complete set of roots   *)
(*Definition set_roots {I : finType} (S : pred_class) c := [qualify a f : {ffun I -> T} | 
      ((c *: \prod_(i : I) ('X - (f i)%:P)) \is a polyOver S)].*)
Definition set_roots (S : pred_class) c := [qualify a f : {fset T} |
      ((c *: \prod_(x <- enum_fset f) ('X - x%:P)) \is a polyOver S)].

Fact set_roots_key S c : pred_key (@set_roots S c). Proof. by []. Qed.
Canonical set_roots_keyed S c := KeyedQualifier (@set_roots_key S c).

Lemma set_rootsE S c f :
  (f \is a set_roots S c) = ((c *: \prod_(x <- enum_fset f) ('X - x%:P)) \is a polyOver S).
Proof. by []. Qed.

(*
Lemma set_roots_seqroots S (ringS : @subringPred T S) (kS : keyed_pred ringS) 
    (P : {poly T}) : P \is a polyOver kS ->
    finfun (tnth (in_tuple (seqroots P))) \is a set_roots kS (lead_coef P).
Proof.
rewrite {1}[P]seqroots_poly /set_roots; set r := index_enum _.
have {1}-> : seqroots P = [seq (fun i => (finfun (tnth (in_tuple (seqroots P)))) i) i | i <- r]. 
  rewrite -{1}[seqroots P]/(tval (in_tuple (seqroots P))).
  rewrite -map_tnth_enum /r /index_enum -enumT /=.
  by apply: eq_map; move=> i; rewrite ffunE.
by rewrite big_map.
Qed.
*)
Lemma set_roots_seqroots S (ringS : @subringPred T S) (kS : keyed_pred ringS)
    (P : {poly T}) : separable_poly P -> P \is a polyOver kS ->
    seq_fset (seqroots P) \is a set_roots kS (lead_coef P).
Proof.
move/seqroots_separable => uniq_P; rewrite {1}[P]seqroots_poly /set_roots.
by rewrite -(eq_big_perm _ (uniq_perm_eq (enum_fset_uniq _) _ (seq_fsetE _))).
Qed.

Lemma set_roots_lead_coef S (ringS : @subringPred T S) (kS : keyed_pred ringS)
    c l : l \is a set_roots kS c -> c \in kS.
Proof.
move/polyOverP; set P := \prod_(_ <- _) _; move/(_ (size P).-1); rewrite coefZ.
have /monicP : P \is monic by apply: monic_prod_XsubC.
by rewrite /lead_coef => ->; rewrite mulr1.
Qed.

(* la définition fera le lien avec le changement pour plus tard *)
(* Definition cset_of_roots {R : finType} P := 
    [qualify a f : {ffun R -> T} | perm_eq (codom f) (seqroots P)]. *)

Local Notation "''s_' ( n , k )" := (@mesym n _ k).

(* revoir le state du th *)
(*
Lemma seqroots_pred S (ringS : @subringPred T S)
      (kS : keyed_pred ringS) c m (l : T ^ m) : 
   l \is a set_roots kS c -> forall i : 'I_m,
  (c *: 's_(m, i.+1)).@[l] \in kS.
Proof.
rewrite /set_roots /=; move=> l_setroots i; rewrite mevalZ.
case: (boolP (c == 0)) => [/eqP -> | /negbTE c_neq0].
  by rewrite mul0r; apply: rpred0.
rewrite -[_.@[ _]](signrMK i.+1) (eq_meval _ (ffun_tupleE _)).
move: (ltn_ord i); rewrite -ltnS => ord_iS. 
rewrite (ordnat ord_iS) -mroots_coeff big_tuple mulrCA rpredMsign -coefZ.
apply/polyOverP; rewrite (eq_bigr (fun i => 'X - (l i)%:P)) // => j _.
by rewrite ffun_tupleE.
Qed.*)
Lemma seqroots_pred S (ringS : @subringPred T S) (kS : keyed_pred ringS) c m 
  (l : T ^ m) : injective l -> 
  [fset (l i) | i : 'I_m]%fset \is a set_roots kS c -> forall i : 'I_m,
  (c *: 's_(m, i.+1)).@[l] \in kS.
Proof.
move=> inj_l; rewrite /set_roots /=; move=> l_setroots i; rewrite mevalZ.
case: (boolP (c == 0)) => [/eqP -> | /negbTE c_neq0].
  by rewrite mul0r; apply: rpred0.
rewrite -[_.@[ _]](signrMK i.+1) (eq_meval _ (ffun_tupleE _)).
move: (ltn_ord i); rewrite -ltnS => ord_iS. 
rewrite (ordnat ord_iS) -mroots_coeff mulrCA rpredMsign -coefZ /=.
apply/polyOverP; erewrite congr2; first exact: l_setroots; last by [].
congr (c *: _). apply: (eq_big_perm _ (uniq_perm_eq _ (enum_fset_uniq _) _)).
  by rewrite map_inj_uniq ?enum_uniq.
move=> j /=; rewrite -[j \in enum_fset _]/(j \in [fset l i0 | i0 in 'I_m]%fset).
apply/mapP/imfsetP => [[k k_in ->] | [k /= k_in ->]]; exists k => //.
by rewrite mem_enum.
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

(* th fond caché, pour les seqroots *)
Lemma sym_fundamental_set_roots_proper S (ringS : @subringPred T S) 
  (kS : keyed_pred ringS) c m p (l : T ^ m) : injective l ->
  [fset (l i) | i : 'I_m]%fset \is a set_roots kS c -> p \is a mpolyOver m kS ->
  p \is symmetric -> c ^+ (msize p).-1 * p.@[l] \in kS.
Proof.
move=> l_inj l_setroots p_over p_sym.  
move: (sym_fundamental_subring p_over p_sym) => [q /andP[/eqP eq_qp /andP[size_le q_over]]].
rewrite {2}eq_qp meval_comp_mpoly -mevalZ [q]mpolyE scaler_sumr rmorph_sum /=.
rewrite big_seq; apply: rpred_sum => i i_msupp /=; rewrite !mevalZ mulrCA.
apply: rpredM; rewrite -?mevalZ; first by move/mpolyOverP: q_over; move/(_ i).
rewrite mpolyXE_id -[(msize p).-1](@subnK (\sum_(j < m) i j)); last first.
  move/(leq_sub2r 1%N): size_le; rewrite [X in (_ <= X)%N]subn1 => size_le.
  apply: (leq_trans _ size_le).
  apply: (leq_trans _ (leq_sub2r 1%N (leq_msize_meight q))). 
  case: (boolP (q == 0)) => [/eqP q_eq0 | H ].
    by move: i_msupp; rewrite q_eq0 msupp0 in_nil.
  rewrite -(leq_add2r 1%N) addn1 subn1 addn1 prednK; last first.
    by rewrite lt0n msize_poly_eq0.
  by rewrite -mdegE msize_mdeg_lt ?i_msupp.
rewrite exprD -scalerA mevalZ.
apply: (rpredM (rpredX _ (set_roots_lead_coef l_setroots))).
rewrite -prodrXr -scaler_prod rmorph_prod /=.
apply: rpred_prod => j _; rewrite -exprZn rmorphX /=.
apply: rpredX; rewrite mevalZ mevalX !tnth_map /= -mevalZ.
by apply: seqroots_pred.
Qed.


Lemma sym_fundamental_set_roots S (ringS : @subringPred T S) 
  (kS : keyed_pred ringS) c m p (l : T ^ m) : injective l ->
  [fset (l i) | i : 'I_m]%fset \is a set_roots kS c -> p \is a mpolyOver m kS ->
  p \is symmetric -> c ^+ (msize p) * p.@[l] \in kS.
Proof.
move=> l_inj l_setroots p_over p_sym.  
move: (sym_fundamental_subring p_over p_sym) => [q /andP[/eqP eq_qp /andP[size_le q_over]]].
rewrite {2}eq_qp meval_comp_mpoly -mevalZ [q]mpolyE scaler_sumr rmorph_sum /=.
rewrite big_seq; apply: rpred_sum => i i_msupp /=; rewrite !mevalZ mulrCA.
apply: rpredM; rewrite -?mevalZ; first by move/mpolyOverP: q_over; move/(_ i).
rewrite mpolyXE_id -[msize p](@subnK (\sum_(j < m) i j)); last first.
  rewrite -mdegE; apply: (leq_trans _ size_le).
  apply: (leq_trans _ (leq_msize_meight q)).
  by apply: (leq_trans _ (msize_mdeg_lt i_msupp)).
rewrite exprD -scalerA mevalZ.
apply: (rpredM (rpredX _ (set_roots_lead_coef l_setroots))).
rewrite -prodrXr -scaler_prod rmorph_prod /=.
apply: rpred_prod => j _; rewrite -exprZn rmorphX /=.
apply: rpredX; rewrite mevalZ mevalX !tnth_map /= -mevalZ.
by apply: seqroots_pred.
Qed.


(* th fond caché, pour les poly de poly : généraliser pour cacher le poly de poly *)
Lemma sym_fundamental_seqroots_empil S (ringS : @subringPred T S) 
  (kS : keyed_pred ringS) c n m p (l : T ^ m) :
  injective l -> [fset (l i) | i : 'I_m]%fset \is a set_roots kS c ->
  p \is a (mpolyOver m (mpolyOver n kS)) -> p \is symmetric -> 
  c ^+ (msize p) *: p.@[finfun ((@mpolyC n T) \o l)] \is a mpolyOver n kS.
Proof.
move=> l_inj l_setroots p_over p_sym.  
move: (sym_fundamental_subring p_over p_sym) => [q /andP[/eqP eq_qp /andP[size_le q_over]]].
rewrite {2}eq_qp meval_comp_mpoly -mul_mpolyC.
set t := tnth _; rewrite -[_%:MP_[n]](mevalC t) -mevalM mul_mpolyC.
rewrite [q]mpolyE scaler_sumr rmorph_sum /=.
rewrite big_seq; apply: rpred_sum => i i_msupp /=; rewrite !mevalZ mulrCA.
apply: rpredM; rewrite -?mevalZ; first by move/mpolyOverP: q_over; move/(_ i).
rewrite mpolyXE_id -[msize p](@subnK (\sum_(j < m) i j)); last first.
  rewrite -mdegE; apply: (leq_trans _ size_le).
  apply: (leq_trans _ (leq_msize_meight q)).
  by apply: (leq_trans _ (msize_mdeg_lt i_msupp)).
rewrite exprD mpolyCM -scalerA mevalZ.
apply: rpredM.
  by rewrite mpolyOverC; apply: (rpredX _ (set_roots_lead_coef l_setroots)).
rewrite rmorphX /= -prodrXr -scaler_prod rmorph_prod /=.
apply: rpred_prod => j _; rewrite -exprZn rmorphX /=.
apply: rpredX; rewrite mevalZ mevalX /t !tnth_map /= tnth_ord_tuple.
move: (seqroots_pred l_inj l_setroots j); rewrite -(mpolyOverC n).
suff -> : ((c *: 's_(m, j.+1)).@[l])%:MP_[n] =
          c%:MP_[n] * ('s_(m, j.+1))
          .@[finfun((mpolyC n (R:=T)) \o l)] by [].
rewrite -mul_mpolyC mevalM mpolyCM mevalC; congr (c%:MP_[n] * _).
rewrite !mesym_tupleE [in RHS]rmorph_sum /=.
rewrite [X in X%:MP_[n]]rmorph_sum /= rmorph_sum /=.
apply: eq_bigr => u Hu; rewrite !rmorph_prod /=.
by apply: eq_bigr => k _; rewrite !mevalX ffunE.
Qed.

Lemma sym_fundamental_seqroots_empil_proper S (ringS : @subringPred T S) 
  (kS : keyed_pred ringS) c n m p (l : T ^ m) :
  injective l -> [fset (l i) | i : 'I_m]%fset \is a set_roots kS c ->
  p \is a (mpolyOver m (mpolyOver n kS)) -> p \is symmetric -> 
  c ^+ (msize p).-1 *: p.@[finfun ((@mpolyC n T) \o l)] \is a mpolyOver n kS.
Proof.
move=> l_inj l_setroots p_over p_sym.  
move: (sym_fundamental_subring p_over p_sym) => [q /andP[/eqP eq_qp /andP[size_le q_over]]].
rewrite {2}eq_qp meval_comp_mpoly -mul_mpolyC.
set t := tnth _; rewrite -[_%:MP_[n]](mevalC t) -mevalM mul_mpolyC.
rewrite [q]mpolyE scaler_sumr rmorph_sum /=.
rewrite big_seq; apply: rpred_sum => i i_msupp /=; rewrite !mevalZ mulrCA.
apply: rpredM; rewrite -?mevalZ; first by move/mpolyOverP: q_over; move/(_ i).
rewrite mpolyXE_id -[(msize p).-1](@subnK (\sum_(j < m) i j)); last first.
  move/(leq_sub2r 1%N): size_le; rewrite [X in (_ <= X)%N]subn1 => size_le.
  apply: (leq_trans _ size_le).
  apply: (leq_trans _ (leq_sub2r 1%N (leq_msize_meight q))). 
  case: (boolP (q == 0)) => [/eqP q_eq0 | H ].
    by move: i_msupp; rewrite q_eq0 msupp0 in_nil.
  rewrite -(leq_add2r 1%N) addn1 subn1 addn1 prednK; last first.
    by rewrite lt0n msize_poly_eq0.
  by rewrite -mdegE msize_mdeg_lt ?i_msupp.
rewrite exprD mpolyCM -scalerA mevalZ.
apply: rpredM.
  by rewrite mpolyOverC; apply: (rpredX _ (set_roots_lead_coef l_setroots)).
rewrite rmorphX /= -prodrXr -scaler_prod rmorph_prod /=.
apply: rpred_prod => j _; rewrite -exprZn rmorphX /=.
apply: rpredX; rewrite mevalZ mevalX /t !tnth_map /= tnth_ord_tuple.
move: (seqroots_pred l_inj l_setroots j); rewrite -(mpolyOverC n).
suff -> : ((c *: 's_(m, j.+1)).@[l])%:MP_[n] =
          c%:MP_[n] * ('s_(m, j.+1))
          .@[finfun((mpolyC n (R:=T)) \o l)] by [].
rewrite -mul_mpolyC mevalM mpolyCM mevalC; congr (c%:MP_[n] * _).
rewrite !mesym_tupleE [in RHS]rmorph_sum /=.
rewrite [X in X%:MP_[n]]rmorph_sum /= rmorph_sum /=.
apply: eq_bigr => u Hu; rewrite !rmorph_prod /=.
by apply: eq_bigr => k _; rewrite !mevalX ffunE.
Qed.

Lemma sym_fundamental_seqroots_mmsym_for S (ringS : @subringPred T S) 
  (kS : keyed_pred ringS) (c : T) m (l : T ^ m.+1) (A : {set 'I_m.+1}) 
  (md : 'X_{1..m.+1}) :
  injective l -> [fset l i | i in A]%fset \is a set_roots kS c -> 
  c ^+ (\sum_(i < #|A|) (md (enum_val i))) *: 
      (@mpeval _ T A l (mmsym_for T A md)) \is a mpolyOver m.+1 kS.
Proof.
move=> inj_l P_set; rewrite mpoly_for_mmsym_for /= rmorphM /= scalerAl -comp_mpolyZ /=.
apply/rpredM; last first.
  rewrite mpolyXE_id rmorph_prod /= rpred_prod // => i _.
  rewrite mnmE.
  case: (boolP (i \in A)) => [_ | /negbTE H]. 
    by rewrite expr0 mpeval1 rpred1.
  by rewrite rmorphX /= rpredX // mpevalXU H mpolyOverX.
rewrite -comp_mpolyZ /=.
set p := _ *: _.
rewrite [X in comp_mpoly _ X]comp_mpolyEX raddf_sum /=.
rewrite (eq_bigr (fun i => p@_i *: ('X_[i]).@[fun i => (l (enum_val i))%:MP])); last first.
  move=> i _; rewrite comp_mpolyZ; congr (_ *: _).
  rewrite !mpolyXE_id !rmorph_prod /=.
  apply: eq_bigr => j _; rewrite !rmorphX /=.
  congr (_ ^+ _); rewrite mevalX comp_mpolyXU -tnth_nth tnth_map tnth_ord_tuple.
  by rewrite comp_mpolyXU -tnth_nth tnth_map tnth_ord_tuple enum_valP.
pose h := finfun (fun i : 'I_#|A| => l (enum_val i)).
rewrite (eq_bigr (fun i => ((p@_i *: 'X_[i]).@[h])%:MP)); last first.
  move=> i _; rewrite mevalZ -mul_mpolyC rmorphM /=.
  congr (_ * _); rewrite !mpolyXE_id !rmorph_prod /=.
  apply: eq_bigr => j _; rewrite !rmorphX /=.
  by congr (_ ^+ _); rewrite !mevalX /h ffunE.
rewrite -raddf_sum /= mpolyOverC -raddf_sum /= -mpolyE /p mevalZ.
set q := mmsym _ _.
suff -> : ((\sum_(i < #|A|) md (enum_val i)) = (msize q).-1)%N.
  apply: sym_fundamental_set_roots_proper.
  + by move=> x y; rewrite /h !ffunE; move/inj_l/enum_val_inj.
  + suff -> : [fset h i | i : {:'I_(#|A|)}]%fset = [fset l i | i in A]%fset by [].
    apply/fsetP => i; apply/imfsetP/imfsetP => [[j /= j_in ->]|[j /= j_in ->]].
      by exists (enum_val j); rewrite ?enum_valP // /h ffunE.
    by exists (enum_rank_in j_in j); rewrite //= /h ffunE enum_rankK_in ?j_in.
  + by rewrite /q mmsymE rpred_sum // => i _; rewrite mpolyOverX.
  + by rewrite /q mmsym_sym.
rewrite msizeE.
set m' := [multinom md (enum_val i) | i < #|A|].
move: (dhomog_mmsym T m').
rewrite -/q dhomogE /= => /allP H.
rewrite [in RHS]big_seq_cond.
rewrite [in RHS](eq_bigr (fun m0 => (mdeg m').+1)); last first.
  by move=> i /andP[i_in _]; move/eqP : (H i i_in) => ->.
rewrite -big_seq_cond.
have -> : \max_(i <- msupp q) (mdeg m').+1 = (mdeg m').+1.
  apply/eqP; rewrite big_tnth eqn_leq; apply/andP; split.
    by apply/bigmax_leqP => i _; rewrite leqnn.
  move: (mmsym_neq0 T m'); rewrite -msupp_eq0 -size_eq0 -/q -lt0n => ord_q.
  by apply: (bigmax_sup (Ordinal ord_q)).
rewrite mdegE /=.
by apply: eq_bigr => i _; rewrite /m' mnmE.
Qed.


Lemma sym_fundamental_seqroots_for S (ringS : @subringPred T S) 
  (kS : keyed_pred ringS) c m p (l : T ^ m.+1) P :
  partition P [set: 'I_m.+1] -> injective l ->
  {in P, forall Q : {set 'I_m.+1}, 
    [fset l i | i in Q]%fset \is a set_roots kS c} ->
  p \is a mpolyOver m.+1 kS -> 
  {in P, forall Q, p \is (@symmetric_for _ _ Q)} -> 
  c ^+ (msize p).-1 * p.@[l] \in kS.
Proof.
move card_P : #|P| => n.
move eq_D : [set: 'I_m.+1] => D.
move=> part_P_D inj_l l_set p_over p_symm.
have n_neq0 : n != 0%N.
  apply/negP; rewrite -card_P cards_eq0 => /eqP P_eq0.
  move/(congr1 (fun s : {set _} => #|s|))/eqP: eq_D.
  rewrite (card_partition part_P_D) P_eq0 big_set0 cardsT card_ord.
  by apply/negP; rewrite -lt0n.
have c_over : c \in kS.
  pose Q := head set0 (enum P).
  have HQ : Q \in enum P by rewrite /Q -nth0 mem_nth // -cardE card_P lt0n.
  have {HQ} Q_in : Q \in P by move: HQ; rewrite /(enum _) mem_filter => /andP[].
  by apply: (set_roots_lead_coef (l_set Q Q_in)).

move: l p inj_l l_set c_over p_over p_symm ; wlog : c / c = 1.
move=> ih l p inj_l l_set c_in p_over p_symm.
move: p_over p_symm; wlog: p / (p \is homog [measure of mdeg]).  
  move=> ihp p_over p_symm.
  rewrite {2}[p](@pihomog_partitionE _ _ [measure of mdeg] _ _ (leqnn _)).
  rewrite rmorph_sum /= mulr_sumr rpred_sum // => i _.
  rewrite -[(msize p).-1](@subnK i); last first.
    rewrite -ltnS prednK ?ltn_ord //.
    by apply: (leq_ltn_trans (leq0n i) (ltn_ord _)).
  rewrite exprD -mulrA rpredM // ?mpolyOverC ?rpredX //.
  set q := pihomog _ _ _.
  case: (boolP (q == 0)) => [/eqP -> | q_neq0].
    by rewrite meval0 mulr0 rpred0.
  have q_dhomog : q \is i.-homog by apply/pihomogP.
  have q_homog : q \is homog [measure of mdeg] by apply/homogP; exists i.
  rewrite -[nat_of_ord _]/(_.+1.-1) -(dhomog_size q_dhomog q_neq0).
  apply: (ihp q q_homog).
    rewrite /q /pihomog rpred_sum // => m' _.
    by rewrite mpolyOverZ ?mpolyOverX ?(mpolyOverP _ p_over).
  move=> Q Q_in; rewrite /q /pihomog.
  apply/issym_forP => s s_on; rewrite raddf_sum /= [in RHS]big_seq_cond.
  rewrite -(eq_big_perm _ (msupp_sym_for (perm_onI s_on) (p_symm Q Q_in))) /=.
  rewrite (eq_big_perm _ (msupp_msym _ (s^-1)%g)) /= big_map /= big_seq_cond.
  apply: congr_big => // m'; rewrite ?mdeg_mperm // => /andP[m'_in m'_deg].
  rewrite msymZ msymX /= fingroup.invgK mpermKV.
  by rewrite -(msym_for_coeff m' s_on (p_symm Q Q_in)) /mperm.
  move=> /homogP[d p_homog] p_over p_symm.  
  case: (boolP (p == 0)) => [/eqP -> | p_neq0].
    by rewrite meval0 mulr0 rpred0.
  case: (boolP (c == 0)) => [/eqP -> | c_neq0].
    rewrite expr0n -subn1 subn_eq0.
    case: (boolP (_ <= _)%N) => [/msize1_polyC -> | _] /=.
      by rewrite mul1r mevalC (mpolyOverP _ p_over).
    by rewrite mul0r rpred0.
  have -> : c ^+ (msize p).-1 * p.@[l] = 1 ^+ (msize p).-1 * 
      p.@[(finfun (fun i : 'I_m.+1 => c * (l i)))]. 
    rewrite expr1n mul1r !mevalE mulr_sumr big_seq_cond [in RHS]big_seq_cond.
    apply: eq_bigr => m' /andP[m'_in _]; rewrite mulrCA.
    congr (_ * _); rewrite (dhomog_size p_homog p_neq0) /=.
    rewrite -(dhomogP _ _ _ (p_homog) m' m'_in) /= mdegE -prodrXr -big_split /=.
    by apply: eq_bigr => i _; rewrite ffunE exprMn.
  have innj_cl : injective (finfun (fun i : 'I_m.+1 => c * l i)).
    by move=> x y; rewrite !ffunE => /(mulfI c_neq0) /inj_l.
  apply: ih => //; rewrite ?rpred1 //.  
  + move=> Q Q_in; rewrite set_rootsE scale1r.
    apply/polyOverP => k; rewrite big_fset_set /=.
    rewrite (eq_bigl (fun i => i \in Q)); last by move=> i; rewrite andbT.
    rewrite big_enum_val /=.
    pose cs := (finfun (fun i : 'I_(#|Q|) => c * l (enum_val i))).
    rewrite (eq_bigr (fun i => 'X - (cs i)%:P)); last first.
      by move=> i _; rewrite /cs !ffunE.
    case: (boolP (k < #|Q|.+1)%N) => [ord_k | ]; last first.
      rewrite -leqNgt => k_gt.
      set q := \prod_ _ _.
      move: k_gt.
      have -> : #|Q|.+1 = size q.
        by rewrite size_prod_XsubC /index_enum -enumT size_enum_ord.
      by move/leq_sizeP/(_ _ (leqnn _)) => ->; apply: rpred0.
    rewrite -[k]/(nat_of_ord (Ordinal ord_k)) mroots_coeff_proper /cs.
    apply/rpredM; rewrite ?rpred_sign //.
   (* have := (seqroots_pred inj_l (l_set Q Q_in)). *)
    move eq_nb : (_ - _)%N => nb; rewrite mesym_tupleE raddf_sum /=.
    rewrite (eq_bigr (fun (i : nb.-tuple 'I_(#|Q|))  => 
      (\prod_(x <- i) (c * ('X_x).@[finfun (l \o enum_val)]) ))); last first.
      move=> t _; rewrite rmorph_prod /=.
      by apply: eq_bigr => i _; rewrite !mevalX !ffunE.
    rewrite (eq_bigr (fun (i : nb.-tuple 'I_(#|Q|)) =>
      (c^+ (\sum_(x <- i) 1%N)%N) * \prod_(x <- i) ('X_x).@[finfun (l \o enum_val)])); last first.
      move=> t _; rewrite -prodrXr -big_split /=.
      by apply: eq_bigr => i _; rewrite expr1.
    rewrite (eq_bigr (fun (i : nb.-tuple 'I_(#|Q|)) =>
      (c^+ nb * (\prod_(x <- i) ('X_x)).@[finfun (l \o enum_val)]))); last first.
      move=> t _; rewrite big_tuple -(big_mkord xpredT (fun i => 1%N)).
      by rewrite sum_nat_const_nat subn0 muln1 -rmorph_prod.
    rewrite -big_distrr /= -raddf_sum /= -mesym_tupleE.
    set q := 's_( _ , _).
    have -> : nb = (msize q).-1.
      rewrite (dhomog_size (dhomog_mesym _ _ _) (mesym_neq0 _ _ )) //=.
      by rewrite -eq_nb leq_subr.
    apply: sym_fundamental_set_roots_proper.
    + by move=> x y; rewrite !ffunE /=; move/inj_l/enum_val_inj.
    + rewrite set_rootsE big_fset /=; last first.
        by move=> x y; rewrite !ffunE /=; move/inj_l/enum_val_inj.
      rewrite (eq_bigr (fun j => ('X - (l (enum_val j))%:P))); last first.
        by move=> i _; rewrite ffunE /=.
      rewrite -(big_enum_val _ Q (fun i => 'X - (l i)%:P)) /=.
      move: (l_set Q Q_in); rewrite set_rootsE big_fset_set ?inj_l //=.
      by rewrite (eq_bigl (fun j => (j \in Q))) // => i; rewrite andbT.
    + by rewrite /q mesymE rpred_sum // => i _; apply: mpolyOverX.
    + by apply: mesym_sym.
    + by move=> x y; rewrite !ffunE /=; move/(mulfI c_neq0)/inj_l.
move=> -> l p inj_l l_set _ p_over p_symm {c}.
rewrite expr1n mul1r.
rewrite -(mpolyOverC m.+1) -mpevalsT eq_D => {eq_D}.
case: n n_neq0 P card_P D part_P_D l_set p p_over p_symm => // n _.
elim: n.
  move=> P /eqP /cards1P [Q ->] {P} D part_D Q_set.
  have {Q_set} Q_set : [fset l i | i in Q]%fset \is a set_roots kS 1.
    by apply: Q_set; rewrite inE.
  move=> p /mpolyOverP p_over p_symm.
  have {p_symm} p_symm : p \is symmetric_for T Q.
    by apply: p_symm; rewrite inE.
  have {part_D} {D} -> : D = Q.
    move: part_D; rewrite /partition => /and3P[].
    by rewrite /cover big_set1 => /eqP -> _ _.
  rewrite (issym_symm_forE p_symm) raddf_sum /=.
  rewrite big_seq_cond rpred_sum //= => i /andP[i_in _].
  rewrite !mpevalZ -mul_mpolyC rpredM //.
    by rewrite mpolyOverC p_over.
  rewrite -[_.@[_, _]]scale1r.  
  have -> : 1 = 1 ^+ (\sum_(j < #|Q|) i (enum_val j)) by move=> t; rewrite expr1n.
  by apply: sym_fundamental_seqroots_mmsym_for.
move=> n ihn P card_P.
have /set0Pn[Q Q_in] : P != set0 by rewrite -card_gt0 card_P.
pose P' := P :\ Q; have /eqP card_P' : #|P'| == n.+1.
  by rewrite -(eqn_add2l 1%N) /P' [X in _ == X]add1n -card_P (cardsD1 Q P) Q_in.
move=> D D_part.
pose D' := cover P'; have D'_part : partition P' D'.
  have /and3P[_ P_triv /negbTE set0_nP] := D_part.
  rewrite /partition /D' eq_refl /= (trivIsetS (subD1set _ _) P_triv) /= /P'.
  by rewrite in_setD1 set0_nP andbF.
have eq_D : D = D' :|: Q.
  by rewrite /D' -(cover_partition D_part) /P' /cover setUC -(big_setD1 _ Q_in).
move=> l_set.
have l'_set : {in P', forall Q : {set 'I_m.+1}, 
          [fset l i | i in Q]%fset \is a set_roots kS 1}.
  by move=> R; rewrite in_setD1 => /andP[_ R_in]; rewrite (l_set R R_in).
move=> p p_over p_sym.
have H_ihn := (ihn P' card_P' D' D'_part l'_set).
rewrite eq_D setUC -mpevalsU.
move eq_p': (_.@[_ , Q]) => p'.
apply: H_ihn.
  rewrite -eq_p' (issym_symm_forE (p_sym Q Q_in)) raddf_sum /= rpred_sum // => m' _.
  rewrite mpevalZ mpolyOverZ ?(mpolyOverP _ p_over) //.
  rewrite -[_.@[_, _]]scale1r.  
  have -> : 1 = 1 ^+ (\sum_(j < #|Q|) m' (enum_val j)) by move=> t; rewrite expr1n.
  apply: sym_fundamental_seqroots_mmsym_for => //.
  by apply: (l_set Q Q_in).
move=> R R_in'; rewrite -eq_p' mpevalE.
apply/issym_forP => s s_on.
rewrite rmorph_sum /= [in RHS]big_seq_cond.
have R_in : R \in P by move: R_in'; rewrite /P' in_setD1 => /andP[_ ].
rewrite -(eq_big_perm _ (msupp_sym_for (perm_onI s_on) (p_sym R R_in))) /=.
rewrite (eq_big_perm _ (msupp_msym _ (s^-1)%g)) /= big_map /= big_seq_cond.
apply: congr_big => // m' /andP[m'_in _]; rewrite msymZ fingroup.invgK.
have Hdis : [disjoint Q & R].
  move: (D_part); rewrite /partition => /and3P[_ /trivIsetP Hdis _].
  apply/(Hdis Q R Q_in R_in)/negP => /eqP Q_eqR.
  by move: R_in'; rewrite -Q_eqR /P' in_setD1 eq_refl.
congr ((_ * _) *: _).
    by rewrite (msym_for_coeff m' s_on (p_sym R R_in)).
  apply: eq_bigr => i i_in; congr (_ ^+ _); rewrite mnmE (out_perm s_on) //.
  have := Hdis; rewrite disjoints_subset => /subsetP.
  by move/(_ _ i_in); rewrite in_setC.
rewrite rmorph_prod /=.
rewrite (eq_bigr (fun i => 'X_(s i) ^+ m' (s i))); last first.
  move=> i i_in; rewrite rmorphX /= msymX /mperm !mnmE.
  congr ('X_[ _ ] ^+ _); apply/mnmP => j; rewrite !mnmE.
  by congr (nat_of_bool _); apply/eqP/eqP => [-> | <- ]; rewrite ?permK ?permKV.
rewrite [RHS](reindex_inj (@perm_inj _ s)) /=.
apply: eq_bigl => i.
move: Hdis; rewrite disjoint_sym disjoints_subset => /setIidPr R_inCQ.
rewrite -(setID (~: Q) R) !in_setU R_inCQ (perm_closed _ s_on) !in_setD.
congr (_ || _); apply/idP/idP => /andP[i_notR i_notQ].
  by rewrite (out_perm s_on i_notR) i_notR i_notQ.
by rewrite -[i](permK s) (out_perm (perm_onI s_on) i_notR) i_notR i_notQ.
Qed.


End ClosedField_ajouts.

Section Seq_ajouts.

Variable T : eqType.

Lemma nth_flatten_size_proper s0 (A : seq (seq T)) s i j:
  (i < size A)%N -> nth s0 A i = s -> (j < size s)%N ->
    ((sumn (shape (take i A)) + j)%N < size (flatten A))%N.
Proof.
move=> ordi nth_i_s_A ordj.
have H2 : (sumn (shape (take i A)) + j < sumn (shape (take i.+1 A)))%N.
  rewrite (take_nth s0) ?index_mem // nth_i_s_A.
  by rewrite {2}/shape map_rcons -/shape -cats1 sumn_cat /= addn0 ltn_add2l.
rewrite size_flatten -{2}[A](@cat_take_drop i.+1) /shape map_cat /= sumn_cat.
by apply: (leq_trans H2 _); apply: leq_addr.
Qed.

Lemma nth_flatten_proper s0 x0 (A : seq (seq T)) s i j:
  (i < size A)%N -> nth s0 A i = s -> (j < size s)%N -> 
  nth x0 (flatten A) (sumn (shape (take i A)) + j)%N = nth x0 s j.
Proof.
elim/last_ind: A i => [i| A l IhA k]; first by rewrite ltn0.
rewrite size_rcons ltnS leq_eqVlt => /orP [/eqP ->| lt_k_size].
  rewrite nth_rcons ltnn eq_refl => -> ordj.
  rewrite -cats1 take_cat ltnn subnn take0 cats0 -size_flatten flatten_cat.
  rewrite nth_cat -[X in (_ < X)%N]addn0 ltn_add2l ltn0 addKn /=.
  by rewrite nth_cat ordj.
rewrite nth_rcons lt_k_size => nth_k ordj.
rewrite -(IhA k lt_k_size nth_k ordj).
rewrite -cats1 flatten_cat takel_cat 1?leq_eqVlt ?lt_k_size ?orbT //.
by rewrite nth_cat (nth_flatten_size_proper lt_k_size nth_k ordj).
Qed.

(* supprimer ? *)
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

End Seq_ajouts.

Section ComplexR_ajouts.

Lemma seqroots_polyMin x (H : x is_algebraic) :
  uniq (seqroots (polyMin H)).
Proof. by rewrite seqroots_separable ?polyMin_separable. Qed.


(*
Local Notation setZroots := ((set_roots Cint) : 
    complexR -> qualifier 1 {fset complexR}).

Lemma bla3 (T : finType) (P : {set {set T}}) (K : {set T} -> complexR) 
                                                           (a : T -> complexR) :
  (forall Q, Q \in P -> [fset a i | i in Q]%fset \is a setZroots (K Q)) ->
  forall Q, Q \in (cover_rel_partition P) -> 
    {c : complexR | [fset a i | i in Q]%fset \is a setZroots c}. 
Proof.  
move=> H R R_in.
set pre_c := \prod_(Q in P | ) (K Q).

Locate partition.
SearchAbout equivalence_partition.
*)


(* récupération d'un poly séparable *)
(* manipulation des racines d'un poly séparable *)

(*
Lemma separable_ffun (n : nat) (f : {ffun 'I_n -> complexR}) :
  (forall i, f i is_algebraic) -> {p : {poly int} | [&& p != 0, 
  [forall i, root (map_poly ZtoC p) (f i)] & separable_poly (map_poly ZtoC p)]}.
Proof.
move=> f_alg.
suff [p /and4P[/negbTE p_neq0 monp /forallP rootp sep_p]]: {p : {poly rat} | 
   [&& p != 0, p \is monic, [forall i, root (map_poly QtoC p) (f i)] & separable_poly p]}.
  have : {q : {poly int} & {a : int_ZmodType | (0 < a) 
       & p = a%:~R^-1 *: map_poly (intr : int -> rat) q}}.
    have [p_ [a /negbTE a_neq0 eq_p_p_]] := intdiv.rat_poly_scale p.
    have [a_gt0 | a_le0 | /eqP] := (ltrgt0P a); last by rewrite a_neq0.
      by exists p_; exists a.
    exists (- p_); exists (- a); rewrite ?oppr_gt0 //.
    by rewrite !rmorphN invrN /= scaleNr scalerN opprK.
  move=> [p_ [a a_gt0 eq_p_p_]].
  have a_neq0 : ratr a%:~R != 0 :> complexR.
    by rewrite ratr_int intr_eq0 lt0r_neq0.    
  have eq_p__p : (map_poly intr p_) = a%:~R *: p.
    by rewrite eq_p_p_ scalerA mulfV ?scale1r // intr_eq0; apply: lt0r_neq0.  
  have p__neq0 : p_ != 0.
    apply/negP => /eqP p__eq0; move/eqP: eq_p__p; rewrite p__eq0 map_poly0. 
    by rewrite eq_sym scale_poly_eq0 p_neq0 intr_eq0 (negbTE (lt0r_neq0 a_gt0)).
  have lc_p_gt0 : (0 < (lead_coef p_)).
    have H : (lead_coef p_)%:~R = a%:~R * lead_coef p.
      rewrite eq_p_p_ lead_coefZ lead_coef_map_eq ?intr_eq0 ?lead_coef_eq0 //.
      by rewrite mulrA mulfV ?mul1r // intr_eq0; apply: (lt0r_neq0 a_gt0).
    by rewrite -(ltr0z rat_numDomainType) H (monicP monp) mulr1 ltr0z.
  have ZtoQtoC : QtoC \o intr =1 ZtoC by move=> y /=; rewrite ratr_int.
  have root_map_p i : root (map_poly intr p_) (f i).
    by rewrite -(eq_map_poly ZtoQtoC) map_poly_comp eq_p__p map_polyZ /= rootZ.
  exists p_; apply/and3P; split; rewrite //; first by apply/forallP.
  rewrite -(eq_map_poly ZtoQtoC) map_poly_comp eq_p__p map_polyZ /=.
  by rewrite (separable_polyZ _ a_neq0) separable_map.
have Hpoly x : x is_algebraic -> 
    {p : {poly rat} | [&& p != 0, p \is monic & root (map_poly QtoC p) x]}.
  move=> x_alg; case: (boolP (x == 0)) => [x_eq0 | x_neq0].
    by exists 'X; rewrite ?polyX_eq0 ?monicX ?map_polyX ?rootX.
  
About separable_map.
have [r /andP[monr /andP[rootr r0_neq0]]] := (poly_caract_root x_alg x_neq0).


pose r := (finfun (fun i : 'I_n => sval (poly_caract_root (f_alg i)))). 
have [r /andP[monr /andP[rootr r0_neq0]]] i := (poly_caract_root (f_alg i)).
have r_neq0 : r != 0.
    by apply/negP => /eqP r_eq0; move/negP: r0_neq0; rewrite r_eq0 coef0.
pose p_ := gcdp r (deriv r); pose lc_ := (lead_coef p_).
have lc_neq0 : lc_ != 0.
  by rewrite /lc_ lead_coef_eq0 gcdp_eq0 negb_and r_neq0.
have lc_p_monic : lc_^-1 *: p_ \is monic.
  by apply/monicP; rewrite lead_coefZ mulrC mulfV.
exists (lc_ *: (r %/ p_)); apply/and4P; split.
+ rewrite -(monicMr _ lc_p_monic) -scalerCA scalerA mulrC mulfV //.
  by rewrite scale1r divpK // dvdp_gcdl.
+ rewrite map_polyZ /= rootZ ?ratr_eq0 //.
  move: (divpK (dvdp_gcdl r (deriv r))); rewrite -/p_ => eq_p.
  rewrite -mu_gt0; last first.
    rewrite map_poly_eq0; apply/negP => /eqP H; rewrite H mul0r in eq_p.
    by rewrite -eq_p eq_refl in r_neq0.
  have rp_neq0 : (map_poly QtoC (r %/ p_)) * (map_poly QtoC p_) != 0. 
    by rewrite -rmorphM eq_p map_poly_eq0.
  rewrite -(ltn_add2r (\mu_x (map_poly ratr p_))) add0n -mu_mul //.
  rewrite -rmorphM /= divpK ?dvdp_gcdl //.
  rewrite (mu_deriv_root _ rootr) ?map_poly_eq0 // addn1 ltnS /p_ /=. 
  rewrite gcdp_map deriv_map /=.
  have H := (divpK (dvdp_gcdr (map_poly ratr r) (map_poly ratr r^`()))).
  rewrite -{2}H mu_mul ?leq_addl // H -size_poly_eq0 -deriv_map size_deriv.
  rewrite -lt0n -ltnS prednK; last by rewrite lt0n size_poly_eq0 map_poly_eq0.
  by apply: (root_size_gt1 _ rootr); rewrite map_poly_eq0.
+ rewrite coefZ mulf_eq0 negb_or lc_neq0 andTb; apply/negP => /eqP eqr.
  move/negP : r0_neq0; apply; rewrite -(divpK (dvdp_gcdl r (deriv r))). 
  rewrite -/p_ coefM big1 // => i _.
  have -> : nat_of_ord i = 0%N by apply/eqP; rewrite -leqn0 -ltnS.
  by rewrite eqr mul0r.
+ by rewrite separable_polyZ ?make_separable //.
Qed.
  

move=> f_alg.
pose pm := finfun (fun i : 'I_n => (polyMin (f_alg i))).
pose Ppm : {poly int} := \prod_(i < n) pm i.
pose g := gcdp Ppm (Ppm^`()).
pose lg := lead_coef g.
pose s : {poly int} := lg *: (Ppm %/ g).
have Ppm_neq0 : Ppm != 0.
  by apply/prodf_eq0 => [[i _]]; rewrite ffunE (negbTE (polyMin_neq0 _)).
have lg_neq0 : lg != 0 by rewrite /lg lead_coef_eq0 gcdp_eq0 negb_and Ppm_neq0.
have s_neq0 : s != 0.
  rewrite /s scale_poly_eq0 negb_or lg_neq0 divpN0 ?gcdp_eq0 ?leq_gcdpl //.
  by rewrite negb_and Ppm_neq0.
have ZtoQtoC : QtoC \o intr =1 ZtoC by move=> y /=; rewrite ratr_int.
have s_sep : separable_poly (map_poly ZtoC s).
  rewrite -(eq_map_poly ZtoQtoC) map_poly_comp separable_map map_polyZ /=.
  rewrite separable_polyZ ?intr_eq0 //.
  set mpQ := map_poly _.
  suff -> : mpQ (Ppm %/ g) = (mpQ Ppm) %/ (gcdp (mpQ Ppm) (mpQ Ppm)^`()).
    by rewrite make_separable // map_poly_eq0_id0 ?intr_eq0 ?lead_coef_eq0.


    
Search _ (map_poly _) (_ == 0).
map_poly_eq0_id0

Search _ (gcdp _) size.


Locate "%/".
Search _ divp in polydiv.

Search _ "Gauss".

Search _ map_poly in polydiv.
Gauss_dvdpl: forall (R : idomainType) (p q d : {poly R}), coprimep d q -> (d %| p * q) = (d %| p)
Gauss_dvdpr: forall (R : idomainType) (p q d : {poly R}), coprimep d q -> (d %| q * p) = (d %| p)
Gauss_dvdp:
  forall (R : idomainType) (m n p : {poly R}), coprimep m n -> (m * n %| p) = (m %| p) && (n %| p)
Gauss_gcdpr: forall (R : idomainType) (p m n : {poly R}), coprimep p m -> gcdp p (m * n) %= gcdp p n
Gauss_gcdpl: forall (R : idomainType) (p m n : {poly R}), coprimep p n -> gcdp p (m * n) %= gcdp p m
*)
End ComplexR_ajouts.







(*
Section MSym.


End MSym.
*)

(*
Section LeC_ajouts.

Variable n : nat.

(* a generaliser *)
Variable r : complexR ^ n.+1.

Hypothesis r_bigmax : bigmaxcff r = r ord0.

Local Notation mnm_to_C := 
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
*)


(*
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

Search _ in finfun.
*)

(*

Lemma extract_poly (n : nat) (a : complexR ^ n.+1) (alpha : complexR ^ n.+1) :
  (forall i : 'I_n.+1, a i \is a Cint) ->
  (forall i : 'I_n.+1, a i != 0) -> 
  (forall i : 'I_n.+1, (i != ord0) -> lttc (alpha i) (alpha ord0)) ->
  let m := (size (undup alpha)).-1 in
  let t_alpha := Tuple (size_undup_tuple alpha) in
  exists (P : {mpoly complexR[m.+1]}), P!= 0 /\ P \is a mpolyOver m.+1 Cint /\
  (P.@[finfun (Cexp \o t_alpha)] = Cexp_span a alpha) /\
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
*)


Section Poly_mrootRing.

Variable R : ringType.

Lemma derivX_XsubC (c : R) n :
  (('X - c%:P) ^+ n) ^`() = ('X - c%:P) ^+ n.-1  *+ n.
Proof.
case: n; first by rewrite expr0 derivC.
elim => [| n ihn]; first by rewrite expr1 /= expr0 derivXsubC.
rewrite -addn1 exprD !derivE expr1 ihn mulr1 -pred_Sn.
by rewrite addn1 /= mulrnAl -!exprSr -mulrSr.
Qed.

Definition mroot (p : {poly R}) m x := Pdiv.CommonRing.rdvdp (('X - x%:P) ^+ m) p.

Lemma mrootP p m x :
  reflect (exists q, p = q * ('X - x%:P) ^+ m ) (mroot p m x).
Proof.
by apply:(iffP (Pdiv.RingMonic.rdvdpP _ p)); rewrite ?monic_exp ?monicXsubC.
Qed.

Lemma mrootdP p m x :
  reflect (forall i : 'I_m, mroot p^`(i) (m - i) x) (mroot p m x).
Proof.
apply:(iffP idP); last first.
  case: m.
    by move=> H; apply/mrootP; exists p; rewrite expr0 mulr1.
  by move=> n /(_ (ord0)); rewrite subn0 derivn0.
move=>  H; case; elim=> [/=  _|n IHn Hn]; first by rewrite subn0.
apply/mrootP; rewrite derivnS /=.
move/(ltn_trans(ltnSn n)):Hn =>Hn1.
move/mrootP :(IHn Hn1)=>[r /= Hr].
rewrite Hr derivM derivX_XsubC -{1}[(m -n)%N]prednK; last by rewrite subn_gt0.
exists (r^`() * ('X - x%:P) + r *+ (m-n)).
by rewrite mulrDl exprS mulrA mulrnAl subnS mulrnAr.
Qed.

Lemma mroot_root p m x :
  (0 < m)%N -> mroot p m x -> root p x.
Proof.
move=> Hle /mrootP [q Heq]; apply/factor_theorem.
exists (q * ('X - x%:P)^+ m.-1).
by rewrite Heq -{1}(prednK Hle) exprSr mulrA.
Qed.

Lemma mroot0 p x : mroot p 0 x.
Proof. by apply/mrootP; rewrite expr0; exists p; rewrite mulr1. Qed.

Lemma root_mroot p x : root p x -> mroot p 1 x.
Proof. by move=> /factor_theorem H; apply/mrootP; rewrite expr1. Qed.

End Poly_mrootRing.

Section Poly_mrootCRing.

Variable R : comRingType.

Lemma mrootM (p : {poly R}) mp q mq x :
  mroot p mp x -> mroot q mq x -> mroot (p * q) (mp + mq) x.
Proof.
move=> /mrootP [pr Hpr] /mrootP [qr Hqr]; apply/mrootP.
exists (pr * qr); rewrite Hpr Hqr.
by rewrite -!mulrA !(mulrC qr) exprD -!mulrA.
Qed.

Lemma mrootX (p : {poly R}) n x : root p x -> mroot (p ^+ n) n x.
Proof.
move=> H.
elim: n => [|n ihn]; first by apply: mroot0.
by rewrite exprS -add1n; apply: mrootM => //; apply: root_mroot.
Qed.

Lemma mrootZ (p : {poly R}) n c x : mroot p n x -> mroot (c *: p) n x.
Proof.
move=> /mrootP [pr Hpr]; apply/mrootP.
by exists (c *: pr); rewrite Hpr scalerAl.
Qed.

End Poly_mrootCRing.

End Theory.

(*
From mathcomp
Require Import algC.

Section PolyDivAlgC_ajouts.

Search _ (0 %| _) in polydiv.
Search _ in algC.

Lemma bla2 (P : {poly rat}) (Q : {poly rat}) (x : algC) :
  P != 0 -> Q != 0 -> root (map_poly ratr P) x -> root (map_poly ratr Q) x ->
  {R : {poly rat} | [&& R != 0, root (map_poly ratr R) x, (R %| P) & (R %| Q)]}. 
Proof.

Search _ irreducible_poly.


End PolyDivAlgC_ajouts.*)