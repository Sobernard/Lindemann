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


Section Wlog1.

(* Hypothèses de base : changer le pre_l en l.+1 *)
Variable pre_l : nat.
Hypothesis pre_l_gt0 : (0%N < pre_l)%N.
Variable pre_alpha : complexR ^ pre_l.
Hypothesis pre_alpha_inj : injective pre_alpha.
Hypothesis pre_alpha_algebraic : forall i : 'I_pre_l, pre_alpha i is_algebraic.
Variable pre_a : complexR ^ pre_l.
Hypothesis pre_a_neq0 : forall i : 'I_pre_l, pre_a i != 0.
Hypothesis pre_a_algebraic : forall i : 'I_pre_l, pre_a i is_algebraic.
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

Lemma a_algebraic : forall i : 'I_l.+1, a i is_algebraic.
Proof. by move=> i; rewrite ffunE tnth_map; apply: pre_a_algebraic. Qed.

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

(* polynôme de chaque a_i *)
Definition poly_a i := (polyMin (a_algebraic i)).

Lemma poly_a_neq0 i : poly_a i != 0.
Proof. by apply: polyMin_neq0. Qed.

Definition sroot_a i := seqroots (poly_a i).

Lemma a_in_sroot_a i : a i \in (sroot_a i).
Proof.
apply/seqrootsP; first by apply: poly_a_neq0.
by apply: (polyMin_root (a_algebraic i)).
Qed.

Lemma size_sroot_a i : (0 < size (sroot_a i))%N.
Proof.
rewrite lt0n; apply/negP; move/eqP/size0nil => eq_nil.
by move: (a_in_sroot_a i); rewrite eq_nil in_nil.
Qed.


(* produit de tous les polynomes *)
(*
Definition prod_poly_a := \prod_(i : 'I_l.+1) (poly_a i).
Definition poly_b := (map_poly ZtoC prod_poly_a).
*)

Definition poly_b := \prod_(i : 'I_l.+1) (poly_a i).

Lemma poly_b_Cint : poly_b \is a polyOver Cint.
Proof. 
apply: rpred_prod => i _ /=.
by apply/polyOverP => c; rewrite coef_map Cint_int. 
Qed.

Lemma poly_b_neq0 : poly_b != 0.
Proof. by apply/prodf_neq0 => i _; apply: poly_a_neq0. Qed.


Definition c := lead_coef poly_b.

Lemma c_Cint : c \is a Cint.
Proof. by apply/polyOverP; apply: poly_b_Cint. Qed.

Lemma c_neq0 : c != 0.
Proof. by rewrite lead_coef_eq0; apply: poly_b_neq0. Qed.

(* on récupère l'ensemble des racines 
en séquence pour l'instant, on doit attendre pour la vraie notation 
et qu'on transforme en L.-tuple : b *)
Definition sroot_b := seqroots poly_b.

Lemma perm_eq_b : 
  perm_eq (flatten [seq (sroot_a i) | i : 'I_l.+1]) sroot_b.
Proof.
rewrite perm_eq_sym /sroot_a /sroot_b /poly_b /index_enum -enumT.
apply: (perm_eq_trans (seqroots_prod _) (perm_eq_refl _)).
by apply/allP => i _ /=; apply: poly_a_neq0.
Qed.

Definition L := (size sroot_b).-1.
Lemma size_b : size sroot_b == L.+1.
Proof.
rewrite /L prednK ?eq_refl // -(perm_eq_size perm_eq_b) lt0n.
apply/negP; move/eqP/size0nil => eq_nil.
have : a ord0 \in flatten [seq sroot_a i | i : 'I_l.+1].
  apply/flatten_mapP; exists ord0; last by apply: a_in_sroot_a.
  by rewrite mem_enum.
by rewrite eq_nil in_nil.
Qed.

Definition b := finfun (tnth (Tuple size_b)).

Lemma leq_l_L : (l.+1 <= L.+1)%N.
Proof.
move: size_b => /eqP <- /=.
rewrite -(perm_eq_size perm_eq_b) size_flatten.
rewrite /shape -ssrcomplements.bignat_sumn big_map -/size.
have eq_l : (l.+1 = \sum_(j < l.+1) 1)%N.
  by rewrite sum1_size /index_enum -enumT size_enum_ord.
rewrite {1}[l.+1]eq_l -/size enumT.
apply: (big_ind2 leq (leqnn 0)).
  by move=> n1 n2 p1 p2; apply: leq_add.
by move=> i _; apply: size_sroot_a.
Qed.

Lemma b_neq0 i : b i != 0.
Proof.
apply/negP => /eqP b_eq0.
have b_inb : b i \in sroot_b by rewrite ffunE mem_tnth.
move: (perm_eq_mem perm_eq_b); move/(_ (b i)); rewrite b_inb.
move/flatten_mapP => [j j_in] /(seqrootsP _ (poly_a_neq0 _)). 
rewrite /sroot_a /poly_a b_eq0 => HrootC.
have /rootP := HrootC; rewrite /polyMin -{1}[0 : complexR]/(intr 0) horner_map.
move/eqP; rewrite intr_eq0 => /eqP HrootZ.
have [Hsize Hdiv] := (polyMinZ_irr (a_algebraic j)).
have : polyMinZ (a_algebraic j) %= 'X.
  rewrite /eqp andbC.
  apply/Hdiv; rewrite ?size_polyX //.
  by move/polyXsubCP: HrootZ; rewrite subr0.
move=> /eqpP[[c1 c2] /= /andP[c1_neq0 c2_neq0] /(congr1 (map_poly ZtoC)) Heq].
have /eqp_root H_eqroot : polyMin (a_algebraic j) %= 'X.
  apply/eqpP; exists (ZtoC c1, ZtoC c2) => /=; rewrite ?intr_eq0 ?c1_neq0 //.
  by rewrite -map_polyZ /= Heq map_polyZ /= map_polyX.
have := (polyMin_root (a_algebraic j)); rewrite H_eqroot rootX.
by apply/negP/a_neq0.
Qed.

Lemma b_cset : 
  c *: \prod_(i < L.+1) ('X - (b i)%:P) \is a polyOver Cint.
Proof.
rewrite /b (_ : _ *: _ = poly_b); first by apply: poly_b_Cint.
rewrite /c [RHS]seqroots_poly.
congr (_ *: _). 
rewrite (big_ffun _ _ (tnth (Tuple size_b)) _ _ (fun i => 'X - i%:P)).
by rewrite -[LHS](big_tuple _ _ (Tuple size_b) xpredT (fun i => 'X - i%:P)) /=.
Qed.


(* lien entre les a et b *)
(* TODO : injective ou injectiveb ?!? *)
Lemma a_in_b :
  {f : 'I_L.+1 ^ l.+1 | injective f & a =1 (b \o f)}.
Proof.
set troot_a := [tuple (sroot_a i) | i < l.+1].
set ind_a := (fun i : 'I_l.+1 => (sumn (shape (take i troot_a))
      + index (a i) (sroot_a i))%N).
have ord_ind_a i : ((ind_a i) < L.+1)%N.
  have -> : L.+1 = size (flatten troot_a).
    by rewrite (perm_eq_size perm_eq_b); move: size_b => /eqP ->.
  apply: (@leq_trans (sumn (shape (take i.+1 troot_a)))).
    rewrite (take_nth [::]) ?size_map -?enumT ?size_enum_ord //=.
    rewrite /shape map_rcons -/shape -cats1 sumn_cat /= addn0 /ind_a. 
    rewrite ltn_add2l (nth_map ord0) ?size_enum_ord //. 
    by rewrite nth_ord_enum index_mem a_in_sroot_a.
  rewrite size_flatten -{2}[tval troot_a](@cat_take_drop i.+1).
  by rewrite /shape map_cat -/shape sumn_cat leq_addr. 
move: perm_eq_b; rewrite -[X in perm_eq _ X]/(tval (Tuple size_b)).
move/tuple_perm_eqP /sig_eqW => [] s.
(* exists *)
exists (finfun (fun i => s (Ordinal (ord_ind_a i)))) => [| i /=]; first last.
  (* égalité *)
  have -> : a i = nth 0 (flatten troot_a) (Ordinal (ord_ind_a i)).
    rewrite [X in nth _ _ X]/= /ind_a (@nth_flatten _ _ [::]) ?size_tuple //.
      by apply: a_in_sroot_a.
    by rewrite -tnth_nth tnth_map tnth_ord_tuple.
  by rewrite ffunE p -tnth_nth tnth_map tnth_ord_tuple ffunE.
(* injective => monotone inégalité stricte : manque mono_inj pour des nat ? *)
move=> i j; rewrite !ffunE; move/perm_inj => eq_ord_ind; apply/eqP.
have {eq_ord_ind} eq_ind : ind_a i = ind_a j.
  by rewrite (ordnat (ord_ind_a i)) (ordnat (ord_ind_a j)) eq_ord_ind.
case: (boolP (i == j)) => //.
suff H (u : 'I_l.+1) (v : 'I_l.+1) : (u < v)%N -> (ind_a u < ind_a v)%N.
  by rewrite neq_ltn => /orP []; move/H; rewrite eq_ind ltnn.
move=> {eq_ind i j} lt_uv; rewrite /ind_a /shape !map_take -/shape.
have : (index (a u) (sroot_a u) < size (sroot_a u))%N.
  by rewrite index_mem; apply: a_in_sroot_a.
rewrite -(ltn_add2l (sumn (take u (shape troot_a)))).
move/leq_trans; apply.
have -> : (sumn (take u (shape troot_a)) + size (sroot_a u)
        = sumn (take u.+1 (shape troot_a)))%N.
  rewrite (take_nth 0%N); last by rewrite size_map size_tuple.
  rewrite -cats1 sumn_cat [RHS]/= addn0.
  apply/eqP; rewrite eqn_add2l; apply/eqP. 
  rewrite (nth_map [::]) ?(nth_map ord0) ?size_map -?enumT ?size_enum_ord //.
  by rewrite nth_ord_enum.
apply: (leq_trans _ (leq_addr _ _)); rewrite -(subnKC lt_uv).
move: (v - u.+1)%N => {v lt_uv}; elim => [ | w].
  by rewrite addn0 leqnn.
move/leq_trans; apply; rewrite addnS.
case: (boolP ((u.+1 + w)%N < size (shape troot_a))%N) => [H|].
  by rewrite (take_nth 0%N H) -cats1 sumn_cat -{1}[(sumn _)]addn0 leq_add2l.
rewrite -leqNgt => le_w; rewrite (take_oversize le_w) take_oversize //.
by apply: (leq_trans le_w).
Qed.


(* produit sur toutes les fonctions injectives de l dans L *)
Definition prod_Cexp_span_b :=
  \prod_(f : 'I_L.+1 ^ l.+1 | injectiveb f) 
    Cexp_span (finfun (b \o f)) alpha.

(* on retrouve le eq0 *)
Lemma prod_Cexp_span_b_eq0 : prod_Cexp_span_b == 0.
Proof.
move: (svalP a_in_b); set f := sval a_in_b; move=> [] /injectiveP inj_f eq_ab.
rewrite /prod_Cexp_span_b (bigD1 _ inj_f) mulf_eq0 /=; apply/orP; left.
move/eqP: Lindemann_false => <-; apply/eqP; congr Cexp_span.
by apply/ffunP => i; rewrite eq_ab ffunE.
Qed.

(* on le reconnait en tant que poly de poly pour faire du th sym *)
Definition R : {mpoly {mpoly complexR[l.+1]}[L.+1]} :=
  \prod_(f : 'I_L.+1 ^ l.+1 | injectiveb f) 
     \sum_(i : 'I_l.+1) 'X_i *: 'X_(f i).

(* egalité valeurs/horner *)
(* TODO : nom et = / == *)
Lemma R_Cexp_span_eq0 :
  (R.@[finfun ((@mpolyC l.+1 complexR_ringType) \o b)])
    .@[finfun (Cexp \o alpha)] == 0.
Proof.
apply/eqP; rewrite /R -[RHS](elimT eqP prod_Cexp_span_b_eq0) /prod_Cexp_span_b.
rewrite !rmorph_prod; apply: eq_bigr => f inj_f /=.
rewrite !(rmorph_sum _ (index_enum (ordinal_finType l.+1))) /=.
apply: eq_bigr => i _; rewrite mulrC mevalZ mevalM !mevalX ![in LHS]ffunE. 
by rewrite mevalC [X in _ = (_ * X)]ffunE.
Qed.

(* coefficients entiers pour th sym *)
Lemma R_overCint : 
  R \is a (mpolyOver L.+1 (mpolyOver l.+1 Cint)).
Proof.
apply: rpred_prod => f _ /=.
apply: rpred_sum => i _ /=; rewrite -mul_mpolyC.
by apply: rpredM => /=; rewrite ?mpolyOverC /= mpolyOverX.
Qed.

(* le poly est sym *)
Lemma R_sym :
  R \is symmetric.
Proof.
apply/issymP => s; rewrite rmorph_prod /R /=.
(* préparation pour un big_map *)
pose h := (fun (f : {ffun 'I_l.+1 -> 'I_L.+1}) => finfun (s \o f)).
pose F := (fun (f : {ffun 'I_l.+1 -> 'I_L.+1}) =>
     (\sum_(i < l.+1) 'X_i *: 'X_(f i)) : {mpoly {mpoly complexR[l.+1]}[L.+1]}).            
have H_eqF (f : {ffun 'I_l.+1 -> 'I_L.+1}) : injectiveb f -> 
    msym s (\sum_(i < l.+1) 'X_i *: 'X_(f i)) = F (h f).
  move=> _; rewrite rmorph_sum /=; apply: eq_bigr => i _.
  rewrite msymZ msymX; congr ('X_i *: @mpolyX _ _ _).
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
  by apply/ffunP => i; apply: (@perm_inj _ s); move: (H_eq i); rewrite !ffunE.
move=> f; rewrite mem_index_enum /h; apply/mapP.
exists (finfun ((fingroup.invg s) \o f)); rewrite ?mem_index_enum //.
by apply/ffunP => i; rewrite ffunE /= ffunE /= permKV.
Qed.


(* on perd un mpoly ! *)
Definition U := 
   (c ^+ (msize R)) *: R.@[finfun ((@mpolyC l.+1 complexR_ringType) \o b)].

Lemma U_Cexp_span_eq0 : U.@[finfun (Cexp \o alpha)] == 0.
Proof. by rewrite /U mevalZ (elimT eqP R_Cexp_span_eq0) mulr0. Qed.

Lemma U_overCint : U \is a mpolyOver l.+1 Cint.
Proof.
rewrite /U /c.
apply: (sym_fundamental_seqroots_empil b_cset R_overCint R_sym).
Qed.

Lemma Xi_in_U (f : 'I_L.+1 ^l.+1) i : 
          ((\sum_(i < l.+1) 'X_i *: 'X_(f i)).@[finfun 
          ((@mpolyC l.+1 complexR_ringType) \o b)])@_(U_( i)%MM) != 0.
rewrite rmorph_sum /=.
rewrite (eq_bigr (fun i0 => (b (f i0)) *: 'X_i0)); last first.
  by move=> j _; rewrite mevalZ mevalX ffunE -mul_mpolyC mulrC.
rewrite (bigD1 i) //= mcoeffD mcoeffZ mcoeffX eq_refl mulr1 raddf_sum /=.
rewrite big1_seq ?addr0 ?b_neq0 // => j /andP[/negbTE i_neq_j _].
rewrite mcoeffZ mcoeffX; apply/eqP; rewrite mulf_eq0; apply/orP; right.
rewrite pnatr_eq0 eqb0; apply/negP; move/eqP /mnmP /(_ i).
by rewrite !mnm1E eq_refl i_neq_j.
Qed.

Lemma U_neq0 : U != 0.
Proof.
rewrite /U scaler_eq0 expf_eq0.
move/negbTE: c_neq0 => ->; rewrite andbF orFb /R rmorph_prod /=.
apply/prodf_neq0 => f _; apply/negP => /eqP H.
by move: (Xi_in_U f ord0); rewrite H mcoeff0 eq_refl. 
Qed.

Definition deg_U := (\sum_(f : 'I_L.+1 ^ l.+1 | injectiveb f) 1)%N.-1.

(* TODO : enlever els leq_l_L : récupérable depuis a _in_b *)
Lemma U_homog : U \is deg_U.+1.-homog.
Proof.
rewrite /U; apply: dhomogZ; rewrite /R /deg_U; set s := (index_enum _).
have sum_lt0 : (0 < \sum_(f <- s | injectiveb f) 1)%N.
  rewrite lt0n sum_nat_eq0 negb_forall; apply/existsP.
  exists (finfun (fun i : 'I_l.+1 => (widen_ord leq_l_L i))).
  rewrite negb_imply /= andbT; apply/injectiveP => x y.
  rewrite !ffunE => H_widen; apply: ord_inj.
  by rewrite -[nat_of_ord _]/(nat_of_ord (widen_ord leq_l_L _)) H_widen.
rewrite (prednK sum_lt0) rmorph_prod -!(big_filter s) /=.
set se := [seq _ <- _ | _].
rewrite -(big_map (fun i => 1%N) xpredT (fun i => i)) /=.
rewrite -(big_map (fun i : 'I_L.+1 ^ l.+1 => (\sum_(j < l.+1) 'X_j *: 'X_(i j))
    .@[finfun ((@mpolyC l.+1 complexR_ringType) \o b)]) xpredT (fun i => i)) /=.
have H_tuple f : [seq f i | i <- se] = map_tuple f (in_tuple se) by [].
rewrite !H_tuple; apply: dhomog_prod => i /=; rewrite !tnth_map rmorph_sum /=.
apply: rpred_sum => j _; rewrite mevalZ mevalX ffunE /= mulrC mul_mpolyC.
by apply: dhomogZ; rewrite dhomogX /= mdeg1.
Qed.

Lemma U_in_all i : U@_(U_( i) *+ deg_U.+1)%MM != 0.
Proof.
rewrite /U mcoeffZ mulf_eq0 negb_or (expf_neq0 _ c_neq0) andTb.
rewrite /R /deg_U; set s := (index_enum _).
have sum_lt0 : (0 < \sum_(f <- s | injectiveb f) 1)%N.
  rewrite lt0n sum_nat_eq0 negb_forall; apply/existsP.
  exists (finfun (fun i : 'I_l.+1 => (widen_ord leq_l_L i))).
  rewrite negb_imply /= andbT; apply/injectiveP => x y.
  rewrite !ffunE => H_widen; apply: ord_inj.
  by rewrite -[nat_of_ord _]/(nat_of_ord (widen_ord leq_l_L _)) H_widen.
rewrite (prednK sum_lt0) rmorph_prod; move: sum_lt0; rewrite -!(big_filter s).
move : [seq _ <- _ | _] => se sum_lt0 /=.
case/lastP: se sum_lt0 => [ | r x _]; first by rewrite big_nil.
elim: r => [/= | y r ihr].
  by rewrite !big_seq1 mulm1n; apply: Xi_in_U.
rewrite rcons_cons big_cons big_cons rmorph_sum big_distrl /= raddf_sum /=.
rewrite {1}(bigD1_seq i) /=; first last.
  + by rewrite /index_enum -enumT enum_uniq.
  + by apply: mem_index_enum.
rewrite mevalZ mevalX ffunE /= ['X_i * _]mulrC mul_mpolyC -scalerAl mcoeffZ.
rewrite ['X_i * _]mulrC {1}mulmS /= mcoeffMX.
rewrite (big1 (index_enum (ordinal_finType l.+1))).
  by rewrite addr0; apply: (mulf_neq0 (b_neq0 _) ihr).
move=> j; rewrite eq_sym => /negbTE neq_ij.
rewrite mevalZ mevalX ffunE /= ['X_j * _]mulrC mul_mpolyC -scalerAl mcoeffZ.
apply/eqP; rewrite mulf_eq0; apply/orP; right.
rewrite mcoeff_eq0 mulrC; apply/negP.
rewrite (perm_eq_mem (msuppMX _ _)); set t := msupp _.
move/mapP => [] m m_in; move/mnmP /(_ j) /eqP; apply/negP.
by rewrite mulmnE mnm1E neq_ij muln0 mnmDE mnm1E eq_refl.
Qed.



(* On va extraire les infos *)

(* Récupérer les sommes d'exponentielles *)
Definition mnm_alpha := 
   (fun (m : 'X_{1..l.+1}) => \sum_(i < l.+1) ((alpha i) *+ m i)). 
   
Definition sum_alpha := 
   map mnm_alpha (msupp U).


(* Faire les sommes de coeff pour els exponentielles identiques *)
Lemma undupA : size (undup sum_alpha) == (size (undup sum_alpha)).-1.+1.
Proof.
rewrite prednK //.
move: (U_in_all ord0); rewrite -mcoeff_msupp.
move/(map_f mnm_alpha); rewrite -/sum_alpha -mem_undup.
by move/perm_to_rem /perm_eq_size => ->.
Qed.

Definition undup_alpha := finfun (tnth (Tuple undupA)).

Definition undup_b := finfun 
   ((fun x => \sum_(m <- msupp U | mnm_alpha m == x) U@_m) \o undup_alpha).

Lemma undup_Cexp_span_eq0 : Cexp_span undup_b undup_alpha == 0.
Proof.
apply/eqP; rewrite -[RHS](elimT eqP U_Cexp_span_eq0) /Cexp_span mevalE /undup_b.
pose F := (fun m => U@_m * Cexp (mnm_alpha m)).
rewrite (eq_bigr (fun i => (fun x => (\sum_(m <- msupp U | (pred1 x) (mnm_alpha m)) 
     F m)) (tnth (Tuple undupA) i))); last first.
  move=> i _; rewrite /undup_alpha !ffunE /= big_distrl /=. 
  apply: eq_big => m; first by rewrite ffunE.
  by rewrite /F; move=> /eqP ->; rewrite ffunE.
rewrite -(big_tuple _ _ (Tuple undupA) xpredT (fun x => 
   (\sum_(m <- msupp U | (pred1 x) (mnm_alpha m)) (F m)))) /=.
rewrite /sum_alpha (eq_bigr F); last first.
  move=> i _; rewrite /F /mnm_alpha (big_morph Cexp Cexp_morph Cexp0).
  by congr (_ * _); apply: eq_bigr => m _; rewrite ffunE /= CexpRX.
move: (msupp_uniq U); move: (msupp U) => r uniq_r.
rewrite (exchange_big_dep xpredT) //= !big_seq.
apply: eq_bigr => m m_in.
set s := [seq mnm_alpha i | i <- r]; rewrite -big_filter.
move: m_in; move/(map_f mnm_alpha); rewrite -/s -mem_undup.
move/(@filter_pred1_uniq _ (undup s) (mnm_alpha m) (undup_uniq s)).
rewrite (@eq_filter _ _ (fun x => (mnm_alpha m == x))); first last.
  by move=> x; rewrite eq_sym.
by move=> ->; rewrite big_seq1.
Qed.

(* faire une finfun pour pouvoir composer ! *)
Definition reindex_seq :=   
  filter (fun i => undup_b i != 0) (enum 'I_(size (undup sum_alpha)).-1.+1). 

Definition final_l := (size reindex_seq).-1.

Lemma tuple_RS : size reindex_seq == final_l.+1.
Proof.
apply/eqP; rewrite /final_l [RHS]prednK //.
rewrite size_filter -has_count; apply/hasP.
move: (U_in_all (index_bmaxf alpha)); rewrite -mcoeff_msupp.
move/(map_f mnm_alpha); rewrite -/sum_alpha -mem_undup.
rewrite -[undup _]/(tval (Tuple undupA)).
move/tnthP => [] imax; rewrite -[X in _ = X]ffunE -/undup_alpha.
move/(congr1 (fun x => \sum_(m <- msupp U | mnm_alpha m == x) U@_m)).
set b1 := \sum_(_ <- _ | _) _; set bimax := \sum_(_ <- _ | _) _; rewrite /b1.
have -> : bimax = undup_b imax by rewrite ffunE.
move=> eq_bimax {bimax} {b1}.
exists imax; first by rewrite mem_enum.
rewrite -eq_bimax -big_filter. 
rewrite (bigD1_seq (U_( index_bmaxf alpha) *+ deg_U.+1)%MM) /=; first last.
  + by apply: filter_uniq; apply: msupp_uniq.
  + by rewrite mem_filter eq_refl andTb mcoeff_msupp U_in_all.
rewrite big_filter_cond big_seq_cond big_pred0 ?addr0 ?U_in_all //.
move=> m; apply/negP => /andP[m_in /andP[eq_mnm_alpha /negP]]; apply.
rewrite -[m]s2mK -[X in _ == X]s2mK; apply/eqP; congr s2m.
move Hm : (m2s m) => ms.
have Hu : m2s (U_( index_bmaxf alpha) *+ deg_U.+1) = 
             nseq deg_U.+1 (index_bmaxf alpha).
  have {2}-> : deg_U.+1 = size (m2s (U_( index_bmaxf alpha) *+ deg_U.+1)). 
    by rewrite size_m2s mdegMn mdeg1 mul1n.
  apply/all_pred1P /allP => i; rewrite /m2s /pred1 /=.
  move/flatten_mapP => [] j _; rewrite mulmnE mnm1E.
  by move/nseqP => [] ->; rewrite eq_sym muln_gt0 /= lt0n eqb0 => /negbNE.  
have H m' : mnm_alpha m' = \sum_(i <- m2s m') (alpha i).
  rewrite /mnm_alpha /m2s big_flatten /= big_map /=.
  rewrite enumT /index_enum; apply: eq_bigr => i _.
  by rewrite big_nseq -Monoid.iteropE /=.
move: eq_mnm_alpha; rewrite !H !Hu Hm big_nseq eq_index_bmaxf -big_const_ord.
have size_ms : size ms == deg_U.+1.
  rewrite -Hm size_m2s.
  by move: U_homog; rewrite /ishomog1 /= => /allP; move/(_ m m_in).
rewrite -[ms]/(tval (Tuple size_ms)).
rewrite -[nseq _ _]/(tval (Tuple (nseq_tupleP deg_U.+1 _))).
rewrite big_tuple; set tm := Tuple _; set tnseq := Tuple _ => /eqP Hsum.
congr tval; apply/eq_from_tnth => j; apply/eqP.
rewrite (tnth_nth ord0 tnseq) nth_nseq ltn_ord.
have : (forall i : 'I_deg_U.+1, true ->
    letcif (alpha (tnth tm i)) (bmaxf alpha) (tnth tm i == index_bmaxf alpha)).
  by move=> i _; apply: (bmaxf_letcif alpha_inj).
by move/letcif_sum; rewrite Hsum; move/letcif_refl/forallP/(_ j)/implyP; apply.
Qed.

(* Eliminer les coeffs nuls *)
Definition final_alpha := finfun (undup_alpha \o (tnth (Tuple tuple_RS))).

Definition final_b := finfun (undup_b \o (tnth (Tuple tuple_RS))).

Lemma final_alpha_inj : injective final_alpha.
Proof.
move=> x y /eqP; rewrite !ffunE /= !ffunE !(tnth_nth 0) /=.
rewrite nth_uniq ?undup_uniq //; first last.
+ by rewrite {4}(elimT eqP undupA) ltn_ord.
+ by rewrite {4}(elimT eqP undupA) ltn_ord.
rewrite !(tnth_nth ord0) (inj_eq (@ord_inj _)) /= nth_uniq ?ltn_ord //.
+ by move/eqP/ord_inj.
+ by apply/(leq_trans (ltn_ord _)); rewrite (elimT eqP tuple_RS).
+ by apply/(leq_trans (ltn_ord _)); rewrite (elimT eqP tuple_RS).
by apply: filter_uniq; apply: enum_uniq.
Qed.

Lemma final_alpha_algebraic : 
    forall i : 'I_final_l.+1, final_alpha i is_algebraic.
Proof.
move=> i; rewrite ffunE /= ; move: (tnth _ _) => j {i}.
rewrite ffunE /= (tnth_nth 0) /=.
have: nth 0 (undup sum_alpha) j \in sum_alpha.
  by rewrite -mem_undup; apply: mem_nth; rewrite {2}(elimT eqP undupA).
move/(nthP 0) => [] i ord_i <- {j}; rewrite (nth_map 0%MM); last first.
  by move: ord_i; rewrite size_map.
rewrite /mnm_alpha; apply: big_ind.
    by apply: algebraic0.
  by apply: algebraic_add.
move=> j _; rewrite -mulr_natr; apply: algebraic_mul => /=.
  by apply: alpha_algebraic.
by rewrite integral_algebraic; apply: integral_nat.
Qed.

Lemma final_b_neq0 : 
    forall i : 'I_final_l.+1, final_b i != 0.
Proof.
move=> i; rewrite ffunE /= (tnth_nth ord0) /=.
have := (@mem_nth _ ord0 (Tuple tuple_RS) i); rewrite size_tuple.
move/(_ (ltn_ord _)); set x := nth _ _ _.
by rewrite mem_filter => /andP[].
Qed.

Lemma final_b_Cint : 
    forall i : 'I_final_l.+1, final_b i \is a Cint.
Proof.
move=> i; rewrite ffunE /=; move: (tnth _ _) => j {i}.
rewrite ffunE /=; apply: rpred_sum => m _.
by move/mpolyOverP: U_overCint; move/(_ m); apply.
Qed.

Lemma final_Lindemann_false : Cexp_span final_b final_alpha == 0.
Proof.
rewrite -(elimT eqP undup_Cexp_span_eq0) /Cexp_span /final_b /final_alpha.
rewrite (eq_bigr (fun j => (fun i => undup_b i * Cexp (undup_alpha i)) 
    (tnth (Tuple tuple_RS) j))); last first.
  by move=> i _; rewrite ![in LHS]ffunE. 
rewrite -(big_tuple _ _ _ xpredT (fun i => undup_b i * Cexp (undup_alpha i))).
apply/eqP; rewrite /reindex_seq big_filter big_mkcond /= /index_enum -enumT /=.
by apply: eq_bigr => i _; case: ifP => // /negbFE /eqP ->; rewrite mul0r.
Qed.

(* Theoreme wlog1 *)
Lemma wlog1 : 
  exists (f_l : nat) (f_alpha : complexR ^ f_l.+1) (f_a : complexR ^ f_l.+1), 
  injective f_alpha /\ 
  (forall i : 'I_f_l.+1, f_alpha i is_algebraic) /\
  (forall i : 'I_f_l.+1, f_a i != 0) /\ (forall i : 'I_f_l.+1, f_a i \is a Cint) /\
  (Cexp_span f_a f_alpha == 0).
Proof.
exists (final_l); exists final_alpha; exists final_b.
split; first by apply: final_alpha_inj.
split; first by apply: final_alpha_algebraic.
split; first by apply: final_b_neq0.
split; first by apply: final_b_Cint.
by apply: final_Lindemann_false.
Qed.

End Wlog1. 



Theorem wlog1_Lindemann :
  (forall (l : nat) (alpha : complexR ^ l.+1) (a : complexR ^ l.+1),
  injective alpha -> (forall i : 'I_l.+1, alpha i is_algebraic) ->
  (forall i : 'I_l.+1, a i != 0) -> (forall i : 'I_l.+1, a i \is a Cint) ->
  (Cexp_span a alpha != 0)) ->
  forall (l : nat) (alpha : complexR ^ l) (a : complexR ^ l),
  (0%N < l)%N -> injective alpha -> (forall i : 'I_l, alpha i is_algebraic) ->
  (forall i : 'I_l, a i != 0) -> (forall i : 'I_l, a i is_algebraic) ->
  (Cexp_span a alpha != 0).
Proof. 
move=> ih l alpha a l_gt0 alpha_inj alpha_alg a_neq0 a_alg; apply/negP => Hspan.
move: (wlog1 l_gt0 alpha_inj alpha_alg a_neq0 a_alg Hspan)=> [fl [falpha [fa]]].
move=> [] falpha_inj [] falpha_alg [] fa_neq0 [] fa_Cint Hspan_eq0.
move: (ih fl falpha fa falpha_inj falpha_alg fa_neq0 fa_Cint).
by rewrite Hspan_eq0.
Qed.