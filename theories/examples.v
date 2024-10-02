From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finfun bigop.
From mathcomp Require Import ssralg ssrint finmap multiset.

Require Import category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Local Open Scope category_scope.


HB.instance Definition _ :=
  isCategory.Build choiceType (fun T : choiceType => T)
    (fun _ _ _ => True) (fun => I) (fun _ _ _ _ _ _ _ => I).
HB.instance Definition _ (a b : [the category of choiceType]) (f : a -> b)
  := isHom.Build [the category of choiceType] a b (f : el a -> el b) I.
Notation Sets := [the category of choiceType].


Fact comp_is_semi_additive (a b c : nmodType) (f : a -> b) (g : b -> c) :
  GRing.semi_additive f -> GRing.semi_additive g -> GRing.semi_additive (g \o f).
Proof. by move=> fM gM; split => [|x y]; rewrite /= fM gM. Qed.
HB.instance Definition _ :=
  isCategory.Build nmodType (fun T : nmodType => T)
    GRing.semi_additive GRing.idfun_is_semi_additive comp_is_semi_additive.
Notation Nmodules := [the category of nmodType].


Fact idfun_is_additive (a : zmodType) : GRing.additive (idfun : a -> a).
Proof. by []. Qed.
Fact comp_is_additive (a b c : zmodType) (f : a -> b) (g : b -> c) :
  GRing.additive f -> GRing.additive g -> GRing.additive (g \o f).
Proof. by move=> fM gM => x y /=; rewrite fM gM. Qed.
HB.instance Definition _ :=
  isCategory.Build zmodType (fun T : zmodType => T)
    GRing.additive idfun_is_additive comp_is_additive.
Notation Zmodules := [the category of zmodType].


Fact idfun_is_multiplicative (a : semiRingType) :
  GRing.multiplicative (idfun : a -> a).
Proof. by []. Qed.
Fact comp_is_multiplicative (a b c : semiRingType) (f : a -> b) (g : b -> c) :
  GRing.multiplicative f -> GRing.multiplicative g -> GRing.multiplicative (g \o f).
Proof. by move=> fM gM; split => [x y|] /=; rewrite fM gM. Qed.
HB.instance Definition _ :=
  isCategory.Build semiRingType (fun T : semiRingType => T)
    GRing.multiplicative idfun_is_multiplicative comp_is_multiplicative.
HB.instance Definition _ :=
  isCategory.Build comSemiRingType (fun T : comSemiRingType => T)
    GRing.multiplicative idfun_is_multiplicative comp_is_multiplicative.
HB.instance Definition _ :=
  isCategory.Build ringType (fun T : ringType => T)
    GRing.multiplicative idfun_is_multiplicative comp_is_multiplicative.
HB.instance Definition _ :=
  isCategory.Build comRingType (fun T : comRingType => T)
    GRing.multiplicative idfun_is_multiplicative comp_is_multiplicative.
HB.instance Definition _ :=
  isCategory.Build unitRingType (fun T : unitRingType => T)
    GRing.multiplicative idfun_is_multiplicative comp_is_multiplicative.
HB.instance Definition _ :=
  isCategory.Build comUnitRingType (fun T : comUnitRingType => T)
    GRing.multiplicative idfun_is_multiplicative comp_is_multiplicative.
Definition SemiRings := [the category of semiRingType].
Definition ComSemiRings := [the category of comSemiRingType].
Definition Rings := [the category of ringType].
Definition ComRings := [the category of comRingType].
Definition UnitRings := [the category of unitRingType].
Definition ComUnitRings := [the category of comUnitRingType].

Section BaseRing.

Variable (R : ringType).

Fact idfun_is_scalable (a : lmodType R) :
  scalable (idfun : a -> a).
Proof. by []. Qed.
Fact comp_is_scalable (a b c : lmodType R) (f : a -> b) (g : b -> c) :
  scalable f -> scalable g -> scalable (g \o f).
Proof. by move=> fM gM n x /=; rewrite fM gM. Qed.
HB.instance Definition _ :=
  isCategory.Build (lmodType R) (fun T : lmodType R => T)
    (fun a b (f : a -> b) => scalable f) idfun_is_scalable comp_is_scalable.

Fact idfun_is_linear (a : lalgType R) :
  linear (idfun : a -> a).
Proof. by []. Qed.
Fact comp_is_linear (a b c : lalgType R) (f : a -> b) (g : b -> c) :
  linear f -> linear g -> linear (g \o f).
Proof. by move=> fM gM n x y /=; rewrite fM gM. Qed.
HB.instance Definition _ :=
  isCategory.Build (lalgType R) (fun T : lalgType R => T)
    (fun a b (f : a -> b) => linear f) idfun_is_linear comp_is_linear.
HB.instance Definition _ :=
  isCategory.Build (algType R) (fun T : algType R => T)
    (fun a b (f : a -> b) => linear f) idfun_is_linear comp_is_linear.
HB.instance Definition _ :=
  isCategory.Build (comAlgType R) (fun T : comAlgType R => T)
    (fun a b (f : a -> b) => linear f) idfun_is_linear comp_is_linear.
HB.instance Definition _ :=
  isCategory.Build (unitAlgType R) (fun T : unitAlgType R => T)
    (fun a b (f : a -> b) => linear f) idfun_is_linear comp_is_linear.
HB.instance Definition _ :=
  isCategory.Build (comUnitAlgType R) (fun T : comUnitAlgType R => T)
    (fun a b (f : a -> b) => linear f) idfun_is_linear comp_is_linear.

End BaseRing.
Definition Lmodule R := [the category of lmodType R].
Definition LAlgebra R := [the category of lalgType R].
Definition Algebra R := [the category of algType R].
Definition ComAlgebra R := [the category of comAlgType R].
Definition UnitAlgebra R := [the category of unitAlgType R].
Definition ComUnitAlgebra R := [the category of comUnitAlgType R].


Section ForgetNmodule_to_Set.

Variable (a b : nmodType) (f : {hom Nmodules ; a, b}).

Definition forget_to_Sets (T : nmodType) : choiceType := T.
HB.instance Definition _ :=
  @isHom.Build Sets a b (f : (a : choiceType) -> b) I.
Definition forget_to_Sets_mor : {hom Sets; a, b} :=
  [the {hom Sets; (a : choiceType), b} of f : a -> b].

End ForgetNmodule_to_Set.

Fact forget_ext : FunctorLaws.ext forget_to_Sets_mor.
Proof. by []. Qed.
Fact forget_id : FunctorLaws.id forget_to_Sets_mor.
Proof. by []. Qed.
Fact forget_comp  : FunctorLaws.comp forget_to_Sets_mor.
Proof. by []. Qed.
HB.instance Definition _ :=
  @isFunctor.Build Nmodules Sets
    forget_to_Sets forget_to_Sets_mor forget_ext forget_id forget_comp.


Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope mset_scope.

HB.instance Definition _ (S : choiceType) := Choice.on {mset S}.
HB.instance Definition _ (S : choiceType) :=
  GRing.isNmodule.Build {mset S} msetDA msetDC mset0D.

Section MsetComplement.

Variable (K : choiceType).
Implicit Types (a b c : K) (A B C D : {mset K}) (s : seq K).

Lemma mset1E a b : [mset a] b = (a == b).
Proof. by rewrite fsfunE /= in_fset1 eq_sym; case eqP. Qed.

Definition mset_head h a A := let: tt := h in A a.
Local Notation coefm a := (mset_head tt a).

Fact coefm_is_additive a : semi_additive (coefm a).
Proof.
split; rewrite /mset_head /= ?mset0E // => A B.
rewrite fsfunE inE.
by case: (boolP (a \in finsupp A)); case: (boolP (a \in finsupp B));
  rewrite !msuppE //= => /mset_eq0P -> /mset_eq0P ->.
Qed.
HB.instance Definition _ a :=
  GRing.isSemiAdditive.Build {mset K} nat _ (coefm_is_additive a).

Lemma msetDE A B a : (A + B) a = A a + B a.
Proof. exact: (raddfD (coefm a)). Qed.
Lemma msetMn A n a : (A *+ n) a = (A a) *+ n.
Proof. exact: (raddfMn (coefm a)). Qed.
Lemma mset_sum I (r : seq I) (s : pred I) (F : I -> {mset K}) a :
  (\sum_(i <- r | s i) F i) a = \sum_(i <- r | s i) (F i) a.
Proof. exact: (raddf_sum (coefm a)). Qed.


Lemma msetE A : \sum_(i <- A) [mset i] = A.
Proof.
apply msetP => u /=; rewrite !mset_sum !sum_mset.
case: (boolP (u \in finsupp A)) => uS.
  rewrite (big_fsetD1 u uS) /= mset1E eqxx muln1.
  rewrite big_seq big1 ?addn0 // => v; rewrite !inE mset1E.
  by case eqP => //=; rewrite muln0.
have:= uS; rewrite msuppE -mset_eq0 => /eqP ->.
rewrite big_seq big1 // => v.
rewrite mset1E; case: (altP (_ =P _)) => [->|]; last by rewrite muln0.
by rewrite (negbTE uS).
Qed.

Section Widen.

Variables (R : Type) (idx : R) (op : Monoid.com_law idx).
Implicit Types (X Y : {mset K}) (P : pred K) (F : K -> R).

Lemma finsupp_widen X Y F :
  (forall i, i \notin finsupp X -> F i = idx) ->
  (\big[op/idx]_(i <- finsupp (X + Y)%R) F i) = (\big[op/idx]_(i <- finsupp X) F i).
Proof.
move=> H.
rewrite (bigID (fun i => i \in finsupp X)) /=.
rewrite [X in (op _ X)]big1 // Monoid.mulm1.
apply: eq_fbig_cond => // i.
rewrite !inE /= andbT.
case: (boolP (i \in finsupp X)); rewrite /= ?andbF ?andbT //.
by rewrite !msuppE in_msetD => ->.
Qed.

End Widen.

Variables (R : Type) (idx : R) (op : Monoid.com_law idx).
Implicit Types (X Y : {mset K}) (P : pred K) (F : K -> R).

Lemma perm_cat_mseq X Y : perm_eq (enum_mset (X + Y)) (X ++ Y).
Proof.
rewrite unlock; apply/permP => i.
rewrite count_cat !count_flatten !sumnE !big_map -natrDE.
have cout (Z : {mset K}) j : j \notin finsupp Z -> count i (nseq (Z j) j) = 0.
  by rewrite count_nseq msuppE -mset_eq0 => /eqP -> /[!muln0].
rewrite -(@finsupp_widen nat 0 _ X Y _ (cout X)) //=.
rewrite -(@finsupp_widen nat 0 _ Y X _ (cout Y)) //= [Y + X]msetDC.
rewrite -[RHS]big_split /=; apply eq_bigr => j _.
by rewrite msetDE nseqD count_cat.
Qed.

Lemma big_msetD X Y P F:
  \big[op/idx]_(i <- (X + Y : {mset K}) | P i) F i =
    op (\big[op/idx]_(i <- X | P i) F i) (\big[op/idx]_(i <- Y | P i) F i).
Proof. by rewrite -big_cat; apply: (perm_big _ (perm_cat_mseq X Y)). Qed.

End MsetComplement.



Section Set_to_FreeNmodule.

Variable (a b : choiceType) (f : {hom Sets ; a, b}).

Definition hom_mset (m : {mset a}) : [the nmodType of {mset b}] :=
                       (\sum_(i <- m | true) [mset f i]).
Lemma hom_mset_additive : semi_additive hom_mset.
Proof.
rewrite /hom_mset; split => [| /= x y]; first by rewrite big_mset0.
apply msetP => u /=; rewrite msetDE !mset_sum !sum_mset.
under eq_bigr => i _ do rewrite msetDE natrDE mulnDl.
rewrite natrDE big_split /=; congr (_ + _)%N.
  apply: finsupp_widen => i.
  by rewrite msuppE -mset_eq0 => /eqP -> /[!mul0n].
rewrite addrC; apply: finsupp_widen => i.
by rewrite msuppE -mset_eq0 => /eqP -> /[!mul0n].
Qed.

End Set_to_FreeNmodule.

Definition FreeNmod (T : choiceType) : nmodType := {mset T}.
HB.instance Definition _ (a b : Sets) (f : a -> b) :=
  @isHom.Build Nmodules {mset a} {mset b}
    (hom_mset f : [the nmodType of {mset a}] -> [the nmodType of {mset b}])
    (hom_mset_additive f).
Definition FreeNmod_mor (a b : Sets) (f : a -> b) :=
  [the {hom Nmodules; FreeNmod a, FreeNmod b} of hom_mset f].

Fact FreeNmod_ext : FunctorLaws.ext FreeNmod_mor.
Proof.
move=> /= a b f g eq y; rewrite /hom_mset.
by apply eq_bigr => x _; rewrite eq.
Qed.
Fact FreeNmod_id : FunctorLaws.id FreeNmod_mor.
Proof. by move=> /= a x /=; rewrite /hom_mset /= msetE. Qed.
Fact FreeNmod_comp  : FunctorLaws.comp FreeNmod_mor.
Proof.
move=> /= a b c f g x; rewrite !/hom_mset /= -{1}(msetE x).
elim: (enum_mset x) => [|y s IHs] /=.
  by rewrite !big_nil !big_mset0.
rewrite !big_cons.
by rewrite !big_msetD /= {}IHs !big_msetn.
Qed.
HB.instance Definition _ :=
  @isFunctor.Build Sets Nmodules
    FreeNmod FreeNmod_mor FreeNmod_ext FreeNmod_id FreeNmod_comp.





