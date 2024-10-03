From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finfun bigop.
From mathcomp Require Import ssralg ssrint finmap multiset.

Require Import category msetcompl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Local Open Scope category_scope.

(* Sets *****************************************************************)

HB.instance Definition _ :=
  isCategory.Build choiceType (fun T : choiceType => T)
    (fun _ _ _ => True) (fun => I) (fun _ _ _ _ _ _ _ => I).
HB.instance Definition _ (a b : [the category of choiceType]) (f : a -> b)
  := isHom.Build [the category of choiceType] a b (f : el a -> el b) I.
Notation Sets := [the category of choiceType].


(* N-modules ************************************************************)

Definition idfun_is_semi_additive := GRing.idfun_is_semi_additive.
Fact comp_is_semi_additive (a b c : nmodType) (f : a -> b) (g : b -> c) :
  GRing.semi_additive f -> GRing.semi_additive g -> GRing.semi_additive (g \o f).
Proof. by move=> fM gM; split => [|x y]; rewrite /= fM gM. Qed.
HB.instance Definition _ :=
  isCategory.Build nmodType (fun T : nmodType => T)
    GRing.semi_additive idfun_is_semi_additive comp_is_semi_additive.
Notation Nmodules := [the category of nmodType].
Fact Nmod_hom_additive a b (f : {hom Nmodules; a, b}) : GRing.semi_additive f.
Proof. by case: f => [/= f [[]]]. Qed.
(* TODO : warning uniform inheritance *)
Coercion additive_of_Nmod a b (f : {hom Nmodules; a, b}) : {additive a -> b} :=
  HB.pack (Hom.sort f) (GRing.isSemiAdditive.Build _ _ _ (Nmod_hom_additive f)).
Lemma additive_of_NmodE a b (f : {hom Nmodules; a, b}) :
  @additive_of_Nmod a b f = f :> (_ -> _).
Proof. by []. Qed.

Module ForgetNmodules_to_Sets.

Section Morphism.

Variable (a b : nmodType) (f : {hom Nmodules ; a, b}).
Definition forget (T : nmodType) : choiceType := T.
HB.instance Definition _ :=
  @isHom.Build Sets a b (f : (a : choiceType) -> b) I.
Definition forget_mor : {hom Sets; a, b} :=
  [the {hom Sets; (a : choiceType), b} of f : a -> b].

End Morphism.

Fact forget_ext  : FunctorLaws.ext forget_mor.  Proof. by []. Qed.
Fact forget_id   : FunctorLaws.id forget_mor.   Proof. by []. Qed.
Fact forget_comp : FunctorLaws.comp forget_mor. Proof. by []. Qed.
HB.instance Definition _ :=
  @isFunctor.Build Nmodules Sets
    forget forget_mor forget_ext forget_id forget_comp.
Definition functor := [the {functor Nmodules -> Sets} of forget].

End ForgetNmodules_to_Sets.

Definition forget_Nmodules_to_Sets := ForgetNmodules_to_Sets.functor.
Lemma forget_Nmodules_to_SetsE a b (f : {hom Nmodules; a, b}) :
  forget_Nmodules_to_Sets # f = f :> (_ -> _).
Proof. by []. Qed.


(* Z-modules ************************************************************)

(* Full subcategory of N-module *)
HB.instance Definition _ :=
  isCategory.Build zmodType (fun T : zmodType => T)
    GRing.semi_additive GRing.idfun_is_semi_additive comp_is_semi_additive.
Notation Zmodules := [the category of zmodType].

Fact Zmodule_mor_additive a b (f : {hom Zmodules; a, b}) :
  GRing.semi_additive f.
Proof. by case: f => [/= f [[]]]. Qed.
(* TODO : warning uniform inheritance *)
Coercion additive_of_Zmod a b (f : {hom Zmodules; a, b}) : {additive a -> b} :=
  HB.pack (Hom.sort f)
    (GRing.isSemiAdditive.Build _ _ f (Zmodule_mor_additive f)).
Lemma additive_of_ZmodE a b (f : {hom Zmodules; a, b}) :
  @additive_of_Zmod a b f = f :> (_ -> _).
Proof. by []. Qed.


Module ForgetZmodules_to_Nmodules.

Section Morphism.

Variable (a b : zmodType) (f : {hom Zmodules ; a, b}).
Definition forget (T : zmodType) : nmodType := T.
Let forget_fun : (a : nmodType) -> (b : nmodType) := f.
HB.instance Definition _ :=
  @isHom.Build Nmodules a b forget_fun (Zmodule_mor_additive f).
Definition forget_mor : {hom Nmodules; a, b} :=
  [the {hom Nmodules; (a : nmodType), b} of forget_fun].

End Morphism.

Local Fact forget_ext  : FunctorLaws.ext forget_mor.  Proof. by []. Qed.
Local Fact forget_id   : FunctorLaws.id forget_mor.   Proof. by []. Qed.
Local Fact forget_comp : FunctorLaws.comp forget_mor. Proof. by []. Qed.
HB.instance Definition _ :=
  @isFunctor.Build Zmodules Nmodules forget
    forget_mor forget_ext forget_id forget_comp.

Definition functor := [the {functor Zmodules -> Nmodules} of forget].

End ForgetZmodules_to_Nmodules.

Definition forget_Zmodules_to_Nmodules := ForgetZmodules_to_Nmodules.functor.
Lemma forget_Zmodules_to_NmodulesE a b (f : {hom Zmodules; a, b}) :
  forget_Zmodules_to_Nmodules # f = f :> (_ -> _).
Proof. by []. Qed.
Definition forget_Zmodules_to_Sets :=
  forget_Nmodules_to_Sets \O forget_Zmodules_to_Nmodules.
Lemma forget_Zmodules_to_SetsE a b (f : {hom Zmodules; a, b}) :
  forget_Zmodules_to_Sets # f = f :> (_ -> _).
Proof. by []. Qed.


(* SemiRings ************************************************************)

Definition semiring_morph (a b : semiRingType) (f : a -> b) : Prop:=
  GRing.semi_additive f * GRing.multiplicative f.
Fact idfun_is_semiring_morph (a : semiRingType) :
  semiring_morph (idfun : a -> a).
Proof. by []. Qed.
Fact comp_is_semiring_morph (a b c : semiRingType) (f : a -> b) (g : b -> c) :
  semiring_morph f -> semiring_morph g -> semiring_morph (g \o f).
Proof.
move=> [fA fM] [gA gM]; split; first exact: comp_is_semi_additive.
by split => [x y|] /=; rewrite fM gM.
Qed.
HB.instance Definition _ :=
  isCategory.Build semiRingType (fun T : semiRingType => T)
    semiring_morph idfun_is_semiring_morph comp_is_semiring_morph.
Notation SemiRings := [the category of semiRingType].

Fact SemiRing_mor_additive a b (f : {hom SemiRings; a, b}) :
  GRing.semi_additive f.
Proof. by case: f => [/= f [[[]]]]. Qed.
Fact SemiRing_mor_multiplicative a b (f : {hom SemiRings; a, b}) :
  GRing.multiplicative f.
Proof. by case: f => [/= f [[[]]]]. Qed.
(* TODO : warning uniform inheritance *)
Coercion rmorph_of_SRing a b (f : {hom SemiRings; a, b}) : {rmorphism a -> b} :=
  HB.pack (Hom.sort f)
    (GRing.isSemiAdditive.Build _ _ _ (SemiRing_mor_additive f))
    (GRing.isMultiplicative.Build _ _ _ (SemiRing_mor_multiplicative f)).
Lemma rmorph_of_SRingE a b (f : {hom SemiRings; a, b}) :
  @rmorph_of_SRing a b f = f :> (_ -> _).
Proof. by []. Qed.

Module ForgetSemiRings_to_Nmodules.

Section Morphism.

Variable (a b : semiRingType) (f : {hom SemiRings ; a, b}).
Definition forget (T : semiRingType) : nmodType := T.
Let forget_fun : (a : nmodType) -> (b : nmodType) := f.
HB.instance Definition _ :=
  @isHom.Build Nmodules a b forget_fun (SemiRing_mor_additive f).
Definition forget_mor : {hom Nmodules; a, b} :=
  [the {hom Nmodules; (a : nmodType), b} of forget_fun].

End Morphism.

Local Fact forget_ext  : FunctorLaws.ext forget_mor.  Proof. by []. Qed.
Local Fact forget_id   : FunctorLaws.id forget_mor.   Proof. by []. Qed.
Local Fact forget_comp : FunctorLaws.comp forget_mor. Proof. by []. Qed.
HB.instance Definition _ :=
  @isFunctor.Build SemiRings Nmodules forget
    forget_mor forget_ext forget_id forget_comp.

Definition functor := [the {functor SemiRings -> Nmodules} of forget].

End ForgetSemiRings_to_Nmodules.

Definition forget_SemiRings_to_Nmodules := ForgetSemiRings_to_Nmodules.functor.
Lemma forget_SemiRings_to_NmodulesE a b (f : {hom SemiRings; a, b}) :
  forget_SemiRings_to_Nmodules # f = f :> (_ -> _).
Proof. by []. Qed.
Definition forget_SemiRings_to_Sets :=
  forget_Nmodules_to_Sets \O forget_SemiRings_to_Nmodules.
Lemma forget_SemiRings_to_SetsE a b (f : {hom SemiRings; a, b}) :
  forget_SemiRings_to_Sets # f = f :> (_ -> _).
Proof. by []. Qed.


(* Rings **********************************************************)

HB.instance Definition _ :=
  isCategory.Build ringType (fun T : ringType => T)
    semiring_morph idfun_is_semiring_morph comp_is_semiring_morph.
Definition Rings := [the category of ringType].
Fact Ring_mor_additive a b (f : {hom Rings; a, b}) :
  GRing.semi_additive f.
Proof. by case: f => [/= f [[[]]]]. Qed.
Fact Ring_mor_multiplicative a b (f : {hom Rings; a, b}) :
  GRing.multiplicative f.
Proof. by case: f => [/= f [[[]]]]. Qed.
Coercion rmorph_of_Ring a b (f : {hom Rings; a, b}) : {rmorphism a -> b} :=
  HB.pack (Hom.sort f)
    (GRing.isSemiAdditive.Build _ _ _ (Ring_mor_additive f))
    (GRing.isMultiplicative.Build _ _ _ (Ring_mor_multiplicative f)).
Lemma rmorph_of_RingE a b (f : {hom Rings; a, b}) :
  @rmorph_of_Ring a b f = f :> (_ -> _).
Proof. by []. Qed.

Module ForgetRings_to_Zmodules.

Section Morphism.

Variable (a b : ringType) (f : {hom Rings ; a, b}).
Definition forget (T : ringType) : zmodType := T.
Let forget_fun : (a : zmodType) -> (b : zmodType) := f.
HB.instance Definition _ :=
  @isHom.Build Zmodules a b forget_fun (Ring_mor_additive f).
Definition forget_mor : {hom Zmodules; a, b} :=
  [the {hom Zmodules; (a : zmodType), b} of forget_fun].

End Morphism.

Local Fact forget_ext  : FunctorLaws.ext forget_mor.  Proof. by []. Qed.
Local Fact forget_id   : FunctorLaws.id forget_mor.   Proof. by []. Qed.
Local Fact forget_comp : FunctorLaws.comp forget_mor. Proof. by []. Qed.
HB.instance Definition _ :=
  @isFunctor.Build Rings Zmodules forget
    forget_mor forget_ext forget_id forget_comp.

Definition functor := [the {functor Rings -> Zmodules} of forget].

End ForgetRings_to_Zmodules.

Definition forget_Rings_to_Zmodules := ForgetRings_to_Zmodules.functor.
Lemma forget_Rings_to_ZmodulesE a b (f : {hom Rings; a, b}) :
  forget_Rings_to_Zmodules # f = f :> (_ -> _).
Proof. by []. Qed.
Definition forget_Rings_to_Sets :=
  forget_Zmodules_to_Sets \O forget_Rings_to_Zmodules.
Lemma forget_Rings_to_SetsE a b (f : {hom Rings; a, b}) :
  forget_Rings_to_Sets # f = f :> (_ -> _).
Proof. by []. Qed.



(* ComSemiRings **********************************************************)

HB.instance Definition _ :=
  isCategory.Build comSemiRingType (fun T : comSemiRingType => T)
    semiring_morph idfun_is_semiring_morph comp_is_semiring_morph.
Definition ComSemiRings := [the category of comSemiRingType].
(* Q : Should there be a coercion
   {hom ComSemiRings; a, b} -> {hom SemiRings; a, b}
(* Need forgetful functor to SemiRings *)
Coercion rmorph_of_ComSRing a b (f : {hom ComSemiRings; a, b}) : {rmorphism a -> b} :=
  HB.pack (Hom.sort f)
    (GRing.isSemiAdditive.Build _ _ _ (SRing_hom_additive f))
    (GRing.isMultiplicative.Build _ _ _ (SRing_hom_multiplicative f)).
Lemma rmorph_of_SRingE a b (f : {hom SemiRings; a, b}) :
  @rmorph_of_SRing a b f = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ :=
  isCategory.Build comRingType (fun T : comRingType => T)
    semiring_morph  idfun_is_semiring_morph comp_is_semiring_morph.
HB.instance Definition _ :=
  isCategory.Build unitRingType (fun T : unitRingType => T)
    semiring_morph  idfun_is_semiring_morph comp_is_semiring_morph.
HB.instance Definition _ :=
  isCategory.Build comUnitRingType (fun T : comUnitRingType => T)
    semiring_morph  idfun_is_semiring_morph comp_is_semiring_morph.
Definition ComSemiRings := [the category of comSemiRingType].
Definition ComRings := [the category of comRingType].
Definition UnitRings := [the category of unitRingType].
Definition ComUnitRings := [the category of comUnitRingType].
 *)


(* L-modules **********************************************************)

Section Lmodules.
Variable (R : ringType).
Fact idfun_is_linear (a : lmodType R) :
  linear (idfun : a -> a).
Proof. by []. Qed.
Fact comp_is_linear (a b c : lmodType R) (f : a -> b) (g : b -> c) :
  linear f -> linear g -> linear (g \o f).
Proof. by move=> fM gM n x y /=; rewrite fM gM. Qed.
HB.instance Definition _ :=
  isCategory.Build (lmodType R) (fun T : lmodType R => T)
    (fun a b (f : a -> b) => linear f) idfun_is_linear comp_is_linear.
End Lmodules.
Notation Lmodules R := [the category of lmodType R].
Fact Lmodules_mor_linear R a b (f : {hom Lmodules R; a, b}) : linear f.
Proof. by case: f => [/= f [[]]]. Qed.
Coercion linear_of_Lmodules R a b (f : {hom Lmodules R; a, b}) : {linear a -> b} :=
  HB.pack (Hom.sort f) (GRing.isLinear.Build _ _ _ _ _ (Lmodules_mor_linear f)).
Lemma linear_of_LmodulesE R a b (f : {hom Lmodules R; a, b}) :
  @linear_of_Lmodules R a b f = f :> (_ -> _).
Proof. by []. Qed.
Lemma Lmodules_mor_semi_additive R a b (f : {hom Lmodules R; a, b}) :
  GRing.semi_additive f.
Proof.
rewrite -linear_of_LmodulesE; split => [| x y]; first by rewrite GRing.raddf0.
by rewrite GRing.raddfD.
Qed.

Module ForgetLmodules_to_Zmodules.

Section BaseRing.

Variable R : ringType.

Section Morphism.

Variables (a b : lmodType R) (f : {hom Lmodules R; a, b}).
Definition forget (T : lmodType R) : zmodType := T.
Let forget_fun : (a : zmodType) -> (b : zmodType) := f.
HB.instance Definition _ :=
  @isHom.Build Zmodules a b forget_fun (Lmodules_mor_semi_additive f).
Definition forget_mor : {hom Zmodules; a, b} :=
  [the {hom Zmodules; (a : zmodType), b} of forget_fun].

End Morphism.

Local Fact forget_ext  : FunctorLaws.ext  forget_mor. Proof. by []. Qed.
Local Fact forget_id   : FunctorLaws.id   forget_mor. Proof. by []. Qed.
Local Fact forget_comp : FunctorLaws.comp forget_mor. Proof. by []. Qed.
HB.instance Definition _ :=
  @isFunctor.Build (Lmodules R) Zmodules forget forget_mor
    forget_ext forget_id forget_comp.

End BaseRing.

Definition functor R := [the {functor Lmodules R -> Zmodules} of (@forget R)].

End ForgetLmodules_to_Zmodules.

Definition forget_Lmodules_to_Zmodules := ForgetLmodules_to_Zmodules.functor.
Lemma forget_Lmodules_to_ZmodulesE R a b (f : {hom Lmodules R; a, b}) :
  forget_Lmodules_to_Zmodules R # f = f :> (_ -> _).
Proof. by []. Qed.
Definition forget_Lmodules_to_Sets R :=
  forget_Zmodules_to_Sets \O forget_Lmodules_to_Zmodules R.
Lemma forget_Lmodules_to_SetsE R a b (f : {hom Lmodules R; a, b}) :
  forget_Lmodules_to_Sets R # f = f :> (_ -> _).
Proof. by []. Qed.

(*
HB.instance Definition _ R :=
  isCategory.Build (lalgType R) (fun T : lalgType R => T)
    (fun a b (f : a -> b) => linear f) (@idfun_is_linear R) (@comp_is_linear R).
HB.instance Definition _ R :=
  isCategory.Build (algType R) (fun T : algType R => T)
    (fun a b (f : a -> b) => linear f) (@idfun_is_linear R) (@comp_is_linear R).
HB.instance Definition _ R :=
  isCategory.Build (comAlgType R) (fun T : comAlgType R => T)
    (fun a b (f : a -> b) => linear f) (@idfun_is_linear R) (@comp_is_linear R).
HB.instance Definition _ R :=
  isCategory.Build (unitAlgType R) (fun T : unitAlgType R => T)
    (fun a b (f : a -> b) => linear f) (@idfun_is_linear R) (@comp_is_linear R).
HB.instance Definition _ R :=
  isCategory.Build (comUnitAlgType R) (fun T : comUnitAlgType R => T)
    (fun a b (f : a -> b) => linear f) (@idfun_is_linear R) (@comp_is_linear R).
*)
(*Notation LAlgebras R := [the category of lalgType R].
Notation Algebras R := [the category of algType R].
Notation ComAlgebras R := [the category of comAlgType R].
Notation UnitAlgebras R := [the category of unitAlgType R].
Notation ComUnitAlgebras R := [the category of comUnitAlgType R].
*)



Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope mset_scope.

Section Set_to_FreeNmodule.

Variable (a b : choiceType) (f : {hom Sets ; a, b}).

Definition hom_mset (m : {mset a}) : [the nmodType of {mset b}] :=
  \sum_(i <- m) [mset f i].

Lemma hom_mset1 x : hom_mset [mset x] = [mset f x].
Proof. by rewrite /hom_mset big_msetn /=. Qed.

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
move=> /= a b c f g.
rewrite -!additive_of_NmodE; apply: additive_msetE => /= x.
by rewrite /hom_mset /= !big_msetn.
Qed.
HB.instance Definition _ :=
  @isFunctor.Build Sets Nmodules
    FreeNmod FreeNmod_mor FreeNmod_ext FreeNmod_id FreeNmod_comp.

Section Adjoint.

Implicit Types (a : choiceType) (T : nmodType).

Let eta_fun a (x : a) := [mset x].
Definition eta : FId ~~> forget_Nmodules_to_Sets \o FreeNmod := eta_fun.
Fact eta_natural : naturality FId (forget_Nmodules_to_Sets \o FreeNmod) eta.
Proof. by move=> /= a b h x /=; rewrite /eta_fun FIdf hom_mset1. Qed.
HB.instance Definition _ :=
  @isNatural.Build Sets Sets FId (forget_Nmodules_to_Sets \o FreeNmod) eta eta_natural.

Let eps_fun T (m : (FreeNmod \o forget_Nmodules_to_Sets) T) : T :=
      \sum_(i <- m : {mset _}) i.
Fact eps_fun_additive T : semi_additive (@eps_fun T).
Proof.
rewrite /eps_fun; split => [|/= s t]; first by rewrite big_mset0.
by rewrite big_msetD.
Qed.
HB.instance Definition _ T :=
  isHom.Build Nmodules ((FreeNmod \o forget_Nmodules_to_Sets) T) (FId T)
    (@eps_fun T) (@eps_fun_additive T).
Definition eps : FreeNmod \o forget_Nmodules_to_Sets ~~> FId := eps_fun.
Fact eps_natural : naturality (FreeNmod \o forget_Nmodules_to_Sets) FId eps.
Proof.
move=> /= a b h.
rewrite -!additive_of_NmodE; apply: additive_msetE => /= x.
by rewrite FIdf /eps_fun /hom_mset /= !big_msetn.
Qed.
HB.instance Definition _ :=
  @isNatural.Build Nmodules Nmodules (FreeNmod \o forget_Nmodules_to_Sets) FId
    eps eps_natural.

Fact triL : TriangularLaws.left eta eps.
Proof.
move=> /= a.
rewrite -!additive_of_NmodE; apply: additive_msetE => /= x.
by rewrite /eta_fun /= /eps_fun /hom_mset /= !big_msetn.
Qed.
Fact triR : TriangularLaws.right eta eps.
Proof. by move=> /= M m; rewrite /eta_fun /= /eps_fun !big_msetn /=. Qed.

Let F : {functor Sets -> Nmodules} := FreeNmod.
Let G : {functor Nmodules -> Sets} := forget_Nmodules_to_Sets.

Definition adj_FreeNmod_forget : FreeNmod -| forget_Nmodules_to_Sets :=
  AdjointFunctors.mk triL triR.

End Adjoint.


Section UniversalProperty.

Variable  (A : choiceType) (M : nmodType) (f : A -> M).

Definition univmap : {additive {mset A} -> M} :=
  eps M \o FreeNmod # f : {hom FreeNmod A, M}.

Lemma univmapP a : univmap [mset a] = f a.
Proof.
rewrite /univmap -[[mset a]]/(eta A a) /= hom_mset1.
by have /= -> := @triR M (f a).
Qed.

Lemma univmap_uniq (g : {additive {mset A} -> M}) :
  (forall a : A, g [mset a] = f a) -> g =1 univmap.
Proof.
move=> eq m; rewrite -(msetE m) !raddf_sum; apply eq_bigr => x _.
by rewrite eq univmapP.
Qed.

End UniversalProperty.
