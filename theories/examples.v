From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finfun bigop.
From mathcomp Require Import ssralg ssrint finmap multiset.

Require Import category msetcompl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import GRing.Theory.

Local Open Scope category_scope.

(* Sets *****************************************************************)

HB.instance Definition _ :=
  isCategory.Build choiceType (fun T : choiceType => T)
    (fun _ _ _ => True) (fun => I) (fun _ _ _ _ _ _ _ => I).
HB.instance Definition _ (a b : choiceType) (f : a -> b)
  := isHom.Build choiceType a b (f : el a -> el b) I.
Notation Sets := [the category of choiceType].


(* N-Modules ************************************************************)

Definition idfun_is_semi_additive := GRing.idfun_is_semi_additive.
Fact comp_is_semi_additive (a b c : nmodType) (f : a -> b) (g : b -> c) :
  semi_additive f -> semi_additive g -> semi_additive (g \o f).
Proof. by move=> fM gM; split => [|x y]; rewrite /= fM gM. Qed.
HB.instance Definition _ :=
  isCategory.Build nmodType (fun T : nmodType => T)
    semi_additive idfun_is_semi_additive comp_is_semi_additive.
Notation NModules := [the category of nmodType].
#[warning="-uniform-inheritance"]
Coercion additive_of_Nmod a b (f : {hom NModules; a, b}) : {additive a -> b} :=
  HB.pack (Hom.sort f) (GRing.isSemiAdditive.Build _ _ _ (isHom_inhom f)).
Lemma additive_of_NmodE a b (f : {hom NModules; a, b}) :
  @additive_of_Nmod a b f = f :> (_ -> _).
Proof. by []. Qed.

Module ForgetNModules_to_Sets.

Section Morphism.
Variable (a b : nmodType) (f : {hom NModules; a, b}).
Definition forget (T : nmodType) : choiceType := T.
HB.instance Definition _ :=
  @isHom.Build Sets a b (f : (a : choiceType) -> b) I.
Definition forget_mor : {hom Sets; a, b} := f : a -> b.
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build NModules Sets forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition functor : {functor NModules -> Sets} := forget.

End ForgetNModules_to_Sets.

Definition forget_NModules_to_Sets := ForgetNModules_to_Sets.functor.
Lemma forget_NModules_to_SetsE a b (f : {hom NModules; a, b}) :
  forget_NModules_to_Sets # f = f :> (_ -> _).
Proof. by []. Qed.


(* Z-Modules ************************************************************)

(* Full subcategory of N-module *)
HB.instance Definition _ :=
  isCategory.Build zmodType (fun T : zmodType => T)
    semi_additive idfun_is_semi_additive comp_is_semi_additive.
Notation ZModules := [the category of zmodType].

#[warning="-uniform-inheritance"]
Coercion additive_of_Zmod a b (f : {hom ZModules; a, b}) : {additive a -> b} :=
  HB.pack (Hom.sort f) (GRing.isSemiAdditive.Build _ _ f (isHom_inhom f)).
Lemma additive_of_ZmodE a b (f : {hom ZModules; a, b}) :
  @additive_of_Zmod a b f = f :> (_ -> _).
Proof. by []. Qed.


Module ForgetZModules_to_NModules.

Section Morphism.
Variable (a b : zmodType) (f : {hom ZModules; a, b}).
Definition forget (T : zmodType) : nmodType := T.
Definition forget_mor : (a : nmodType) -> (b : nmodType) := f.
HB.instance Definition _ := @isHom.Build NModules a b forget_mor (isHom_inhom f).
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build ZModules NModules forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition functor : {functor ZModules -> NModules} := forget.

End ForgetZModules_to_NModules.

Definition forget_ZModules_to_NModules := ForgetZModules_to_NModules.functor.
Lemma forget_ZModules_to_NModulesE a b (f : {hom ZModules; a, b}) :
  forget_ZModules_to_NModules # f = f :> (_ -> _).
Proof. by []. Qed.
Definition forget_ZModules_to_Sets :=
  forget_NModules_to_Sets \O forget_ZModules_to_NModules.
Lemma forget_ZModules_to_SetsE a b (f : {hom ZModules; a, b}) :
  forget_ZModules_to_Sets # f = f :> (_ -> _).
Proof. by []. Qed.


(* SemiRings ************************************************************)

Definition semiring_morph (a b : semiRingType) (f : a -> b) : Prop :=
  semi_additive f * multiplicative f.
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

#[warning="-uniform-inheritance"]
Coercion rmorph_of_SRing a b (f : {hom SemiRings; a, b}) : {rmorphism a -> b} :=
  HB.pack (Hom.sort f)
    (GRing.isSemiAdditive.Build _ _ _ (fst (isHom_inhom f)))
    (GRing.isMultiplicative.Build _ _ _ (snd (isHom_inhom f))).
Lemma rmorph_of_SRingE a b (f : {hom SemiRings; a, b}) :
  @rmorph_of_SRing a b f = f :> (_ -> _).
Proof. by []. Qed.

Module ForgetSemiRings_to_NModules.

Section Morphism.
Variable (a b : semiRingType) (f : {hom SemiRings; a, b}).
Definition forget (T : semiRingType) : nmodType := T.
Definition forget_mor : (a : nmodType) -> (b : nmodType) := f.
HB.instance Definition _ :=
  @isHom.Build NModules a b forget_mor (fst (isHom_inhom f)).
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build SemiRings NModules forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition functor : {functor SemiRings -> NModules} := forget.

End ForgetSemiRings_to_NModules.

Definition forget_SemiRings_to_NModules := ForgetSemiRings_to_NModules.functor.
Lemma forget_SemiRings_to_NModulesE a b (f : {hom SemiRings; a, b}) :
  forget_SemiRings_to_NModules # f = f :> (_ -> _).
Proof. by []. Qed.
Definition forget_SemiRings_to_Sets :=
  forget_NModules_to_Sets \O forget_SemiRings_to_NModules.
Lemma forget_SemiRings_to_SetsE a b (f : {hom SemiRings; a, b}) :
  forget_SemiRings_to_Sets # f = f :> (_ -> _).
Proof. by []. Qed.


(* Rings **********************************************************)

HB.instance Definition _ :=
  isCategory.Build ringType (fun T : ringType => T)
    semiring_morph idfun_is_semiring_morph comp_is_semiring_morph.
Notation Rings := [the category of ringType].
#[warning="-uniform-inheritance"]
Coercion rmorph_of_Ring a b (f : {hom Rings; a, b}) : {rmorphism a -> b} :=
  HB.pack (Hom.sort f)
    (GRing.isSemiAdditive.Build _ _ _ (fst (isHom_inhom f)))
    (GRing.isMultiplicative.Build _ _ _ (snd (isHom_inhom f))).
Lemma rmorph_of_RingE a b (f : {hom Rings; a, b}) :
  @rmorph_of_Ring a b f = f :> (_ -> _).
Proof. by []. Qed.

Module ForgetRings_to_ZModules.

Section Morphism.
Variable (a b : ringType) (f : {hom Rings; a, b}).
Definition forget (T : ringType) : zmodType := T.
Definition forget_mor : (a : zmodType) -> (b : zmodType) := f.
HB.instance Definition _ :=
  @isHom.Build ZModules a b forget_mor (fst (isHom_inhom f)).
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build Rings ZModules forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition functor : {functor Rings -> ZModules} := forget.

End ForgetRings_to_ZModules.

Definition forget_Rings_to_ZModules := ForgetRings_to_ZModules.functor.
Lemma forget_Rings_to_ZModulesE a b (f : {hom Rings; a, b}) :
  forget_Rings_to_ZModules # f = f :> (_ -> _).
Proof. by []. Qed.
Definition forget_Rings_to_Sets :=
  forget_ZModules_to_Sets \O forget_Rings_to_ZModules.
Lemma forget_Rings_to_SetsE a b (f : {hom Rings; a, b}) :
  forget_Rings_to_Sets # f = f :> (_ -> _).
Proof. by []. Qed.


(* ComSemiRings **********************************************************)

HB.instance Definition _ :=
  isCategory.Build comSemiRingType (fun T : comSemiRingType => T)
    semiring_morph idfun_is_semiring_morph comp_is_semiring_morph.
Notation ComSemiRings := [the category of comSemiRingType].

Module ForgetComSemiRings_to_SemiRings.

Section Morphism.
Variable (a b : comSemiRingType) (f : {hom ComSemiRings; a, b}).
Definition forget (T : comSemiRingType) : semiRingType := T.
Definition forget_mor : (a : semiRingType) -> (b : semiRingType) := f.
HB.instance Definition _ :=
  @isHom.Build SemiRings a b forget_mor (isHom_inhom f).
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build ComSemiRings SemiRings forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition functor : {functor ComSemiRings -> SemiRings} := forget.

End ForgetComSemiRings_to_SemiRings.

Definition forget_ComSemiRings_to_SemiRings :=
  ForgetComSemiRings_to_SemiRings.functor.
Lemma forget_ComSemiRings_to_SemiRingsE a b (f : {hom ComSemiRings; a, b}) :
  forget_ComSemiRings_to_SemiRings # f = f :> (_ -> _).
Proof. by []. Qed.
#[warning="-uniform-inheritance"]
Coercion rmorph_of_ComSemiRing a b (f : {hom ComSemiRings; a, b}) :
  {rmorphism a -> b} := forget_ComSemiRings_to_SemiRings # f.
Lemma rmorph_of_ComSemiRingE a b (f : {hom ComSemiRings; a, b}) :
  rmorph_of_ComSemiRing f = f :> (_ -> _).
Proof. by []. Qed.

(* Q : Should there be a coercion
   {hom ComSemiRings; a, b} -> {hom SemiRings; a, b} *)


(* ComRings **********************************************************)

HB.instance Definition _ :=
  isCategory.Build comRingType (fun T : comRingType => T)
    semiring_morph  idfun_is_semiring_morph comp_is_semiring_morph.
Notation ComRings := [the category of comRingType].

Module ForgetComRings_to_Rings.

Section Morphism.
Variable (a b : comRingType) (f : {hom ComRings; a, b}).
Definition forget (T : comRingType) : ringType := T.
Definition forget_mor : (a : ringType) -> (b : ringType) := f.
HB.instance Definition _ := @isHom.Build Rings a b forget_mor (isHom_inhom f).
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build ComRings Rings forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition functor : {functor ComRings -> Rings} := forget.

End ForgetComRings_to_Rings.

Definition forget_ComRings_to_Rings := ForgetComRings_to_Rings.functor.
Lemma forget_ComRings_to_RingsE a b (f : {hom ComRings; a, b}) :
  forget_ComRings_to_Rings # f = f :> (_ -> _).
Proof. by []. Qed.
#[warning="-uniform-inheritance"]
Coercion rmorph_of_comRing a b (f : {hom ComRings; a, b}) :
  {rmorphism a -> b} := rmorph_of_Ring (forget_ComRings_to_Rings # f).


(* L-Modules **********************************************************)

Section LModules.
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
End LModules.
Notation LModules R := [the category of lmodType R].
#[warning="-uniform-inheritance"]
Coercion linear_of_Lmod R a b (f : {hom LModules R; a, b}) : {linear a -> b} :=
  HB.pack (Hom.sort f) (GRing.isLinear.Build _ _ _ _ _ (isHom_inhom f)).
Lemma linear_of_LmodE R a b (f : {hom LModules R; a, b}) :
  @linear_of_Lmod R a b f = f :> (_ -> _).
Proof. by []. Qed.
Fact LModules_mor_semi_additive R a b (f : {hom LModules R; a, b}) :
  semi_additive f.
Proof.
rewrite -linear_of_LmodE; split => [| x y]; first by rewrite raddf0.
by rewrite raddfD.
Qed.

Module ForgetLModules_to_ZModules.

Section BaseRing.
Variable R : ringType.

Section Morphism.
Variables (a b : lmodType R) (f : {hom LModules R; a, b}).
Definition forget (T : lmodType R) : zmodType := T.
Definition forget_mor : (a : zmodType) -> (b : zmodType) := f.
HB.instance Definition _ :=
  @isHom.Build ZModules a b forget_mor (LModules_mor_semi_additive f).
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build (LModules R) ZModules forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
End BaseRing.
Definition functor R : {functor LModules R -> ZModules} := @forget R.

End ForgetLModules_to_ZModules.

Definition forget_LModules_to_ZModules := ForgetLModules_to_ZModules.functor.
Lemma forget_LModules_to_ZModulesE R a b (f : {hom LModules R; a, b}) :
  forget_LModules_to_ZModules R # f = f :> (_ -> _).
Proof. by []. Qed.
Definition forget_LModules_to_Sets R :=
  forget_ZModules_to_Sets \O forget_LModules_to_ZModules R.
Lemma forget_LModules_to_SetsE R a b (f : {hom LModules R; a, b}) :
  forget_LModules_to_Sets R # f = f :> (_ -> _).
Proof. by []. Qed.


(* L-algebras ************************************************************)
Section LAlgebras.

Variable (R : ringType).
Definition lalg_morph (a b : lalgType R) (f : a -> b) : Prop:=
  linear f * multiplicative f.
Fact idfun_is_lalg_morph (a : lalgType R) :
  lalg_morph (idfun : a -> a).
Proof. by []. Qed.
Fact comp_is_lalg_morph (a b c : lalgType R) (f : a -> b) (g : b -> c) :
  lalg_morph f -> lalg_morph g -> lalg_morph (g \o f).
Proof.
move=> [fA fM] [gA gM]; split; first exact: comp_is_linear.
by split => [x y|] /=; rewrite fM gM.
Qed.
HB.instance Definition _ :=
  isCategory.Build (lalgType R) (fun T : lalgType R => T)
    (fun a b (f : a -> b) => lalg_morph f)
    idfun_is_lalg_morph comp_is_lalg_morph.
End LAlgebras.
Notation LAlgebras R := [the category of lalgType R].
#[warning="-uniform-inheritance"]
Coercion lrmorphism_of_LAlgebras R a b (f : {hom LAlgebras R; a, b}) :
  {lrmorphism a -> b} := HB.pack (Hom.sort f)
     (GRing.isLinear.Build _ _ _ _ _ (fst (isHom_inhom f)))
     (GRing.isMultiplicative.Build _ _ _ (snd (isHom_inhom f))).
Lemma lrmorphism_of_LAlgebrasE R a b (f : {hom LAlgebras R; a, b}) :
  @lrmorphism_of_LAlgebras R a b f = f :> (_ -> _).
Proof. by []. Qed.
Fact LAlgebras_mor_rmorphism R a b (f : {hom LAlgebras R; a, b}) :
  semiring_morph f.
Proof.
split; last by case: f => [/= f [[[fL FM]]]].
rewrite -lrmorphism_of_LAlgebrasE; split => [| x y]; first by rewrite raddf0.
by rewrite raddfD.
Qed.

Module ForgetLAlgebras_to_LModules.

Section BaseRing.
Variable R : ringType.

Section Morphism.
Variables (a b : lalgType R) (f : {hom LAlgebras R; a, b}).
Definition forget (T : lalgType R) : lmodType R := T.
Definition forget_mor : (a : lmodType R) -> (b : lmodType R) := f.
HB.instance Definition _ :=
  @isHom.Build (LModules R) a b forget_mor (fst (isHom_inhom f)).
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build (LAlgebras R) (LModules R) forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
End BaseRing.
Definition functor R : {functor LAlgebras R -> LModules R} := @forget R.

End ForgetLAlgebras_to_LModules.

Definition forget_LAlgebras_to_LModules := ForgetLAlgebras_to_LModules.functor.
Lemma forget_LAlgebras_to_LModulesE R a b (f : {hom LAlgebras R; a, b}) :
  forget_LAlgebras_to_LModules R # f = f :> (_ -> _).
Proof. by []. Qed.

Module ForgetLAlgebras_to_Rings.

Section BaseRing.
Variable R : ringType.

Section Morphism.
Variables (a b : lalgType R) (f : {hom LAlgebras R; a, b}).
Definition forget (T : lalgType R) : ringType := T.
Definition forget_mor : (a : ringType) -> (b : ringType) := f.
HB.instance Definition _ :=
  @isHom.Build Rings a b forget_mor (LAlgebras_mor_rmorphism f).
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build (LAlgebras R) Rings forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
End BaseRing.
Definition functor R : {functor LAlgebras R -> Rings} := @forget R.

End ForgetLAlgebras_to_Rings.

Definition forget_LAlgebras_to_Rings := ForgetLAlgebras_to_Rings.functor.
Lemma forget_LAlgebras_to_RingsE R a b (f : {hom LAlgebras R; a, b}) :
  forget_LAlgebras_to_Rings R # f = f :> (_ -> _).
Proof. by []. Qed.

Lemma unicity_of_forgetful_functors (R : ringType) :
  forget_Rings_to_ZModules \O forget_LAlgebras_to_Rings R
    =#= forget_LModules_to_ZModules R \O forget_LAlgebras_to_LModules R.
Proof. exact: (@functor_ext _ _ _ _ (fun=> _)). Qed.


(* Algebras ************************************************************)

HB.instance Definition _ R :=
  isCategory.Build (algType R) (fun T : algType R => T)
    (fun a b (f : a -> b) => lalg_morph f)
    (@idfun_is_lalg_morph R) (@comp_is_lalg_morph R).
Notation Algebras R := [the category of algType R].

Module ForgetAlgebras_to_LAlgebras.

Section BaseRing.
Variable R : ringType.

Section Morphism.
Variables (a b : algType R) (f : {hom Algebras R; a, b}).
Definition forget (T : algType R) : lalgType R := T.
Definition forget_mor : (a : lalgType R) -> (b : lalgType R) := f.
HB.instance Definition _ :=
  @isHom.Build (LAlgebras R) a b forget_mor (isHom_inhom f).
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build (Algebras R) (LAlgebras R) forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
End BaseRing.
Definition functor R : {functor Algebras R -> LAlgebras R} := @forget R.

End ForgetAlgebras_to_LAlgebras.

Definition forget_Algebras_to_LAlgebras := ForgetAlgebras_to_LAlgebras.functor.
Lemma forget_Algebras_to_LAlgebrasE R a b (f : {hom Algebras R; a, b}) :
  forget_Algebras_to_LAlgebras R # f = f :> (_ -> _).
Proof. by []. Qed.
#[warning="-uniform-inheritance"]
Coercion lrmorphism_of_Algebras R a b (f : {hom Algebras R; a, b}) :
  {lrmorphism a -> b} := forget_Algebras_to_LAlgebras R # f.
Lemma lrmorphism_of_AlgebrasE R a b (f : {hom Algebras R; a, b}) :
  lrmorphism_of_Algebras f = f :> (_ -> _).
Proof. by []. Qed.


(* ComAlgebras *****************************************************)

HB.instance Definition _ R :=
  isCategory.Build (comAlgType R) (fun T : comAlgType R => T)
    (fun a b (f : a -> b) => lalg_morph f)
    (@idfun_is_lalg_morph R) (@comp_is_lalg_morph R).
Notation ComAlgebras R := [the category of comAlgType R].

Module ForgetComAlgebras_to_Algebras.

Section BaseRing.
Variable R : ringType.

Section Morphism.
Variables (a b : comAlgType R) (f : {hom ComAlgebras R; a, b}).
Definition forget (T : comAlgType R) : algType R := T.
Definition forget_mor : (a : algType R) -> (b : algType R) := f.
HB.instance Definition _ :=
  @isHom.Build (Algebras R) a b forget_mor (isHom_inhom f).
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build (ComAlgebras R) (Algebras R) forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
End BaseRing.
Definition functor R : {functor ComAlgebras R -> Algebras R} := @forget R.

End ForgetComAlgebras_to_Algebras.

Definition forget_ComAlgebras_to_Algebras := ForgetComAlgebras_to_Algebras.functor.
Lemma forget_ComAlgebras_to_AlgebrasE R a b (f : {hom ComAlgebras R; a, b}) :
  forget_ComAlgebras_to_Algebras R # f = f :> (_ -> _).
Proof. by []. Qed.
#[warning="-uniform-inheritance"]
Coercion lrmorphism_of_ComAlgebras R a b (f : {hom ComAlgebras R; a, b}) :
  {lrmorphism a -> b} :=
  lrmorphism_of_Algebras (forget_ComAlgebras_to_Algebras R # f).
Lemma lrmorphism_of_ComAlgebrasE R a b (f : {hom ComAlgebras R; a, b}) :
  lrmorphism_of_ComAlgebras f = f :> (_ -> _).
Proof. by []. Qed.


(*
HB.instance Definition _ :=
  isCategory.Build unitRingType (fun T : unitRingType => T)
    semiring_morph idfun_is_semiring_morph comp_is_semiring_morph.
Notation UnitRings := [the category of unitRingType].

HB.instance Definition _ :=
  isCategory.Build comUnitRingType (fun T : comUnitRingType => T)
    semiring_morph idfun_is_semiring_morph comp_is_semiring_morph.
Notation ComUnitRings := [the category of comUnitRingType].

HB.instance Definition _ R :=
  isCategory.Build (unitAlgType R) (fun T : unitAlgType R => T)
    (fun a b (f : a -> b) => lalg_morph f)
    (@idfun_is_lalg_morph R) (@comp_is_lalg_morph R).
Notation UnitAlgebras R := [the category of unitAlgType R].

HB.instance Definition _ R :=
  isCategory.Build (comUnitAlgType R) (fun T : comUnitAlgType R => T)
    (fun a b (f : a -> b) => lalg_morph f)
    (@idfun_is_lalg_morph R) (@comp_is_lalg_morph R).
Notation ComUnitAlgebras R := [the category of comUnitAlgType R].
*)



(** Adjonction between forget : NModules -> Sets and free N-Modules *)

Local Open Scope ring_scope.
Local Open Scope mset_scope.

Section Set_to_FreeNmodule.

Variable (a b : choiceType) (f : {hom Sets; a, b}).

Definition hom_mset (m : {mset a}) : {mset b} :=
  \sum_(i <- m) [mset f i].

Lemma hom_mset1 x : hom_mset [mset x] = [mset f x].
Proof. by rewrite /hom_mset big_msetn /=. Qed.

Lemma hom_mset_additive : semi_additive hom_mset.
Proof.
rewrite /hom_mset; split => [| /= x y]; first by rewrite big_mset0.
apply msetP => u /=; rewrite msetDE !mset_sum !sum_mset.
under eq_bigr => i _ do rewrite msetDE natrDE mulnDl.
rewrite natrDE big_split /=; congr (_ + _)%N.
  apply: finsupp_widenD => i.
  by rewrite msuppE -mset_eq0 => /eqP -> /[!mul0n].
rewrite addrC; apply: finsupp_widenD => i.
by rewrite msuppE -mset_eq0 => /eqP -> /[!mul0n].
Qed.

End Set_to_FreeNmodule.

Definition FreeNmod (T : choiceType) : nmodType := {mset T}.
HB.instance Definition _ (a b : Sets) (f : a -> b) :=
  @isHom.Build NModules {mset a} {mset b}
    (hom_mset f : [the nmodType of {mset a}] -> [the nmodType of {mset b}])
    (hom_mset_additive f).
Definition FreeNmod_mor (a b : Sets) (f : a -> b)
  : {hom NModules; FreeNmod a, FreeNmod b} := hom_mset f.

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
  @isFunctor.Build Sets NModules
    FreeNmod FreeNmod_mor FreeNmod_ext FreeNmod_id FreeNmod_comp.

Section Adjoint.

Definition functor_FreeNmod : {functor Sets -> NModules} := FreeNmod.

Implicit Types (a : choiceType) (T : nmodType).

Let eta_fun a (x : a) := [mset x].
Definition eta : FId ~~> forget_NModules_to_Sets \o FreeNmod := eta_fun.
Fact eta_natural : naturality FId (forget_NModules_to_Sets \o FreeNmod) eta.
Proof. by move=> /= a b h x /=; rewrite /eta_fun FIdf hom_mset1. Qed.
HB.instance Definition _ :=
  @isNatural.Build Sets Sets FId
    (forget_NModules_to_Sets \o FreeNmod) eta eta_natural.

Let eps_fun T (m : (FreeNmod \o forget_NModules_to_Sets) T) : T :=
      \sum_(i <- m : {mset _}) i.
Fact eps_fun_additive T : semi_additive (@eps_fun T).
Proof.
rewrite /eps_fun; split => [|/= s t]; first by rewrite big_mset0.
by rewrite big_msetD.
Qed.
HB.instance Definition _ T :=
  isHom.Build NModules ((FreeNmod \o forget_NModules_to_Sets) T) (FId T)
    (@eps_fun T) (@eps_fun_additive T).
Definition eps : FreeNmod \o forget_NModules_to_Sets ~~> FId := eps_fun.
Fact eps_natural : naturality (FreeNmod \o forget_NModules_to_Sets) FId eps.
Proof.
move=> /= a b h.
rewrite -!additive_of_NmodE; apply: additive_msetE => /= x.
by rewrite FIdf /eps_fun /hom_mset /= !big_msetn.
Qed.
HB.instance Definition _ :=
  @isNatural.Build NModules NModules
    (FreeNmod \o forget_NModules_to_Sets) FId eps eps_natural.

Fact triL : TriangularLaws.left eta eps.
Proof.
move=> /= a.
rewrite -!additive_of_NmodE; apply: additive_msetE => /= x.
by rewrite /eta_fun /= /eps_fun /hom_mset /= !big_msetn.
Qed.
Fact triR : TriangularLaws.right eta eps.
Proof. by move=> /= M m; rewrite /eta_fun /= /eps_fun !big_msetn /=. Qed.

Let F : {functor Sets -> NModules} := FreeNmod.
Let G : {functor NModules -> Sets} := forget_NModules_to_Sets.

Definition adj_FreeNmod_forget : FreeNmod -| forget_NModules_to_Sets :=
  AdjointFunctors.mk triL triR.

End Adjoint.


Section UniversalProperty.

Variables (A : choiceType) (M : nmodType) (f : A -> M).

Definition univmap : {additive {mset A} -> M} :=
  eps M \o FreeNmod # f : {hom FreeNmod A, M}.

Lemma univmapP a : univmap [mset a] = f a.
Proof.
rewrite /univmap -[[mset a]]/(eta A a) /= hom_mset1.
exact: triR.
Qed.

Lemma univmap_uniq (g : {additive {mset A} -> M}) :
  (forall a : A, g [mset a] = f a) -> g =1 univmap.
Proof.
move=> eq m; rewrite -(msetE m) !raddf_sum; apply eq_bigr => x _.
by rewrite eq univmapP.
Qed.

End UniversalProperty.


(** Adjonction between forget : L-Modules -> Sets and free L-Modules *)

Section Set_to_FreeLmodule.

Variable R : ringType.

Variable (a b : choiceType) (f : a -> b).

Definition hom_fm (m : {freemod R[a]}) : {freemod R[b]} :=
  \sum_(i <- finsupp m) [fm: f i => m i].

Lemma hom_fm1 (x : a) : hom_fm [fm: x => 1] = [fm: f x => 1].
Proof. by rewrite /hom_fm finsupp_fm1 /= big_seq_fset1 fm1E eqxx. Qed.

Fact hom_fm_linear : linear hom_fm.
Proof.
rewrite /hom_fm => c /= m n; rewrite scaler_sumr.
rewrite -!(finsupp_widen _ (S := finsupp m `|` finsupp n)%fset) /=.
- rewrite -big_split /=; apply: eq_bigr => x _.
  apply/fsfunP => y; rewrite !addfmE !scalefmE !fm1E.
  by case: eqP => // _; rewrite addr0 mulr0.
- by move=> i /[!memNfinsupp] /eqP ->; rewrite fm10eq0.
- by move=> x; rewrite inE orbC => ->.
- by move=> i /[!memNfinsupp] /eqP ->; rewrite fm10eq0 scaler0.
- by move=> x; rewrite inE => ->.
- by move=> i /[!memNfinsupp] /eqP ->; rewrite fm10eq0.
- move=> x; rewrite inE; apply contraLR.
  rewrite negb_or !memNfinsupp addfmE scalefmE => /andP [/eqP -> /eqP ->].
  by rewrite mulr0 addr0.
Qed.
HB.instance Definition _ :=
  GRing.isLinear.Build R {freemod R[a]} {freemod R[b]} _ hom_fm hom_fm_linear.

End Set_to_FreeLmodule.

Section Functor.
Variable (R : ringType).

HB.instance Definition _ (a b : Sets) (f : {hom Sets; a, b}) :=
  @isHom.Build (LModules R) {freemod R[a]} {freemod R[b]}
    (hom_fm f : (_ : lmodType R) -> _) (hom_fm_linear f).
Definition freeLmod_mor (a b : Sets) (f : a -> b)
  : {hom LModules R; {freemod R[a]}, {freemod R[b]}} := hom_fm f.

Fact freeLmod_ext : FunctorLaws.ext freeLmod_mor.
Proof.
move=> /= a b f g eq y; rewrite /hom_mset.
by apply eq_bigr => x _; rewrite eq.
Qed.
Fact freeLmod_id : FunctorLaws.id freeLmod_mor.
Proof.
move=> /= a x /=; rewrite /hom_mset /= -[RHS]fmE.
by rewrite /hom_fm; apply: eq_bigr => i _.
Qed.
Fact freeLmod_comp  : FunctorLaws.comp freeLmod_mor.
Proof.
move=> /= a b c f g.
rewrite -!linear_of_LmodE; apply: linear_fmE => /= x.
by rewrite /hom_fm /= !(finsupp_fm1, big_seq_fset1, fm1E, eqxx).
Qed.

Definition functor_freeLmod a : lmodType R := {freemod R[a]}.
HB.instance Definition _ :=
  @isFunctor.Build Sets (LModules R) functor_freeLmod
     freeLmod_mor freeLmod_ext freeLmod_id freeLmod_comp.

End Functor.

Section Adjoint.

Variable R : ringType.
Implicit Types (a : choiceType) (T : lmodType R).
Local Notation fmf := (@functor_freeLmod R).
Local Notation forgetf := (forget_LModules_to_Sets R).
Let eta_fun a (x : a) : {freemod R[a]} := [fm: x => 1].
Definition eta_fm : FId ~~> forgetf \o fmf := eta_fun.
Fact eta_fm_natural : naturality FId (forgetf \o fmf) eta_fm.
Proof. by move=> /= a b h x /=; rewrite /eta_fun FIdf hom_fm1. Qed.
HB.instance Definition _ :=
  @isNatural.Build Sets Sets FId
    (forgetf \o fmf) eta_fm eta_fm_natural.

Let eps_fun T (m : (fmf \o forgetf) T) : T :=
      \sum_(i <- finsupp (m : {freemod R[_]})) (m i) *: i.
Fact eps_fun_linear T : linear (@eps_fun T).
Proof.
rewrite /eps_fun => c s t; rewrite scaler_sumr.
rewrite -!(finsupp_widen _ (S := finsupp s `|` finsupp t)%fset) /=.
- rewrite -big_split /=; apply: eq_bigr => x _.
  by rewrite addfmE scalefmE scalerDl scalerA.
- by move=> i /[!memNfinsupp] /eqP ->; rewrite scale0r.
- by move=> x; rewrite inE orbC => ->.
- by move=> i /[!memNfinsupp] /eqP ->; rewrite scale0r scaler0.
- by move=> x; rewrite inE => ->.
- by move=> i /[!memNfinsupp] /eqP ->; rewrite scale0r.
- move=> x; rewrite inE; apply contraLR.
  rewrite negb_or !memNfinsupp addfmE scalefmE => /andP [/eqP -> /eqP ->].
  by rewrite mulr0 addr0.
Qed.
HB.instance Definition _ T :=
  isHom.Build (LModules R) ((fmf \o forgetf) T) (FId T)
    (@eps_fun T) (@eps_fun_linear T).
Definition eps_fm : fmf \o forgetf ~~> FId := eps_fun.
Fact eps_fm_natural : naturality (fmf \o forgetf) FId eps_fm.
Proof.
move=> /= a b h.
rewrite -!linear_of_LmodE; apply: linear_fmE => /= x.
rewrite FIdf /eps_fun /= hom_fm1.
by rewrite !finsupp_fm1 !big_seq_fset1 !fm1E !eqxx !scale1r.
Qed.
HB.instance Definition _ :=
  @isNatural.Build (LModules R) (LModules R)
    (fmf \o forgetf) FId eps_fm eps_fm_natural.

Fact triL_fm : TriangularLaws.left eta_fm eps_fm.
Proof.
move=> /= a.
rewrite -!linear_of_LmodE; apply: linear_fmE => /= x.
rewrite /eta_fun /= /eps_fun /= hom_fm1.
by rewrite !finsupp_fm1 !big_seq_fset1 !fm1E !eqxx !scale1r.
Qed.
Fact triR_fm : TriangularLaws.right eta_fm eps_fm.
Proof.
move=> /= M m; rewrite /eta_fun /= /eps_fun.
by rewrite finsupp_fm1 big_seq_fset1 fm1E eqxx scale1r.
Qed.

Let F : {functor Sets -> LModules R} := functor_freeLmod R.
Let G : {functor LModules R -> Sets} := forget_LModules_to_Sets R.

Definition adj_FreeLmod_forget : F -| G :=
  AdjointFunctors.mk triL_fm triR_fm.

End Adjoint.

Section UniversalProperty.

Variable (R : ringType).

Variables (A : choiceType) (M : lmodType R) (f : A -> M).

Definition univmap_fm : {linear {freemod R[A]} -> M} :=
  eps_fm M \o (functor_freeLmod R) # f : {hom _, M}.

Lemma univmap_fmP a : univmap_fm [fm: a => 1] = f a.
Proof.
rewrite /univmap_fm -[[fm: a => 1]]/(eta_fm R A a) /= !hom_fm1.
exact: triR_fm.
Qed.

Lemma univmap_fm_uniq (g : {linear {freemod R[A]} -> M}) :
  (forall a : A, g [fm: a => 1] = f a) -> g =1 univmap_fm.
Proof.
move=> eq m.
rewrite -(fmE m) !raddf_sum; apply eq_bigr => x _.
by rewrite fm1ZE [LHS]linearZ [RHS]linearZ eq univmap_fmP.
Qed.

End UniversalProperty.


