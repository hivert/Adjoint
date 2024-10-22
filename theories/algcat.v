From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finfun bigop.
From mathcomp Require Import ssralg ssrint finmap multiset.

Require Import category msetcompl algcompl.

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
Definition Sets : category := choiceType.


(* N-Modules ************************************************************)

Definition idfun_is_semi_additive := GRing.idfun_is_semi_additive.
Fact comp_is_semi_additive (a b c : nmodType) (f : a -> b) (g : b -> c) :
  semi_additive f -> semi_additive g -> semi_additive (g \o f).
Proof. by move=> fM gM; split => [|x y]; rewrite /= fM gM. Qed.
HB.instance Definition _ :=
  isCategory.Build nmodType (fun T : nmodType => T)
    semi_additive idfun_is_semi_additive comp_is_semi_additive.
Definition NModules : category := nmodType.
#[warning="-uniform-inheritance"]
Definition additive_of_Nmod a b (f : {hom[NModules] a -> b}) : {additive a -> b} :=
  HB.pack (Hom.sort f) (GRing.isSemiAdditive.Build _ _ _ (isHom_inhom f)).
Lemma additive_of_NmodE a b (f : {hom[NModules] a -> b}) :
  @additive_of_Nmod a b f = f :> (_ -> _).
Proof. by []. Qed.

Module ForgetNModules_to_Sets.

Section Morphism.
Variable (a b : NModules) (f : {hom[NModules] a -> b}).
Definition forget (T : NModules) : Sets := T.
HB.instance Definition _ :=
  @isHom.Build Sets a b (f : (a : Sets) -> b) I.
Definition forget_mor : {hom[Sets] a -> b} := f : a -> b.
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build NModules Sets forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition functor : {functor NModules -> Sets} := forget.

End ForgetNModules_to_Sets.

Definition forget_NModules_to_Sets := ForgetNModules_to_Sets.functor.
Lemma forget_NModules_to_SetsE a b (f : {hom[NModules] a -> b}) :
  forget_NModules_to_Sets # f = f :> (_ -> _).
Proof. by []. Qed.


(* Z-Modules ************************************************************)

(* Full subcategory of N-module *)
HB.instance Definition _ :=
  isCategory.Build zmodType (fun T : zmodType => T)
    (@inhom NModules) (@idfun_inhom NModules) (@funcomp_inhom NModules).
Definition ZModules : category := zmodType.

#[warning="-uniform-inheritance"]
Coercion additive_of_Zmod a b (f : {hom[ZModules] a -> b}) : {additive a -> b} :=
  HB.pack (Hom.sort f) (GRing.isSemiAdditive.Build _ _ f (isHom_inhom f)).
Lemma additive_of_ZmodE a b (f : {hom[ZModules] a -> b}) :
  [the {additive _ -> _} of @additive_of_Zmod a b f] = f :> (_ -> _).
Proof. by []. Qed.


Module ForgetZModules_to_NModules.

Section Morphism.
Variable (a b : ZModules) (f : {hom[ZModules] a -> b}).
Definition forget (T : ZModules) : NModules := T.
Definition forget_mor : (a : NModules) -> (b : NModules) := f.
HB.instance Definition _ := @isHom.Build NModules a b forget_mor (isHom_inhom f).
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build ZModules NModules forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition functor : {functor ZModules -> NModules} := forget.

End ForgetZModules_to_NModules.

Definition forget_ZModules_to_NModules := ForgetZModules_to_NModules.functor.
Lemma forget_ZModules_to_NModulesE a b (f : {hom[ZModules] a -> b}) :
  forget_ZModules_to_NModules # f = f :> (_ -> _).
Proof. by []. Qed.
Definition forget_ZModules_to_Sets :=
  forget_NModules_to_Sets \O forget_ZModules_to_NModules.
Lemma forget_ZModules_to_SetsE a b (f : {hom[ZModules] a -> b}) :
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
Definition SemiRings : category := semiRingType.

#[warning="-uniform-inheritance"]
Coercion rmorph_of_SRing a b (f : {hom[SemiRings] a -> b}) : {rmorphism a -> b} :=
  HB.pack (Hom.sort f)
    (GRing.isSemiAdditive.Build _ _ _ (fst (isHom_inhom f)))
    (GRing.isMultiplicative.Build _ _ _ (snd (isHom_inhom f))).
Lemma rmorph_of_SRingE a b (f : {hom[SemiRings] a -> b}) :
  [the {rmorphism a -> b} of @rmorph_of_SRing a b f] = f :> (_ -> _).
Proof. by []. Qed.

Module ForgetSemiRings_to_NModules.

Section Morphism.
Variable (a b : SemiRings) (f : {hom[SemiRings] a -> b}).
Definition forget (T : SemiRings) : NModules := T.
Definition forget_mor : (a : NModules) -> (b : NModules) := f.
HB.instance Definition _ :=
  @isHom.Build NModules a b forget_mor (fst (isHom_inhom f)).
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build SemiRings NModules forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition functor : {functor SemiRings -> NModules} := forget.

End ForgetSemiRings_to_NModules.

Definition forget_SemiRings_to_NModules := ForgetSemiRings_to_NModules.functor.
Lemma forget_SemiRings_to_NModulesE a b (f : {hom[SemiRings] a -> b}) :
  forget_SemiRings_to_NModules # f = f :> (_ -> _).
Proof. by []. Qed.
Definition forget_SemiRings_to_Sets :=
  forget_NModules_to_Sets \O forget_SemiRings_to_NModules.
Lemma forget_SemiRings_to_SetsE a b (f : {hom[SemiRings] a -> b}) :
  forget_SemiRings_to_Sets # f = f :> (_ -> _).
Proof. by []. Qed.


(* Rings **********************************************************)

(** Full subcategory of SemiRing *)
HB.instance Definition _ :=
  isCategory.Build ringType (fun T : ringType => T)
    (@inhom SemiRings) (@idfun_inhom SemiRings) (@funcomp_inhom SemiRings).
Definition Rings : category := ringType.
#[warning="-uniform-inheritance"]
Coercion rmorph_of_Ring a b (f : {hom[Rings] a -> b}) : {rmorphism a -> b} :=
  HB.pack (Hom.sort f)
    (GRing.isSemiAdditive.Build _ _ _ (fst (isHom_inhom f)))
    (GRing.isMultiplicative.Build _ _ _ (snd (isHom_inhom f))).
Lemma rmorph_of_RingE a b (f : {hom[Rings] a -> b}) :
  [the {rmorphism a -> b} of @rmorph_of_Ring a b f] = f :> (_ -> _).
Proof. by []. Qed.


Module ForgetRings_to_SemiRings.

Section Morphism.
Variable (a b : Rings) (f : {hom[Rings] a -> b}).
Definition forget (T : Rings) : SemiRings := T.
Definition forget_mor : (a : SemiRings) -> (b : SemiRings) := f.
HB.instance Definition _ :=
  @isHom.Build SemiRings a b forget_mor (isHom_inhom f).
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build Rings SemiRings forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition functor : {functor Rings -> SemiRings} := forget.

End ForgetRings_to_SemiRings.

Definition forget_Rings_to_SemiRings := ForgetRings_to_SemiRings.functor.
Lemma forget_Rings_to_SemiRingsE a b (f : {hom[Rings] a -> b}) :
  forget_Rings_to_SemiRings # f = f :> (_ -> _).
Proof. by []. Qed.


Module ForgetRings_to_ZModules.

Section Morphism.
Variable (a b : Rings) (f : {hom[Rings] a -> b}).
Definition forget (T : Rings) : ZModules := T.
Definition forget_mor : (a : ZModules) -> (b : ZModules) := f.
HB.instance Definition _ :=
  @isHom.Build ZModules a b forget_mor (fst (isHom_inhom f)).
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build Rings ZModules forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition functor : {functor Rings -> ZModules} := forget.

End ForgetRings_to_ZModules.

Definition forget_Rings_to_ZModules := ForgetRings_to_ZModules.functor.
Lemma forget_Rings_to_ZModulesE a b (f : {hom[Rings] a -> b}) :
  forget_Rings_to_ZModules # f = f :> (_ -> _).
Proof. by []. Qed.

Definition forget_Rings_to_Sets :=
  forget_ZModules_to_Sets \O forget_Rings_to_ZModules.
Lemma forget_Rings_to_SetsE a b (f : {hom[Rings] a -> b}) :
  forget_Rings_to_Sets # f = f :> (_ -> _).
Proof. by []. Qed.
Lemma unicity_forget_Rings_to_Sets :
  forget_SemiRings_to_Sets \O forget_Rings_to_SemiRings =#=
    forget_Rings_to_Sets.
Proof. exact: (functor_ext (eq := fun=> _)). Qed.


(* ComSemiRings **********************************************************)

(** Full subcategory of SemiRings *)
HB.instance Definition _ :=
  isCategory.Build comSemiRingType (fun T : comSemiRingType => T)
    (@inhom SemiRings) (@idfun_inhom SemiRings) (@funcomp_inhom SemiRings).
Definition ComSemiRings : category := comSemiRingType.

Module ForgetComSemiRings_to_SemiRings.

Section Morphism.
Variable (a b : ComSemiRings) (f : {hom[ComSemiRings] a -> b}).
Definition forget (T : ComSemiRings) : SemiRings := T.
Definition forget_mor : (a : SemiRings) -> (b : SemiRings) := f.
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
Lemma forget_ComSemiRings_to_SemiRingsE a b (f : {hom[ComSemiRings] a -> b}) :
  forget_ComSemiRings_to_SemiRings # f = f :> (_ -> _).
Proof. by []. Qed.
Definition forget_ComSemiRings_to_Sets :=
  forget_SemiRings_to_Sets \O forget_ComSemiRings_to_SemiRings.
Lemma forget_ComSemiRings_to_SetsE a b (f : {hom[ComSemiRings] a -> b}) :
  forget_ComSemiRings_to_Sets # f = f :> (_ -> _).
Proof. by []. Qed.

#[warning="-uniform-inheritance"]
Coercion rmorph_of_ComSemiRing a b (f : {hom[ComSemiRings] a -> b}) :
  {rmorphism a -> b} := forget_ComSemiRings_to_SemiRings # f.
Lemma rmorph_of_ComSemiRingE a b (f : {hom[ComSemiRings] a -> b}) :
  [the {rmorphism a -> b} of rmorph_of_ComSemiRing f] = f :> (_ -> _).
Proof. by []. Qed.

(* Q : Should there be a coercion
   {hom[ComSemiRings] a -> b} -> {hom[SemiRings] a -> b} *)


(* ComRings **********************************************************)

(** Full subcategory of Rings *)
HB.instance Definition _ :=
  isCategory.Build comRingType (fun T : comRingType => T)
    (@inhom Rings) (@idfun_inhom Rings) (@funcomp_inhom Rings).
Definition ComRings : category := comRingType.

Module ForgetComRings_to_Rings.

Section Morphism.
Variable (a b : ComRings) (f : {hom[ComRings] a -> b}).
Definition forget (T : ComRings) : Rings := T.
Definition forget_mor : (a : Rings) -> (b : Rings) := f.
HB.instance Definition _ := @isHom.Build Rings a b forget_mor (isHom_inhom f).
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build ComRings Rings forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition functor : {functor ComRings -> Rings} := forget.

End ForgetComRings_to_Rings.

Definition forget_ComRings_to_Rings := ForgetComRings_to_Rings.functor.
Lemma forget_ComRings_to_RingsE a b (f : {hom[ComRings] a -> b}) :
  forget_ComRings_to_Rings # f = f :> (_ -> _).
Proof. by []. Qed.
Definition forget_ComRings_to_Sets :=
  forget_Rings_to_Sets \O forget_ComRings_to_Rings.
Lemma forget_ComRings_to_SetsE a b (f : {hom[ComRings] a -> b}) :
  forget_ComRings_to_Sets # f = f :> (_ -> _).
Proof. by []. Qed.

#[warning="-uniform-inheritance"]
Coercion rmorph_of_ComRing a b (f : {hom[ComRings] a -> b}) :
  {rmorphism a -> b} := rmorph_of_Ring (forget_ComRings_to_Rings # f).
Lemma rmorph_of_ComRingE a b (f : {hom[ComRings] a -> b}) :
  [the {rmorphism a -> b} of @rmorph_of_ComRing a b f] = f :> (_ -> _).
Proof. by []. Qed.

Module ForgetComRings_to_ComSemiRings.

Section Morphism.
Variable (a b : ComRings) (f : {hom[ComRings] a -> b}).
Definition forget (T : ComRings) : ComSemiRings := T.
Definition forget_mor : (a : ComSemiRings) -> (b : ComSemiRings) := f.
HB.instance Definition _ :=
  @isHom.Build ComSemiRings a b forget_mor (isHom_inhom f).
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build ComRings ComSemiRings forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition functor : {functor ComRings -> ComSemiRings} := forget.

End ForgetComRings_to_ComSemiRings.
Definition forget_ComRings_to_ComSemiRings :=
  ForgetComRings_to_ComSemiRings.functor.
Lemma forget_ComRings_to_ComSemiRingsE a b (f : {hom[ComRings] a -> b}) :
  forget_ComRings_to_ComSemiRings # f = f :> (_ -> _).
Proof. by []. Qed.

Lemma unicity_ForgetComRings_to_Sets :
  forget_ComSemiRings_to_Sets \O forget_ComRings_to_ComSemiRings
    =#= forget_ComRings_to_Sets.
Proof. exact: (functor_ext (eq := fun=> _)). Qed.


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
Definition LModules R : category := lmodType R.
#[warning="-uniform-inheritance"]
Coercion linear_of_Lmod R a b (f : {hom[LModules R] a -> b}) : {linear a -> b} :=
  HB.pack (Hom.sort f) (GRing.isLinear.Build _ _ _ _ _ (isHom_inhom f)).
Lemma linear_of_LmodE R a b (f : {hom[LModules R] a -> b}) :
  [the {linear a -> b} of @linear_of_Lmod R a b f] = f :> (_ -> _).
Proof. by []. Qed.

Fact LModules_mor_semi_additive R a b (f : {hom[LModules R] a -> b}) :
  semi_additive f.
Proof.
rewrite -linear_of_LmodE; split => [| x y]; first by rewrite raddf0.
by rewrite raddfD.
Qed.

Module ForgetLModules_to_ZModules.

Section BaseRing.
Variable R : ringType.

Section Morphism.
Variables (a b : LModules R) (f : {hom[LModules R] a -> b}).
Definition forget (T : LModules R) : ZModules := T.
Definition forget_mor : (a : ZModules) -> (b : ZModules) := f.
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
Lemma forget_LModules_to_ZModulesE R a b (f : {hom[LModules R] a -> b}) :
  forget_LModules_to_ZModules R # f = f :> (_ -> _).
Proof. by []. Qed.
Definition forget_LModules_to_Sets R :=
  forget_ZModules_to_Sets \O forget_LModules_to_ZModules R.
Lemma forget_LModules_to_SetsE R a b (f : {hom[LModules R] a -> b}) :
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
Definition LAlgebras R : category := lalgType R.
#[warning="-uniform-inheritance"]
Coercion lrmorphism_of_LAlgebras R a b (f : {hom[LAlgebras R] a -> b}) :
  {lrmorphism a -> b} := HB.pack (Hom.sort f)
     (GRing.isLinear.Build _ _ _ _ _ (fst (isHom_inhom f)))
     (GRing.isMultiplicative.Build _ _ _ (snd (isHom_inhom f))).
Lemma lrmorphism_of_LAlgebrasE R a b (f : {hom[LAlgebras R] a -> b}) :
  [the {lrmorphism a -> b} of @lrmorphism_of_LAlgebras R a b f] = f :> (_ -> _).
Proof. by []. Qed.
Fact LAlgebras_mor_rmorphism R a b (f : {hom[LAlgebras R] a -> b}) :
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
Variables (a b : LAlgebras R) (f : {hom[LAlgebras R] a -> b}).
Definition forget (T : LAlgebras R) : LModules R := T.
Definition forget_mor : (a : LModules R) -> (b : LModules R) := f.
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
Lemma forget_LAlgebras_to_LModulesE R a b (f : {hom[LAlgebras R] a -> b}) :
  forget_LAlgebras_to_LModules R # f = f :> (_ -> _).
Proof. by []. Qed.
Definition forget_LAlgebras_to_Sets R :=
  (forget_LModules_to_Sets R) \O (forget_LAlgebras_to_LModules R).
Lemma forget_LAlgebras_to_SetsE R a b (f : {hom[LAlgebras R] a -> b}) :
  forget_LAlgebras_to_Sets R # f = f :> (_ -> _).
Proof. by []. Qed.

Module ForgetLAlgebras_to_Rings.

Section BaseRing.
Variable R : ringType.

Section Morphism.
Variables (a b : LAlgebras R) (f : {hom[LAlgebras R] a -> b}).
Definition forget (T : LAlgebras R) : Rings := T.
Definition forget_mor : (a : Rings) -> (b : Rings) := f.
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
Lemma forget_LAlgebras_to_RingsE R a b (f : {hom[LAlgebras R] a -> b}) :
  forget_LAlgebras_to_Rings R # f = f :> (_ -> _).
Proof. by []. Qed.

Lemma unicity_forget_LAlgebras_to_ZModules (R : Rings) :
  forget_Rings_to_ZModules \O forget_LAlgebras_to_Rings R
    =#= forget_LModules_to_ZModules R \O forget_LAlgebras_to_LModules R.
Proof. exact: (functor_ext (eq := fun=> _)). Qed.

Lemma unicity_forget_LAlgebras_to_Sets (R : Rings) :
  forget_Rings_to_Sets \O (forget_LAlgebras_to_Rings R) =#=
    (forget_LAlgebras_to_Sets R).
Proof. exact: (functor_ext (eq := fun=> _)). Qed.


(* Algebras ************************************************************)

(** Full subcategory of LAlgebras *)
HB.instance Definition _ R :=
  isCategory.Build (algType R) (fun T : algType R => T)
    (@inhom (LAlgebras R)) (@idfun_inhom (LAlgebras R))
    (@funcomp_inhom (LAlgebras R)).
Definition Algebras R : category := algType R.

Module ForgetAlgebras_to_LAlgebras.

Section BaseRing.
Variable R : ringType.

Section Morphism.
Variables (a b : Algebras R) (f : {hom[Algebras R] a -> b}).
Definition forget (T : Algebras R) : LAlgebras R := T.
Definition forget_mor : (a : LAlgebras R) -> (b : LAlgebras R) := f.
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
Lemma forget_Algebras_to_LAlgebrasE R a b (f : {hom[Algebras R] a -> b}) :
  forget_Algebras_to_LAlgebras R # f = f :> (_ -> _).
Proof. by []. Qed.
#[warning="-uniform-inheritance"]
Coercion lrmorphism_of_Algebras R a b (f : {hom[Algebras R] a -> b}) :
  {lrmorphism a -> b} := forget_Algebras_to_LAlgebras R # f.
Lemma lrmorphism_of_AlgebrasE R a b (f : {hom[Algebras R] a -> b}) :
  [the {lrmorphism a -> b} of lrmorphism_of_Algebras f] = f :> (_ -> _).
Proof. by []. Qed.
Definition forget_Algebras_to_Sets R :=
  forget_LAlgebras_to_Sets R \O forget_Algebras_to_LAlgebras R.
Lemma forget_Algebras_to_SetsE R a b (f : {hom[Algebras R] a -> b}) :
  forget_Algebras_to_Sets R # f = f :> (_ -> _).
Proof. by []. Qed.


(* ComAlgebras *****************************************************)

HB.instance Definition _ R :=
  isCategory.Build (comAlgType R) (fun T : comAlgType R => T)
    (@inhom (Algebras R)) (@idfun_inhom (Algebras R))
    (@funcomp_inhom (Algebras R)).
Definition ComAlgebras R : category := comAlgType R.

Module ForgetComAlgebras_to_Algebras.

Section BaseRing.
Variable R : ringType.

Section Morphism.
Variables (a b : ComAlgebras R) (f : {hom[ComAlgebras R] a -> b}).
Definition forget (T : ComAlgebras R) : Algebras R := T.
Definition forget_mor : (a : Algebras R) -> (b : Algebras R) := f.
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
Lemma forget_ComAlgebras_to_AlgebrasE R a b (f : {hom[ComAlgebras R] a -> b}) :
  forget_ComAlgebras_to_Algebras R # f = f :> (_ -> _).
Proof. by []. Qed.
#[warning="-uniform-inheritance"]
Coercion lrmorphism_of_ComAlgebras R a b (f : {hom[ComAlgebras R] a -> b}) :
  {lrmorphism a -> b} :=
  lrmorphism_of_Algebras (forget_ComAlgebras_to_Algebras R # f).
Lemma lrmorphism_of_ComAlgebrasE R a b (f : {hom[ComAlgebras R] a -> b}) :
  [the {lrmorphism a -> b} of lrmorphism_of_ComAlgebras f] = f :> (_ -> _).
Proof. by []. Qed.

Definition forget_ComAlgebras_to_Sets R :=
  forget_Algebras_to_Sets R \O forget_ComAlgebras_to_Algebras R.
Lemma forget_ComAlgebras_to_SetsE R a b (f : {hom[ComAlgebras R] a -> b}) :
  forget_ComAlgebras_to_Sets R # f = f :> (_ -> _).
Proof. by []. Qed.


(* Monoid ************************************************************)

Fact comp_is_monmorphism_fun (a b c : monoidType) (f : a -> b) (g : b -> c) :
  monmorphism f -> monmorphism g -> monmorphism (g \o f).
Proof. by move=> fM gM; split => [x y|]; rewrite /= fM gM. Qed.
HB.instance Definition _ :=
  isCategory.Build monoidType (fun T : monoidType => T)
    monmorphism idfun_is_monmorphism comp_is_monmorphism_fun.
Definition Monoids : category := monoidType.
#[warning="-uniform-inheritance"]
Coercion mmorphism_of_Monoids a b (f : {hom[Monoids] a -> b}) : {mmorphism a -> b} :=
  HB.pack (Hom.sort f) (isMonMorphism.Build _ _ _ (isHom_inhom f)).
Lemma mmorphism_of_MonoidsE a b (f : {hom[Monoids] a -> b}) :
  [the {mmorphism a -> b} of @mmorphism_of_Monoids a b f] = f :> (_ -> _).
Proof. by []. Qed.

Module ForgetMonoids_to_Sets.

Section Morphism.
Variable (a b : Monoids) (f : {hom[Monoids] a -> b}).
Definition forget (T : Monoids) : Sets := T.
HB.instance Definition _ :=
  @isHom.Build Sets a b (f : (a : Sets) -> b) I.
Definition forget_mor : {hom[Sets] a -> b} := f : a -> b.
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build Monoids Sets forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition functor : {functor Monoids -> Sets} := forget.

End ForgetMonoids_to_Sets.

Definition forget_Monoids_to_Sets := ForgetMonoids_to_Sets.functor.
Lemma forget_Monoids_to_SetsE a b (f : {hom[Monoids] a -> b}) :
  forget_Monoids_to_Sets # f = f :> (_ -> _).
Proof. by []. Qed.

Local Open Scope monoid_scope.


Definition freeMonoid (a : Sets) := seq a.
HB.instance Definition _ (a : Sets) := Choice.on (freeMonoid a).
HB.instance Definition _ (a : Sets) :=
  isMonoid.Build (freeMonoid a) (@catA a) (@cat0s a) (@cats0 a).

Notation "{ 'freemon' T }" := (freeMonoid T)
                                (at level 0, format "{ 'freemon'  T }").
Notation "[fmon x ]" := ([:: x] : {freemon _})
                        (at level 0, format "[fmon  x ]").

Lemma freeMonoidE (a : Sets) (x : freeMonoid a) : x = \prod_(i <- x) [fmon i].
Proof.
by elim: x => [|s s0 {1}->]; rewrite ?big_nil // big_cons [RHS]cat1s.
Qed.

Section FreeMonoid.

Variables (a b c : Sets) (f : {hom[Sets] a -> b}).

Definition hom_freeMonoid (m : {freemon a}) : {freemon b} :=
  [seq f i | i <- m].

Lemma hom_freeMonoid1 x : hom_freeMonoid [fmon x] = [fmon f x].
Proof. by []. Qed.
Lemma hom_freeMonoidE (s : {freemon a}) :
  hom_freeMonoid s = \prod_(i <- s) [fmon f i].
Proof. by elim: s => [//=| s0 s /= ->]; rewrite ?big_nil ?big_cons. Qed.
Lemma hom_freeMonoid_monmorphism : monmorphism hom_freeMonoid.
Proof. by rewrite /hom_freeMonoid; split => [/= x y| //]; rewrite map_cat. Qed.

End FreeMonoid.

HB.instance Definition _ (a b : Sets) (f : {hom[Sets] a -> b}) :=
  @isHom.Build Monoids {freemon a} {freemon b}
    (hom_freeMonoid f : [the Monoids of {freemon a}] -> {freemon b})
    (hom_freeMonoid_monmorphism f).
Definition freeMonoid_mor (a b : Sets) (f : {hom[Sets] a -> b})
  : {hom[Monoids] {freemon a} -> {freemon b}} := hom_freeMonoid f.

Fact freeMonoid_ext : FunctorLaws.ext freeMonoid_mor.
Proof. by move=> /= a b f g eq y; rewrite /hom_freeMonoid; exact: eq_map. Qed.
Fact freeMonoid_id : FunctorLaws.id freeMonoid_mor.
Proof. by move=> /= a x /=; rewrite /hom_freeMonoid /= map_id. Qed.
Fact freeMonoid_comp  : FunctorLaws.comp freeMonoid_mor.
Proof. by move=> /= a b c f g x; rewrite /hom_freeMonoid /= map_comp. Qed.
Definition functor_freeMon T : Monoids := {freemon T}.
HB.instance Definition _ :=
  @isFunctor.Build Sets Monoids
    functor_freeMon freeMonoid_mor freeMonoid_ext freeMonoid_id freeMonoid_comp.


Module FreeMonAdjoint.
Section Adjoint.

Definition eta : FId ~~> forget_Monoids_to_Sets \o functor_freeMon :=
  fun a => [hom fun x : a => [fmon x]].
Fact eta_natural : naturality FId (forget_Monoids_to_Sets \o functor_freeMon) eta.
Proof. by move=> /= a b h x /=; rewrite FIdf. Qed.
HB.instance Definition _ :=
  @isNatural.Build Sets Sets FId
    (forget_Monoids_to_Sets \o functor_freeMon) eta eta_natural.

Definition eps_fun T (m : (functor_freeMon \o forget_Monoids_to_Sets) T) : T :=
      \prod_(i <- m : {freemon _}) i.
Fact eps_fun_monmorphism T : monmorphism (@eps_fun T).
Proof. by rewrite /eps_fun; split => [s t |]; rewrite ?big_nil ?big_cat. Qed.
HB.instance Definition _ T :=
  isHom.Build Monoids ((functor_freeMon \o forget_Monoids_to_Sets) T) (FId T)
    (@eps_fun T) (@eps_fun_monmorphism T).
Definition eps : functor_freeMon \o forget_Monoids_to_Sets ~~> FId := eps_fun.
Fact eps_natural : naturality (functor_freeMon \o forget_Monoids_to_Sets) FId eps.
Proof.
move=> /= a b h x /=.
rewrite -!mmorphism_of_MonoidsE [LHS]mmorph_prod /=.
by rewrite FIdf /eps_fun /= /hom_freeMonoid big_map.
Qed.
HB.instance Definition _ :=
  @isNatural.Build Monoids Monoids
    (functor_freeMon \o forget_Monoids_to_Sets) FId eps eps_natural.

Fact triL : TriangularLaws.left eta eps.
Proof.
move=> /= a x.
rewrite -!mmorphism_of_MonoidsE /= /eps_fun /hom_freeMonoid.
by rewrite big_map [RHS]freeMonoidE.
Qed.
Fact triR : TriangularLaws.right eta eps.
Proof. by move=> /= M m; rewrite /= /eps_fun big_cons big_nil mulm1. Qed.

Let F : {functor Sets -> Monoids} := functor_freeMon.
Let G : {functor Monoids -> Sets} := forget_Monoids_to_Sets.

Definition adjoint : F -| G := AdjointFunctors.mk triL triR.

End Adjoint.
End FreeMonAdjoint.
Definition adjoint_freeMonoid_forget_to_Sets := FreeMonAdjoint.adjoint.

Section UniversalProperty.

Variables (A : Sets) (M : Monoids) (f : {hom[Sets] A -> M}).

Local Notation eps := (AdjointFunctors.eps adjoint_freeMonoid_forget_to_Sets).
Local Notation eta := (AdjointFunctors.eta adjoint_freeMonoid_forget_to_Sets).
Local Notation triR := (AdjointFunctors.triR adjoint_freeMonoid_forget_to_Sets).

Definition univmap_freemon : {hom[Monoids] {freemon A} -> M} :=
  eps M \o functor_freeMon # f : {hom _ -> M}.

Lemma univmap_freemonP a : univmap_freemon [fmon a] = f a.
Proof. by rewrite /univmap_freemon -[[fmon a]]/(eta A a) /=; exact: triR. Qed.

Lemma univmap_freemon_uniq (g : {hom[Monoids] {freemon A} -> M}) :
  (forall a : A, g [fmon a] = f a) -> g =1 univmap_freemon.
Proof.
move=> eq m.
rewrite (freeMonoidE m) -!mmorphism_of_MonoidsE !mmorph_prod; apply eq_bigr => i _.
by rewrite [LHS]eq [RHS]univmap_freemonP.
Qed.

End UniversalProperty.


(** Commutative Monoids *********************************************)
(* Full subcategory of Monoids *)
HB.instance Definition _ :=
  isCategory.Build comMonoidType (fun T : comMonoidType => T)
    (@inhom Monoids) (@idfun_inhom Monoids) (@funcomp_inhom Monoids).
Definition ComMonoids : category := comMonoidType.
#[warning="-uniform-inheritance"]
Coercion mmorphism_of_ComMonoids a b (f : {hom[ComMonoids] a -> b}) :
  {mmorphism a -> b} :=
  HB.pack (Hom.sort f) (isMonMorphism.Build _ _ _ (isHom_inhom f)).
Lemma mmorphism_of_ComMonoidsE a b (f : {hom[ComMonoids] a -> b}) :
  [the {mmorphism a -> b} of @mmorphism_of_ComMonoids a b f] = f :> (_ -> _).
Proof. by []. Qed.

Module ForgetComMonoids_to_Monoids.

Section Morphism.
Variable (a b : ComMonoids) (f : {hom[ComMonoids] a -> b}).
Definition forget (T : ComMonoids) : Monoids := T.
Definition forget_mor : (a : Monoids) -> (b : Monoids) := f.
HB.instance Definition _ :=  @isHom.Build Monoids a b forget_mor (isHom_inhom f).
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build ComMonoids Monoids forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition functor : {functor ComMonoids -> Monoids} := forget.

End ForgetComMonoids_to_Monoids.

Definition forget_ComMonoids_to_Monoids := ForgetComMonoids_to_Monoids.functor.
Lemma forget_ComMonoids_to_MonoidsE a b (f : {hom[ComMonoids] a -> b}) :
  forget_ComMonoids_to_Monoids # f = f :> (_ -> _).
Proof. by []. Qed.
Definition forget_ComMonoids_to_Sets :=
  forget_Monoids_to_Sets \O forget_ComMonoids_to_Monoids.
Lemma forget_ComMonoids_to_SetsE a b (f : {hom[ComMonoids] a -> b}) :
  forget_ComMonoids_to_Sets # f = f :> (_ -> _).
Proof. by []. Qed.


(** Equivalence ComMonoid NModule ***********************************)
Definition NMod_of_ComMonoid_type (M : ComMonoids) : Type := M.
HB.lock Definition nmod_of_commonoid (M : ComMonoids) (x : M)
  : (NMod_of_ComMonoid_type M) := x.
Canonical nmod_of_commonoid_unlock := Unlockable nmod_of_commonoid.unlock.
HB.lock Definition nmod_of_commonoid_inv M (x : NMod_of_ComMonoid_type M) : M := x.
Canonical nmod_of_commonoid_inv_unlock := Unlockable nmod_of_commonoid_inv.unlock.

Lemma nmod_of_commonoidK M :
  cancel (@nmod_of_commonoid M) (@nmod_of_commonoid_inv M).
Proof. by rewrite !unlock. Qed.
Lemma nmod_of_commonoid_invK M :
  cancel (@nmod_of_commonoid_inv M) (@nmod_of_commonoid M).
Proof. by rewrite !unlock. Qed.

Section Defs.

Variable M : ComMonoids.
Local Notation nmodM := (NMod_of_ComMonoid_type M).
HB.instance Definition _ := Choice.on nmodM.

Let zeronm := @nmod_of_commonoid M 1%M.
Let addnm (x y : nmodM) :=
  nmod_of_commonoid (nmod_of_commonoid_inv x * nmod_of_commonoid_inv y).
Fact addnmA : associative addnm.
Proof. by move=> x y z; rewrite /addnm !unlock mulmA. Qed.
Fact addnmC : commutative addnm.
Proof. by move=> x y; rewrite /addnm !unlock mulmC. Qed.
Fact add0nm : left_id zeronm addnm.
Proof. by move=> x; rewrite /addnm /zeronm !unlock mul1m. Qed.
HB.instance Definition _ := GRing.isNmodule.Build nmodM addnmA addnmC add0nm.
Definition NMod_of_ComMonoid : NModules := nmodM.

Lemma nmod_of_commonoid1 : 0%R = nmod_of_commonoid 1 :> nmodM.
Proof. by []. Qed.
Lemma nmod_of_commonoidM :
  {morph @nmod_of_commonoid M : x y / (x * y)%M >-> (x + y)%R}.
Proof. by move=> x y; rewrite /GRing.add /= /addnm !nmod_of_commonoidK. Qed.

End Defs.

Section Functor_on_Hom.

Variables (M N : ComMonoids) (f : {hom[ComMonoids] M -> N}).
Let nmod_of_commonoid_mor : (NMod_of_ComMonoid M) -> (NMod_of_ComMonoid N) :=
  (@nmod_of_commonoid N) \o f \o (@nmod_of_commonoid_inv M).

Fact nmod_of_commonoid_mor_is_additive : semi_additive nmod_of_commonoid_mor.
Proof.
rewrite /nmod_of_commonoid_mor; split => /= [|x y /=].
  rewrite nmod_of_commonoid1 nmod_of_commonoidK.
  by rewrite -(mmorphism_of_ComMonoidsE f) mmorph1.
rewrite -nmod_of_commonoidM -(mmorphism_of_ComMonoidsE f) -mmorphM; congr (_ (f _)).
apply (can_inj (@nmod_of_commonoidK _)).
by rewrite nmod_of_commonoidM !nmod_of_commonoid_invK.
Qed.
HB.instance Definition _ :=
  isHom.Build NModules (NMod_of_ComMonoid M) (NMod_of_ComMonoid N)
    nmod_of_commonoid_mor nmod_of_commonoid_mor_is_additive.
Definition NMod_of_ComMonoid_mor
  : {hom[NModules] NMod_of_ComMonoid M -> NMod_of_ComMonoid N}
  := nmod_of_commonoid_mor.

End Functor_on_Hom.

Fact NMod_of_ComMonoid_ext : FunctorLaws.ext NMod_of_ComMonoid_mor.
Proof. by move=> /= a b f g eq y; rewrite /= eq. Qed.
Fact NMod_of_ComMonoid_id : FunctorLaws.id NMod_of_ComMonoid_mor.
Proof. by move=> /= a x /=; rewrite /= nmod_of_commonoid_invK. Qed.
Fact NMod_of_ComMonoid_comp  : FunctorLaws.comp NMod_of_ComMonoid_mor.
Proof. by move=> /= a b c f g x /=; rewrite nmod_of_commonoidK. Qed.
HB.instance Definition _ :=
  @isFunctor.Build ComMonoids NModules NMod_of_ComMonoid NMod_of_ComMonoid_mor
    NMod_of_ComMonoid_ext NMod_of_ComMonoid_id NMod_of_ComMonoid_comp.


Definition ComMonoid_of_NMod_type (M : NModules) : Type := M.
HB.lock Definition commonoid_of_nmod (M : NModules) (x : M)
  : (ComMonoid_of_NMod_type M) := x.
Canonical commonoid_of_nmod_unlock := Unlockable commonoid_of_nmod.unlock.
HB.lock Definition commonoid_of_nmod_inv M (x : ComMonoid_of_NMod_type M) : M := x.
Canonical commonoid_of_nmod_inv_unlock := Unlockable commonoid_of_nmod_inv.unlock.

Lemma commonoid_of_nmodK M :
  cancel (@commonoid_of_nmod M) (@commonoid_of_nmod_inv M).
Proof. by rewrite !unlock. Qed.
Lemma commonoid_of_nmod_invK M :
  cancel (@commonoid_of_nmod_inv M) (@commonoid_of_nmod M).
Proof. by rewrite !unlock. Qed.

Section Defs.

Variable M : NModules.
Local Notation cmonM := (ComMonoid_of_NMod_type M).
HB.instance Definition _ := Choice.on cmonM.

Let onecm := @commonoid_of_nmod M 0%R.
Let mulcm (x y : cmonM) :=
  commonoid_of_nmod (commonoid_of_nmod_inv x + commonoid_of_nmod_inv y).
Fact mulcmA : associative mulcm.
Proof. by move=> x y z; rewrite /mulcm !unlock addrA. Qed.
Fact mulcmC : commutative mulcm.
Proof. by move=> x y; rewrite /mulcm !unlock addrC. Qed.
Fact mul1cm : left_id onecm mulcm.
Proof. by move=> x; rewrite /mulcm /onecm !unlock add0r. Qed.
HB.instance Definition _ := isComMonoid.Build cmonM mulcmA mul1cm mulcmC.
Definition ComMonoid_of_NMod : ComMonoids := cmonM.

Lemma commonoid_of_nmod0 : 1%M = commonoid_of_nmod 0%R :> cmonM.
Proof. by []. Qed.
Lemma commonoid_of_nmodD :
  {morph @commonoid_of_nmod M : x y / (x + y)%R >-> (x * y)%M}.
Proof. by move=> x y; rewrite /mul /= /mulcm !commonoid_of_nmodK. Qed.

End Defs.

Section Functor_on_Hom.

Variables (M N : NModules) (f : {hom[NModules] M -> N}).
Let commonoid_of_nmod_mor : (ComMonoid_of_NMod M) -> (ComMonoid_of_NMod N) :=
  (@commonoid_of_nmod N) \o f \o (@commonoid_of_nmod_inv M).

Fact commonoid_of_nmod_mor_monmorphism : monmorphism commonoid_of_nmod_mor.
Proof.
rewrite /commonoid_of_nmod_mor; split => /= [x y /=|].
  rewrite -commonoid_of_nmodD -(additive_of_NmodE f) -raddfD; congr (_ (f _)).
  apply (can_inj (@commonoid_of_nmodK _)).
  by rewrite commonoid_of_nmodD !commonoid_of_nmod_invK.
rewrite commonoid_of_nmod0 commonoid_of_nmodK.
by rewrite -(additive_of_NmodE f) raddf0.
Qed.
HB.instance Definition _ :=
  isHom.Build ComMonoids (ComMonoid_of_NMod M) (ComMonoid_of_NMod N)
    commonoid_of_nmod_mor commonoid_of_nmod_mor_monmorphism.
Definition ComMonoid_of_NMod_mor
  : {hom[ComMonoids] ComMonoid_of_NMod M -> ComMonoid_of_NMod N}
  := commonoid_of_nmod_mor.

End Functor_on_Hom.

Fact ComMonoid_of_NMod_ext : FunctorLaws.ext ComMonoid_of_NMod_mor.
Proof. by move=> /= a b f g eq y; rewrite /= eq. Qed.
Fact ComMonoid_of_NMod_id : FunctorLaws.id ComMonoid_of_NMod_mor.
Proof. by move=> /= a x /=; rewrite /= commonoid_of_nmod_invK. Qed.
Fact ComMonoid_of_NMod_comp  : FunctorLaws.comp ComMonoid_of_NMod_mor.
Proof. by move=> /= a b c f g x /=; rewrite commonoid_of_nmodK. Qed.
HB.instance Definition _ :=
  @isFunctor.Build NModules ComMonoids ComMonoid_of_NMod ComMonoid_of_NMod_mor
    ComMonoid_of_NMod_ext ComMonoid_of_NMod_id ComMonoid_of_NMod_comp.

(** Doesn't seems to be provable, equality is too strong.
Lemma CM_id : ComMonoid_of_NMod \O NMod_of_ComMonoid =#= FId.
 *)

Local Notation CM := (ComMonoid_of_NMod \O NMod_of_ComMonoid).
Local Notation MC := (NMod_of_ComMonoid \O ComMonoid_of_NMod).

(** Build natural isom *)
Section IsoCM.

Variable M : ComMonoids.
Definition isoCM_map : CM M -> FId M :=
  (@nmod_of_commonoid_inv _) \o (@commonoid_of_nmod_inv (NMod_of_ComMonoid M)).
Definition isoCM_inv : FId M -> CM M :=
  (@commonoid_of_nmod _) \o (@nmod_of_commonoid M).

Fact isoCM_mapK : cancel isoCM_map isoCM_inv.
Proof.
rewrite /isoCM_map {}/isoCM_inv => x /=.
by rewrite !(nmod_of_commonoid_invK, commonoid_of_nmod_invK).
Qed.
Fact isoCM_invK : cancel isoCM_inv isoCM_map.
Proof.
rewrite /isoCM_map {}/isoCM_inv => x /=.
by rewrite !(nmod_of_commonoidK, commonoid_of_nmodK).
Qed.
Fact isoCM_monmorphism : monmorphism isoCM_map.
Proof.
split => [x y |].
  rewrite -{1}(isoCM_mapK x) -{1}(isoCM_mapK y).
  move: (isoCM_map x) (isoCM_map y) => {}x {}y.
  rewrite /isoCM_map /= {1}/mul /= {1}/GRing.add /=.
  rewrite nmod_of_commonoidM commonoid_of_nmodD.
  by rewrite !(nmod_of_commonoidK, commonoid_of_nmodK).
rewrite commonoid_of_nmod0 nmod_of_commonoid1 /isoCM_map /=.
by rewrite !(nmod_of_commonoidK, commonoid_of_nmodK).
Qed.
HB.instance Definition _ :=
  isHom.Build ComMonoids (CM M) M isoCM_map isoCM_monmorphism.

Fact isoCM_inv_monmorphism : monmorphism isoCM_inv.
Proof.
rewrite /isoCM_inv; split => [x y |] /=.
  by rewrite nmod_of_commonoidM commonoid_of_nmodD.
by rewrite commonoid_of_nmod0 nmod_of_commonoid1.
Qed.
HB.instance Definition _ :=
  isIsom.Build ComMonoids (CM M) M isoCM_map
    isoCM_inv_monmorphism isoCM_mapK isoCM_invK.

End IsoCM.

Section IsoCMTrans.

Let isoCM_hom : CM ~~> FId := isoCM_map.
Fact natural_isoCM : naturality CM FId isoCM_hom.
Proof.
move=> a b h x.
rewrite -(isoCM_mapK x); move: (isoCM_map x) => /= {}x.
rewrite /isoCM_inv /isoCM_map /=.
by rewrite !(nmod_of_commonoidK, commonoid_of_nmodK) FIdf.
Qed.
HB.instance Definition _ :=
  isNatural.Build ComMonoids ComMonoids CM FId isoCM_hom natural_isoCM.
Definition isoCM : CM ~> FId := isoCM_hom.

End IsoCMTrans.


Section IsoMC.

Variable M : NModules.
Definition isoMC_map : MC M -> FId M :=
  (@commonoid_of_nmod_inv _) \o (@nmod_of_commonoid_inv (ComMonoid_of_NMod M)).
Definition isoMC_inv : FId M -> MC M :=
  (@nmod_of_commonoid _) \o (@commonoid_of_nmod M).

Fact isoMC_mapK : cancel isoMC_map isoMC_inv.
Proof.
rewrite /isoMC_map {}/isoMC_inv => x /=.
by rewrite !(nmod_of_commonoid_invK, commonoid_of_nmod_invK).
Qed.
Fact isoMC_invK : cancel isoMC_inv isoMC_map.
Proof.
rewrite /isoMC_map {}/isoMC_inv => x /=.
by rewrite !(nmod_of_commonoidK, commonoid_of_nmodK).
Qed.
Fact isoMC_additive : semi_additive isoMC_map.
Proof.
split => [| x y].
  rewrite nmod_of_commonoid1 commonoid_of_nmod0 /isoMC_map /=.
  by rewrite !(nmod_of_commonoidK, commonoid_of_nmodK).
rewrite -{1}(isoMC_mapK x) -{1}(isoMC_mapK y).
move: (isoMC_map x) (isoMC_map y) => {}x {}y.
rewrite /isoMC_map /= {1}/GRing.add /= {1}/mul /=.
rewrite commonoid_of_nmodD nmod_of_commonoidM.
by rewrite !(nmod_of_commonoidK, commonoid_of_nmodK).
Qed.
HB.instance Definition _ :=
  isHom.Build NModules (MC M) M isoMC_map isoMC_additive.

Fact isoMC_inv_additive : semi_additive isoMC_inv.
Proof.
rewrite /isoMC_inv; split => [| x y] /=.
  by rewrite nmod_of_commonoid1 commonoid_of_nmod0.
by rewrite commonoid_of_nmodD nmod_of_commonoidM.
Qed.
HB.instance Definition _ :=
  isIsom.Build NModules (MC M) M isoMC_map
    isoMC_inv_additive isoMC_mapK isoMC_invK.

End IsoMC.

Section IsoMCTrans.

Let isoMC_hom : MC ~~> FId := isoMC_map.
Fact natural_isoMC : naturality MC FId isoMC_hom.
Proof.
move=> a b h x.
rewrite -(isoMC_mapK x); move: (isoMC_map x) => /= {}x.
rewrite /isoMC_inv /isoMC_map /=.
by rewrite !(nmod_of_commonoidK, commonoid_of_nmodK) FIdf.
Qed.
HB.instance Definition _ :=
  isNatural.Build NModules NModules MC FId isoMC_hom natural_isoMC.
Definition isoMC : MC ~> FId := isoMC_hom.

End IsoMCTrans.

Definition equivalence_ComMonoids_NModules :
  equivalence_category NMod_of_ComMonoid ComMonoid_of_NMod :=
  EquivalenceCategory natural_isoMC natural_isoCM.


(* TODO: Those are full subcategories, devise some infrastructure to
   - handle trivial forgetful functors
   - morphisms coercions. *)
HB.instance Definition _ :=
  isCategory.Build unitRingType (fun T : unitRingType => T)
    semiring_morph idfun_is_semiring_morph comp_is_semiring_morph.
Definition UnitRings : category := unitRingType.

HB.instance Definition _ :=
  isCategory.Build comUnitRingType (fun T : comUnitRingType => T)
    semiring_morph idfun_is_semiring_morph comp_is_semiring_morph.
Definition ComUnitRings : category := comUnitRingType.

HB.instance Definition _ R :=
  isCategory.Build (unitAlgType R) (fun T : unitAlgType R => T)
    (fun a b (f : a -> b) => lalg_morph f)
    (@idfun_is_lalg_morph R) (@comp_is_lalg_morph R).
Definition UnitAlgebras R : category := unitAlgType R.

HB.instance Definition _ R :=
  isCategory.Build (comUnitAlgType R) (fun T : comUnitAlgType R => T)
    (fun a b (f : a -> b) => lalg_morph f)
    (@idfun_is_lalg_morph R) (@comp_is_lalg_morph R).
Definition ComUnitAlgebras R : category := comUnitAlgType R.


Local Open Scope ring_scope.
Local Open Scope mset_scope.

(** Adjonction between forget : NModules -> Sets and free N-Modules *)
Section Set_to_FreeNmodule.

Variable (a b : Sets) (f : {hom[Sets] a -> b}).

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

Definition FreeNmod (T : Sets) : NModules := {mset T}.
(* TODO Cyril : The following declaration was

Definition FreeNmod (T : choiceType) : nmodType := {mset T}.
  HB.instance Definition _ (a b : Sets) (f : a -> b) :=
   @isHom.Build NModules {mset a} {mset b}
   (hom_mset f : [the nmodType of {mset a}] -> [the nmodType of {mset b}])
   (hom_mset_additive f).

the [the nmodType of ... ] was needed... Why ???
*)
HB.instance Definition _ (a b : Sets) (f : {hom[Sets] a -> b}) :=
  @isHom.Build NModules (FreeNmod a) (FreeNmod b)
    (hom_mset f : FreeNmod a -> FreeNmod b)
    (hom_mset_additive f).
Definition FreeNmod_mor (a b : Sets) (f : {hom[Sets] a -> b})
  : {hom[NModules] FreeNmod a -> FreeNmod b} := hom_mset f.

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
Definition functor_FreeNmod : {functor Sets -> NModules} := FreeNmod.


Module FreeNModAdjoint.
Section Adjoint.

Implicit Types (a : Sets) (T : NModules).

Definition eta_fun a (x : a) := [mset x].
Definition eta : FId ~~> forget_NModules_to_Sets \o FreeNmod := eta_fun.
Fact eta_natural :
  naturality FId (forget_NModules_to_Sets \o FreeNmod) eta.
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
Fact eps_natural :
  naturality (FreeNmod \o forget_NModules_to_Sets) FId eps.
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

Definition adjoint : FreeNmod -| forget_NModules_to_Sets :=
  AdjointFunctors.mk triL triR.

End Adjoint.
End FreeNModAdjoint.
Definition adjoint_freeNModule_forget_to_Sets := FreeNModAdjoint.adjoint.


Section UniversalProperty.

Variables (A : Sets) (M : NModules) (f : {hom[Sets] A -> M}).

Local Notation eps := (AdjointFunctors.eps adjoint_freeNModule_forget_to_Sets).
Local Notation eta := (AdjointFunctors.eta adjoint_freeNModule_forget_to_Sets).
Local Notation triR := (AdjointFunctors.triR adjoint_freeNModule_forget_to_Sets).

Definition univmap : {hom[NModules] {mset A} -> M} := eps M \o FreeNmod # f.

Lemma univmap_FreeNmodP a : univmap [mset a] = f a.
Proof.
by rewrite -[[mset a]]/(eta A a) /= hom_mset1; exact: triR.
Qed.

Lemma univmap_FreeNmod_uniq (g : {hom[NModules] {mset A} -> M}) :
  (forall a : A, g [mset a] = f a) -> g =1 univmap.
Proof.
move=> eq m; rewrite -(msetE m) -!additive_of_NmodE !raddf_sum; apply eq_bigr => x _.
by rewrite [LHS]eq [RHS]univmap_FreeNmodP.
Qed.

End UniversalProperty.

Local Close Scope monoid_scope.


Local Open Scope ring_scope.

(** Adjonction free L-Modules -| forget L-Modules to Sets and *)
Section Set_to_FreeLmodule.

Variable R : ringType.

Lemma freeLmodE (a : Sets) (T : LModules R)
  (f g : {hom[LModules R] {freemod R[a]} -> T}) :
  (forall x : a, f [fm / x |-> 1] = g [fm / x |-> 1]) -> f =1 g.
Proof.
move=> eq x; rewrite -(linear_of_LmodE f) -(linear_of_LmodE g).
exact: linear_fmE.
Qed.

Variable (a b : Sets) (f : {hom[Sets] a -> b}).
Definition hom_flm (m : {freemod R[a]}) : {freemod R[b]} :=
  \sum_(i <- finsupp m) [fm / f i |-> m i].

Lemma hom_flm1 (x : a) : hom_flm [fm / x |-> 1] = [fm / f x |-> 1].
Proof. by rewrite /hom_flm finsupp_fm1 /= big_seq_fset1 fm1E eqxx. Qed.
Fact hom_flm_linear : linear hom_flm.
Proof.
rewrite /hom_flm => c /= m n; rewrite scaler_sumr /=.
rewrite -!(finsupp_widen _ (S := finsupp m `|` finsupp n)%fset) /=.
- rewrite -big_split /=; apply: eq_bigr => x _.
  apply/fsfunP => y; rewrite !addfmE !scalefmE !fm1E.
  by case: eqP => // _; rewrite addr0 mulr0.
- by move=> i /[!memNfinsupp] /eqP ->; rewrite fm0eq0.
- by move=> x; rewrite inE orbC => ->.
- by move=> i /[!memNfinsupp] /eqP ->; rewrite fm0eq0 scaler0.
- by move=> x; rewrite inE => ->.
- by move=> i /[!memNfinsupp] /eqP ->; rewrite fm0eq0.
- move=> x; rewrite inE; apply contraLR.
  rewrite negb_or !memNfinsupp addfmE scalefmE => /andP [/eqP -> /eqP ->].
  by rewrite mulr0 addr0.
Qed.
HB.instance Definition _ :=
  GRing.isLinear.Build R {freemod R[a]} {freemod R[b]} _ hom_flm hom_flm_linear.

Lemma hom_flmc (x : a) (c : R) : hom_flm [fm / x |-> c] = [fm / f x |-> c].
Proof. by rewrite -fm1ZE linearZ /= hom_flm1 fm1ZE. Qed.

End Set_to_FreeLmodule.

Section Functor.
Variable (R : ringType).

HB.instance Definition _ (a b : Sets) (f : {hom[Sets] a -> b}) :=
  @isHom.Build (LModules R) {freemod R[a]} {freemod R[b]}
    (hom_flm f : (_ : LModules R) -> _) (hom_flm_linear f).
Definition freeLmod_mor (a b : Sets) (f : {hom[Sets] a -> b})
  : {hom[LModules R] {freemod R[a]} -> {freemod R[b]}} := hom_flm f.

Fact freeLmod_ext : FunctorLaws.ext freeLmod_mor.
Proof.
move=> /= a b f g eq y; rewrite /hom_mset /hom_flm.
by apply eq_bigr => x _; rewrite eq.
Qed.
Fact freeLmod_id : FunctorLaws.id freeLmod_mor.
Proof.
move=> /= a x /=; rewrite /hom_mset /= -[RHS]fmE.
by rewrite /hom_flm; apply: eq_bigr => i _.
Qed.
Fact freeLmod_comp  : FunctorLaws.comp freeLmod_mor.
Proof.
move=> /= a b c f g.
rewrite -!linear_of_LmodE; apply: linear_fmE => /= x.
by rewrite /hom_flm /= !(finsupp_fm1, big_seq_fset1, fm1E, eqxx).
Qed.

Definition functor_freeLmod a : LModules R := {freemod R[a]}.
HB.instance Definition _ :=
  @isFunctor.Build Sets (LModules R) functor_freeLmod
     freeLmod_mor freeLmod_ext freeLmod_id freeLmod_comp.

End Functor.


Module FreeLModAdjoint.
Section Adjoint.

Variable R : ringType.
Implicit Types (a : Sets) (T : LModules R).
Local Notation fmf := (@functor_freeLmod R).
Local Notation forgetf := (forget_LModules_to_Sets R).
Definition eta_fun a (x : a) : {freemod R[a]} := [fm / x |-> 1].
Definition eta : FId ~~> forgetf \o fmf := eta_fun.
Fact eta_natural : naturality FId (forgetf \o fmf) eta.
Proof. by move=> /= a b h x /=; rewrite /eta_fun FIdf hom_flm1. Qed.
HB.instance Definition _ :=
  @isNatural.Build Sets Sets FId (forgetf \o fmf) eta eta_natural.

Definition eps_fun T (m : (fmf \o forgetf) T) : T :=
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
Definition eps : fmf \o forgetf ~~> FId := eps_fun.
Fact eps_natural : naturality (fmf \o forgetf) FId eps.
Proof.
move=> /= a b h.
rewrite -!linear_of_LmodE; apply: linear_fmE => /= x.
rewrite FIdf /eps_fun /= hom_flm1.
by rewrite !finsupp_fm1 !big_seq_fset1 !fm1E !eqxx !scale1r.
Qed.
HB.instance Definition _ :=
  @isNatural.Build (LModules R) (LModules R)
    (fmf \o forgetf) FId eps eps_natural.

Fact triL : TriangularLaws.left eta eps.
Proof.
move=> /= a.
rewrite -!linear_of_LmodE; apply: linear_fmE => /= x.
rewrite /eta_fun /= /eps_fun /= hom_flm1.
by rewrite !finsupp_fm1 !big_seq_fset1 !fm1E !eqxx !scale1r.
Qed.
Fact triR : TriangularLaws.right eta eps.
Proof.
move=> /= M m; rewrite /eta_fun /= /eps_fun.
by rewrite finsupp_fm1 big_seq_fset1 fm1E eqxx scale1r.
Qed.

Let F : {functor Sets -> LModules R} := functor_freeLmod R.
Let G : {functor LModules R -> Sets} := forget_LModules_to_Sets R.

Definition adjoint : F -| G := AdjointFunctors.mk triL triR.

End Adjoint.
End FreeLModAdjoint.
Definition adjoint_freeLMod_forget_to_Sets := FreeLModAdjoint.adjoint.

Section UniversalProperty.

Variable (R : Rings).

Variables (A : Sets) (M : LModules R) (f : {hom[Sets] A -> M}).

Local Notation eps := (AdjointFunctors.eps (adjoint_freeLMod_forget_to_Sets R)).
Local Notation eta := (AdjointFunctors.eta (adjoint_freeLMod_forget_to_Sets R)).
Local Notation triR := (AdjointFunctors.triR (adjoint_freeLMod_forget_to_Sets R)).

Definition univmap_freelmod : {hom[LModules R] {freemod R[A]} -> M} :=
  eps M \o (functor_freeLmod R) # f.

Lemma univmap_freelmodP a : univmap_freelmod [fm / a |-> 1] = f a.
Proof. by rewrite /= !hom_flm1; exact: triR. Qed.

Lemma univmap_freelmod_uniq (g : {hom[LModules R] {freemod R[A]} -> M}) :
  (forall a : A, g [fm / a |-> 1] = f a) -> g =1 univmap_freelmod.
Proof.
by move=> eq m; apply: freeLmodE => x; rewrite eq univmap_freelmodP.
Qed.

End UniversalProperty.


(** HB incompatible Forgetful functor SemiRings -> Monoids *)
Module ForgetSemiRings_to_Monoids.

HB.instance Definition _ (R S : semiRingType) (f : {rmorphism R -> S}) :=
  @isHom.Build Monoids (multMon R : Monoids) (multMon S : Monoids)
    (multMon_mor f : (_ : Monoids) -> _) (multMon_mor_monmorphism f).
Definition functor_multMon_fun (R : SemiRings) : Monoids := multMon R.
Fact multMon_ext : FunctorLaws.ext multMon_mor.
Proof. by move=> /= a b f g eq y; rewrite /multMon_mor /= eq. Qed.
Fact multMon_id : FunctorLaws.id multMon_mor.
Proof. by move=> /= a x /=; rewrite /multMon_mor /=; exact: val_inj. Qed.
Fact multMon_comp  : FunctorLaws.comp multMon_mor.
Proof. by move=> /= a b c f g x; rewrite /multMon_mor /=. Qed.
HB.instance Definition _ :=
  @isFunctor.Build SemiRings Monoids
    functor_multMon_fun multMon_mor multMon_ext multMon_id multMon_comp.
Definition functor : {functor SemiRings -> Monoids} := functor_multMon_fun.

Definition multComMon_mor (R S : comSemiRingType) (f : {hom[ComSemiRings] R -> S})
  : (multMon R : ComMonoids) -> (multMon S : ComMonoids)
  := multMon_mor (rmorph_of_ComSemiRing f).  (* Why the coercion does't work *)
HB.instance Definition _ (R S : comSemiRingType) (f : {hom[ComSemiRings] R -> S}) :=
  @isHom.Build ComMonoids (multMon R : ComMonoids) (multMon S : ComMonoids)
    (multComMon_mor f)
    (multMon_mor_monmorphism (rmorph_of_ComSemiRing f)).
Definition functor_multComMon_fun (R : ComSemiRings) : ComMonoids := multMon R.
Fact multComMon_ext : FunctorLaws.ext multComMon_mor.
Proof. by move=> /= a b f g eq; exact: multMon_ext. Qed.
Fact multComMon_id : FunctorLaws.id multComMon_mor.
Proof. by move=> /= a; exact: multMon_id. Qed.
Fact multComMon_comp  : FunctorLaws.comp multComMon_mor.
Proof. by move=> /= a b c f g x; rewrite /multComMon_mor /multMon_mor. Qed.
HB.instance Definition _ :=
  @isFunctor.Build ComSemiRings ComMonoids
    functor_multComMon_fun multComMon_mor
    multComMon_ext multComMon_id multComMon_comp.
Definition functorCom : {functor ComSemiRings -> ComMonoids} :=
  functor_multComMon_fun.

End ForgetSemiRings_to_Monoids.
Definition forget_SemiRings_to_Monoids := ForgetSemiRings_to_Monoids.functor.
Lemma forget_SemiRings_to_MonoidsE a b (f : {hom[SemiRings] a -> b}) :
  forget_SemiRings_to_Monoids # f = multMon_mor f :> (_ -> _).
Proof. by []. Qed.
Definition forget_ComSemiRings_to_ComMonoids :=
  ForgetSemiRings_to_Monoids.functorCom.
Lemma forget_ComSemiRings_to_ComMonoidsE a b (f : {hom[ComSemiRings] a -> b}) :
  forget_ComSemiRings_to_ComMonoids # f =
    multMon_mor (rmorph_of_ComSemiRing f) :> (_ -> _).
Proof. by []. Qed.


(** Fix the non HB forgetful inheritance SemiRings -> Monoids *)
Local Notation multSet :=  (* Multiplicative forgetful Sets of a SemiRings *)
  (forget_Monoids_to_Sets \o forget_SemiRings_to_Monoids).

Section FixForgetMultMon.
Variable (R : SemiRings).

Definition transf_to_multmon_fun :
  forget_SemiRings_to_Sets R -> multSet R := fun (r : R) => to_multMon r.
Definition transf_from_multmon_fun :
  multSet R -> forget_SemiRings_to_Sets R := fun (r : multSet R) => \val r.
Lemma transf_to_multmonK : cancel transf_to_multmon_fun transf_from_multmon_fun.
Proof. by []. Qed.
Lemma transf_from_multmonK : cancel transf_from_multmon_fun transf_to_multmon_fun.
Proof. by move=> x; apply val_inj. Qed.

HB.instance Definition _ :=
  isHom.Build Sets (forget_SemiRings_to_Sets R) (multSet R)
    transf_to_multmon_fun I.
HB.instance Definition _ :=
  isIsom.Build Sets (forget_SemiRings_to_Sets R) (multSet R)
    transf_to_multmon_fun I transf_to_multmonK transf_from_multmonK.

Lemma transf_to_multmon_invE :
  inv_hom transf_to_multmon_fun = transf_from_multmon_fun.
Proof. by []. Qed.

End FixForgetMultMon.

Definition transf_to_multmon :
  forget_SemiRings_to_Sets ~~> multSet := transf_to_multmon_fun.
Definition transf_from_multmon :
  multSet ~~> forget_SemiRings_to_Sets := transf_from_multmon_fun.
Fact transf_to_multmon_natural :
  naturality forget_SemiRings_to_Sets multSet transf_to_multmon.
Proof. by []. Qed.
HB.instance Definition _ :=
  @isNatural.Build SemiRings Sets forget_SemiRings_to_Sets multSet
    transf_to_multmon transf_to_multmon_natural.
Fact transf_from_multmon_natural :
  naturality multSet forget_SemiRings_to_Sets transf_from_multmon.
Proof. by []. Qed.
HB.instance Definition _ :=
  @isNatural.Build SemiRings Sets multSet forget_SemiRings_to_Sets
    transf_from_multmon transf_from_multmon_natural.


Local Open Scope monoid_scope.

(* Adjonction Free L-modules -| forget Algebras -> Monoids *)
Definition monalg (R : Rings) (A : Monoids) := {freemod R[A]}.
Notation "{ 'monalg' R [ T ] }" := (monalg R T)
  (at level 0, format "{ 'monalg'  R [ T ] }").

Module MonoidAlgebra.
Section MonoidAlgebra.

Variable (R : Rings) (A : Monoids).
Implicit Types (r s : R) (a b c : A) (x y z : {monalg R[A]}).

Definition one_ma : {monalg R[A]} := [fm / 1 |-> 1].
Definition mul_mma a : {hom[LModules R] {monalg R[A]} -> {monalg R[A]}} :=
  (@functor_freeLmod R) # [the {hom[Sets] A -> A} of *%M a].
Lemma mul_mma_comp a b : mul_mma b \o mul_mma a =1 mul_mma (b * a).
Proof.
rewrite /mul_mma => c.
rewrite -[LHS](functor_o (F := functor_freeLmod R)).
apply: (functor_ext_hom (functor_freeLmod R)).
by move=> {}c /=; rewrite mulmA.
Qed.
Lemma mul_mmacE a b r : mul_mma a [fm / b |-> r] = [fm / a * b |-> r].
Proof. by rewrite /mul_mma /= hom_flmc. Qed.

Let mul_mma_fun x a := mul_mma a x.
Definition mul_mar x : {hom[LModules R] {monalg R[A]} -> {monalg R[A]}} :=
  univmap_freelmod (mul_mma_fun x).
Lemma mul_mar1E x a : mul_mar x [fm / a |-> 1] = mul_mma a x.
Proof. by rewrite /mul_mar univmap_freelmodP /mul_mma_fun. Qed.

Definition mul_ma x := mul_mar^~ x.
Lemma mul_maccE a b r s :
  mul_ma [fm / a |-> r] [fm / b |-> s] = [fm / a * b |-> r * s].
Proof.
rewrite /mul_ma -(fm1ZE _ r) -!linear_of_LmodE linearZ linear_of_LmodE.
rewrite mul_mar1E mul_mmacE -(fm1ZE _ s) -(fm1ZE _ (r * s)).
by rewrite /= scalerA.
Qed.
Lemma mul_maA : associative mul_ma.
Proof.
rewrite /mul_ma=> x y z.
rewrite -[RHS]compapp; apply: (freeLmodE (g := mul_mar _ \o _)) => {x} a.
rewrite [RHS]compapp !mul_mar1E -[LHS]compapp -[RHS]compapp.
apply: (freeLmodE (g := mul_mar _ \o _)) => {y} b.
rewrite [LHS]compapp [RHS]compapp mul_mmacE !mul_mar1E -[LHS]compapp.
apply: (freeLmodE (f := mul_mma _ \o _)) => {z} c.
by rewrite [LHS]compapp !mul_mmacE mulmA.
Qed.
Fact mul_1ma : left_id one_ma mul_ma.
Proof.
rewrite /mul_ma /one_ma => x.
rewrite mul_mar1E; apply (freeLmodE (g := idfun)) => {x}a.
by rewrite mul_mmacE mul1m.
Qed.
Fact mul_ma1 : right_id one_ma mul_ma.
rewrite /mul_ma /one_ma => x; apply (freeLmodE (g := idfun)) => {x}a.
by rewrite mul_mar1E mul_mmacE mulm1.
Qed.
Fact mul_maDl : left_distributive mul_ma +%R.
Proof. by rewrite /mul_ma => z y x; rewrite -!linear_of_LmodE linearD. Qed.
Fact mul_maDr : right_distributive mul_ma +%R.
rewrite /mul_ma => z x y.
pose f := fun z => mul_mar x z + mul_mar y z; rewrite -[RHS]/(f z).
have lin_f : linear f.
  move => c u v.
  by rewrite /f -!linear_of_LmodE !linearP scalerDr addrACA -!addrA.
pose flM := @isHom.Build (LModules R) {monalg R[A]} {monalg R[A]} f lin_f.
pose fL : {hom[LModules R] {monalg R[A]} -> {monalg R[A]}} := HB.pack f flM.
apply: (freeLmodE (g := fL)) => a.
rewrite /fL /f.
rewrite [RHS]/(mul_mar x [fm / a |-> 1] + mul_mar y [fm / a |-> 1]) !mul_mar1E.
by rewrite -!linear_of_LmodE linearD.
Qed.
Fact one_ma_neq0 : one_ma != 0.
Proof.
apply/negP => /eqP/fsfunP/(_ 1).
rewrite !fsfunE inE eqxx.
have /[swap] -> := oner_eq0 R.
by rewrite eqxx.
Qed.
#[export]
HB.instance Definition _ :=
  GRing.Zmodule_isRing.Build {freemod R[A]}
             mul_maA mul_1ma mul_ma1 mul_maDl mul_maDr one_ma_neq0.

Fact scaler_maAl r x y : (r *: (x * y) = (r *: x) * y)%R.
Proof.
rewrite -(fmE y) !mulr_sumr scaler_sumr; apply eq_bigr => a _.
rewrite -(fmE x) !mulr_suml !scaler_sumr mulr_suml; apply eq_bigr => b _.
by rewrite /GRing.mul /= fmcZE !mul_maccE [LHS]fmcZE mulrA.
Qed.
#[export]
HB.instance Definition _ :=
  GRing.Lmodule_isLalgebra.Build R {freemod R[A]} scaler_maAl.

End MonoidAlgebra.

Module Exports.
HB.reexport MonoidAlgebra.

Section Theory.

Variable (R : Rings) (A : Monoids).
Implicit Types (r s : R) (a b c : A) (x y z : {monalg R[A]}).

Lemma onemaE : 1%R = [fm / 1 |-> 1%R] :> {monalg R[A]}.
Proof. by []. Qed.

Lemma mulmaccE a b r s :
  ([fm / a |-> r] * [fm / b |-> s])%R = [fm / a * b |-> r * s].
Proof. by rewrite [LHS]/GRing.mul /= !mul_maccE. Qed.

Lemma mulmaccC a b :
  a * b = b * a -> @GRing.comm {monalg R[A]} [fm / a |-> 1] [fm / b |-> 1].
Proof. by rewrite /GRing.comm => comm; rewrite !mulmaccE comm. Qed.

End Theory.
End Exports.
End MonoidAlgebra.
HB.export MonoidAlgebra.Exports.


Section FunctorMonoidLAlgebra.
Variable R : Rings.

Section Morphisms.
Variables (A B : Monoids) (f : {hom[Monoids] A -> B}).

Definition hom_fun (a : A) : {monalg R[B]} := [fm / f a |-> 1].
Definition hom_MonoidLAlgebra : {monalg R[A]} -> {monalg R[B]} :=
  univmap_freelmod hom_fun.

Fact hom_MonoidLAlgebra_lalg_morph : lalg_morph hom_MonoidLAlgebra.
Proof.
rewrite /hom_MonoidLAlgebra; repeat split; first 2 last.
- rewrite !onemaE univmap_freelmodP /hom_fun /=.
  by rewrite -(mmorphism_of_MonoidsE f) mmorph1.
- exact: isHom_inhom (univmap_freelmod hom_fun).
move=> x y; rewrite -(fmE x) mulr_suml -!linear_of_LmodE !raddf_sum mulr_suml.
apply eq_bigr => a _.
rewrite -(fmE y) mulr_sumr !raddf_sum mulr_sumr; apply eq_bigr => b _.
rewrite mulmaccE -(fm1ZE _ (x a)) -(fm1ZE _ (y b)) -(fm1ZE _ (_ * _)).
rewrite [LHS]linearZ [X in _ = (X * _)%R]linearZ [X in _ = (_ * X)%R]linearZ.
rewrite !linear_of_LmodE !univmap_freelmodP /=.
rewrite /hom_fun !fm1ZE mulmaccE.
by have /= -> := mmorphM f a b.
Qed.
HB.instance Definition _ :=
  @isHom.Build (LAlgebras R) {monalg R[A]} {monalg R[B]}
    (hom_MonoidLAlgebra : [the LAlgebras R of {monalg R[A]}] -> _)
    hom_MonoidLAlgebra_lalg_morph.
Definition MonoidLAlgebra_mor
  : {hom[LAlgebras R] {monalg R[A]} -> {monalg R[B]}} := hom_MonoidLAlgebra.

End Morphisms.


Fact MonoidLAlgebra_ext : FunctorLaws.ext MonoidLAlgebra_mor.
Proof.
rewrite /MonoidLAlgebra_mor => A B f g eq.
apply univmap_freelmod_uniq => a.
by rewrite univmap_freelmodP /hom_fun /= eq.
Qed.
Fact MonoidLAlgebra_id : FunctorLaws.id MonoidLAlgebra_mor.
Proof.
rewrite /MonoidLAlgebra_mor /= => A; apply fsym => x /=.
by have <- := univmap_freelmod_uniq (f := hom_fun idfun) (g := idfun) _ x.
Qed.
Fact MonoidLAlgebra_comp  : FunctorLaws.comp MonoidLAlgebra_mor.
Proof.
rewrite /MonoidLAlgebra_mor => A B C f g; apply fsym => x.
set gf := (X in X x = _).
have <- // := univmap_freelmod_uniq (f := hom_fun (f \o g)) (g := gf) _ x.
by move=> {x} a; rewrite [LHS]compapp !univmap_freelmodP.
Qed.
Definition MonoidLAlgebra (T : Monoids) : LAlgebras R := {monalg R[T]}.
HB.instance Definition _ :=
  @isFunctor.Build Monoids (LAlgebras R)
    MonoidLAlgebra MonoidLAlgebra_mor
    MonoidLAlgebra_ext MonoidLAlgebra_id MonoidLAlgebra_comp.
Definition functor_MonoidLAlgebra : {functor Monoids -> LAlgebras R}
  := MonoidLAlgebra.

End FunctorMonoidLAlgebra.


Section FunctorMonoidAlgebra.

Variable (R : ComRings).

Fact scaler_maAr (A : Monoids) r (x y : {freemod R[A]}) :
  (r *: (x * y) = x * (r *: y))%R.
Proof.
rewrite -(fmE y) [in RHS]scaler_sumr !mulr_sumr scaler_sumr; apply eq_bigr => a _.
rewrite -(fmE x) !mulr_suml !scaler_sumr; apply eq_bigr => b _.
by rewrite !(mulmaccE, fmcZE) mulrCA.
Qed.
HB.instance Definition _ (A : Monoids) :=
  GRing.Lalgebra_isAlgebra.Build R {freemod R[A]} (@scaler_maAr A).

Lemma monalgE (A : Monoids) (T : Algebras R)
  (f g : {hom[Algebras R] {monalg R[A]} -> T}) :
  (forall a : A, f [fm / a |-> 1] = g [fm / a |-> 1]) -> f =1 g.
Proof.
move=> eq x; rewrite -(lrmorphism_of_AlgebrasE f) -(lrmorphism_of_AlgebrasE g).
exact: linear_fmE.
Qed.


Section Homs.
Variables (A B : Monoids) (f : {hom[Monoids] A -> B}).

Definition hom_MonoidAlgebra :=
  (@hom_MonoidLAlgebra R A B f: [the Algebras R of {monalg R[A]}] -> _).

HB.instance Definition _  :=
  @isHom.Build (Algebras R) {monalg R[A]} {monalg R[B]}
    hom_MonoidAlgebra (@hom_MonoidLAlgebra_lalg_morph R A B f).
Definition MonoidAlgebra_mor
  : {hom[Algebras R] {monalg R[A]} -> {monalg R[B]}} := hom_MonoidAlgebra.

End Homs.

Fact MonoidAlgebra_ext : FunctorLaws.ext MonoidAlgebra_mor.
Proof. exact: MonoidLAlgebra_ext. Qed.
Fact MonoidAlgebra_id : FunctorLaws.id MonoidAlgebra_mor.
Proof. exact: MonoidLAlgebra_id. Qed.
Fact MonoidAlgebra_comp  : FunctorLaws.comp MonoidAlgebra_mor.
Proof. exact: MonoidLAlgebra_comp. Qed.
Definition MonoidAlgebra (T : Monoids) : Algebras R := {monalg R[T]}.
HB.instance Definition _ :=
  @isFunctor.Build Monoids (Algebras R)
    MonoidAlgebra MonoidAlgebra_mor
    MonoidAlgebra_ext MonoidAlgebra_id MonoidAlgebra_comp.
Definition functor_MonoidAlgebra : {functor Monoids -> Algebras R}
  := MonoidAlgebra.

End FunctorMonoidAlgebra.


(** Adjonction Monoid Algebras |- forget Algebras to Monoids *)
Definition forget_Algebras_to_Monoids R : {functor Algebras R -> Monoids} :=
  forget_SemiRings_to_Monoids
    \O forget_Rings_to_SemiRings
    \O (@forget_LAlgebras_to_Rings R) \O (@forget_Algebras_to_LAlgebras R).


Module MonoidAlgebraAdjoint.
Section Adjoint.
Variable R : ComRings.
Implicit Types (A : Monoids) (T : Algebras R).

Local Notation forgetf := (forget_Algebras_to_Monoids R).
Local Notation fMA := (MonoidAlgebra R).

Section def_ETA.
Variable A : Monoids.

Definition eta_fun (a : A) : (forgetf \o fMA) A := @to_multMon _ [fm / a |-> 1].
Fact eta_fun_monmorphism : monmorphism eta_fun.
Proof.
split => //; rewrite /eta_fun => a b.
by rewrite monME mulmaccE mulr1.
Qed.
HB.instance Definition _ :=
  isHom.Build Monoids A ((forgetf \o fMA) A) eta_fun eta_fun_monmorphism.

End def_ETA.

Definition eta : FId ~~> forgetf \o fMA := eta_fun.
Fact eta_natural : naturality FId (forgetf \o fMA) eta.
Proof.
move=> /= A B h x /=; rewrite FIdf /eta_fun /=.
by rewrite /multMon_mor /= /hom_MonoidAlgebra univmap_freelmodP.
Qed.
HB.instance Definition _ :=
  @isNatural.Build Monoids Monoids FId (forgetf \o fMA) eta eta_natural.

Section def_EPS.
Variable T : Algebras R.

Definition eps_fun (m : (fMA \o forgetf) T) : T :=
  (\sum_(i <- finsupp (m : {freemod R[_]})) (m i *: \val i)).

Lemma eps_fun1E t r : eps_fun [fm / t |-> r] = r *: \val t.
Proof.
rewrite /eps_fun.
case : (altP (r =P 0)) => [-> | /finsupp_fmZ ->].
  by rewrite /= fm0eq0 scale0r finsupp0 big_nil.
by rewrite big_seq_fset1 fm1E eqxx.
Qed.

Fact eps_fun_linear : linear eps_fun.
Proof.
(* TODO : copypasted from eps_fun_linear / problem with \val due to not forgetful *)
rewrite /eps_fun => r x y; rewrite scaler_sumr /=.
rewrite -!(finsupp_widen _ (S := finsupp x `|` finsupp y)%fset) /=.
rewrite -big_split /=; apply: eq_bigr => a _.
  by rewrite addfmE scalefmE scalerDl scalerA.
- by move=> i /[!memNfinsupp] /eqP ->; rewrite scale0r.
- by move=> a; rewrite inE orbC => ->.
- by move=> i /[!memNfinsupp] /eqP ->; rewrite scale0r scaler0.
- by move=> a; rewrite inE => ->.
- by move=> i /[!memNfinsupp] /eqP ->; rewrite scale0r.
- move=> a; rewrite inE; apply contraLR.
  rewrite negb_or !memNfinsupp addfmE scalefmE => /andP [/eqP -> /eqP ->].
  by rewrite mulr0 addr0.
Qed.
HB.instance Definition _ :=
  GRing.isLinear.Build R ((fMA \o forgetf) T) T _ eps_fun eps_fun_linear.

Fact eps_fun_lalg_morph : lalg_morph eps_fun.
Proof.
repeat split; first 2 last.
- by rewrite /eps_fun finsupp_fm1 big_seq_fset1 fsfunE inE eqxx scale1r.
- exact: eps_fun_linear.
move=> x y; rewrite -(fmE y) mulr_sumr !linear_sum mulr_sumr.
apply eq_bigr => b _; rewrite /= eps_fun1E /=.
rewrite -(fmE x) mulr_suml !linear_sum /= mulr_suml; apply eq_bigr => a _.
rewrite mulmaccE !eps_fun1E /=.
by rewrite -!scalerAr -!scalerAl scalerA mulrC.
Qed.
HB.instance Definition _ :=
  isHom.Build (Algebras R) ((fMA \o forgetf) T) T eps_fun eps_fun_lalg_morph.

End def_EPS.

Definition eps : fMA \o forgetf ~~> FId := eps_fun.
Fact eps_natural : naturality (fMA \o forgetf) FId eps.
Proof.
move=> /= A B h x /=; rewrite FIdf -(fmE x); move: (finsupp x) => S.
rewrite [eps_fun _]linear_sum /= -lrmorphism_of_AlgebrasE [LHS]linear_sum.
rewrite -(lrmorphism_of_AlgebrasE (hom_MonoidAlgebra _)).
rewrite [X in _ = eps_fun X]linear_sum [eps_fun _]linear_sum.
apply eq_bigr => {S} a _ /=.
rewrite eps_fun1E -[X in eps_fun (_ _ X)](fm1ZE _ (x _)).
rewrite -!lrmorphism_of_AlgebrasE linearZ /= [eps_fun _]linearZ /=.
rewrite univmap_freelmodP eps_fun1E scale1r /=.
have /= -> := forget_Algebras_to_LAlgebrasE h.
by rewrite -!lrmorphism_of_AlgebrasE linearZ.
Qed.
HB.instance Definition _ :=
  @isNatural.Build (Algebras R) (Algebras R) (fMA \o forgetf) FId eps eps_natural.

Fact triL : TriangularLaws.left eta eps.
Proof.
move=> /= a.
rewrite -linear_of_LmodE; apply: linear_fmE => x /=.
rewrite -[X in eps_fun X]/(univmap_freelmod _ _) univmap_freelmodP /=.
by rewrite /eta_fun /= eps_fun1E scale1r /=.
Qed.
Fact triR : TriangularLaws.right eta eps.
Proof.
move=> /= M m; rewrite /eta_fun /= /multMon_mor /= eps_fun1E scale1r /=.
exact: val_inj.
Qed.

Let F : {functor Monoids -> Algebras R} := fMA.
Let G : {functor Algebras R -> Monoids} := forgetf.

Definition adjoint : F -| G := AdjointFunctors.mk triL triR.

End Adjoint.
End MonoidAlgebraAdjoint.
Definition adjoint_MonoidAlgebra_forget_to_Monoids := MonoidAlgebraAdjoint.adjoint.

Section UniversalProperty.

Variable (R : ComRings).

Variables (A : Monoids) (M : Algebras R)
  (f : {hom[Monoids] A -> forget_Algebras_to_Monoids R M}).

Local Notation eps :=
  (AdjointFunctors.eps (adjoint_MonoidAlgebra_forget_to_Monoids R)).
Local Notation eta :=
  (AdjointFunctors.eta (adjoint_MonoidAlgebra_forget_to_Monoids R)).

Definition univmap_monalg : {hom[Algebras R] {monalg R[A]} -> M} :=
  eps M \o (functor_MonoidAlgebra R) # f.

Lemma univmap_monalgP a : univmap_monalg [fm / a |-> 1] = \val (f a).
Proof.
(* Todo use MonoidAlgebraAdjoint.triR instead of reproving it *)
rewrite /univmap_monalg /= /hom_MonoidAlgebra /hom_MonoidLAlgebra.
rewrite univmap_freelmodP /hom_fun /=.
by rewrite MonoidAlgebraAdjoint.eps_fun1E scale1r.
Qed.

Lemma univmap_monalg_uniq (g : {hom[Algebras R] {monalg R[A]} -> M}) :
  (forall a : A, g [fm / a |-> 1] = \val (f a)) -> g =1 univmap_monalg.
Proof.
by move=> eq m; apply monalgE => x; rewrite eq univmap_monalgP.
Qed.

End UniversalProperty.


Definition FreeAlg R := MonoidAlgebra R \O functor_freeMon.

Module FreeAlgebraAdjoint.
Section FixAdjonctionFreeAlgebra.
Variable (R : ComRings).

Definition forgetMult := forget_Monoids_to_Sets \O forget_Algebras_to_Monoids R.

Definition forget_Algebra_to_Semirings :=
  forget_Rings_to_SemiRings \O forget_LAlgebras_to_Rings R
    \O forget_Algebras_to_LAlgebras R.

Definition transf_Algebra_to_multmon : forget_Algebras_to_Sets R ~> forgetMult
  :=
  [NEq forget_Monoids_to_Sets \O forget_SemiRings_to_Monoids \O
         forget_Algebra_to_Semirings,
       forgetMult]
    \v (transf_to_multmon \h NId forget_Algebra_to_Semirings)
    \v [NEq forget_Algebras_to_Sets R,
            forget_SemiRings_to_Sets \O forget_Algebra_to_Semirings].

Definition transf_multmon_to_Algebra : forgetMult ~> forget_Algebras_to_Sets R
  :=
  [NEq forget_SemiRings_to_Sets \O forget_Algebra_to_Semirings,
       forget_Algebras_to_Sets R]
    \v (transf_from_multmon \h NId forget_Algebra_to_Semirings)
    \v [NEq forgetMult,
            forget_Monoids_to_Sets \O forget_SemiRings_to_Monoids \O
              forget_Algebra_to_Semirings].

Lemma transf_Algebra_to_multmonE A :
  transf_Algebra_to_multmon A =1 transf_to_multmon A.
Proof. Proof. by move=> a; rewrite /= !HCompId. Qed.
Lemma transf_multmon_to_AlgebraE A :
  transf_multmon_to_Algebra A =1 transf_from_multmon A.
Proof. Proof. by move=> a; rewrite /= !HCompId. Qed.
Lemma transf_Algebra_to_multmonK A :
  cancel (transf_Algebra_to_multmon A) (transf_multmon_to_Algebra A).
Proof. by move=> a; rewrite /= !HCompId /= transf_to_multmonK. Qed.
Lemma transf_multmon_to_AlgebraK A :
  cancel (transf_multmon_to_Algebra A) (transf_Algebra_to_multmon A).
Proof. by move=> a; rewrite /= !HCompId /= transf_from_multmonK. Qed.

Definition adjoint  : FreeAlg R -| forget_Algebras_to_Sets R :=
  adj_natisomR transf_multmon_to_AlgebraK transf_Algebra_to_multmonK
    (adj_comp
       (adjoint_freeMonoid_forget_to_Sets)
       (adjoint_MonoidAlgebra_forget_to_Monoids R)).

End FixAdjonctionFreeAlgebra.
End FreeAlgebraAdjoint.
Definition adjoint_FreeAlgebra_forget_to_Sets := FreeAlgebraAdjoint.adjoint.


Section ComMonoidAlgebra.

Variable (R : ComRings) (A : ComMonoids).
Implicit Types (r s : R) (a b c : A) (x y z : {monalg R[A]}).

Fact mulma_comm : commutative (@GRing.mul {monalg R[A]}).
Proof.
move=> x y; rewrite -(fmE y) mulr_suml mulr_sumr; apply eq_bigr => b _.
rewrite -(fmE x) mulr_suml mulr_sumr; apply eq_bigr => a _.
by rewrite !mulmaccE mulrC mulmC.
Qed.
HB.instance Definition _ := GRing.Lalgebra.on {monalg R[A]}.
HB.instance Definition _ :=
  GRing.SemiRing_hasCommutativeMul.Build {monalg R[A]} mulma_comm.
HB.instance Definition _ :=
  GRing.Lalgebra_isComAlgebra.Build R {monalg R[A]}.

End ComMonoidAlgebra.
