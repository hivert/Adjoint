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
Coercion additive_of_Nmod a b (f : {hom[NModules] a -> b}) : {additive a -> b} :=
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
Notation ZModules := [the category of zmodType].

#[warning="-uniform-inheritance"]
Coercion additive_of_Zmod a b (f : {hom[ZModules] a -> b}) : {additive a -> b} :=
  HB.pack (Hom.sort f) (GRing.isSemiAdditive.Build _ _ f (isHom_inhom f)).
Lemma additive_of_ZmodE a b (f : {hom[ZModules] a -> b}) :
  @additive_of_Zmod a b f = f :> (_ -> _).
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
Notation SemiRings := [the category of semiRingType].

#[warning="-uniform-inheritance"]
Coercion rmorph_of_SRing a b (f : {hom[SemiRings] a -> b}) : {rmorphism a -> b} :=
  HB.pack (Hom.sort f)
    (GRing.isSemiAdditive.Build _ _ _ (fst (isHom_inhom f)))
    (GRing.isMultiplicative.Build _ _ _ (snd (isHom_inhom f))).
Lemma rmorph_of_SRingE a b (f : {hom[SemiRings] a -> b}) :
  @rmorph_of_SRing a b f = f :> (_ -> _).
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
Notation Rings := [the category of ringType].
#[warning="-uniform-inheritance"]
Coercion rmorph_of_Ring a b (f : {hom[Rings] a -> b}) : {rmorphism a -> b} :=
  HB.pack (Hom.sort f)
    (GRing.isSemiAdditive.Build _ _ _ (fst (isHom_inhom f)))
    (GRing.isMultiplicative.Build _ _ _ (snd (isHom_inhom f))).
Lemma rmorph_of_RingE a b (f : {hom[Rings] a -> b}) :
  @rmorph_of_Ring a b f = f :> (_ -> _).
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


(* ComSemiRings **********************************************************)

(** Full subcategory of SemiRings *)
HB.instance Definition _ :=
  isCategory.Build comSemiRingType (fun T : comSemiRingType => T)
    (@inhom SemiRings) (@idfun_inhom SemiRings) (@funcomp_inhom SemiRings).
Notation ComSemiRings := [the category of comSemiRingType].

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
#[warning="-uniform-inheritance"]
Coercion rmorph_of_ComSemiRing a b (f : {hom[ComSemiRings] a -> b}) :
  {rmorphism a -> b} := forget_ComSemiRings_to_SemiRings # f.
Lemma rmorph_of_ComSemiRingE a b (f : {hom[ComSemiRings] a -> b}) :
  rmorph_of_ComSemiRing f = f :> (_ -> _).
Proof. by []. Qed.

(* Q : Should there be a coercion
   {hom[ComSemiRings] a -> b} -> {hom[SemiRings] a -> b} *)


(* ComRings **********************************************************)

(** Full subcategory of Rings *)
HB.instance Definition _ :=
  isCategory.Build comRingType (fun T : comRingType => T)
    (@inhom Rings) (@idfun_inhom Rings) (@funcomp_inhom Rings).
Notation ComRings := [the category of comRingType].

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
#[warning="-uniform-inheritance"]
Coercion rmorph_of_comRing a b (f : {hom[ComRings] a -> b}) :
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
Coercion linear_of_Lmod R a b (f : {hom[LModules R] a -> b}) : {linear a -> b} :=
  HB.pack (Hom.sort f) (GRing.isLinear.Build _ _ _ _ _ (isHom_inhom f)).
Lemma linear_of_LmodE R a b (f : {hom[LModules R] a -> b}) :
  @linear_of_Lmod R a b f = f :> (_ -> _).
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
Notation LAlgebras R := [the category of lalgType R].
#[warning="-uniform-inheritance"]
Coercion lrmorphism_of_LAlgebras R a b (f : {hom[LAlgebras R] a -> b}) :
  {lrmorphism a -> b} := HB.pack (Hom.sort f)
     (GRing.isLinear.Build _ _ _ _ _ (fst (isHom_inhom f)))
     (GRing.isMultiplicative.Build _ _ _ (snd (isHom_inhom f))).
Lemma lrmorphism_of_LAlgebrasE R a b (f : {hom[LAlgebras R] a -> b}) :
  @lrmorphism_of_LAlgebras R a b f = f :> (_ -> _).
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

Lemma unicity_of_forgetful_functors (R : Rings) :
  forget_Rings_to_ZModules \O forget_LAlgebras_to_Rings R
    =#= forget_LModules_to_ZModules R \O forget_LAlgebras_to_LModules R.
Proof. exact: (functor_ext (eq := fun=> _)). Qed.


(* Algebras ************************************************************)

(** Full subcategory of LAlgebras *)
HB.instance Definition _ R :=
  isCategory.Build (algType R) (fun T : algType R => T)
    (@inhom (LAlgebras R)) (@idfun_inhom (LAlgebras R))
    (@funcomp_inhom (LAlgebras R)).
Notation Algebras R := [the category of algType R].

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
  lrmorphism_of_Algebras f = f :> (_ -> _).
Proof. by []. Qed.


(* ComAlgebras *****************************************************)

HB.instance Definition _ R :=
  isCategory.Build (comAlgType R) (fun T : comAlgType R => T)
    (@inhom (Algebras R)) (@idfun_inhom (Algebras R))
    (@funcomp_inhom (Algebras R)).
Notation ComAlgebras R := [the category of comAlgType R].

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
  lrmorphism_of_ComAlgebras f = f :> (_ -> _).
Proof. by []. Qed.



(* Monoid ************************************************************)

Fact comp_is_monmorphism_fun (a b c : monoidType) (f : a -> b) (g : b -> c) :
  monmorphism f -> monmorphism g -> monmorphism (g \o f).
Proof. by move=> fM gM; split => [x y|]; rewrite /= fM gM. Qed.
HB.instance Definition _ :=
  isCategory.Build monoidType (fun T : monoidType => T)
    monmorphism idfun_is_monmorphism comp_is_monmorphism_fun.
Notation Monoids := [the category of monoidType].
#[warning="-uniform-inheritance"]
Coercion mmorphism_of_Monoids a b (f : {hom[Monoids] a -> b}) : {mmorphism a -> b} :=
  HB.pack (Hom.sort f) (isMonMorphism.Build _ _ _ (isHom_inhom f)).
Lemma mmorphism_of_MonoidsE a b (f : {hom[Monoids] a -> b}) :
  @mmorphism_of_Monoids a b f = f :> (_ -> _).
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
by elim: x => [| s s0 {1}->]; rewrite ?big_nil // big_cons [RHS]cat1s.
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

Implicit Types (a : Sets) (T : Monoids).

Definition eta_fun a (x : a) := [fmon x].
Definition eta : FId ~~> forget_Monoids_to_Sets \o functor_freeMon := eta_fun.
Fact eta_natural : naturality FId (forget_Monoids_to_Sets \o functor_freeMon) eta.
Proof. by move=> /= a b h x /=; rewrite /eta_fun FIdf. Qed.
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
rewrite -!mmorphism_of_MonoidsE /=.
rewrite /eta_fun /= /eps_fun /hom_freeMonoid.
by rewrite big_map [RHS]freeMonoidE.
Qed.
Fact triR : TriangularLaws.right eta eps.
Proof. by move=> /= M m; rewrite /eta_fun /= /eps_fun big_cons big_nil mulm1. Qed.

Let F : {functor Sets -> Monoids} := functor_freeMon.
Let G : {functor Monoids -> Sets} := forget_Monoids_to_Sets.

Definition adjoint : F -| G := AdjointFunctors.mk triL triR.

End Adjoint.
End FreeMonAdjoint.
Definition adjoint_freeMon_forget := FreeMonAdjoint.adjoint.

Section UniversalProperty.

Variables (A : choiceType) (M : monoidType) (f : A -> M).

Local Notation eps := (AdjointFunctors.eps adjoint_freeMon_forget).
Local Notation eta := (AdjointFunctors.eta adjoint_freeMon_forget).

Definition univmap_freemon : {mmorphism {freemon A} -> M} :=
  eps M \o functor_freeMon # f : {hom _ -> M}.

Lemma univmap_freemonP a : univmap_freemon [fmon a] = f a.
Proof.
rewrite /univmap_freemon -[[fmon a]]/(eta A a) /=.
exact: (AdjointFunctors.triR adjoint_freeMon_forget).
Qed.

Lemma univmap_freemon_uniq (g : {mmorphism {freemon A} -> M}) :
  (forall a : A, g [fmon a] = f a) -> g =1 univmap_freemon.
Proof.
move=> eq m.
rewrite (freeMonoidE m) !mmorph_prod; apply eq_bigr => i _.
by rewrite eq univmap_freemonP.
Qed.

End UniversalProperty.


(** Commutative Monoids *********************************************)
(* Full subcategory of Monoids *)
HB.instance Definition _ :=
  isCategory.Build comMonoidType (fun T : comMonoidType => T)
    (@inhom Monoids) (@idfun_inhom Monoids) (@funcomp_inhom Monoids).
Notation ComMonoids := [the category of comMonoidType].
#[warning="-uniform-inheritance"]
Coercion mmorphism_of_ComMonoids a b (f : {hom[ComMonoids] a -> b}) :
  {mmorphism a -> b} :=
  HB.pack (Hom.sort f) (isMonMorphism.Build _ _ _ (isHom_inhom f)).
Lemma mmorphism_of_ComMonoidsE a b (f : {hom[ComMonoids] a -> b}) :
  @mmorphism_of_ComMonoids a b f = f :> (_ -> _).
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

(** Doesn't seems to be provable
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


Definition Equiv_ComMonoids_NModules :
  equivalence_category NMod_of_ComMonoid ComMonoid_of_NMod :=
  EquivalenceCategory natural_isoMC natural_isoCM.


(* TODO Those are full subcategories. Devise some infrastructure.
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

Let F : {functor Sets -> NModules} := FreeNmod.
Let G : {functor NModules -> Sets} := forget_NModules_to_Sets.

Definition adjoint : FreeNmod -| forget_NModules_to_Sets :=
  AdjointFunctors.mk triL triR.

End Adjoint.
End FreeNModAdjoint.
Definition adjoint_freeNMod_forget := FreeNModAdjoint.adjoint.


Section UniversalProperty.

Variables (A : choiceType) (M : nmodType) (f : A -> M).

Local Notation eps := (AdjointFunctors.eps adjoint_freeNMod_forget).
Local Notation eta := (AdjointFunctors.eta adjoint_freeNMod_forget).

Definition univmap : {additive {mset A} -> M} :=
  eps M \o FreeNmod # f : {hom FreeNmod A -> M}.

Lemma univmapP a : univmap [mset a] = f a.
Proof.
rewrite /univmap -[[mset a]]/(eta A a) /= hom_mset1.
exact: (AdjointFunctors.triR adjoint_freeNMod_forget).
Qed.

Lemma univmap_uniq (g : {additive {mset A} -> M}) :
  (forall a : A, g [mset a] = f a) -> g =1 univmap.
Proof.
move=> eq m; rewrite -(msetE m) !raddf_sum; apply eq_bigr => x _.
by rewrite eq univmapP.
Qed.

End UniversalProperty.

Local Close Scope monoid_scope.


Local Open Scope ring_scope.
(** Adjonction between forget : L-Modules -> Sets and free L-Modules *)

Section Set_to_FreeLmodule.

Variable R : ringType.

Variable (a b : Sets) (f : {hom[Sets] a -> b}).

Definition hom_fm (m : {freemod R[a]}) : {freemod R[b]} :=
  \sum_(i <- finsupp m) [fm / f i |-> m i].

Lemma hom_fm1 (x : a) : hom_fm [fm / x |-> 1] = [fm / f x |-> 1].
Proof. by rewrite /hom_fm finsupp_fm1 /= big_seq_fset1 fm1E eqxx. Qed.

Fact hom_fm_linear : linear hom_fm.
Proof.
rewrite /hom_fm => c /= m n; rewrite scaler_sumr /=.
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
  GRing.isLinear.Build R {freemod R[a]} {freemod R[b]} _ hom_fm hom_fm_linear.

End Set_to_FreeLmodule.

Section Functor.
Variable (R : ringType).

HB.instance Definition _ (a b : Sets) (f : {hom[Sets] a -> b}) :=
  @isHom.Build (LModules R) {freemod R[a]} {freemod R[b]}
    (hom_fm f : (_ : LModules R) -> _) (hom_fm_linear f).
Definition freeLmod_mor (a b : Sets) (f : {hom[Sets] a -> b})
  : {hom[LModules R] {freemod R[a]} -> {freemod R[b]}} := hom_fm f.

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
Proof. by move=> /= a b h x /=; rewrite /eta_fun FIdf hom_fm1. Qed.
HB.instance Definition _ :=
  @isNatural.Build Sets Sets FId (forgetf \o fmf) eta eta_natural.

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
Definition eps : fmf \o forgetf ~~> FId := eps_fun.
Fact eps_natural : naturality (fmf \o forgetf) FId eps.
Proof.
move=> /= a b h.
rewrite -!linear_of_LmodE; apply: linear_fmE => /= x.
rewrite FIdf /eps_fun /= hom_fm1.
by rewrite !finsupp_fm1 !big_seq_fset1 !fm1E !eqxx !scale1r.
Qed.
HB.instance Definition _ :=
  @isNatural.Build (LModules R) (LModules R)
    (fmf \o forgetf) FId eps eps_natural.

Fact triL : TriangularLaws.left eta eps.
Proof.
move=> /= a.
rewrite -!linear_of_LmodE; apply: linear_fmE => /= x.
rewrite /eta_fun /= /eps_fun /= hom_fm1.
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
Definition adjoint_freeLMod_forget := FreeLModAdjoint.adjoint.

Section UniversalProperty.

Variable (R : ringType).

Variables (A : choiceType) (M : lmodType R) (f : A -> M).

Local Notation eps := (AdjointFunctors.eps (adjoint_freeLMod_forget R)).
Local Notation eta := (AdjointFunctors.eta (adjoint_freeLMod_forget R)).

Definition univmap_freelmod : {linear {freemod R[A]} -> M} :=
  eps M \o (functor_freeLmod R) # f : {hom _ -> M}.

Lemma univmap_freelmodP a : univmap_freelmod [fm / a |-> 1] = f a.
Proof.
rewrite /univmap -[[fm / a |-> 1]]/(eta A a) /= !hom_fm1.
exact: (AdjointFunctors.triR (adjoint_freeLMod_forget R)).
Qed.

Lemma univmap_freelmod_uniq (g : {linear {freemod R[A]} -> M}) :
  (forall a : A, g [fm / a |-> 1] = f a) -> g =1 univmap_freelmod.
Proof.
move=> eq m.
rewrite -(fmE m) !raddf_sum; apply eq_bigr => x _.
by rewrite fm1ZE [LHS]linearZ [RHS]linearZ eq univmap_freelmodP.
Qed.

End UniversalProperty.


(* Monoid of SemiRing Forgetful functor *)
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
