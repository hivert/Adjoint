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
HB.instance Definition _ (a b : [the category of choiceType]) (f : a -> b)
  := isHom.Build [the category of choiceType] a b (f : el a -> el b) I.
Notation Sets := [the category of choiceType].


(* N-Modules ************************************************************)

Definition idfun_is_semi_additive := GRing.idfun_is_semi_additive.
Fact comp_is_semi_additive (a b c : nmodType) (f : a -> b) (g : b -> c) :
  GRing.semi_additive f -> GRing.semi_additive g -> GRing.semi_additive (g \o f).
Proof. by move=> fM gM; split => [|x y]; rewrite /= fM gM. Qed.
HB.instance Definition _ :=
  isCategory.Build nmodType (fun T : nmodType => T)
    GRing.semi_additive idfun_is_semi_additive comp_is_semi_additive.
Notation NModules := [the category of nmodType].
Fact Nmod_hom_additive a b (f : {hom NModules; a, b}) : GRing.semi_additive f.
Proof. by case: f => [/= f [[]]]. Qed.
(* TODO : warning uniform inheritance *)
Coercion additive_of_Nmod a b (f : {hom NModules; a, b}) : {additive a -> b} :=
  HB.pack (Hom.sort f) (GRing.isSemiAdditive.Build _ _ _ (Nmod_hom_additive f)).
Lemma additive_of_NmodE a b (f : {hom NModules; a, b}) :
  @additive_of_Nmod a b f = f :> (_ -> _).
Proof. by []. Qed.

Module ForgetNModules_to_Sets.

Section Morphism.

Variable (a b : nmodType) (f : {hom NModules ; a, b}).
Definition forget (T : nmodType) : choiceType := T.
HB.instance Definition _ :=
  @isHom.Build Sets a b (f : (a : choiceType) -> b) I.
Definition forget_mor : {hom Sets; a, b} :=
  [the {hom Sets; (a : choiceType), b} of f : a -> b].

End Morphism.

HB.instance Definition _ :=
  @isFunctor.Build NModules Sets forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition functor := [the {functor NModules -> Sets} of forget].

End ForgetNModules_to_Sets.

Definition forget_NModules_to_Sets := ForgetNModules_to_Sets.functor.
Lemma forget_NModules_to_SetsE a b (f : {hom NModules; a, b}) :
  forget_NModules_to_Sets # f = f :> (_ -> _).
Proof. by []. Qed.


(* Z-Modules ************************************************************)

(* Full subcategory of N-module *)
HB.instance Definition _ :=
  isCategory.Build zmodType (fun T : zmodType => T)
    GRing.semi_additive GRing.idfun_is_semi_additive comp_is_semi_additive.
Notation ZModules := [the category of zmodType].

Fact Zmodule_mor_additive a b (f : {hom ZModules; a, b}) :
  GRing.semi_additive f.
Proof. by case: f => [/= f [[]]]. Qed.
(* TODO : warning uniform inheritance *)
Coercion additive_of_Zmod a b (f : {hom ZModules; a, b}) : {additive a -> b} :=
  HB.pack (Hom.sort f)
    (GRing.isSemiAdditive.Build _ _ f (Zmodule_mor_additive f)).
Lemma additive_of_ZmodE a b (f : {hom ZModules; a, b}) :
  @additive_of_Zmod a b f = f :> (_ -> _).
Proof. by []. Qed.


Module ForgetZModules_to_NModules.

Section Morphism.

Variable (a b : zmodType) (f : {hom ZModules ; a, b}).
Definition forget (T : zmodType) : nmodType := T.
Let forget_fun : (a : nmodType) -> (b : nmodType) := f.
HB.instance Definition _ :=
  @isHom.Build NModules a b forget_fun (Zmodule_mor_additive f).
Definition forget_mor : {hom NModules; a, b} :=
  [the {hom NModules; (a : nmodType), b} of forget_fun].

End Morphism.

HB.instance Definition _ :=
  @isFunctor.Build ZModules NModules forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition functor := [the {functor ZModules -> NModules} of forget].

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

Module ForgetSemiRings_to_NModules.

Section Morphism.

Variable (a b : semiRingType) (f : {hom SemiRings ; a, b}).
Definition forget (T : semiRingType) : nmodType := T.
Let forget_fun : (a : nmodType) -> (b : nmodType) := f.
HB.instance Definition _ :=
  @isHom.Build NModules a b forget_fun (SemiRing_mor_additive f).
Definition forget_mor : {hom NModules; a, b} :=
  [the {hom NModules; (a : nmodType), b} of forget_fun].

End Morphism.

HB.instance Definition _ :=
  @isFunctor.Build SemiRings NModules forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition functor := [the {functor SemiRings -> NModules} of forget].

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

Module ForgetRings_to_ZModules.

Section Morphism.

Variable (a b : ringType) (f : {hom Rings ; a, b}).
Definition forget (T : ringType) : zmodType := T.
Let forget_fun : (a : zmodType) -> (b : zmodType) := f.
HB.instance Definition _ :=
  @isHom.Build ZModules a b forget_fun (Ring_mor_additive f).
Definition forget_mor : {hom ZModules; a, b} :=
  [the {hom ZModules; (a : zmodType), b} of forget_fun].

End Morphism.

HB.instance Definition _ :=
  @isFunctor.Build Rings ZModules forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).

Definition functor := [the {functor Rings -> ZModules} of forget].

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
Fact LModules_mor_linear R a b (f : {hom LModules R; a, b}) : linear f.
Proof. by case: f => [/= f [[]]]. Qed.
Coercion linear_of_LModules R a b (f : {hom LModules R; a, b}) : {linear a -> b} :=
  HB.pack (Hom.sort f) (GRing.isLinear.Build _ _ _ _ _ (LModules_mor_linear f)).
Lemma linear_of_LModulesE R a b (f : {hom LModules R; a, b}) :
  @linear_of_LModules R a b f = f :> (_ -> _).
Proof. by []. Qed.
Fact LModules_mor_semi_additive R a b (f : {hom LModules R; a, b}) :
  GRing.semi_additive f.
Proof.
rewrite -linear_of_LModulesE; split => [| x y]; first by rewrite raddf0.
by rewrite raddfD.
Qed.

Module ForgetLModules_to_ZModules.

Section BaseRing.

Variable R : ringType.

Section Morphism.

Variables (a b : lmodType R) (f : {hom LModules R; a, b}).
Definition forget (T : lmodType R) : zmodType := T.
Let forget_fun : (a : zmodType) -> (b : zmodType) := f.
HB.instance Definition _ :=
  @isHom.Build ZModules a b forget_fun (LModules_mor_semi_additive f).
Definition forget_mor : {hom ZModules; a, b} :=
  [the {hom ZModules; (a : zmodType), b} of forget_fun].

End Morphism.

HB.instance Definition _ :=
  @isFunctor.Build (LModules R) ZModules forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
End BaseRing.

Definition functor R := [the {functor LModules R -> ZModules} of (@forget R)].

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
  linear f * GRing.multiplicative f.
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

Fact LAlgebras_mor_linear R a b (f : {hom LAlgebras R; a, b}) : linear f.
Proof. by case: f => [/= f [[[]]]]. Qed.
Fact LAlgebras_mor_multiplicative R a b (f : {hom LAlgebras R; a, b}) :
  GRing.multiplicative f.
Proof. by case: f => [/= f [[[]]]]. Qed.
Coercion lrmorphism_of_LAlgebras R a b (f : {hom LAlgebras R; a, b}) :
  {lrmorphism a -> b} := HB.pack (Hom.sort f)
     (GRing.isLinear.Build _ _ _ _ _ (LAlgebras_mor_linear f))
     (GRing.isMultiplicative.Build _ _ _ (LAlgebras_mor_multiplicative f)).
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
Let forget_fun : (a : lmodType R) -> (b : lmodType R) := f.
HB.instance Definition _ :=
  @isHom.Build (LModules R) a b forget_fun (LAlgebras_mor_linear f).
Definition forget_mor : {hom LModules R; a, b} :=
  [the {hom LModules R; (a : lmodType R), b} of forget_fun].

End Morphism.

HB.instance Definition _ :=
  @isFunctor.Build (LAlgebras R) (LModules R) forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
End BaseRing.

Definition functor R := [the {functor LAlgebras R -> LModules R} of (@forget R)].

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
Let forget_fun : (a : ringType) -> (b : ringType) := f.
HB.instance Definition _ :=
  @isHom.Build Rings a b forget_fun (LAlgebras_mor_rmorphism f).
Definition forget_mor : {hom Rings; a, b} :=
  [the {hom Rings; (a : ringType), b} of forget_fun].

End Morphism.

HB.instance Definition _ :=
  @isFunctor.Build (LAlgebras R) Rings forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
End BaseRing.

Definition functor R := [the {functor LAlgebras R -> Rings} of (@forget R)].

End ForgetLAlgebras_to_Rings.

Definition forget_LAlgebras_to_Rings := ForgetLAlgebras_to_Rings.functor.
Lemma forget_LAlgebras_to_RingsE R a b (f : {hom LAlgebras R; a, b}) :
  forget_LAlgebras_to_Rings R # f = f :> (_ -> _).
Proof. by []. Qed.


(*
HB.instance Definition _ R :=
  isCategory.Build (algType R) (fun T : algType R => T)
    (fun a b (f : a -> b) => lalg_morph f)
    (@idfun_is_lalg_morph R) (@comp_is_lalg_morph R).
Notation Algebras R := [the category of algType R].
HB.instance Definition _ R :=
  isCategory.Build (comAlgType R) (fun T : comAlgType R => T)
    (fun a b (f : a -> b) => lalg_morph f)
    (@idfun_is_lalg_morph R) (@comp_is_lalg_morph R).
Notation ComAlgebras R := [the category of comAlgType R].
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
  @isHom.Build NModules {mset a} {mset b}
    (hom_mset f : [the nmodType of {mset a}] -> [the nmodType of {mset b}])
    (hom_mset_additive f).
Definition FreeNmod_mor (a b : Sets) (f : a -> b) :=
  [the {hom NModules; FreeNmod a, FreeNmod b} of hom_mset f].

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

Implicit Types (a : choiceType) (T : nmodType).

Let eta_fun a (x : a) := [mset x].
Definition eta : FId ~~> forget_NModules_to_Sets \o FreeNmod := eta_fun.
Fact eta_natural : naturality FId (forget_NModules_to_Sets \o FreeNmod) eta.
Proof. by move=> /= a b h x /=; rewrite /eta_fun FIdf hom_mset1. Qed.
HB.instance Definition _ :=
  @isNatural.Build Sets Sets FId (forget_NModules_to_Sets \o FreeNmod) eta eta_natural.

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
  @isNatural.Build NModules NModules (FreeNmod \o forget_NModules_to_Sets) FId
    eps eps_natural.

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
