(* Categories for the working MathComp developpers                            *)
(* Copyright (C) 2020 monae authors, 2024-2026 Florent Hivert,                *)
(* license: LGPL-3.0-or-later                                                 *)
From Corelib Require Import Setoid.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finfun bigop.
From mathcomp Require Import ssralg.
(******************************************************************************)
(*                                                                            *)
(* This file is mostly copied and adapted from monae.                         *)
(*   https://github.com/affeldt-aist/monae                                    *)
(*                                                                            *)
(******************************************************************************)



(******************************************************************************)
(*                  Formalization of basic category theory                    *)
(*                                                                            *)
(* This file provides definitions of category, functor, monad, as well as     *)
(* basic theorems. It comes as a generalization of the first part of          *)
(* hierarchy.v which is specialized to the category of sets.                  *)
(*                                                                            *)
(*            category == type of categories, a category C is implemented     *)
(*                        with a universe a la Tarski, there is a realizer    *)
(*                        function el that associates to each object A the    *)
(*                        type el A of its elements; this corresponds to the  *)
(*                        definition of concrete categories                   *)
(*     {hom[C] A -> B} == the hom-set of morphisms from A to B, where A and B *)
(*                        are objects of a category C                         *)
(*        {hom A -> B} == the hom-set where the ategory C is inferred         *)
(*             [hom f] == morphism corresponding to the function f            *)
(*                  CT := [the category of Type]                              *)
(*         FunctorLaws == module that defines the functor laws                *)
(*                  \O == functor composition                                 *)
(*             F ~~> G == forall a, {hom F a, G a}, which corresponds to a    *)
(*                        natural transformation when it satisfies the        *)
(*                        predicate naturality                                *)
(*              F ~> G == natural transformation from F to G                  *)
(*                 NId == the identity natural transformation                 *)
(*          [NEq F, G] == natural transformation from F to G where F and G    *)
(*                        are convertible, especially when they are           *)
(*                        compositions, and differ only by associativity or   *)
(*                        insertion of unit functors                          *)
(*                  \v == vertical composition                                *)
(*                  \h == horizontal composition, or Godement product         *)
(*              F -| G == pair of adjoint functors (Module                    *)
(*                        Module AdjointFunctors); see also TriangularLaws.   *)
(*      Module AdjComp == define a pair of adjoint functors by composition of *)
(*                        two pairs of adjoint functors                       *)
(* MonadLaws, BindLaws == modules that define the monad laws                  *)
(*             isMonad == mixin that defines the monad interface              *)
(*   Monad_of_ret_bind == factory, monad defined by ret and bind              *)
(*   Monad_of_munit_mu == factory, monad defined by munit and mu              *)
(* Monad_of_adjoint_functors == module that defines a monad by a pair of      *)
(*                        adjoint functors                                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope category_scope.

Reserved Notation "f \O g" (at level 50, format "f  \O  g").
Reserved Notation "f \@ g" (at level 50, format "f  \@  g").
Reserved Notation "F ~~> G" (at level 51).
Reserved Notation "f ~> g" (at level 51).
Reserved Notation "F # g" (at level 11).
Reserved Notation "F =m= g" (at level 70, no associativity).
Reserved Notation "F =#= g" (at level 70, no associativity).
Reserved Notation "F =%= g" (at level 70, no associativity).
Reserved Notation "F -| G" (at level 51, G at next level).
Reserved Notation "f \v g" (at level 50, format "'[v' f '/' \v  g ']'", left associativity).
Reserved Notation "f \h g" (at level 50, format "f  \h  g").
Reserved Notation "m >>= f" (at level 49).

Reserved Notation "'{' 'hom' U '->' V '}'"
  (at level 0, U at level 98, V at level 99, format "{ 'hom'  U  ->  V }").
Reserved Notation "'{' 'hom' '[' C ']' U '->' V '}'"
  (at level 0, U at level 98, V at level 99, format "{ 'hom' [ C ]  U  ->  V }").
Reserved Notation "'{' 'isom' U '->' V '}'"
  (at level 0, U at level 98, V at level 99, format "{ 'isom'  U  ->  V }").
Reserved Notation "'{' 'isom' '[' C ']' U '->' V '}'"
  (at level 0, U at level 98, V at level 99, format "{ 'isom' [ C ]  U  ->  V }").

Declare Scope category_scope.
Delimit Scope category_scope with category.
Local Open Scope category_scope.


(* opaque ssrfun.frefl blocks some proofs involving functor_ext *)
#[global]
Remove Hints frefl : core.

(* Our categories are always concrete; morphisms are just functions. *)
HB.mixin Record isCategory (obj : Type) := {
  el : obj -> Type ;
  inhom : forall a b, (el a -> el b) -> Prop ;
  idfun_inhom : forall a, @inhom a a idfun ;
  funcomp_inhom : forall a b c (f : el a -> el b) (g : el b -> el c),
      inhom _ _ f -> inhom _ _ g -> inhom _ _ (g \o f)
}.
Arguments isCategory.phant_Build : clear implicits.

#[short(type=category)]
HB.structure Definition Category := {C of isCategory C}.

Arguments idfun_inhom [C] : rename.
Arguments funcomp_inhom [C a b c f g] : rename.

HB.mixin Record isHom (C : category) (a b : C) (f : el a -> el b) := {
  isHom_inhom : inhom a b f
}.
HB.structure Definition Hom (C : category) (a b : C) :=
  {f of isHom C a b f}.
Arguments isHom_inhom [C a b].

Notation "{ 'hom' U -> V }" := (Hom.type U V) : category_scope.
Notation "{ 'hom' '[' C ']' U '->' V }" := (@Hom.type C U V)
  (only parsing) : category_scope.
(* TODO: FIX: At some places, this [hom f] notation is not used for printing and
   [the {hom ...} of f] is undesirably printed instead. *)
Notation "[ 'hom' f ]" := [the {hom _ -> _} of f]
  (at level 0, format "[ 'hom'  f ]") : category_scope.


Section hom_interface.
Variable C : category.
Implicit Types a b c : C.

HB.instance Definition _ c := isHom.Build _ _ _ (@idfun (el c)) (idfun_inhom c).

HB.instance Definition _ (a b c : C) (f : {hom b -> c}) (g : {hom a -> b}):=
  isHom.Build _ _ _ (f \o g) (funcomp_inhom (isHom_inhom g) (isHom_inhom f)).
End hom_interface.

Definition eq_morphism (C : category) (B A : C) (f g : {hom A -> B}) := f =1 g.
Definition comp_morphism (C : category) (U V W : C) :
  {hom V -> U} -> {hom W -> V} -> {hom W -> U} := @comp (el U) (el V) (el W).

Notation "f =m= g" := (eq_morphism f g).
Notation "f \@ g" := (comp_morphism f g).

(* Notation [\o f , .. , g , h] for hom compositions. *)
Module comps_notation.
Notation "[ '\@' f , .. , g , h ]" := (f \@ .. (g \@ h) ..) (at level 0,
  format "[ '[' '\@'  f ,  '/' .. ,  '/' g ,  '/' h ']' ]") : category_scope.
End comps_notation.

Add Parametric Relation (C : category) (A B : C) :
  {hom A -> B} (@eq_morphism C B A)
    reflexivity proved by (fun _ _ => erefl _)
    symmetry proved by (@fsym (el B) (el A))
    transitivity proved by (@ftrans (el B) (el A))
    as eq_mor.
Add Parametric Morphism  (C : category) (U V W : C) :
  (@comp_morphism C U V W : {hom V -> U} -> {hom W -> V} -> {hom W -> U})
    with signature
    (@eq_morphism C U V) ==> (@eq_morphism C V W) ==> (@eq_morphism C U W)
      as comp_mor.
Proof. by move=> /= f1 f2 eqf g1 g2 eqg x; rewrite /= eqg eqf. Qed.

Section category_lemmas.
Variable C : category.

Lemma homfunK (a b : C) (f : {hom a -> b}) : [hom f] =1 f.
Proof. by []. Qed.

Lemma homcompA (a b c d : C)
  (h : {hom c -> d}) (g : {hom b -> c}) (f : {hom a -> b}) :
  (h \@ g) \@ f =m= h \@ (g \@ f).
Proof. by []. Qed.

Lemma hom_compId (a b : C) (f : {hom a -> b}) : f \@ idfun =m= f.
Proof. by []. Qed.
Lemma hom_Idcomp (a b : C) (f : {hom a -> b}) : idfun \@ f =m= f.
Proof. by []. Qed.


Import comps_notation.

End category_lemmas.

(* transportation of hom along equality *)
Section transport_lemmas.
Variable C : category.
Definition transport_dom
  (a a' b : C) (p : a = a') (f : {hom a -> b}) : {hom a' -> b} :=
    eq_rect a (fun x => {hom x -> b}) f a' p.
Definition transport_codom
  (a b b' : C) (p : b = b') (f : {hom a -> b}) : {hom a -> b'} :=
    eq_rect b (fun x => {hom a -> x}) f b' p.
Definition transport_hom (a a' b b' : C) (pa : a = a') (pb : b = b')
  (f : {hom a -> b}) : {hom a' -> b'} :=
  eq_rect b (fun y => {hom a' -> y})
          (eq_rect a (fun x => {hom x -> b}) f a' pa)
          b' pb.
Definition hom_of_eq (a b : C) (p : a = b) : {hom a -> b} :=
  transport_codom p [hom idfun].


(* F for factorization *)
Lemma transport_domF (a a' b : C) (p : a = a') (f : {hom a -> b}) :
  transport_dom p f =m= f \@ hom_of_eq (esym p).
Proof. by subst a'. Qed.
Lemma transport_codomF (a b b' : C) (p : b = b') (f : {hom a -> b}) :
  transport_codom p f =m= hom_of_eq p \@ f.
Proof. by subst b'. Qed.
Lemma transport_homF (a a' b b' : C) (pa : a = a') (pb : b = b') (f : {hom a -> b}) :
  transport_hom pa pb f =m= hom_of_eq pb \@ f \@ hom_of_eq (esym pa).
Proof. by subst a' b'. Qed.

Add Parametric Morphism  (a a' b b' : C) (pa : a = a') (pb : b = b') :
  (transport_hom pa pb)
    with signature (@eq_morphism C b a) ==> (@eq_morphism C b' a')
      as transport_homE.
Proof. by subst a b. Qed.

Lemma transport_hom_inj (a a' b b' : C) (pa : a = a') (pb : b = b')
  (f g : {hom a -> b}) :
  transport_hom pa pb f =m= transport_hom pa pb g -> f =m= g.
Proof. by subst a b. Qed.
Lemma transport_hom_trans (a a' a'' b b' b'' : C)
      (pa : a = a') (pa' : a' = a'') (pb : b = b') (pb' : b' = b'')
      (f : {hom a -> b}) :
  (transport_hom pa' pb' \o transport_hom pa pb) f =m=
    transport_hom (eq_trans pa pa') (eq_trans pb pb') f.
Proof. by subst a a' b b'. Qed.

End transport_lemmas.


HB.mixin Record isIsom (C : category) (a b : C) (f : el a -> el b) := {
    inv_hom : el b -> el a;
    ishom_inv_hom : inhom b a inv_hom;
    homK : cancel f inv_hom;
    inv_homK : cancel inv_hom f;
  }.
HB.structure Definition Isom (C : category) (a b : C) :=
  {f of isIsom C a b f & isHom C a b f}.
Notation "{ 'isom' U -> V }" := (Isom.type U V) : category_scope.
Notation "{ 'isom' '[' C ']' U '->' V }" := (@Isom.type C U V)
  (only parsing) : category_scope.
Arguments inv_hom [C a b].
Arguments ishom_inv_hom [C a b].
Arguments homK [C a b].
Arguments inv_homK [C a b].


Section isom_interface.
Variable C : category.
Implicit Types a b c : C.

#[local] Lemma idfunK A : cancel (@idfun A) idfun. Proof. by []. Qed.

HB.instance Definition _ c :=
  isIsom.Build _ _ _ (@idfun (el c))
    (idfun_inhom c) (@idfunK (el c)) (@idfunK (el c)).

HB.instance Definition _ (a b c : C) (f : {isom b -> c}) (g : {isom a -> b}):=
  isIsom.Build _ _ _ (f \o g)
    (funcomp_inhom (ishom_inv_hom f) (ishom_inv_hom g))
    (can_comp (homK f) (homK g)) (can_comp (inv_homK g) (inv_homK f)).

HB.instance Definition _ (a b : C) (f : {isom a -> b}) :=
  isHom.Build _ _ _ (inv_hom f : el b -> el a) (ishom_inv_hom f).
HB.instance Definition _ (a b : C) (f : {isom a -> b}) :=
  isIsom.Build _ _ _ (inv_hom f : el b -> el a)
    (isHom_inhom f) (inv_homK f) (homK f).

End isom_interface.

Section ismorphism_lemmas.
Variable C : category.

Lemma isom_bij (a b : C) (f : {isom a -> b}) : bijective f.
Proof. by exists (inv_hom f); [exact: homK | exact: inv_homK]. Qed.

Lemma isomK (a b : C) (f : {isom a -> b}) : inv_hom f \@ f =m= idfun.
Proof. exact: homK. Qed.

Lemma isom_invK (a b : C) (f : {isom a -> b}) : f \@ inv_hom f =m= idfun.
Proof. exact: inv_homK. Qed.

Lemma comp_isom_inj (a b c : C) (f : {isom a -> b}) (g1 g2 : {hom b -> c}) :
  g1 \@ f =m= g2 \@ f -> g1 =m= g2.
Proof.
move=> eq; rewrite -(hom_compId g1) -(hom_compId g2) -(isom_invK f).
by rewrite -!homcompA eq.
Qed.

Lemma isom_comp_inj (a b c : C) (f1 f2 : {hom a -> b}) (g : {isom b -> c}) :
  g \@ f1 =m= g \@ f2 -> f1 =m= f2.
Proof.
move=> eq; rewrite -(hom_Idcomp f1) -(hom_Idcomp f2) -(isomK g).
by rewrite !homcompA eq.
Qed.

End ismorphism_lemmas.

HB.factory Record hasInverse (C : category) (a b : C) (f : el a -> el b)
  of isHom C a b f := {
    mkinv : {hom b -> a};
    mkhomK : mkinv \@ f =m= idfun;
    mkinvK : f \@ mkinv =m= idfun;
  }.
HB.builders Context C a b f of hasInverse C a b f.
Lemma isom_mkhomK : cancel f mkinv.
Proof. exact: mkhomK. Qed.
Lemma isom_mkinvK : cancel mkinv f.
Proof. exact: mkinvK. Qed.
HB.instance Definition _:=
  isIsom.Build C a b f (isHom_inhom mkinv) isom_mkhomK isom_mkinvK.
HB.end.


Module FunctorLaws.
Section def.
Variable (C D : category).
Variable (F : C -> D) (actm : forall a b, {hom a -> b} -> {hom F a -> F b}).
Definition ext := forall a b (f g : {hom a -> b}),
    f =m= g -> actm f =m= actm g.
Definition id := forall a,
    actm [hom idfun] =m= ([hom idfun] : {hom F a -> F a}).
Definition comp := forall a b c (g : {hom b -> c}) (h : {hom a -> b}),
    actm (g \@ h) =m= (actm g \@ actm h).
End def.
End FunctorLaws.

HB.mixin Record isFunctor (C D : category) (F : C -> D) := {
    actm : forall a b, {hom a -> b} -> {hom F a -> F b} ;
    functor_ext_hom : FunctorLaws.ext actm ;
    functor_id_hom : FunctorLaws.id actm ;
    functor_comp_hom : FunctorLaws.comp actm
  }.
HB.structure Definition Functor C D := {F of isFunctor C D F}.

Arguments functor_ext_hom {C D s}.


Definition functor_phant (C D : category) of phant (C -> D) := Functor.type C D.
Arguments actm [C D] F [a b] f: rename.
Arguments functor_ext_hom [C D] F [a b] f: rename.
Notation "F # f" := (actm F f) : category_scope.
Notation "{ 'functor' fCD }" := (functor_phant (Phant fCD))
  (format "{ 'functor'  fCD }") : category_scope.

Add Parametric Morphism (C D : category) (F : {functor C -> D}) (A B : C):
  (@actm C D F A B) with
    signature (@eq_morphism C B A) ==> (@eq_morphism D (F B) (F A))
      as functor_mor.
Proof. exact: functor_ext_hom. Qed.

Record eq_functor (C D : category)
  (F : {functor C -> D}) (G : {functor C -> D}) : Prop := EqFunctor {
    pm : F =1 G;
    eq_transport : forall (A B : C) (f : {hom A  -> B}),
      transport_hom (pm A) (pm B) (F # f) =m= G # f
  }.
Notation "F =#= G" := (eq_functor F G).

Section functor_lemmas.
Variables (C D : category) (F : {functor C -> D}).

Lemma functor_id a : F # idfun =m= (idfun : {hom F a -> F a}).
Proof.
by move=> x; rewrite (functor_ext_hom _ _ _ (homfunK _)) functor_id_hom.
Qed.

Lemma functor_o a b c (g : {hom b -> c}) (h : {hom a -> b}) :
  F # (g \@ h) =m= F # g \@ F # h.
Proof. by move=> fa; rewrite functor_comp_hom. Qed.

Lemma functor_ext (G : {functor C -> D}) (eq : F =1 G) :
  (forall (A B : C) (f : {hom A -> B}),
      transport_hom (eq A) (eq B) (F # f) =m= G # f) -> F =#= G.
Proof. exact: EqFunctor. Qed.

End functor_lemmas.
Arguments functor_o [C D] F.


Section functor_equality.

Variables (C D : category).

Lemma eq_functor_refl (F : {functor C -> D}) : F =#= F.
Proof. exact: (functor_ext (eq := (fun=> _))). Qed.

Lemma eq_functor_trans (F G H : {functor C -> D}) :
  F =#= G -> G =#= H -> F =#= H.
Proof.
move=> [pmFG eqFG] [pmGH eqGH].
apply: (functor_ext (eq := fun A => eq_trans (pmFG A) (pmGH A))) => A B f.
rewrite -transport_hom_trans /= -eqGH /=.
exact/transport_homE/eqFG.
Qed.

Lemma eq_functor_sym (F G : {functor C -> D}) : F =#= G -> G =#= F.
Proof.
move=> [pm eq].
apply: (functor_ext (eq := fun A => esym (pm A))) => A B f.
apply (transport_hom_inj (pa := pm A) (pb := pm B)).
rewrite {}eq; move: (G # f) => {f}.
by case:_/(pm B); case:_/(pm A).
Qed.

Add Parametric Relation : {functor C -> D} (@eq_functor C D)
    reflexivity proved by eq_functor_refl
    symmetry proved by  eq_functor_sym
    transitivity proved by eq_functor_trans
    as eq_functor_equiv.

End functor_equality.


Section functor_o_head.

Import comps_notation.
Variable C D : category.

Lemma functor_o_head (a b c : C)
  (g : {hom b -> c}) (h : {hom a -> b}) d (F : {functor C -> D})
    (k : {hom d -> F a}) :
  (F # (g \@ h)) \@ k =m= [\@ F # g, F # h, k].
Proof. by rewrite functor_comp_hom. Qed.

End functor_o_head.
Arguments functor_o_head [C D a b c g h d] F.


Section functorid.

Variables C : category.
Definition id_f (A B : C) (f : {hom A -> B}) := f.

Fact id_ext : FunctorLaws.ext id_f. Proof. by []. Qed.
Fact id_id : FunctorLaws.id id_f. Proof. by []. Qed.
Fact id_comp : FunctorLaws.comp id_f. Proof. by []. Qed.
HB.instance Definition _ := isFunctor.Build _ _ idfun id_ext id_id id_comp.

Definition FId : {functor C -> C} := idfun.
Lemma FIdf (A B : C) (f : {hom A -> B}) : FId # f = f.
Proof. by []. Qed.

End functorid.
Arguments FId {C}.


Section functorcomposition.

Variables C0 C1 C2 : category.
Variables (F : {functor C1 -> C2}) (G : {functor C0 -> C1}).
Definition functorcomposition a b :=
  fun h : {hom[C0] a -> b} => (F # (G # h) : {hom[C2] F (G a) -> F (G b)}).

Fact functorcomposition_ext : FunctorLaws.ext functorcomposition.
Proof.
by move=> A B f g eq_fg; do 2 apply: functor_ext_hom.
Qed.
Fact functorcomposition_id : FunctorLaws.id functorcomposition.
Proof.
rewrite /functorcomposition => A.
rewrite (functor_ext_hom _ _ _ (functor_id (a := A))).
exact: functor_id.
Qed.
Fact functorcomposition_comp : FunctorLaws.comp functorcomposition.
Proof.
rewrite /functorcomposition => a b c g h.
rewrite (functor_ext_hom _ _ _ (functor_comp_hom _ _ _ _ _)).
exact: functor_comp_hom.
Qed.
HB.instance Definition _ :=
  isFunctor.Build C0 C2 (F \o G)
    functorcomposition_ext functorcomposition_id functorcomposition_comp.
End functorcomposition.
Notation "F \O G" := ([the {functor _ -> _} of F \o G]) : category_scope.


Section functorcomposition_lemmas.
Variables (C0 C1 C2 C3 : category).

Lemma FCompE (F : {functor C1 -> C2}) (G : {functor C0 -> C1}) a b (k : {hom a -> b}) :
  (F \O G) # k = F # (G # k).
Proof. by []. Qed.

Lemma FCompId (F : {functor C0 -> C1}) : F \O FId =#= F.
Proof. exact: (functor_ext (eq := fun=> _)). Qed.

Lemma FIdComp (F : {functor C0 -> C1}) : FId \O F =#= F.
Proof. exact: (functor_ext (eq := fun=> _)). Qed.

Lemma FCompA
  (F : {functor C2 -> C3}) (G : {functor C1 -> C2}) (H : {functor C0 -> C1}) :
  (F \O G) \O H =#= F \O (G \O H).
Proof. exact: (functor_ext (eq := fun=> _)). Qed.

End functorcomposition_lemmas.


Section functor_inv_hom.

Variables (C D : category) (a b : C) (h : {isom a -> b}) (F : {functor C -> D}).

Let hom := F # h : _ -> _.
HB.instance Definition _ := Hom.on hom.
Local Lemma homE : hom =m= F # h.
Proof. by []. Qed.
Fact functor_homK : F # (inv_hom h) \@ hom =m= idfun.
Proof. by rewrite homE -functor_o isomK functor_id. Qed.
Fact functor_inv_homK : hom \@ F # (inv_hom h) =m= idfun.
Proof. by rewrite homE -functor_o isom_invK functor_id. Qed.

HB.instance Definition _ :=
  hasInverse.Build D (F a) (F b) hom functor_homK functor_inv_homK.

Lemma functor_inv_homE : inv_hom hom = F # (inv_hom h).
Proof. by []. Qed.

End functor_inv_hom.


Notation "F ~~> G" := (forall a, {hom F a -> G a}) : category_scope.
Definition naturality (C D : category) (F G : {functor C -> D}) (f : F ~~> G) :=
  forall (a b : C) (h : {hom a -> b}), (G # h) \@ (f a) =m= (f b) \@ (F # h).
Arguments naturality [C D].
HB.mixin Record isNatural
    (C D : category) (F G : {functor C -> D}) (f : F ~~> G) :=
  { natural : naturality F G f }.
#[short(type=nattrans)]
HB.structure Definition Natural (C D : category) (F G : {functor C -> D}) :=
  { f of isNatural C D F G f }.
Arguments natural [C D F G] phi : rename.
Notation "F ~> G" := (nattrans F G) : category_scope.


Section natural_transformation_lemmas.

Import comps_notation.
Variables (C D : category) (F G : {functor C -> D}).

Lemma natural_head (phi : F ~> G) a b c (h : {hom a -> b}) (f : {hom c -> F a}) :
  [\@ G # h, phi a, f] =m= [\@ phi b, F # h, f].
Proof. by rewrite -!homcompA (natural phi). Qed.

Definition eq_nattrans (phi psi : F ~> G) := forall a : C, (phi a =m= psi a).
Notation "p =%= q" := (eq_nattrans p q).

Lemma eq_nattrans_refl (phi : F ~> G) : phi =%= phi.
Proof. by []. Qed.
Lemma eq_nattrans_sym (phi psi : F ~> G) : phi =%= psi -> psi =%= phi.
Proof. by move=> eq a /[!eq]. Qed.
Lemma eq_nattrans_trans (phi psi ksi : F ~> G) :
  phi =%= psi -> psi =%= ksi -> phi =%= ksi.
Proof. by move=> eqp eqk a /[!eqp] /[!eqk]. Qed.

Add Parametric Relation : (F ~> G) eq_nattrans
    reflexivity proved by eq_nattrans_refl
    symmetry proved by  eq_nattrans_sym
    transitivity proved by eq_nattrans_trans
    as eq_nattrans_equiv.

End natural_transformation_lemmas.
Arguments natural_head [C D F G].
Notation "p =%= q" := (eq_nattrans p q).


Section id_natural_transformation.

Variables (C D : category) (F : {functor C -> D}).
Definition unnattrans_id := fun (a : C) => [hom (@idfun (el (F a)))].
Fact natural_id : naturality _ _ unnattrans_id.
Proof. by []. Qed.
HB.instance Definition _ := isNatural.Build C D F F unnattrans_id natural_id.
Definition NId : F ~> F := [the _ ~> _ of unnattrans_id].
Lemma NIdE : NId  = (fun a => [hom idfun]) :> (_ ~~> _).
Proof. by []. Qed.
End id_natural_transformation.


Module NEq.
Section def.

Import comps_notation.
Variables (C D : category) (F G : {functor C -> D}).
Variable (Iobj : forall c, F c = G c).
Local Notation tc := (transport_codom (Iobj _)).
Local Notation td := (transport_dom (esym (Iobj _))).
Variable (Imor : forall a b (f : {hom a -> b}), tc (F # f) =m= td (G # f)).
(* tc (F # f) and td (G # f) : {hom F a -> G b}) *)
Definition f : F ~~> G := fun (c : C) => tc [hom idfun].

Fact natural : naturality F G f.
Proof.
by move=> a b h; rewrite -transport_codomF Imor transport_domF esymK.
Qed.
HB.instance Definition _ := isNatural.Build C D F G f natural.
Definition n : F ~> G := [the _ ~> _ of f].

End def.

Module Exports.
Arguments n [C D] : simpl never.
Notation NEq := n.
Lemma NEqE C D F G Iobj Imor : @NEq C D F G Iobj Imor =
  (fun a => transport_codom (Iobj _) [hom idfun]) :> (_ ~~> _).
Proof. by []. Qed.
End Exports.
End NEq.
Export NEq.Exports.
Notation "[ 'NEq' F , G ]" :=
  (NEq F G (fun a => erefl) (fun a b f x => erefl))
    (at level 0, format "[ 'NEq'  F ,  G ]") : category_scope.

(* Inverse of a natural isomorphism *)
Lemma natural_inv (C D : category) (F G : {functor C -> D})
  (T : forall a, {isom F a -> G a}) :
  naturality F G T -> naturality G F (fun a => inv_hom (T a)).
Proof.
move=> T_nat A B f; apply: (isom_comp_inj (g := T B)).
pose Tn := Natural.Pack (Natural.Class (isNatural.Build C D F G T T_nat)).
have /= <- := natural_head Tn A B _ f (inv_hom (T A)).
by rewrite isom_invK -homcompA isom_invK hom_compId hom_Idcomp.
Qed.


Section vertical_composition.

Variables (C D : category) (F G H : {functor C -> D}).
Variables (g : G ~> H) (f : F ~> G).
Definition vcomp := fun a => g a \@ f a.

Fact natural_vcomp : naturality _ _ vcomp.
Proof.
by rewrite /vcomp => A B h; rewrite -homcompA natural homcompA natural.
Qed.
HB.instance Definition _ := isNatural.Build C D F H
  vcomp natural_vcomp.
Definition VComp : F ~> H := [the F ~> H of vcomp].

End vertical_composition.
Notation "f \v g" := (VComp f g).


Section vcomp_lemmas.

Variables (C D : category) (F G H I : {functor C -> D}).
Variables (h : H ~> I) (g : G ~> H) (f : F ~> G).

Lemma VCompId : f \v NId F =%= f.
Proof. by []. Qed.
Lemma VIdComp : NId G \v f =%= f.
Proof. by []. Qed.
Lemma VCompA : (h \v g) \v f =%= h \v (g \v f).
Proof. by []. Qed.
Lemma VCompE_nat : g \v f = (fun a => g a \@ f a) :> (_ ~~> _).
Proof. by []. Qed.
Lemma VCompE a : (g \v f) a = g a \@ f a.
Proof. by []. Qed.

End vcomp_lemmas.


Section horizontal_composition.

Variables (C D E : category) (F G : {functor C -> D}) (F' G' : {functor D -> E}).
Variables (s : F ~> G) (t : F' ~> G').
Definition hcomp : F' \O F ~~> G' \O G :=
  fun (c : C) => t (G c) \@ F' # s c.

Fact natural_hcomp : naturality (F' \O F) (G' \O G) hcomp.
Proof.
rewrite /hcomp => c0 c1 h /=.
by rewrite !FCompE -!homcompA (natural t) !homcompA -!functor_o (natural s).
Qed.
HB.instance Definition _ := isNatural.Build C E (F' \O F) (G' \O G)
  hcomp natural_hcomp.
Definition HComp : F' \O F ~> G' \O G := [the _ ~> _ of hcomp].

End horizontal_composition.
Notation "f \h g" := (locked (HComp g f)).


Section hcomp_extensionality_lemmas.

Variables (C D E : category) (F G : {functor C -> D}) (F' G' : {functor D -> E}).
Variables (s : F ~> G) (t : F' ~> G').

Lemma HCompE_def : t \h s = HComp s t. Proof. by unlock. Qed.
Lemma HCompE c : (t \h s) c =m= t (G c) \@ F' # s c.
Proof. by unlock. Qed.
Lemma HCompE_alt c : (t \h s) c =m= G' # (s c) \@ t (F c).
Proof. by rewrite HCompE natural. Qed.

End hcomp_extensionality_lemmas.


Section hcomp_id_assoc_lemmas.

Import comps_notation.
Variables C D E Z : category.
Variables
  (F   G   : {functor C -> D})
  (F'  G'  : {functor D -> E})
  (F'' G'' : {functor E -> Z}).
Variables (s : F ~> G) (t : F' ~> G') (u : F'' ~> G'').

Lemma HCompId c : (t \h NId F) c =m= t (F c).
Proof. by rewrite HCompE NIdE functor_id. Qed.
Lemma HIdComp c : (NId G' \h s) c =m= G' # s c.
Proof. by rewrite HCompE NIdE. Qed.
Lemma HCompA c : ((u \h t) \h s) c =m= (u \h (t \h s)) c.
Proof. by rewrite !HCompE homcompA -!functor_o. Qed.

End hcomp_id_assoc_lemmas.


Section hcomp_lemmas.

Variables (C D E : category).
Variables (F G : {functor C -> D}) (F' G' : {functor D -> E}).
Variables (s : F ~> G) (t : F' ~> G').

(* higher level horizontal composition is a vertical composition of
   horizontal compositions *)
Lemma HComp_VH : t \h s =%= (t \h NId G) \v (NId F' \h s).
Proof. by move=> a; rewrite VCompE HCompE /= HIdComp HCompId. Qed.
Lemma HComp_VH_aux : t \h s =%= (NId G' \h s) \v (t \h NId F).
Proof. by move=> a; rewrite VCompE HCompE /= HIdComp HCompId natural. Qed.
Lemma NIdFId c : NId (@FId C) c = [hom idfun].
Proof. by []. Qed.
Lemma NIdFComp : NId (F' \O F) =%= NId F' \h NId F.
Proof. by move=> c; rewrite HCompE /= hom_Idcomp functor_id. Qed.

(* horizontal and vertical compositions interchange *)
Variables (H : {functor C -> D}) (H' : {functor D -> E}).
Variables (s' : G ~> H) (t' : G' ~> H').

Lemma HCompACA : (t' \h s') \v (t \h s) =%= (t' \v t) \h (s' \v s).
Proof.
move=> c; rewrite !(HCompE, VCompE) !homcompA.
by rewrite -(natural t _ (H c)) functor_o homcompA natural.
Qed.

End hcomp_lemmas.


(* Category equivalence *)
Record equivalence_category (C D : category)
  (F : {functor C -> D}) (G : {functor D -> C}) := EquivalenceCategory {
     eqFGId : forall a, {isom (F \O G) a -> FId a};
     eqGFId : forall a, {isom (G \O F) a -> FId a};
     natural_eqFGId : naturality (F \O G) FId eqFGId;
     natural_eqGFId : naturality (G \O F) FId eqGFId;
}.

Section equiv_cat_interface.

Variables (C D : category) (F : {functor C -> D}) (G : {functor D -> C}).
Variable (eq : equivalence_category F G).
Definition eqFGId_map : (F \O G) ~~> FId := eqFGId eq.
Definition eqGFId_map : (G \O F) ~~> FId := eqGFId eq.
Definition eqIdFG_map : FId ~~> (F \O G) := fun a => inv_hom (eqFGId eq a).
Definition eqIdGF_map : FId ~~> (G \O F) := fun a => inv_hom (eqGFId eq a).
HB.instance Definition _ :=
  isNatural.Build D D (F \O G) FId eqFGId_map (natural_eqFGId eq).
HB.instance Definition _ :=
  isNatural.Build C C (G \O F) FId eqGFId_map (natural_eqGFId eq).
HB.instance Definition _ :=
  isNatural.Build D D FId (F \O G) eqIdFG_map
    (natural_inv (natural_eqFGId eq)).
HB.instance Definition _ :=
  isNatural.Build C C FId (G \O F) eqIdGF_map
    (natural_inv (natural_eqGFId eq)).

Definition eqFGId_trans : (F \O G) ~> FId := eqFGId_map.
Definition eqGFId_trans : (G \O F) ~> FId := eqGFId_map.
Definition eqIdFG_trans : FId ~> (F \O G) := eqIdFG_map.
Definition eqIdGF_trans : FId ~> (G \O F) := eqIdGF_map.

End equiv_cat_interface.


Definition EquivRefl (C : category) :=
  @EquivalenceCategory C C (@FId C) (@FId C) (fun _ => idfun) (fun _ => idfun)
    (@natural_id _ _ _) (@natural_id _ _ _).
Definition EquivSym
  (C D : category) (F : {functor C -> D}) (G : {functor D -> C})
  (eq : equivalence_category F G)
  := @EquivalenceCategory D C G F (eqGFId eq) (eqFGId eq)
                         (natural_eqGFId eq) (natural_eqFGId eq).


Module EquivCatTrans.

Section Defs.

Variables (C D E : category).
Variables (F : {functor C -> D}) (G : {functor D -> C})
          (H : {functor D -> E}) (I : {functor E -> D}).
Variable (eq : equivalence_category F G) (eq' : equivalence_category H I).

Definition trans_eqFGId : (H \O F) \O (G \O I) ~> FId :=
  eqFGId_trans eq'
    \v [NEq H \O FId \O I, H \O I]
    \v (NId H \h eqFGId_trans eq \h NId I)
    \v [NEq (H \O F) \O (G \O I), H \O (F \O G) \O I].
Definition fun_eqFGId (e : E) : _ -> _ := trans_eqFGId e.
Definition trans_eqIdFG : FId ~> (H \O F) \O (G \O I):=
  [NEq H \O (F \O G) \O I, (H \O F) \O (G \O I)]
  \v (NId H \h eqIdFG_trans eq \h NId I)
  \v [NEq H \O I, H \O FId \O I]
  \v (eqIdFG_trans eq').
Definition fun_eqIdFG (e : E) : _ -> _ := trans_eqIdFG e.

Fact fun_eqFGIdK (e : E) : cancel (@fun_eqFGId e) (@fun_eqIdFG e).
Proof.
(* TODO: point-free proof ? *)
move=> x; rewrite /fun_eqFGId /fun_eqIdFG /= homK !HCompId !HIdComp.
by rewrite -functor_inv_homE homK.
Qed.
Fact fun_eqIdFGK (e : E) : cancel (trans_eqIdFG e) (trans_eqFGId e).
Proof.
(* TODO: point-free proof ? *)
move=> x; rewrite /fun_eqFGId /fun_eqIdFG /= !HCompId !HIdComp /=.
by rewrite -functor_inv_homE !inv_homK.
Qed.
HB.instance Definition _ (e : E) := Hom.on (@fun_eqFGId e).
HB.instance Definition _ (e : E) :=
  isIsom.Build _ _ _ (@fun_eqFGId e) (isHom_inhom (@fun_eqIdFG e))
               (@fun_eqFGIdK e) (@fun_eqIdFGK e).


Definition trans_eqGFId : (G \O I) \O (H \O F) ~> FId :=
  eqGFId_trans eq
    \v [NEq G \O FId \O F, G \O F]
    \v (NId G \h eqGFId_trans eq' \h NId F)
    \v [NEq (G \O I) \O (H \O F), G \O (I \O H) \O F].
Definition fun_eqGFId (c : C) : _ -> _ := (trans_eqGFId c).
Definition trans_eqIdGF : FId ~> (G \O I) \O (H \O F) :=
  [NEq G \O (I \O H) \O F, (G \O I) \O (H \O F)]
  \v (NId G \h eqIdGF_trans eq' \h NId F)
  \v [NEq G \O F, G \O FId \O F]
  \v (eqIdGF_trans eq).
Definition fun_eqIdGF (c : C) : _ -> _ := trans_eqIdGF c.

Fact fun_eqGFIdK (c : C) : cancel (@fun_eqGFId c) (@fun_eqIdGF c).
Proof.
(* TODO: point-free proof ? *)
move=> x; rewrite /fun_eqGFId /fun_eqIdGF /= homK !HCompId !HIdComp.
by rewrite -functor_inv_homE homK.
Qed.
Fact fun_eqIdGFK (c : C) : cancel (@fun_eqIdGF c) (@fun_eqGFId c).
Proof.
(* TODO: point-free proof ? *)
move=> x; rewrite /fun_eqGFId /fun_eqIdGF /= !HCompId !HIdComp.
by rewrite -functor_inv_homE FCompE FIdf /= !inv_homK.
Qed.
HB.instance Definition _ (c : C) := Hom.on (@fun_eqGFId c).
HB.instance Definition _ (c : C) :=
  isIsom.Build _ _ _ (@fun_eqGFId c) (isHom_inhom (@fun_eqIdGF c))
               (@fun_eqGFIdK c) (@fun_eqIdGFK c).

Definition equiv : equivalence_category (H \O F) (G \O I) :=
  @EquivalenceCategory C E (H \O F) (G \O I)
    fun_eqFGId fun_eqGFId (natural trans_eqFGId) (natural trans_eqGFId).

End Defs.

End EquivCatTrans.
Definition EquivTrans := EquivCatTrans.equiv.


Section EquivLemmas.

Variables (C D : category) (F : {functor C -> D}) (G : {functor D -> C}).
Variable (eq : equivalence_category F G).

Lemma EquivSymK : EquivSym (EquivSym eq) = eq.
Proof. by case: eq. Qed.

End EquivLemmas.



(* adjoint functor *)
(* We define adjointness F -| G in terms of its unit and counit. *)
Module TriangularLaws.
Section triangularlaws.
Variables (C D : category) (F : {functor C -> D}) (G : {functor D -> C}).
Variables (eta : FId ~> G \O F) (eps : F \O G ~> FId).
Definition left := forall c, eps (F c) \@ F # (eta c) =m= idfun.
Definition right := forall d, G # (eps d) \@ eta (G d) =m= idfun.
End triangularlaws.
End TriangularLaws.

Module AdjointFunctors.
Section def.
Variables (C D : category) (F : {functor C -> D}) (G : {functor D -> C}).
Record t := mk {
  eta : FId ~> G \O F ;
  eps : F \O G ~> FId ;
  triL : TriangularLaws.left eta eps ;
  triR : TriangularLaws.right eta eps
}.
End def.
Section lemmas.
Local Notation "F -| G" := (t F G).
Variables (C D : category) (F : {functor C -> D}) (G : {functor D -> C}).
Variable A : F -| G.

Definition hom_iso c d : {hom F c -> d} -> {hom c -> G d} :=
  fun h => (G # h) \@ (eta A c).

Definition hom_inv c d : {hom c -> G d} -> {hom F c -> d} :=
  fun h => (eps A d) \@ (F # h).

Import comps_notation.

Lemma hom_isoK (c : C) (d : D) (f : {hom F c -> d}) :
  hom_inv (hom_iso f) =m= f.
Proof.
rewrite /hom_inv /hom_iso /= functor_o -!FCompE -homcompA /=.
by rewrite -(natural (eps A)) homcompA triL.
Qed.
Lemma hom_invK (c : C) (d : D) (g : {hom c -> G d}) :
  hom_iso (hom_inv g) =m= g.
Proof.
rewrite /hom_inv /hom_iso /= functor_o -!FCompE homcompA /=.
by rewrite (natural (eta A)) -homcompA triR.
Qed.
Lemma hom_iso_inj (c : C) (d : D) (f g : {hom F c -> d}) :
  hom_iso f =m= hom_iso g -> f =m= g.
Proof.
by move=> eq; rewrite -(hom_isoK f) -(hom_isoK g) /hom_inv eq.
Qed.
Lemma hom_inv_inj (c : C) (d : D) (f g : {hom c -> G d}) :
  hom_inv f =m= hom_inv g -> f =m= g.
Proof.
by move=> eq; rewrite -(hom_invK f) -(hom_invK g) /hom_iso eq.
Qed.

Lemma eta_hom_iso (c : C) : eta A c =m= hom_iso idfun.
Proof. by rewrite /hom_iso => x /=; rewrite functor_id. Qed.
Lemma eps_hom_inv (d : D) : eps A d =m= hom_inv idfun.
Proof. by rewrite /hom_iso => x /=; rewrite functor_id. Qed.

(*
Lemma ext (B : F -| G) : eta A =1 eta B -> eps A =1 eps B -> A =1 B.
Proof.
move: A B => [? ? ? ?] [? ? ? ?] /= ? ?; subst.
congr mk; exact/proof_irr.
Qed.
*)
(*
Lemma left_unique (F' : functor C D) (B : adjunction F' G) :
  exists phi, phi : natural_isomorphism F F'.
Lemma right_unique (G' : functor D C) (B : adjunction F G') :
  exists phi, phi : natural_isomorphism G G'.
*)

End lemmas.
Arguments hom_isoK [C D F G].
Arguments hom_invK [C D F G].
Arguments hom_iso_inj [C D F G].
Arguments hom_inv_inj [C D F G].
End AdjointFunctors.
Notation "F -| G" := (AdjointFunctors.t F G).


Module AdjComp.
Section def.

Import comps_notation.
Variables C0 C1 C2 : category.
Variables (F0 : {functor C0 -> C1}) (G0 : {functor C1 -> C0}).
Variables (F1 : {functor C1 -> C2}) (G1 : {functor C2 -> C1}).
Variables
  (eta0 : FId ~> G0 \O F0) (eta1 : FId ~> G1 \O F1)
  (eps0 : F0 \O G0 ~> FId) (eps1 : F1 \O G1 ~> FId)
  (triL0 : TriangularLaws.left eta0 eps0)
  (triL1 : TriangularLaws.left eta1 eps1)
  (triR0 : TriangularLaws.right eta0 eps0)
  (triR1 : TriangularLaws.right eta1 eps1).

Let F := F1 \O F0.
Let G := G0 \O G1.

Definition Eta : FId ~> G \O F :=
  [NEq G0 \O (G1 \O F1) \O F0 , G \O F]
    \v (NId G0 \h eta1 \h NId F0)
    \v [NEq G0 \O F0 , G0 \O FId \O F0]
    \v eta0.
Lemma EtaE a : Eta a =m= G0 # (eta1 (F0 a)) \@ (eta0 a).
(* TODO: point-free proof ? *)
Proof. by move=> x /=; rewrite HCompId HIdComp. Qed.
Lemma EtaE_hom a : Eta a =m= G0 # (eta1 (F0 a)) \@ (eta0 a).
(* TODO: point-free proof ? *)
Proof. by move=> x; rewrite EtaE. Qed.

Definition Eps : F \O G ~> FId :=
  (eps1)
    \v [NEq F1 \O FId \O G1 , F1 \O G1]
    \v (NId F1 \h eps0 \h NId G1)
    \v [NEq F \O G , (F1 \O (F0 \O G0)) \O G1].
Lemma EpsE a : Eps a =m= (eps1 _) \@ F1 # (eps0 (G1 a)).
(* TODO: point-free proof ? *)
Proof. by move=> x /=; rewrite HCompId HIdComp. Qed.
Lemma EpsE_hom a : Eps a =m= (eps1 _) \@ F1 # (eps0 (G1 a)).
(* TODO: point-free proof ? *)
Proof. by move=> x; rewrite EpsE. Qed.

Lemma triL : TriangularLaws.left Eta Eps.
Proof.
move=> c; rewrite EpsE EtaE_hom homcompA (functor_o F) /F.
rewrite -(functor_o_head F1).
set X := (X in F1 # X).
evar (TY : Type).
evar (Y : TY).
have -> : X =m= Y by rewrite /X -(natural eps0) => x; apply: erefl.
rewrite (functor_o_head F1) FIdf.
rewrite -!homcompA triL1 hom_Idcomp.
by rewrite -(functor_o F1) triL0 functor_id.
Qed.

(* [\o eps (F c), F # eta c] =1 idfun *)
Lemma triR : TriangularLaws.right Eta Eps.
Proof.
move=> c.
rewrite EpsE_hom EtaE (functor_o_head G) -(functor_o_head G0 (eta0 _)).
(* FRAGILE!
   simpl here breaks the notation and renders the following set X impossible *)
set X := (X in G0 # X).
evar (TY : Type).
evar (Y : TY).
have -> : G0 # X =m= G0 # Y
  by rewrite /X /= (natural eta1) => x; exact: erefl.
rewrite (functor_o G0) homcompA FIdf triR0 hom_compId.
by rewrite -(functor_o G0) triR1 functor_id.
Qed.

End def.

Module Exports.
Section adj_comp.
Variables (C0 C1 C2 : category).
Variables (F : {functor C0 -> C1}) (G : {functor C1 -> C0}) (A0 : F -| G).
Variables (F' : {functor C1 -> C2}) (G' : {functor C2 -> C1}) (A1 : F' -| G').
Definition adj_comp := AdjointFunctors.mk
  (triL (AdjointFunctors.triL A0) (AdjointFunctors.triL A1))
  (triR (AdjointFunctors.triR A0) (AdjointFunctors.triR A1)).
End adj_comp.
End Exports.
End AdjComp.
Export AdjComp.Exports.


(** Adjonction through a natural isomorhism *)
Module Adjoint_NatIsom.
Section adjNatIsom.

Variables (C D : category) (F : {functor C -> D}) (G G' : {functor D -> C}).
Variables (GG' : G ~> G') (G'G : G' ~> G).
Hypothesis GG'K : forall d, cancel (GG' d) (G'G d).
Hypothesis G'GK : forall d, cancel (G'G d) (GG' d).
Hypothesis adj : F -| G.

Definition eps := (AdjointFunctors.eps adj) \v (NId F \h G'G).
Definition eta := (GG'\h NId F) \v (AdjointFunctors.eta adj).

Fact triL : TriangularLaws.left eta eps.
Proof.
rewrite /eps /eta => A.
have:= AdjointFunctors.triL adj.
move: (AdjointFunctors.eps adj) => eps.
move: (AdjointFunctors.eta adj) => eta <-.
rewrite !VCompE homcompA HIdComp /= -functor_o.
rewrite HCompId -homcompA.
(* TODO: point-free proof ? *)
have -> : G'G (F A) \@ GG' (F A) =m= idfun by move=> x /=; rewrite GG'K.
by rewrite functor_o functor_id hom_Idcomp.
Qed.

Fact triR : TriangularLaws.right eta eps.
Proof.
rewrite /eps /eta => A.
have:= AdjointFunctors.triR adj.
move: (AdjointFunctors.eps adj) => eps.
move: (AdjointFunctors.eta adj) => eta triR.
rewrite !(HIdComp, HCompId, VCompE) /= functor_o !homcompA.
rewrite (natural_head GG' (F (G' A))) -FCompE (natural eta) FIdf.
rewrite (natural_head GG') -(homcompA (G # _)) triR.
(* TODO: point-free proof ? *)
by rewrite hom_Idcomp => x /=; rewrite G'GK.
Qed.

End adjNatIsom.

Module Exports.
Section adj_nat.

Variables (C D : category) (F : {functor C -> D}) (G G' : {functor D -> C}).
Variables (GG' : G ~> G') (G'G : G' ~> G).
Hypothesis GG'K : forall d, cancel (GG' d) (G'G d).
Hypothesis G'GK : forall d, cancel (G'G d) (GG' d).
Hypothesis adj : F -| G.

Definition adj_natisomR : F -| G' :=
  AdjointFunctors.mk (triL GG'K adj) (triR G'GK adj).

End adj_nat.
End Exports.
End Adjoint_NatIsom.
Export Adjoint_NatIsom.Exports.


Module JoinLaws.
Section join_laws.
Variables (C : category) (M : {functor C -> C}) .
Variables (ret : FId ~~> M) (join : M \O M ~~> M).
Definition left_unit  := forall a, join a \@ ret (M a) =m= idfun.
Definition right_unit := forall a, join a \@ M # ret a =m= idfun.
Definition associativity :=
  forall a, join a \@ M # join a =m= join a \@ join (M a).
End join_laws.
End JoinLaws.

Module BindLaws.
Section bindlaws.
Variables (C : category) (M : C -> C).
Variable b : forall A B, {hom A -> M B} -> {hom M A -> M B}.
Local Notation "m >>= f" := (b f m).

Fact associative_aux x y z (f : {hom x -> M y}) (g : {hom y -> M z}) :
  (fun w => (f w >>= g)) =1 (b g \@ f).
Proof. by []. Qed.
Definition associative :=
  forall A B C (f : {hom A -> M B}) (g : {hom B -> M C}),
       b g \@ b f =m= b (b g \@ f).
Definition left_neutral (r : forall A, {hom A -> M A}) :=
  forall A B (f : {hom A -> M B}), b f \@ r A =m= f.
Definition right_neutral (r : forall A, {hom A -> M A}) :=
  forall A, b (r A) =m= idfun.
End bindlaws.
End BindLaws.


Section bind_lemmas.

Variables (C : category) (M : C -> C).
Variable b : forall A B, {hom A -> M B} -> {hom M A -> M B}.
Local Notation "m >>= f" := (b f m).

Lemma bind_left_neutral_hom_fun (r : forall A, {hom A -> M A}) :
  BindLaws.left_neutral b r
  <-> forall A B (f : {hom A -> M B}), (b f \@ r A) =m= f.
Proof. by []. Qed.
Lemma bind_right_neutral_hom_fun (r : forall A, {hom A -> M A}) :
  BindLaws.right_neutral b r <-> forall A (m : el (M A)), m >>= r _ = m.
Proof. by []. Qed.
Lemma associative_hom_fun :
  BindLaws.associative b
  <-> forall A B C (m : el (M A)) (f : {hom A -> M B}) (g : {hom B -> M C}),
  (m >>= f) >>= g = m >>= (b g \@ f).
Proof. by split => [H U V W m f g | H U V W f g m]; exact: H. Qed.

End bind_lemmas.


HB.mixin Record isMonad (C : category) (M : C -> C) of @Functor C C M := {
  ret : FId ~> [the {functor C -> C} of M] ;
  join : [the {functor C -> C} of M] \O [the {functor C -> C} of M] ~>
         [the {functor C -> C} of M] ;
  bind : forall (a b : C), {hom a -> M b} -> {hom M a -> M b} ;
  bind_ext : forall (a b : C) (f g : {hom a -> M b}),
    f =m= g -> bind a b f =m= bind a b g;
  bindE : forall (a b : C) (f : {hom a -> M b}) (m : el (M a)),
    bind a b f m = join b (([the {functor C -> C} of M] # f) m) ;
  joinretM : JoinLaws.left_unit ret join ;
  joinMret : JoinLaws.right_unit ret join ;
  joinA : JoinLaws.associativity join
}.
#[short(type=monad)]
HB.structure Definition Monad (C : category) :=
  {M of isMonad C M & isFunctor C C M}.
Arguments bind {C M a b} : rename, simpl never.
Notation "m >>= f" := (bind f m).


Section monad_interface.

Variable (C : category) (M : monad C).
(* *_head lemmas are for [fun of f] \o ([fun of g] \o ([fun of h] \o ..))*)

Import comps_notation.
Lemma joinretM_head a (c : C) (f : {hom c -> M a}) :
  [\@ join _, ret _, f] =m= f.
Proof. by rewrite -homcompA joinretM. Qed.
Lemma joinMret_head a (c : C) (f : {hom c -> M a}) :
  [\@ join _, M # ret _, f] =m= f.
Proof. by rewrite -homcompA joinMret. Qed.
Lemma joinA_head a (c : C) (f : {hom c -> M (M (M a))}) :
  [\@ join _, M # join _, f] =m= [\@ join _, join _, f].
Proof. by rewrite -homcompA joinA. Qed.

End monad_interface.


HB.factory Record Monad_of_ret_join (C : category) (M : C -> C)
           of @Functor C C M := {
  ret : FId ~> [the {functor C -> C} of M] ;
  join : M \O M ~> [the {functor C -> C} of M] ;
  joinretM : JoinLaws.left_unit ret join ;
  joinMret : JoinLaws.right_unit ret join ;
  joinA : JoinLaws.associativity join
}.
HB.builders Context C M of Monad_of_ret_join C M.
Let F := [the {functor _ -> _} of M].
Let bind (a b : C) (f : {hom a -> M b}) : {hom M a -> M b} :=
      join _ \@ (F # f).
Let bind_ext (a b : C) (f g : {hom a -> M b}) :
  f =m= g -> bind f =m= bind g.
Proof. by rewrite /bind => /functor_ext_hom ->. Qed.
Let bindE (a b : C) (f : {hom a -> M b}) (m : el (M a)) :
    bind f m = join b (([the {functor C -> C} of M] # f) m).
Proof. by []. Qed.
HB.instance Definition _ :=
  isMonad.Build C M bind_ext bindE joinretM joinMret joinA.
HB.end.


(* Monads defined by ret and bind; M need not be a priori a functor *)
HB.factory Record Monad_of_ret_bind (C : category) (acto : C -> C) := {
  ret' : forall a, {hom a -> acto a} ;
  bind : forall (a b : C), {hom a -> acto b} -> {hom acto a -> acto b} ;
  bind_ext_hom : forall (a b : C) (f g : {hom a -> acto b}),
    f =m= g -> bind a b f =m= bind a b g;
  bindretf : BindLaws.left_neutral bind ret' ;
  bindmret : BindLaws.right_neutral bind ret' ;
  bindA : BindLaws.associative bind ;
}.
HB.builders Context C M of Monad_of_ret_bind C M.
Let fmap a b (f : {hom a -> b}) := bind [hom ret' b \o f].
Let bindretf_fun : (forall (a b : C) (f : {hom a -> M b}),
  bind f \@ ret' a =m= f).
Proof. by apply/bind_left_neutral_hom_fun/bindretf. Qed.
Let fmap_id : FunctorLaws.id fmap.
Proof. by move=> A; rewrite /fmap bind_ext_hom; last exact: bindmret. Qed.
Let fmap_ext : FunctorLaws.ext fmap.
Proof. by move=> A B f g eq; apply: bind_ext_hom; rewrite /= eq. Qed.
Let fmap_o : FunctorLaws.comp fmap.
Proof.
move=> a b c g h; rewrite /fmap.
rewrite [X in _ =m= X]bindA/=; apply: bind_ext_hom.
by rewrite -!homcompA bindretf_fun.
Qed.
HB.instance Definition _ := isFunctor.Build C C M fmap_ext fmap_id fmap_o.
Notation F := [the {functor _ -> _} of M].

Let ret'_naturality : naturality FId F ret'.
Proof. by move=> A B h; rewrite FIdf bindretf_fun. Qed.
HB.instance Definition _ := isNatural.Build _ _ FId F
  (ret' : FId ~~> M)(*NB: fails without this type constraint*) ret'_naturality.
Definition ret := [the FId ~> F of ret'].
Let join' : F \O F ~~> F := fun _ => bind [hom idfun].
Let fmap_bind a b c (f : {hom a ->b}) (g : {hom c ->F a}) :
  (fmap f) \@ (bind g) =m= bind (fmap f \@ g).
Proof. by rewrite /fmap bindA. Qed.
Let join'_naturality : naturality (F \O F) F join'.
Proof.
move=> A B h; rewrite /join /=.
rewrite fmap_bind bindA; apply: bind_ext_hom.
by rewrite -!homcompA bindretf_fun.
Qed.
HB.instance Definition _ := isNatural.Build _ _ _ _ _ join'_naturality.
Definition join := [the F \O F ~> F of join'].

Let bind_fmap a b c (f : {hom a -> b}) (g : {hom b -> F c}) :
  bind g \@ (fmap f) =m= bind (g \@ f).
Proof.
rewrite bindA /=; apply: bind_ext_hom.
by rewrite -!homcompA bindretf_fun.
Qed.
Lemma bindE (a b : C) (f : {hom a -> F b}) : bind f =m= join b \@ F # f.
Proof. by rewrite /join /= bind_fmap; apply: bind_ext_hom. Qed.
Lemma joinretM : JoinLaws.left_unit ret join.
Proof.
rewrite /join => A /=.
exact: bindretf_fun.
Qed.
Lemma joinMret : JoinLaws.right_unit ret join.
Proof.
rewrite /join => A /=.
rewrite bind_fmap -[X in _ =m= X]bindmret.
exact: bind_ext_hom.
Qed.
Lemma joinA : JoinLaws.associativity join.
Proof.
move=> A; rewrite /join /=.
rewrite bind_fmap /= bindA /=.
exact: bind_ext_hom.
Qed.
HB.instance Definition _ :=
  isMonad.Build C M bind_ext_hom bindE joinretM joinMret joinA.
HB.end.


Module _Monad_of_adjoint_functors.
Section def.

Import comps_notation.
Variables C D : category.
Variables (F : {functor C -> D}) (G : {functor D -> C}).
Variable A : F -| G.
Definition eps := AdjointFunctors.eps A.
Definition eta := AdjointFunctors.eta A.
Definition M := G \O F.
Definition join : M \O M ~~> M := fun a => G # (eps (F a)).
Definition ret : FId ~~> M := fun a => eta a.
Let triL := AdjointFunctors.triL A.
Let triR := AdjointFunctors.triR A.

Lemma naturality_ret : naturality FId M ret.
Proof. by move=> a b f; rewrite (natural eta). Qed.
HB.instance Definition _ := isNatural.Build C C FId M ret naturality_ret.
Lemma naturality_join : naturality (M \O M) M join.
Proof.
rewrite /join => a b h.
rewrite /M !FCompE -2!(@functor_o _ _ G) /=; apply: functor_ext_hom.
exact: (natural eps).
Qed.
HB.instance Definition _ := isNatural.Build C C (M \O M) M join naturality_join.

Let joinE : join = fun a => G # (@eps (F a)).
Proof. by []. Qed.
Let join_associativity' a : join a \@ join (M a) =m= join a \@ (M # join a).
Proof.
rewrite joinE -2!(@functor_o _ _ G) /=.
apply: functor_ext_hom.
exact: (natural eps).
Qed.
Lemma join_associativity : JoinLaws.associativity join.
Proof. by move=> a; rewrite join_associativity'. Qed.
Lemma join_left_unit : JoinLaws.left_unit ret join.
Proof. by move=> a; rewrite joinE triR. Qed.
Lemma join_right_unit :JoinLaws.right_unit ret join.
Proof.
move=> a; rewrite joinE /M FCompE /=.
by rewrite -(functor_o G) triL functor_id.
Qed.

HB.instance Definition _ :=
  Monad_of_ret_join.Build C (G \o F) join_left_unit join_right_unit join_associativity.

End def.


Definition build (C D : category)
           (F : {functor C -> D}) (G : {functor D -> C}) (A : F -| G) :=
  Monad.Pack (Monad.Class (category_Monad_of_ret_join__to__category_isMonad A)).

End _Monad_of_adjoint_functors.
Notation Monad_of_adjoint_functors := _Monad_of_adjoint_functors.build.
(* TODO: Can we turn this into a factory? *)

Lemma Monad_of_adjoint_functorsE (C D : category)
  (F : {functor C -> D}) (G : {functor D -> C}) (A : F -| G) :
  Monad_of_adjoint_functors A = G \O F :> {functor C -> C}.
Proof. by []. Qed.
