(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finfun bigop.
From mathcomp Require Import ssralg.


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
(*          {hom A, B} == the hom-set of morphisms from A to B, where A and B *)
(*                        are objects of a category C                         *)
(*             [hom f] == morphism corresponding to the function f            *)
(*                  CT := [the category of Type]                              *)
(*         FunctorLaws == module that defines the functor laws                *)
(*                  \O == functor composition                                 *)
(*             F ~~> G == forall a, {hom F a, G a}, which corresponds to a    *)
(*                        natural transformation when it satisfies the        *)
(*                        predicate naturality                                *)
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
(* Monad_of_category_monad == module, interface to isMonad from hierarchy.v   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope category_scope.

Reserved Notation "f \O g" (at level 50, format "f  \O  g").
Reserved Notation "F ~~> G" (at level 51).
Reserved Notation "f ~> g" (at level 51).
Reserved Notation "F # g" (at level 11).
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

Declare Scope category_scope.
Delimit Scope category_scope with category.
Local Open Scope category_scope.


Lemma compfid A B (f : A -> B) : f \o id = f. Proof. by []. Qed.
Lemma compidf A B (f : A -> B) : id \o f = f. Proof. by []. Qed.
(* Help to rewrite with compositions *)
Lemma compapp A B C (f : A -> B) (g : B -> C) (a : A) :
  (g \o f) a = g (f a). Proof. by []. Qed.

(* opaque ssrfun.frefl blocks some proofs involving functor_ext *)
#[global]
Remove Hints frefl : core.

Lemma frefl_transparent A B (f : A -> B) : f =1 f.
Proof. by []. Defined.

#[global]
Hint Resolve frefl_transparent : core.

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

HB.instance Definition _ (a b c : C) (f : {hom b -> c}) (g : {hom[C] a -> b}):=
  isHom.Build _ _ _ (f \o g) (funcomp_inhom (isHom_inhom g) (isHom_inhom f)).
End hom_interface.

(* Notation [\o f , .. , g , h] for hom compositions. *)
Module comps_notation.
Notation "[ '\o' f , .. , g , h ]" := (f \o .. (g \o h) ..) (at level 0,
  format "[ '[' '\o'  f ,  '/' .. ,  '/' g ,  '/' h ']' ]") : category_scope.
End comps_notation.

Section category_lemmas.
Variable C : category.

Lemma homfunK (a b : C) (f : {hom a -> b}) : [hom f] =1 f.
Proof. by []. Qed.

Lemma homcompA (a b c d : C)
  (h : {hom c -> d}) (g : {hom b -> c}) (f : {hom a -> b}) :
  [hom [hom h \o g] \o f] =1 [hom h \o [hom g \o f]].
Proof. by []. Qed.

Lemma homcompE (a b c : C) (g : {hom b -> c}) (f : {hom a -> b}) :
  [hom g \o f] =1 g \o f :> (el a -> el c).
Proof. by []. Qed.

Lemma hom_compE (a b c : C) (g : {hom b -> c}) (f : {hom a -> b}) x :
  g (f x) = (g \o f) x.
Proof. by [].  Qed.

Import comps_notation.

(* Restricting the components of a composition to homs and using the lemma
   homcompA, we can avoid the infinite sequence of redundunt compositions
   "_ \o id" or "id \o _" that pops out when we "rewrite !compA".*)
Lemma hom_compA (a b c d : C)
  (h : {hom c -> d}) (g : {hom b -> c}) (f : {hom a -> b}) :
  (h \o g) \o f =1 [\o h, g, f] :> (el a -> el d).
Proof. exact: homcompA. Qed.

Example hom_compA' (a b c d : C)
  (h : {hom c -> d}) (g : {hom b -> c}) (f : {hom a -> b}) :
  (h \o g) \o f = [\o h, g, f].
Proof. by []. Qed.

(* Tactic support is desirable for the following two cases :
   1. rewriting at the head of the sequence;
      compare for example the lemmas natural and natural_head below
   2. rewriting under [hom _];
      dependent type errors and explicit application of hom_ext is tedious.
*)

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
  transport_dom p f =1 [hom f \o hom_of_eq (esym p)].
Proof. by subst a'. Qed.
Lemma transport_codomF (a b b' : C) (p : b = b') (f : {hom a -> b}) :
  transport_codom p f =1 [hom hom_of_eq p \o f].
Proof. by subst b'. Qed.
Lemma transport_homF (a a' b b' : C) (pa : a = a') (pb : b = b') (f : {hom a -> b}) :
  transport_hom pa pb f =1 [hom hom_of_eq pb \o f \o hom_of_eq (esym pa)].
Proof. by subst a' b'. Qed.

Lemma transport_homE (a a' b b' : C) (pa : a = a') (pb : b = b')
  (f g : {hom a -> b}) :
  f =1 g -> transport_hom pa pb f =1 transport_hom pa pb g.
Proof. by subst a b. Qed.
Lemma transport_hom_inj (a a' b b' : C) (pa : a = a') (pb : b = b')
  (f g : {hom a -> b}) :
  transport_hom pa pb f =1 transport_hom pa pb g -> f =1 g.
Proof. by subst a b. Qed.
Lemma transport_hom_trans (a a' a'' b b' b'' : C)
  (pa : a = a') (pa' : a' = a'') (pb : b = b') (pb' : b' = b'') (f : {hom a -> b}) :
  (transport_hom pa' pb' \o transport_hom pa pb) f =1
    transport_hom (eq_trans pa pa') (eq_trans pb pb') f.
Proof. by subst a a' b b'. Qed.

End transport_lemmas.


Module FunctorLaws.
Section def.
Variable (C D : category).
Variable (F : C -> D) (actm : forall a b, {hom a -> b} -> {hom F a -> F b}).
Definition ext := forall a b (f g : {hom a -> b}),
    f =1 g -> actm f =1 actm g.
Definition id := forall a,
    actm [hom idfun] =1 [hom idfun] :> {hom F a -> F a}.
Definition comp := forall a b c (g : {hom b -> c}) (h : {hom a -> b}),
    actm [hom g \o h] =1 [hom actm g \o actm h].
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
Notation "F # f" := (actm F f) : category_scope.
Notation "{ 'functor' fCD }" := (functor_phant (Phant fCD))
  (format "{ 'functor'  fCD }") : category_scope.


Record eq_functor (C D : category)
  (F : {functor C -> D}) (G : {functor C -> D}) : Prop := EqFunctor {
    pm : F =1 G;
    eq_transport : forall (A B : C) (f : {hom A  -> B}),
      transport_hom (pm A) (pm B) (F # f) =1 G # f
  }.
Notation "F =#= G" := (eq_functor F G).

Section functor_lemmas.
Variables (C D : category) (F : {functor C -> D}).

Lemma functor_id a : F # [hom idfun] =1 idfun :> (el (F a) -> el (F a)).
Proof.
move=> x.
by rewrite (functor_ext_hom _ _ _ _ (homfunK _)) functor_id_hom.
Qed.

Lemma functor_o a b c (g : {hom b -> c}) (h : {hom a -> b}) :
  F # [hom g \o h] =1 F # g \o F # h :> (el (F a) -> el (F c)).
Proof. by move=> fa; rewrite functor_comp_hom. Qed.

Lemma functor_ext (G : {functor C -> D}) (eq : F =1 G) :
  (forall (A B : C) (f : {hom A -> B}),
      transport_hom (eq A) (eq B) (F # f) =1 G # f) -> F =#= G.
Proof. exact: EqFunctor. Qed.

End functor_lemmas.


Section functor_equality.

Variables (C D : category).

Lemma eq_functor_refl (F : {functor C -> D}) : F =#= F.
Proof. exact: (functor_ext (eq := (fun=> _))). Qed.

Lemma eq_functor_trans (F G H : {functor C -> D}) :
  F =#= G -> G =#= H -> F =#= H.
Proof.
move=> [pmFG eqFG] [pmGH eqGH].
apply: (functor_ext (eq := fun A => eq_trans (pmFG A) (pmGH A))) => A B f x.
rewrite -transport_hom_trans -eqGH /=.
exact: transport_homE.
Qed.

Lemma eq_functor_sym (F G : {functor C -> D}) : F =#= G -> G =#= F.
Proof.
move=> [pm eq].
apply: (functor_ext (eq := fun A => esym (pm A))) => A B f.
apply: (@transport_hom_inj _ _ _ _ _ (pm A) (pm B)) => x.
rewrite {}eq; move: x; rewrite -/(_ =1 _).
move: (G # f) => {f}.
by case:_/(pm B); case:_/(pm A).
Qed.

End functor_equality.


Section functor_o_head.

Import comps_notation.
Variable C D : category.

Lemma functor_o_head (a b c : C)
  (g : {hom b -> c}) (h : {hom a -> b}) d (F : {functor C -> D})
    (k : {hom d -> F a}) :
  (F # [hom g \o h]) \o k =1 [\o F # g, F # h, k].
Proof. by move=> x /=; rewrite functor_comp_hom. Qed.

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
  fun h : {hom[C0] a -> b} => F # (G # h) : {hom[C2] F (G a) -> F (G b)}.

Fact functorcomposition_ext : FunctorLaws.ext functorcomposition.
Proof.
move=> A B f g eq_fg x; rewrite /functorcomposition.
by do 2 apply: functor_ext_hom.
Qed.
Fact functorcomposition_id : FunctorLaws.id functorcomposition.
Proof.
move=> A x; rewrite /functorcomposition [RHS]/=.
rewrite (functor_ext_hom _ _ _ _ (functor_id (a := A))).
exact: functor_id.
Qed.
Fact functorcomposition_comp : FunctorLaws.comp functorcomposition.
Proof.
move=> a b c g h x; rewrite /functorcomposition.
rewrite (functor_ext_hom _ _ _ _ (functor_comp_hom _ _ _ _ _)).
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


Notation "F ~~> G" := (forall a, {hom F a -> G a}) : category_scope.
Definition naturality (C D : category) (F G : {functor C -> D}) (f : F ~~> G) :=
  forall a b (h : {hom a -> b}), (G # h) \o (f a) =1 (f b) \o (F # h).
Arguments naturality [C D].
HB.mixin Record isNatural
    (C D : category) (F G : {functor C -> D}) (f : F ~~> G) :=
  { natural : naturality F G f }.
#[short(type=nattrans)]
HB.structure Definition _ (C D : category) (F G : {functor C -> D}) :=
  { f of isNatural C D F G f }.
Arguments natural [C D F G] phi : rename.
Notation "F ~> G" := (nattrans F G) : category_scope.


Section natural_transformation_lemmas.

Import comps_notation.
Variables (C D : category) (F G : {functor C -> D}).

Lemma natural_head (phi : F ~> G) a b c (h : {hom a -> b}) (f : {hom c -> F a}) :
  [\o G # h, phi a, f] =1 [\o phi b, F # h, f].
Proof.
move=> x; rewrite -!hom_compA /=.
case: phi => [t [[]]] /=; rewrite /naturality /= => nat_t.
exact: nat_t a b h (f x).
Qed.

Definition eq_nattrans (phi psi : F ~> G) :=
  forall a : C, (phi a =1 psi a :> (_ -> _)).
Notation "p =%= q" := (eq_nattrans p q).

Lemma eq_nattrans_refl (phi : F ~> G) : phi =%= phi.
Proof. by []. Qed.
Lemma eq_nattrans_sym (phi psi : F ~> G) : phi =%= psi -> psi =%= phi.
Proof. by move=> eq a x /[!eq]. Qed.
Lemma eq_nattrans_trans (phi psi ksi : F ~> G) :
  phi =%= psi -> psi =%= ksi -> phi =%= ksi.
Proof. by move=> eqp eqk a x /[!eqp] /[!eqk]. Qed.

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
Variable (Imor : forall a b (f : {hom a -> b}), tc (F # f) =1 td (G # f)).
(* tc (F # f) and td (G # f) : {hom F a -> G b}) *)
Definition f : F ~~> G := fun (c : C) => tc [hom idfun].

Fact natural : naturality F G f.
Proof.
move=> a b h x.
rewrite /f /= 2!transport_codomF 2!homcompE 2!compfid.
rewrite !hom_compE -[RHS]transport_codomF.
by rewrite Imor transport_domF homfunK /= esymK.
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


Section vertical_composition.

Variables (C D : category) (F G H : {functor C -> D}).
Variables (g : G ~> H) (f : F ~> G).
Definition vcomp := fun a => [hom g a \o f a].

Fact natural_vcomp : naturality _ _ vcomp.
Proof. by move=> A B h x; rewrite (natural_head g) compapp (natural f). Qed.
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
Lemma VCompE_nat : g \v f = (fun a => [hom g a \o f a]) :> (_ ~~> _).
Proof. by []. Qed.
Lemma VCompE a : (g \v f) a = g a \o f a :> (_ -> _).
Proof. by []. Qed.

End vcomp_lemmas.


Section horizontal_composition.

Variables (C D E : category) (F G : {functor C -> D}) (F' G' : {functor D -> E}).
Variables (s : F ~> G) (t : F' ~> G').
Definition hcomp : F' \O F ~~> G' \O G :=
  fun (c : C) => [hom t (G c) \o F' # s c].

Fact natural_hcomp : naturality (F' \O F) (G' \O G) hcomp.
Proof.
move=> c0 c1 h x; rewrite [in LHS]compA [LHS](natural t).
rewrite !hom_compE -[in LHS]compA -[in RHS]compA; apply: eq_comp => // {}x.
rewrite [in RHS]FCompE -2!functor_o; apply: functor_ext_hom => {}x.
by rewrite /= !hom_compE natural.
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
Lemma HCompE c : (t \h s) c = t (G c) \o F' # s c :> (_ -> _).
Proof. by unlock. Qed.
Lemma HCompE_alt c : (t \h s) c =1 G' # (s c) \o t (F c) :> (_ -> _).
Proof. by move=> x; rewrite HCompE natural. Qed.

End hcomp_extensionality_lemmas.


Section hcomp_id_assoc_lemmas.

Import comps_notation.
Variables C D E Z : category.
Variables
  (F   G   : {functor C -> D})
  (F'  G'  : {functor D -> E})
  (F'' G'' : {functor E -> Z}).
Variables (s : F ~> G) (t : F' ~> G') (u : F'' ~> G'').

Lemma HCompId c : (t \h NId F) c =1 t (F c).
Proof. by move=> x; rewrite HCompE NIdE /= functor_id. Qed.
Lemma HIdComp c : (NId G' \h s) c =1 G' # s c.
Proof. by move=> x; rewrite HCompE NIdE. Qed.
Lemma HCompA c : ((u \h t) \h s) c =1 (u \h (t \h s)) c.
Proof.
move=> x; rewrite [in LHS]HCompE [in RHS]HCompE [in LHS]HCompE.
rewrite hom_compA /= (hom_compE _ _ x) -functor_o; apply: eq_comp => // {x}.
by apply: functor_ext_hom; rewrite HCompE.
Qed.

End hcomp_id_assoc_lemmas.


Section hcomp_lemmas.

Variables (C D E : category).
Variables (F G : {functor C -> D}) (F' G' : {functor D -> E}).
Variables (s : F ~> G) (t : F' ~> G').

(* higher level horizontal composition is a vertical composition of
   horizontal compositions *)
Lemma HComp_VH : t \h s =%= (t \h NId G) \v (NId F' \h s).
Proof. by move=> a x; rewrite VCompE HCompE /= HIdComp HCompId. Qed.
Lemma HComp_VH_aux : t \h s =%= (NId G' \h s) \v (t \h NId F).
Proof.
move=> a x; rewrite VCompE HCompE /= HIdComp HCompId.
by rewrite hom_compE -natural.
Qed.
Lemma NIdFId c : NId (@FId C) c = [hom idfun].
Proof. by []. Qed.
Lemma NIdFComp : NId (F' \O F) =%= NId F' \h NId F.
Proof. by move=> c; rewrite HCompE /= compidf => x; rewrite functor_id. Qed.

(* horizontal and vertical compositions interchange *)
Variables (H : {functor C -> D}) (H' : {functor D -> E}).
Variables (s' : G ~> H) (t' : G' ~> H').

Lemma HCompACA : (t' \h s') \v (t \h s) =%= (t' \v t) \h (s' \v s).
Proof.
move=> c /= x.
rewrite !HCompE !VCompE -compA -[in RHS]compA.
apply: eq_comp => // {}x; rewrite natural_head /=.
by rewrite (hom_compE _ _ x) -functor_o.
Qed.

End hcomp_lemmas.


(* adjoint functor *)
(* We define adjointness F -| G in terms of its unit and counit. *)
Module TriangularLaws.
Section triangularlaws.
Variables (C D : category) (F : {functor C -> D}) (G : {functor D -> C}).
Variables (eta : FId ~> G \O F) (eps : F \O G ~> FId).
Definition left := forall c, eps (F c) \o F # (eta c) =1 idfun.
Definition right := forall d, G # (eps d) \o eta (G d) =1 idfun.
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
  fun h => [hom (G # h) \o (eta A c)].

Definition hom_inv c d : {hom c -> G d} -> {hom F c -> d} :=
  fun h => [hom (eps A d) \o (F # h)].

Import comps_notation.

Lemma hom_isoK (c : C) (d : D) (f : {hom F c -> d}) : hom_inv (hom_iso f) =1 f.
Proof.
rewrite /hom_inv /hom_iso => x.
rewrite /= functor_o -[LHS](natural_head (eps A)).
by rewrite compapp triL.
Qed.
Lemma hom_invK (c : C) (d : D) (g : {hom c -> G d}) : hom_iso (hom_inv g) =1 g.
Proof.
rewrite /hom_inv /hom_iso => x.
rewrite /= functor_o.
rewrite !hom_compE hom_compA compapp (natural (eta A)).
by rewrite !(hom_compE _ _ x) -hom_compA compapp triR.
Qed.

Lemma hom_iso_inj (c : C) (d : D) (f g : {hom F c -> d}) :
  hom_iso f =1 hom_iso g -> f =1 g.
Proof.
move=> eq x.
rewrite -[LHS]hom_isoK -[RHS]hom_isoK /=.
by rewrite (functor_ext_hom (s := F) _ _ _ _ eq).
Qed.
Lemma hom_inv_inj (c : C) (d : D) (f g : {hom c -> G d}) :
  hom_inv f =1 hom_inv g -> f =1 g.
Proof.
move=> eq x.
rewrite -[LHS]hom_invK -[RHS]hom_invK /=.
by rewrite (functor_ext_hom (s := G) _ _ _ _ eq).
Qed.

Lemma eta_hom_iso (c : C) : eta A c =1 hom_iso [hom idfun].
Proof. by rewrite /hom_iso => x /=; rewrite functor_id. Qed.
Lemma eps_hom_inv (d : D) : eps A d =1 hom_inv [hom idfun].
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

Definition F := F1 \O F0.
Definition G := G0 \O G1.

Definition Eta : FId ~> G \O F :=
  [NEq G0 \O (G1 \O F1) \O F0 , G \O F]
    \v (NId G0 \h eta1 \h NId F0)
    \v [NEq G0 \O F0 , G0 \O FId \O F0]
    \v eta0.
Lemma EtaE a : Eta a =1 G0 # (eta1 (F0 a)) \o (eta0 a).
Proof. by move=> x /=; rewrite HCompId HIdComp. Qed.
Lemma EtaE_hom a : Eta a =1 [hom G0 # (eta1 (F0 a)) \o (eta0 a)].
Proof. by move=> x; rewrite EtaE. Qed.

Definition Eps : F \O G ~> FId :=
  (eps1)
    \v [NEq F1 \O FId \O G1 , F1 \O G1]
    \v (NId F1 \h eps0 \h NId G1)
    \v [NEq F \O G , (F1 \O (F0 \O G0)) \O G1].
Lemma EpsE a : Eps a =1 (eps1 _) \o F1 # (eps0 (G1 a)) :> (_ -> _).
Proof. by move=> x /=; rewrite HCompId HIdComp. Qed.
Lemma EpsE_hom a : Eps a =1 [hom (eps1 _) \o F1 # (eps0 (G1 a))].
Proof. by move=> x; rewrite EpsE. Qed.

Lemma triL : TriangularLaws.left Eta Eps.
Proof.
move=> c x.
rewrite [RHS]/= [LHS]EpsE (functor_ext_hom _ _ _ _ (@EtaE_hom c)).
rewrite (hom_compE _ _ x) hom_compA /= (functor_o (F := F)) /F /=.
rewrite 2!(hom_compE _ _ x) -(functor_o_head F1).
set X := [hom [\o _, _]].
have /= -> : F1 # X =1 F1 # ((FId # eta1 (F0 c)) \o (eps0 (F0 c))).
  by move=> y; apply functor_ext_hom => {}y /=; rewrite -[LHS](natural eps0).
  rewrite (hom_compE _ _ x) (functor_o_head F1) FIdf.
have /= -> := triL1 (_ (_ x)).
rewrite -[RHS]/(idfun x) -[in RHS](functor_id (F := F1)).
rewrite -[LHS]functor_o; apply functor_ext_hom => /= {}x.
by rewrite triL0.
Qed.

(* [\o eps (F c), F # eta c] =1 idfun *)
Lemma triR : TriangularLaws.right Eta Eps.
Proof.
move=> c x.
have := functor_ext_hom _ _ _ _ (EpsE_hom (a := c)) (Eta (G c) x).
rewrite (hom_compE _ _ x) => ->; rewrite EtaE.
rewrite (hom_compE _ _ x) (functor_o_head G).
have /= <- := functor_o_head G0 (eta0 (G c)) x.
rewrite !(hom_compE _ _ x).
set X := (X in G0 # X).
have /= -> : G0 # X =1 G0 # [\o eta1 (G1 c), FId # eps0 (G1 c)].
  move => {}x; apply functor_ext_hom => {}x; rewrite /X /=.
  by rewrite !(hom_compE _ _ x) (natural eta1). 
rewrite (functor_o (F := G0)) (hom_compE _ _ x) hom_compA FIdf.
have /= -> := triR0 (_ x).
rewrite -[RHS]/(idfun x) -[in RHS](functor_id (F := G0)).
rewrite -[LHS](functor_o (F := G0)).
apply functor_ext_hom => {x} /= x.
by rewrite triR1.
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


Module MonadLaws.
Section monad_laws.

Variables (C : category) (M : {functor C -> C}) .
Variables (unit : FId ~~> M) (mu : M \O M ~~> M).
Definition left_unit :=
  forall a, mu a \o unit (M a) =1 idfun :> (el (M a) -> el (M a)).
Definition right_unit :=
  forall a, mu a \o M # unit a =1 idfun :> (el (M a) -> el (M a)).
Definition associativity :=
  forall a, mu a \o M # mu a =1 mu a \o mu (M a) :>
                                    (el (M (M (M a))) -> el (M a)).
End monad_laws.
End MonadLaws.


Module BindLaws.
Section bindlaws.

Variables (C : category) (M : C -> C).
Variable b : forall A B, {hom A -> M B} -> {hom M A -> M B}.
Local Notation "m >>= f" := (b f m).

Fact associative_aux x y z (f : {hom x -> M y}) (g : {hom y -> M z}) :
  (fun w => (f w >>= g)) =1 (b g \o f).
Proof. by []. Qed.
Definition associative :=
  forall A B C (m : el (M A)) (f : {hom A -> M B}) (g : {hom B -> M C}),
  (m >>= f) >>= g = m >>= [hom b g \o f].
Definition left_neutral (r : forall A, {hom A -> M A}) :=
  forall A B (f : {hom A -> M B}), [hom (b f \o r A)] =1 f.
Definition right_neutral (r : forall A, {hom A -> M A}) :=
  forall A (m : el (M A)), m >>= r _ = m.

End bindlaws.
End BindLaws.


Section bind_lemmas.

Variables (C : category) (M : C -> C).
Variable b : forall A B, {hom A -> M B} -> {hom M A -> M B}.
Local Notation "m >>= f" := (b f m).

Lemma bind_left_neutral_hom_fun (r : forall A, {hom A -> M A})
  : BindLaws.left_neutral b r
    <-> forall A B (f : {hom A -> M B}), b f \o r A =1 f.
Proof. by split; move=> H A B f; exact: (H A B f). Qed.

End bind_lemmas.


HB.mixin Record isMonad (C : category) (M : C -> C) of @Functor C C M := {
  munit : FId ~> [the {functor C -> C} of M] ;
  mu : [the {functor C -> C} of M] \O [the {functor C -> C} of M] ~>
         [the {functor C -> C} of M] ;
  bind : forall (a b : C), {hom a -> M b} -> {hom M a -> M b} ;
  bind_ext : forall (a b : C) (f g : {hom a -> M b}),
    f =1 g -> bind a b f =1 bind a b g;
  bindE : forall (a b : C) (f : {hom a -> M b}) (m : el (M a)),
    bind a b f m = mu b (([the {functor C -> C} of M] # f) m) ;
  mumunitM : MonadLaws.left_unit munit mu ;
  muMmunit : MonadLaws.right_unit munit mu ;
  muA : MonadLaws.associativity mu
}.
#[short(type=monad)]
HB.structure Definition Monad (C : category) :=
  {M of isMonad C M & @Functor C C M}.
Arguments bind {C M a b} : rename, simpl never.
Notation "m >>= f" := (bind f m).


Section monad_interface.

Variable (C : category) (M : monad C).
(* *_head lemmas are for [fun of f] \o ([fun of g] \o ([fun of h] \o ..))*)

Import comps_notation.
Lemma mumunitM_head a (c : C) (f : {hom c -> M a}) : [\o mu _, munit _, f] =1 f.
Proof.
by move=> x; rewrite compA (compapp _ (mu a \o munit (M a))) mumunitM.
Qed.
Lemma muMmunit_head a (c : C) (f : {hom c -> M a}) : [\o mu _, M # munit _, f] =1 f.
Proof.
by move=> x; rewrite compA (compapp _ (mu a \o M # munit a)) muMmunit.
Qed.
Lemma muA_head a (c : C) (f : {hom c -> M (M (M a))}) :
  [\o mu _, M # mu _, f] =1 [\o mu _, mu _, f].
Proof. by move=> x; rewrite compA compapp muA. Qed.

End monad_interface.


HB.factory Record Monad_of_munit_mu (C : category) (M : C -> C)
           of @Functor C C M := {
  munit : FId ~> [the {functor C -> C} of M] ;
  mu : M \O M ~> [the {functor C -> C} of M] ;
  mumunitM : MonadLaws.left_unit munit mu ;
  muMmunit : MonadLaws.right_unit munit mu ;
  muA : MonadLaws.associativity mu
}.
HB.builders Context C M of Monad_of_munit_mu C M.
Let F := [the {functor _ -> _} of M].
Let bind (a b : C) (f : {hom a -> M b}) : {hom M a -> M b} := [hom mu _ \o (F # f)].
Let bind_ext (a b : C) (f g : {hom a -> M b}) :
  f =1 g -> bind f =1 bind g.
Proof. by rewrite /bind => eq x /=; rewrite (functor_ext_hom _ _ _ _ eq). Qed.
Let bindE (a b : C) (f : {hom a -> M b}) (m : el (M a)) :
    bind f m = mu b (([the {functor C -> C} of M] # f) m).
Proof. by []. Qed.
HB.instance Definition _ :=
  isMonad.Build C M bind_ext bindE mumunitM muMmunit muA.
HB.end.


(* Monads defined by ret and bind; M need not be a priori a functor *)
HB.factory Record Monad_of_ret_bind (C : category) (acto : C -> C) := {
  ret : forall a, {hom a -> acto a} ;
  bind : forall (a b : C), {hom a -> acto b} -> {hom acto a -> acto b} ;
  bind_ext_hom : forall (a b : C) (f g : {hom a -> acto b}),
    f =1 g -> bind a b f =1 bind a b g;
  bindmunitf : BindLaws.left_neutral bind ret ;
  bindmmunit : BindLaws.right_neutral bind ret ;
  bindA : BindLaws.associative bind ;
}.
HB.builders Context C M of Monad_of_ret_bind C M.
Let fmap a b (f : {hom a -> b}) := bind [hom ret b \o f].
Let bindmunitf_fun : (forall (a b : C) (f : {hom a -> M b}),
  bind f \o ret a =1 f).
Proof. by apply/bind_left_neutral_hom_fun/bindmunitf. Qed.
Let fmap_ext : FunctorLaws.ext fmap.
Proof.
by move=> A B f g eq; rewrite /fmap; apply: bind_ext_hom => x /= /[!eq].
Qed.
Let fmap_id : FunctorLaws.id fmap.
Proof.
move=> A m; rewrite /fmap; rewrite /idfun.
rewrite -[in RHS](bindmmunit m).
by apply: bind_ext_hom => x.
Qed.
Let fmap_o : FunctorLaws.comp fmap.
Proof.
move=> a b c g h x; rewrite /fmap.
rewrite [RHS]bindA/=; apply: bind_ext_hom => {}x /=.
by rewrite -[RHS]compapp bindmunitf_fun.
Qed.
HB.instance Definition _ := isFunctor.Build C C M fmap_ext fmap_id fmap_o.
Notation F := [the {functor _ -> _} of M].

Let ret_naturality : naturality FId F ret.
Proof. by move=> A B h x; rewrite FIdf bindmunitf_fun. Qed.
HB.instance Definition _ := isNatural.Build _ _ FId F
  (ret : FId ~~> M)(*NB: fails without this type constraint*) ret_naturality.
Definition munit := [the FId ~> F of ret].
Let mu' : F \O F ~~> F := fun _ => bind [hom idfun].
Let fmap_bind a b c (f : {hom a ->b}) m (g : {hom c ->F a}) :
  (fmap f) (bind g m) = bind [hom fmap f \o g] m.
Proof. by rewrite /fmap bindA. Qed.
Let mu'_naturality : naturality (F \O F) F mu'.
Proof.
move=> A B h m; rewrite /mu /=.
rewrite fmap_bind bindA; apply: bind_ext_hom => {}m /=.
by rewrite -[RHS]compapp bindmunitf_fun.
Qed.
HB.instance Definition _ := isNatural.Build _ _ _ _ _ mu'_naturality.
Definition mu := [the F \O F ~> F of mu'].

Let bind_fmap a b c (f : {hom a -> b}) (m : el (F a)) (g : {hom b -> F c}) :
  bind g (fmap f m) = bind [hom g \o f] m .
Proof.
rewrite bindA /=; apply: bind_ext_hom => {}m /=.
by rewrite -[LHS]compapp bindmunitf_fun.
Qed.
Lemma bindE (a b : C) (f : {hom a -> F b}) (m : el (F a)) :
  bind f m = mu b (([the {functor C -> C} of F] # f) m).
Proof. by rewrite /mu /= bind_fmap /=; apply: bind_ext_hom. Qed.
Lemma mumunitM : MonadLaws.left_unit munit mu.
Proof. by rewrite /mu => A m /=; rewrite -[LHS]compapp bindmunitf_fun. Qed.
Let bind_fmap_fun a b c (f : {hom a ->b}) (g : {hom b -> F c}) :
  bind g \o fmap f =1 bind [hom g \o f].
Proof. by move=> m; exact: bind_fmap. Qed.
Lemma muMmunit : MonadLaws.right_unit munit mu.
Proof.
rewrite /mu => A ma /=.
rewrite -[LHS]compapp bind_fmap_fun/= -[in RHS](bindmmunit ma).
exact: bind_ext_hom.
Qed.
Lemma muA : MonadLaws.associativity mu.
Proof.
move => A mmma; rewrite /mu.
rewrite bind_fmap_fun/= bindA/=.
exact: bind_ext_hom.
Qed.
HB.instance Definition _ :=
  isMonad.Build C M bind_ext_hom bindE mumunitM muMmunit muA.
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
Definition mu : M \O M ~~> M := fun a => G # (eps (F a)).
Definition munit : FId ~~> M := fun a => eta a.
Let triL := AdjointFunctors.triL A.
Let triR := AdjointFunctors.triR A.

Lemma naturality_munit : naturality FId M munit.
Proof. by move=> a b f x; rewrite (natural eta). Qed.
HB.instance Definition _ := isNatural.Build C C FId M munit naturality_munit.
Lemma naturality_mu : naturality (M \O M) M mu.
Proof.
rewrite /mu => a b h x.
rewrite /M !FCompE -2!(@functor_o _ _ G) /=; apply: functor_ext_hom => {}x.
exact: (natural eps).
Qed.
HB.instance Definition _ := isNatural.Build C C (M \O M) M mu naturality_mu.

Let muE : mu = fun a => G # (@eps (F a)).
Proof. by []. Qed.
Let mu_associativity' a : mu a \o mu (M a) =1 mu a \o (M # mu a).
Proof.
move=> x; rewrite muE -2!(@functor_o _ _ G) /=; apply: functor_ext_hom => {}x /=.
exact: (natural eps).
Qed.
Lemma mu_associativity : MonadLaws.associativity mu.
Proof. by move=> a x; rewrite mu_associativity'. Qed.
Lemma mu_left_unit : MonadLaws.left_unit munit mu.
Proof. by move=> a x; rewrite muE triR. Qed.
Lemma mu_right_unit : MonadLaws.right_unit munit mu.
Proof.
move=> a x; rewrite muE /M FCompE /=.
rewrite -[LHS](@functor_o _ _ G) -[RHS](@functor_id _ _ G).
apply: functor_ext_hom => {}x; exact: triL.
Qed.

(*TODO: make this go through
HB.instance Definition _ :=
 Monad_of_munit_mu.Build _ _ mu_left_unit mu_right_unit mu_associativity.*)

Let bind (a b : C) (f : {hom a -> M b}) : {hom M a -> M b} :=
      [hom mu _ \o (M # f)].
Fact bind_ext (a b : C) (f g : {hom a -> M b}) :
  f =1 g -> bind f =1 bind g.
Proof.
by rewrite /bind => eq x /=; rewrite (functor_ext_hom _ _ _ _ eq).
Qed.
Let bindE (a b : C) (f : {hom a -> M b}) (m : el (M a)) :
  bind f m = mu b (([the {functor C -> C} of M] # f) m).
Proof. by []. Qed.
HB.instance Definition monad_of_adjoint_mixin :=
  isMonad.Build C (G \o F)
    bind_ext bindE mu_left_unit mu_right_unit mu_associativity.
End def.

Definition build (C D : category)
           (F : {functor C -> D}) (G : {functor D -> C}) (A : F -| G) :=
  Monad.Pack (Monad.Class (monad_of_adjoint_mixin A)).

End _Monad_of_adjoint_functors.
Notation Monad_of_adjoint_functors := _Monad_of_adjoint_functors.build.
(* TODO: Can we turn this into a factory? *)

Lemma Monad_of_adjoint_functorsE (C D : category)
  (F : {functor C -> D}) (G : {functor D -> C}) (A : F -| G) :
  Monad_of_adjoint_functors A = G \O F :> {functor C -> C}.
Proof. by []. Qed.

Section Essai.

Variable (C D : category)
           (F : {functor C -> D}) (G : {functor D -> C}) (A : F -| G).

Canonical MA := Monad_of_adjoint_functors A.
Let bla := G \O F : monad C.

End Essai.
