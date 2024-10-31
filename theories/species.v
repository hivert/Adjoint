From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Require Import category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Local Open Scope category_scope.

Declare Scope species_scope.
Delimit Scope category_scope with species.
Local Open Scope species_scope.


Reserved Notation "\X" (at level 0).

Module FinBijCat.

Fact idfun_is_bjective T : bijective (@idfun T).
Proof. by exists idfun. Qed.

HB.instance Definition _ :=
  isCategory.Build finType (fun T : finType => T)
    (fun (a b : finType) (f : a -> b) => bijective f) idfun_is_bjective
    (fun (a b c : finType) (f : a -> b) (g : b -> c)
         (fb : bijective f) (gb : bijective g) => bij_comp gb fb).
Definition cat : category :=  finType.

End FinBijCat.
Notation Bij := FinBijCat.cat.


Section Homs.

Variable (A B : Bij) (f : {hom[Bij] A -> B}).

Lemma hom_is_isom :
  { finv | bijective finv & (cancel finv f * cancel f finv)%type }.
Proof.
have:= isHom_inhom f; rewrite /inhom /= => f_bij.
pose ff := [ffun x : el A => f x : el B].
have ff_bij : bijective ff by apply: (eq_bij f_bij) => x; rewrite /ff ffunE.
have ff_onto : codom ff =i predT.
  apply/subset_cardP; last exact/subsetP.
  by rewrite (card_codom (bij_inj ff_bij)) (bij_eq_card ff_bij).
pose finv := fun x => iinv (ff_onto x).
have fKV : cancel finv f.
  by move=> x /=; rewrite -[RHS](f_iinv (ff_onto x)) ffunE.
have fK : cancel f finv by rewrite -bij_can_sym.
by exists finv; repeat split => //; exists f.
Qed.
Definition finv : el B -> el A := let: exist2 finv P1 P2 := hom_is_isom in finv.

Lemma finv_bij : bijective finv.
Proof. by rewrite /finv; case: hom_is_isom. Qed.
HB.instance Definition _ := isHom.Build _ B A finv finv_bij.

Lemma finvK : cancel f finv.
Proof. by rewrite /finv; case: hom_is_isom => x _ []. Qed.
Lemma finvKV : cancel finv f.
Proof. by rewrite /finv; case: hom_is_isom => x _ []. Qed.

End Homs.

HB.factory Record Bijhom (A B : Bij)
  (f : el A -> el B) := { finsetsbij_hom : bijective f }.
HB.builders Context (A B : Bij)
  (f : el A -> el B) of Bijhom A B f.
HB.instance Definition _ := isHom.Build _ A B f finsetsbij_hom.
HB.instance Definition _ := isIsom.Build _ A B f (finv_bij f) (finvK f) (finvKV f).
HB.end.

Lemma Bijhom_eq_card (A B : Bij) (f : {hom[Bij] A -> B}) : #|A| = #|B|.
Proof. exact: (bij_eq_card (isHom_inhom f)). Qed.

Definition voidB := (void : Bij).
Definition unitB := (unit : Bij).
Definition boolB := (bool : Bij).

Definition negbB : el boolB -> el boolB := negb.

HB.instance Definition _ :=
  Bijhom.Build boolB boolB negbB (inv_bij negbK).


Definition Species := {functor Bij -> Bij}.

Definition Sp0_fun := fun _ : Bij => voidB.
Definition Sp0_mor (A B : Bij) (f : {hom[Bij] A -> B}) :
  {hom[Bij] voidB -> voidB} := idfun.
HB.instance Definition _ :=
  @isFunctor.Build Bij Bij Sp0_fun Sp0_mor
    (fun _ _ _ _ _ => frefl _) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition Sp0 : Species := Sp0_fun.
Notation "0" := Sp0 : species_scope.


Section SpDelta.

Variable (C : nat).
Definition SpDelta_fun := fun S : Bij => if #|S| == C then unitB else voidB.
Lemma SpDelta_funE (A B : Bij) (f : {hom[Bij] A -> B}) :
  SpDelta_fun A = SpDelta_fun B.
Proof. by rewrite /SpDelta_fun (Bijhom_eq_card f). Qed.
Lemma SpDelta_fun_uniq (A : Bij) (x y : SpDelta_fun A) : x = y.
Proof. by move: x y; rewrite /SpDelta_fun; case: eqP => _ [] []. Qed.
Definition SpDelta_mor (A B : Bij) (f : {hom[Bij] A -> B}) :
  {hom[Bij] SpDelta_fun A -> SpDelta_fun B} :=
  eq_rect _ (fun x => {hom x -> SpDelta_fun B}) idfun _ (esym (SpDelta_funE f)).
Fact SpDelta_ext : FunctorLaws.ext SpDelta_mor.
Proof. by move=> /= A B f g _ x; apply: SpDelta_fun_uniq. Qed.
Fact SpDelta_id : FunctorLaws.id SpDelta_mor.
Proof. move=> /= a x; apply: SpDelta_fun_uniq. Qed.
Fact SpDelta_comp  : FunctorLaws.comp SpDelta_mor.
Proof. by move=> /= a b c f g x; apply: SpDelta_fun_uniq. Qed.
HB.instance Definition _ := @isFunctor.Build Bij Bij SpDelta_fun SpDelta_mor
                              SpDelta_ext SpDelta_id SpDelta_comp.
Definition SpDelta : Species := SpDelta_fun.

End SpDelta.
Notation "1" := (SpDelta 0) : species_scope.
Notation "\X" := (SpDelta 1) : species_scope.


Section SumSpecies.

Variable A B : Species.

Definition SumSp_fun S : Bij := (A S + B S)%type.
Definition SumSp_mor S T (f : {hom[Bij] S -> T}) :
  el (SumSp_fun S) -> el (SumSp_fun T) :=
  fun x => match x with
           | inl a => inl ((A # f) a)
           | inr b => inr ((B # f) b)
           end.
Lemma SumSp_mor_bij S T (f : {hom[Bij] S -> T}) : bijective (SumSp_mor f).
Proof.
exists (SumSp_mor (finv f)); case => [a|b] /=; congr (_ _);
  rewrite -[LHS]compapp -functor_o.
- by rewrite -[RHS](@functor_id _ _ A); apply/functor_ext_hom/finvK.
- by rewrite -[RHS](@functor_id _ _ B); apply/functor_ext_hom/finvK.
- by rewrite -[RHS](@functor_id _ _ A); apply/functor_ext_hom/finvKV.
- by rewrite -[RHS](@functor_id _ _ B); apply/functor_ext_hom/finvKV.
Qed.
HB.instance Definition _ S T (f : {hom[Bij] S -> T}) :=
  Bijhom.Build (SumSp_fun S) (SumSp_fun T) (SumSp_mor f) (SumSp_mor_bij f).
Fact SumSp_ext : FunctorLaws.ext SumSp_mor.
Proof. by move=> S T f g eq [a|b] /=; congr (_ _); apply: functor_ext_hom. Qed.
Fact SumSp_id : FunctorLaws.id SumSp_mor.
Proof. by move=> S [a|b] /=; rewrite functor_id. Qed.
Fact SumSp_comp  : FunctorLaws.comp SumSp_mor.
Proof. by move=> S T U f g [a|b]; rewrite /= functor_o. Qed.
HB.instance Definition _ :=
  @isFunctor.Build Bij Bij SumSp_fun SumSp_mor SumSp_ext SumSp_id SumSp_comp.
Definition SumSp : Species := SumSp_fun.

End SumSpecies.

Notation "f + g" := (SumSp f g) : species_scope.


Section SumSpeciesCom.

Implicit Types (A B : Species).

Definition SumSpC_fun A B S : el ((A + B) S) -> el ((B + A) S) :=
  fun x => match x with inl a => inr a | inr b => inl b end.

Lemma SumSpC_funK A B S : cancel (@SumSpC_fun A B S) (@SumSpC_fun B A S).
Proof. by case. Qed.
Fact SumSpC_bij A B S : bijective (@SumSpC_fun A B S).
Proof. by exists (SumSpC_fun (S := S)); exact: SumSpC_funK. Qed.
HB.instance Definition _ A B S :=
  @isHom.Build Bij ((A + B) S) ((B + A) S)
    (@SumSpC_fun A B S) (@SumSpC_bij A B S).
Definition SumSpC A B : (A + B) ~~> (B + A) := @SumSpC_fun A B.

Fact SumSpC_natural A B : naturality (A + B) (B + A) (SumSpC A B).
Proof. by move=> S T h []. Qed.
HB.instance Definition _ A B :=
  @isNatural.Build Bij Bij (A + B) (B + A)
    (SumSpC A B) (@SumSpC_natural A B).

Lemma SumSpCK A B : SumSpC B A \v SumSpC A B =%= NId (A + B).
Proof. by move=> S []. Qed.

End SumSpeciesCom.


Section SumSpeciesZero.

Implicit Types (A B : Species).

Section Mor.

Variables (A : Species) (S : Bij).
Definition SumSp0_fun : (el ((A + 0) S)) -> (el (A S)) :=
  fun x => match x with inl a => a | inr b => match b with end end.
Definition SumSp0_inv : (el (A S)) -> (el ((A + 0) S)) := fun a => inl a.
Let SumSp0_funK : cancel SumSp0_fun SumSp0_inv.
Proof. by case => [|[]]. Qed.
Let SumSp0_invK : cancel SumSp0_inv SumSp0_fun.
Proof. by []. Qed.
Fact SumSp0_fun_bij : bijective SumSp0_fun.
Proof. by exists SumSp0_inv. Qed.
Fact SumSp0_inv_bij : bijective SumSp0_inv.
Proof. by exists SumSp0_fun. Qed.
HB.instance Definition _ :=
  @isHom.Build Bij ((A + 0) S) (A S) SumSp0_fun SumSp0_fun_bij.
HB.instance Definition _ :=
  @isHom.Build Bij (A S) ((A + 0) S) SumSp0_inv SumSp0_inv_bij.

End Mor.
Definition SumSp0  A : A + 0 ~~> A := @SumSp0_fun A.
Definition SumSp0V A : A ~~> A + 0 := @SumSp0_inv A.

Fact SumSp0_natural A : naturality (A + 0) A (SumSp0 A).
Proof. by move=> S T h []. Qed.
Fact SumSp0V_natural A : naturality A (A + 0) (SumSp0V A).
Proof. by []. Qed.
HB.instance Definition _ A :=
  @isNatural.Build Bij Bij (A + 0) A (SumSp0 A) (@SumSp0_natural A).
HB.instance Definition _ A :=
  @isNatural.Build Bij Bij A (A + 0) (SumSp0V A) (@SumSp0V_natural A).

Lemma SumSp0K A : SumSp0V A \v SumSp0 A =%= NId (A + 0).
Proof. by move=> S []. Qed.
Lemma SumSp0VK A : SumSp0 A \v SumSp0V A =%= NId A.
Proof. by []. Qed.

Definition Sum0Sp A : 0 + A ~> A := (SumSp0 A) \v (SumSpC 0 A).
Definition Sum0SpV A : A ~> 0 + A := (SumSpC A 0) \v (SumSp0V A).

Lemma Sum0SpK A : Sum0SpV A \v Sum0Sp A =%= NId (0 + A).
Proof. by move=> S []. Qed.
Lemma Sum0SpVK A : Sum0Sp A \v Sum0SpV A =%= NId A.
Proof. by []. Qed.

End SumSpeciesZero.


(** TODO Associativity *)

