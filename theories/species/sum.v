From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup.

Require Import category species.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Local Open Scope category_scope.

Declare Scope species_scope.
Delimit Scope category_scope with species.
Local Open Scope species_scope.


Section SumSpecies.

Variable A B : Species.

Definition sumSp_fun U : Bij := (A U + B U)%type.
Definition sumSp_mor U V (f : {hom U -> V}) :
  el (sumSp_fun U) -> el (sumSp_fun V) :=
  fun x => match x with
           | inl a => inl ((A # f) a)
           | inr b => inr ((B # f) b)
           end.
Lemma sumSp_mor_bij U V (f : {hom U -> V}) : bijective (sumSp_mor f).
Proof.
by exists (sumSp_mor (finv f)); case => [a|b] /=; rewrite ?SpfinvK ?SpfinvKV.
Qed.
HB.instance Definition _ U V (f : {hom U -> V}) :=
  BijHom.Build (sumSp_fun U) (sumSp_fun V) (sumSp_mor f) (sumSp_mor_bij f).
Fact sumSp_ext : FunctorLaws.ext sumSp_mor.
Proof. by move=> U V f g eq [a|b] /=; congr (_ _); apply: functor_ext_hom. Qed.
Fact sumSp_id : FunctorLaws.id sumSp_mor.
Proof. by move=> U [a|b] /=; rewrite functor_id. Qed.
Fact sumSp_comp  : FunctorLaws.comp sumSp_mor.
Proof. by move=> U V W f g [a|b]; rewrite /= functor_o. Qed.
HB.instance Definition _ :=
  isFunctor.Build Bij Bij sumSp_fun sumSp_ext sumSp_id sumSp_comp.
Definition sumSp : Species := sumSp_fun.

End SumSpecies.

Notation "f + g" := (sumSp f g) : species_scope.

Lemma card_sumSp A B n : cardSp (A + B) n = (cardSp A n + cardSp B n)%N.
Proof. by rewrite /sumSp /sumSp_fun /= /cardSp /= card_sum. Qed.

Lemma cardiso_sumSp A B n : cardiso (A + B) n = (cardiso A n + cardiso B n)%N.
Proof.
rewrite -!cardiso_ordE.
pose fA (C : {set A 'I_n}) := (inl @: C) : {set ((A + B)%species 'I_n)}.
have fA_inj : injective fA by apply: imset_inj => x y [].
pose fB (C : {set B 'I_n}) := (inr @: C) : {set ((A + B)%species 'I_n)}.
have fB_inj : injective fB by apply: imset_inj => x y [].
rewrite -(card_imset _ fA_inj) -(card_imset _ fB_inj) -cardsUI.
rewrite [X in (_ + #|pred_of_set X|)%N](_ : _ = set0) ?cards0 ?addn0; first last.
  apply: disjoint_setI0; rewrite disjoint_subset; apply/subsetP => x.
  rewrite inE => /imsetP[/= a Ha {x}->]; apply/negP => /imsetP[/= b _].
  move: Ha => /imsetP[x _ {a}->] eq.
  suff /imsetP[y _] : inl x \in fB b by [].
  rewrite -{}eq mem_imset; last by move=> u v [].
  exact: orbit_refl.
congr #|pred_of_set _|.
apply/setP => /= S; rewrite !inE.
apply/imsetP/orP => [[[a|b] _ {S}->] | [] /imsetP[T /imsetP[x _ {T}->] {S}->]].
- left; apply/imsetP; exists (orbit (actSp A  'I_n) setT a); first exact: imset_f.
  by rewrite -[LHS]nattransp_isoclass.
- right; apply/imsetP; exists (orbit (actSp B  'I_n) setT b); first exact: imset_f.
  by rewrite -[LHS]nattransp_isoclass.
- by exists (inl x) => //; rewrite -[RHS]nattransp_isoclass.
- by exists (inr x) => //; rewrite -[RHS]nattransp_isoclass.
Qed.


Section SumSpeciesCommutative.

Implicit Types (A B : Species).

Definition sumSpC_fun A B U : el ((A + B) U) -> el ((B + A) U) :=
  fun x => match x with inl a => inr a | inr b => inl b end.

Lemma sumSpC_funK A B U : cancel (@sumSpC_fun A B U) (@sumSpC_fun B A U).
Proof. by case. Qed.
Fact sumSpC_bij A B U : bijective (@sumSpC_fun A B U).
Proof. by exists (sumSpC_fun (U := U)); exact: sumSpC_funK. Qed.
HB.instance Definition _ A B U :=
  @BijHom.Build ((A + B) U) ((B + A) U) (@sumSpC_fun A B U) (@sumSpC_bij A B U).
Definition sumSpC A B : A + B ~~> B + A := @sumSpC_fun A B.

Fact sumSpC_natural A B : naturality (A + B) (B + A) (sumSpC A B).
Proof. by move=> U V h []. Qed.
HB.instance Definition _ A B :=
  @isNatural.Build Bij Bij (A + B) (B + A)
    (sumSpC A B) (@sumSpC_natural A B).

Lemma sumSpCK A B : sumSpC B A \v sumSpC A B =%= NId (A + B).
Proof. by move=> U []. Qed.

End SumSpeciesCommutative.


Section SumSpeciesZero.
Variable (A : Species).

Section Mor.
Variable (U : Bij).
Definition sumSp0_fun : (el ((A + 0) U)) -> (el (A U)) :=
  fun x => match x with inl a => a | inr b => match b with end end.
Definition sumSp0_inv : (el (A U)) -> (el ((A + 0) U)) := fun a => inl a.
Fact sumSp0_funK : cancel sumSp0_fun sumSp0_inv.
Proof. by case => [|[]]. Qed.
Fact sumSp0_invK : cancel sumSp0_inv sumSp0_fun.
Proof. by []. Qed.
Fact sumSp0_fun_bij : bijective sumSp0_fun.
Proof. by exists sumSp0_inv; [exact: sumSp0_funK | exact: sumSp0_invK]. Qed.
Fact sumSp0_inv_bij : bijective sumSp0_inv.
Proof. by exists sumSp0_fun; [exact: sumSp0_invK | exact: sumSp0_funK]. Qed.
HB.instance Definition _ :=
  @BijHom.Build ((A + 0) U) (A U) sumSp0_fun sumSp0_fun_bij.
HB.instance Definition _ :=
  @BijHom.Build (A U) ((A + 0) U) sumSp0_inv sumSp0_inv_bij.

End Mor.
Definition sumSp0  : A + 0 ~~> A := @sumSp0_fun.

Fact sumSp0_natural : naturality (A + 0) A sumSp0.
Proof. by move=> U V h []. Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (A + 0) A sumSp0 sumSp0_natural.

Lemma sumSp0_invE : isoSpinv sumSp0 =%= sumSp0_inv.
Proof. by apply: eq_nattrans_sym; apply: isoSpinvrE => U; apply: sumSp0_funK. Qed.

End SumSpeciesZero.


Section SumSpeciesAssociative.
Variables (A B C : Species).

Section Mor.
Variable (U : Bij).
Definition sumSpA_fun : el ((A + (B + C)) U) -> el ((A + B + C) U) :=
  fun x => match x with
           | inl a => inl (inl a)
           | inr (inl b) => inl (inr b)
           | inr (inr a) => inr a
           end.
Definition sumSpA_inv : el ((A + B + C) U) -> el ((A + (B + C)) U) :=
  fun x => match x with
           | inl (inl a) => inl a
           | inl (inr b) => inr (inl b)
           | inr a => inr (inr a)
           end.
Fact sumSpA_funK : cancel sumSpA_fun sumSpA_inv.
Proof. by case => [|[]]. Qed.
Fact sumSpA_invK : cancel sumSpA_inv sumSpA_fun.
Proof. by case => [[]|]. Qed.
Fact sumSpA_fun_bij : bijective sumSpA_fun.
Proof. by exists sumSpA_inv; [exact sumSpA_funK | exact: sumSpA_invK]. Qed.
Fact sumSpA_inv_bij : bijective sumSpA_inv.
Proof. by exists sumSpA_fun; [exact sumSpA_invK | exact: sumSpA_funK]. Qed.
HB.instance Definition _ :=
  @BijHom.Build ((A + (B + C)) U) ((A + B + C) U) sumSpA_fun sumSpA_fun_bij.
HB.instance Definition _ :=
  @BijHom.Build ((A + B + C) U) ((A + (B + C)) U) sumSpA_inv sumSpA_inv_bij.

End Mor.
Definition sumSpA  : A + (B + C) ~~> A + B + C := sumSpA_fun.
Definition sumSpAV : A + B + C ~~> A + (B + C) := sumSpA_inv.

Fact sumSpA_natural : naturality (A + (B + C)) (A + B + C) sumSpA.
Proof. by move=> U V h [|[]]. Qed.
Fact sumSpAV_natural : naturality (A + B + C) (A + (B + C)) sumSpAV.
Proof. by move=> U V h [[]|]. Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (A + (B + C)) (A + B + C) sumSpA sumSpA_natural.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (A + B + C) (A + (B + C)) sumSpAV sumSpAV_natural.

Lemma sumSpAVE : sumSpAV =%= isoSpinv sumSpA.
Proof. by apply isoSpinvrE => U x /=; rewrite sumSpA_funK. Qed.

End SumSpeciesAssociative.


Section SumNatTransf.

Variable (A1 A2 B1 B2 : Species) (tA : A1 ~> A2) (tB : B1 ~> B2).

Section Defs.
Variable (U : Bij).

Definition sumSpTr_fun (x : el ((A1 + B1)%species U)) : el ((A2 + B2)%species U) :=
  match x with
  | inl a => inl (tA U a)
  | inr b => inr (tB U b)
  end.
Definition sumSpTr_inv (x : el ((A2 + B2)%species U)) : el ((A1 + B1)%species U) :=
  match x with
  | inl a => inl (finv (tA U) a)
  | inr b => inr (finv (tB U) b)
  end.
Lemma sumSpTr_funK : cancel sumSpTr_fun sumSpTr_inv.
Proof. by case=> [] x /=; rewrite finvK. Qed.
Lemma sumSpTr_invK : cancel sumSpTr_inv sumSpTr_fun.
Proof. by case=> [] x /=; rewrite finvKV. Qed.
Fact sumSpTr_fun_bij : bijective sumSpTr_fun.
Proof. by exists sumSpTr_inv; [exact sumSpTr_funK | exact sumSpTr_invK]. Qed.
HB.instance Definition _ :=
  BijHom.Build ((A1 + B1)%species U) ((A2 + B2)%species U)
    sumSpTr_fun sumSpTr_fun_bij.
End Defs.

Definition sumSpTr : A1 + B1 ~~> A2 + B2 := @sumSpTr_fun.
Fact sumSpTr_natural : naturality (A1 + B1) (A2 + B2) sumSpTr.
Proof. by move=> U V h [a|b] /=; rewrite !hom_compE natural. Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (A1 + B1) (A2 + B2) sumSpTr sumSpTr_natural.

End SumNatTransf.

Lemma sumSpTr_invE (A1 A2 B1 B2 : Species) (tA : A1 ~> A2) (tB : B1 ~> B2) :
  isoSpinv (sumSpTr tA tB) =%= sumSpTr (isoSpinv tA) (isoSpinv tB).
Proof. by apply: eq_nattrans_sym; apply: isoSpinvrE => U [] x /= /[!finvK]. Qed.
