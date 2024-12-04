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


Section SSRCompl.

Variable (S T : finType) (f : S -> T) (I : {set S}).

Lemma imsetCE : bijective f -> [set f y | y in ~: I] =  ~: [set f i | i in I].
Proof.
move=> f_bij.
apply/setP => y; rewrite inE.
apply/imsetP/(negPP imsetP) => [[x /[swap] ->{y}] |].
  by rewrite inE => /[swap] [[z z_in_I /(bij_inj f_bij)-> /[!z_in_I]]].
move: f_bij => [g fK gK] nex.
exists (g y); last by rewrite gK.
rewrite inE; apply/negP => gy_in_i; apply: nex.
by exists (g y); last rewrite gK.
Qed.

Lemma imsetT : bijective f -> [set f y | y in [set: S]] = [set: T].
Proof.
move=> [fV fK fKV]; apply/setP => i; rewrite inE; apply/imsetP.
by exists (fV i).
Qed.

End SSRCompl.



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

Lemma BijP (S T : Bij) (f : {hom S -> T}) : bijective f.
Proof. exact: (isHom_inhom f). Qed.
Hint Resolve BijP : core.

Section Homs.

Variable (S T : Bij) (f : {hom[Bij] S -> T}).

Lemma hom_is_isom :
  { finv | bijective finv & (cancel finv f * cancel f finv)%type }.
Proof.
have:= isHom_inhom f; rewrite /inhom /= => f_bij.
pose ff := [ffun x : el S => f x : el T].
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
Definition finv : el T -> el S := let: exist2 finv P1 P2 := hom_is_isom in finv.

Lemma finv_bij : bijective finv.
Proof. by rewrite /finv; case: hom_is_isom. Qed.
HB.instance Definition _ := isHom.Build _ T S finv finv_bij.

Lemma finvK : cancel f finv.
Proof. by rewrite /finv; case: hom_is_isom => x _ []. Qed.
Lemma finvKV : cancel finv f.
Proof. by rewrite /finv; case: hom_is_isom => x _ []. Qed.

End Homs.

HB.factory Record BijHom (S T : Bij)
  (f : el S -> el T) := { finsetsbij_hom : bijective f }.
HB.builders Context (S T : Bij)
  (f : el S -> el T) of BijHom S T f.
HB.instance Definition _ := isHom.Build _ S T f finsetsbij_hom.
HB.instance Definition _ := isIsom.Build _ S T f (finv_bij f) (finvK f) (finvKV f).
HB.end.

Lemma BijHom_eq_card (S T : Bij) (f : {hom[Bij] S -> T}) : #|S| = #|T|.
Proof. exact: (bij_eq_card (isHom_inhom f)). Qed.


Definition voidB := (void : Bij).
Definition unitB := (unit : Bij).
Definition boolB := (bool : Bij).

Definition negbB : el boolB -> el boolB := negb.

HB.instance Definition _ :=
  BijHom.Build boolB boolB negbB (inv_bij negbK).


Definition Species := {functor Bij -> Bij}.


Section Cardinality.

Definition TinSet (T : Bij) (X : {set T}) : Bij := {x : T | x \in X} : Bij.

Lemma card_TinSet (T : Bij) (S : {set T}) : #|TinSet S| = #|S|.
Proof.
rewrite -[LHS](card_imset _ val_inj); congr #|pred_of_set _|.
apply/setP => x; apply/imsetP/idP => [[/= [y y_in_S] _ ->] // | x_in_S].
by exists (exist _ x x_in_S).
Qed.

HB.instance Definition _ (S : Bij) :=
  BijHom.Build _ _ (@enum_rank S : el S -> el ('I_#|S| : Bij)) (@enum_rank_bij S).
Definition enum_rankBij (S : Bij) : {hom[Bij] S -> 'I_#|S|} :=
  @enum_rank S : el S -> el ('I_#|S| : Bij).

Definition cardSp (A : Species) (n : nat) := #|A 'I_n|.
Lemma cardSpE (A : Species) (S : Bij) : #|A S| = cardSp A #|S|.
Proof. exact: BijHom_eq_card (A # (@enum_rankBij S)). Qed.

Definition SpSet (A : Species) (S : Bij) : predArgType :=
  { I : {set S} & A (TinSet I) }.
Lemma cardSp_set (A : Species) (T : Bij) (S : {set T}) :
  cardSp A #|S| = #|[set p : SpSet A T | tag p == S]|.
Proof.
rewrite -(card_TinSet S) -cardSpE.
pose totag (x : A (TinSet S)) : SpSet A T :=
  Tagged (fun U : {set T} => A (TinSet U)) x.
have totag_inj : injective totag.
  by rewrite /totag=> x y /eqP /[!eq_Tagged] /= /eqP.
rewrite -(card_imset _ totag_inj); congr #|pred_of_set _|.
apply/setP => /= x; apply/imsetP/idP => [[y _ ->{x}] /[!inE] //| ].
move: x => [U x /[!inE] /= /eqP U_eq_S]; subst S.
by exists x.
Qed.

End Cardinality.


Section Localization.

Definition setTB (T : Bij) : Bij := TinSet [set: T] : Bij.

Section Defs.
Variable (T : Bij).
Definition toSetT_fun (x : el T) : setTB T := exist _ x (in_setT x).
Definition toSetT_inv (x : el (setTB T)) : T := \val x.
Lemma toSetT_funK : cancel toSetT_fun toSetT_inv.
Proof. by []. Qed.
Lemma toSetT_invK : cancel toSetT_inv toSetT_fun.
Proof. by move=> [x pf]; apply val_inj. Qed.
Lemma toSetT_bij : bijective toSetT_fun.
Proof. by exists toSetT_inv; [exact: toSetT_funK | exact: toSetT_invK]. Qed.
Fact toSetT_inv_bij : bijective toSetT_inv.
Proof. by exists toSetT_fun; [exact: toSetT_invK | exact: toSetT_funK]. Qed.
HB.instance Definition _ :=
  @BijHom.Build T (setTB T) toSetT_fun toSetT_bij.
HB.instance Definition _ :=
  @BijHom.Build (setTB T) T toSetT_inv toSetT_inv_bij.

End Defs.

Definition setTB_mor (T U : Bij) (f : {hom T -> U}) : {hom setTB T -> setTB U} :=
  [hom @toSetT_fun U \o f \o @toSetT_inv T].
Fact setTB_ext : FunctorLaws.ext setTB_mor.
Proof. by move=> T U f g eq x; apply val_inj; rewrite /= eq. Qed.
Fact setTB_id : FunctorLaws.id setTB_mor.
Proof. by move=> T x; apply val_inj. Qed.
Fact setTB_comp  : FunctorLaws.comp setTB_mor.
Proof. by move=> /= T U V f g x; apply val_inj. Qed.
HB.instance Definition _ := @isFunctor.Build Bij Bij setTB setTB_mor
                              setTB_ext setTB_id setTB_comp.

Definition SpSetT : Species := setTB.

Definition toSetT : FId ~~> SpSetT := toSetT_fun.
Definition toSetTV : SpSetT ~~> FId := toSetT_inv.
Lemma toSetT_natural : naturality FId SpSetT toSetT.
Proof. by []. Qed.
Lemma toSetTV_natural : naturality SpSetT FId toSetTV.
Proof. by []. Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij FId SpSetT toSetT toSetT_natural.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij SpSetT FId toSetTV toSetTV_natural.

Lemma toSetTK : toSetTV \v toSetT =%= NId FId.
Proof. by move=> S x /=; rewrite toSetT_funK. Qed.
Lemma toSetTVK : toSetT \v toSetTV =%= NId setTB.
Proof. by move=> S x /=; rewrite toSetT_invK. Qed.

End Localization.


Section ZeroSpecies.

Definition Sp0_fun := fun _ : Bij => voidB.
Definition Sp0_mor (A B : Bij) (f : {hom[Bij] A -> B}) :
  {hom[Bij] voidB -> voidB} := idfun.
HB.instance Definition _ :=
  @isFunctor.Build Bij Bij Sp0_fun Sp0_mor
    (fun _ _ _ _ _ => frefl _) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition Sp0 : Species := Sp0_fun.
Lemma cardSp0 n : cardSp Sp0 n = 0%N.
Proof. by rewrite /cardSp /= card_void. Qed.

End ZeroSpecies.
Notation "0" := Sp0 : species_scope.


Section SpDelta.

Variable (C : nat).
Definition SpDelta_fun := fun S : Bij => if #|S| == C then unitB else voidB.
Lemma SpDelta_funE (A B : Bij) (f : {hom[Bij] A -> B}) :
  SpDelta_fun A = SpDelta_fun B.
Proof. by rewrite /SpDelta_fun (BijHom_eq_card f). Qed.
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

Lemma card_SpDelta n : cardSp SpDelta n = (n == C).
Proof.
rewrite /cardSp /= /SpDelta_fun /= card_ord.
by case: eqP => _; rewrite ?card_unit ?card_void.
Qed.

End SpDelta.
Notation "1" := (SpDelta 0) : species_scope.
Notation "\X" := (SpDelta 1) : species_scope.

Lemma cardSp1 n : cardSp 1 n = (n == 0%N).
Proof. exact: card_SpDelta. Qed.
Lemma cardSpX n : cardSp \X n = (n == 1%N).
Proof. exact: card_SpDelta. Qed.

Lemma SpDeltaE n S (x : SpDelta n S) : all_equal_to x.
Proof. by apply: fintype_le1P; rewrite cardSpE card_SpDelta; case eqP. Qed.

Section SumSpecies.

Variable A B : Species.

Definition sumSp_fun S : Bij := (A S + B S)%type.
Definition sumSp_mor S T (f : {hom[Bij] S -> T}) :
  el (sumSp_fun S) -> el (sumSp_fun T) :=
  fun x => match x with
           | inl a => inl ((A # f) a)
           | inr b => inr ((B # f) b)
           end.
Lemma sumSp_mor_bij S T (f : {hom[Bij] S -> T}) : bijective (sumSp_mor f).
Proof.
exists (sumSp_mor (finv f)); case => [a|b] /=; congr (_ _);
  rewrite -[LHS]compapp -functor_o.
- by rewrite -[RHS](@functor_id _ _ A); apply/functor_ext_hom/finvK.
- by rewrite -[RHS](@functor_id _ _ B); apply/functor_ext_hom/finvK.
- by rewrite -[RHS](@functor_id _ _ A); apply/functor_ext_hom/finvKV.
- by rewrite -[RHS](@functor_id _ _ B); apply/functor_ext_hom/finvKV.
Qed.
HB.instance Definition _ S T (f : {hom[Bij] S -> T}) :=
  BijHom.Build (sumSp_fun S) (sumSp_fun T) (sumSp_mor f) (sumSp_mor_bij f).
Fact sumSp_ext : FunctorLaws.ext sumSp_mor.
Proof. by move=> S T f g eq [a|b] /=; congr (_ _); apply: functor_ext_hom. Qed.
Fact sumSp_id : FunctorLaws.id sumSp_mor.
Proof. by move=> S [a|b] /=; rewrite functor_id. Qed.
Fact sumSp_comp  : FunctorLaws.comp sumSp_mor.
Proof. by move=> S T U f g [a|b]; rewrite /= functor_o. Qed.
HB.instance Definition _ :=
  @isFunctor.Build Bij Bij sumSp_fun sumSp_mor sumSp_ext sumSp_id sumSp_comp.
Definition sumSp : Species := sumSp_fun.

End SumSpecies.

Notation "f + g" := (sumSp f g) : species_scope.

Lemma card_sumSp A B n : cardSp (A + B) n = (cardSp A n + cardSp B n)%N.
Proof. by rewrite /sumSp /sumSp_fun /= /cardSp /= card_sum. Qed.


Section SumSpeciesCommutative.

Implicit Types (A B : Species).

Definition sumSpC_fun A B S : el ((A + B) S) -> el ((B + A) S) :=
  fun x => match x with inl a => inr a | inr b => inl b end.

Lemma sumSpC_funK A B S : cancel (@sumSpC_fun A B S) (@sumSpC_fun B A S).
Proof. by case. Qed.
Fact sumSpC_bij A B S : bijective (@sumSpC_fun A B S).
Proof. by exists (sumSpC_fun (S := S)); exact: sumSpC_funK. Qed.
HB.instance Definition _ A B S :=
  @BijHom.Build ((A + B) S) ((B + A) S) (@sumSpC_fun A B S) (@sumSpC_bij A B S).
Definition sumSpC A B : (A + B) ~~> (B + A) := @sumSpC_fun A B.

Fact sumSpC_natural A B : naturality (A + B) (B + A) (sumSpC A B).
Proof. by move=> S T h []. Qed.
HB.instance Definition _ A B :=
  @isNatural.Build Bij Bij (A + B) (B + A)
    (sumSpC A B) (@sumSpC_natural A B).

Lemma sumSpCK A B : sumSpC B A \v sumSpC A B =%= NId (A + B).
Proof. by move=> S []. Qed.

End SumSpeciesCommutative.


Section SumSpeciesZero.
Variable (A : Species).

Section Mor.
Variable (S : Bij).
Definition sumSp0_fun : (el ((A + 0) S)) -> (el (A S)) :=
  fun x => match x with inl a => a | inr b => match b with end end.
Definition sumSp0_inv : (el (A S)) -> (el ((A + 0) S)) := fun a => inl a.
Let sumSp0_funK : cancel sumSp0_fun sumSp0_inv.
Proof. by case => [|[]]. Qed.
Let sumSp0_invK : cancel sumSp0_inv sumSp0_fun.
Proof. by []. Qed.
Fact sumSp0_fun_bij : bijective sumSp0_fun.
Proof. by exists sumSp0_inv. Qed.
Fact sumSp0_inv_bij : bijective sumSp0_inv.
Proof. by exists sumSp0_fun. Qed.
HB.instance Definition _ :=
  @BijHom.Build ((A + 0) S) (A S) sumSp0_fun sumSp0_fun_bij.
HB.instance Definition _ :=
  @BijHom.Build (A S) ((A + 0) S) sumSp0_inv sumSp0_inv_bij.

End Mor.
Definition sumSp0  : A + 0 ~~> A := @sumSp0_fun.
Definition sumSp0V : A ~~> A + 0 := @sumSp0_inv.

Fact sumSp0_natural : naturality (A + 0) A sumSp0.
Proof. by move=> S T h []. Qed.
Fact sumSp0V_natural : naturality A (A + 0) sumSp0V.
Proof. by []. Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (A + 0) A sumSp0 sumSp0_natural.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij A (A + 0) sumSp0V sumSp0V_natural.

Lemma sumSp0K : sumSp0V \v sumSp0 =%= NId (A + 0).
Proof. by move=> S []. Qed.
Lemma sumSp0VK : sumSp0 \v sumSp0V =%= NId A.
Proof. by []. Qed.

Definition Sum0Sp : 0 + A ~> A := sumSp0 \v (sumSpC 0 A).
Definition Sum0SpV : A ~> 0 + A := (sumSpC A 0) \v sumSp0V.

Lemma Sum0SpK : Sum0SpV \v Sum0Sp =%= NId (0 + A).
Proof. by move=> S []. Qed.
Lemma Sum0SpVK : Sum0Sp \v Sum0SpV =%= NId A.
Proof. by []. Qed.

End SumSpeciesZero.


Section SumSpeciesAssociative.
Variables (A B C : Species).

Section Mor.
Variable (S : Bij).
Definition sumSpA_fun : el ((A + (B + C)) S) -> el ((A + B + C) S) :=
  fun x => match x with
           | inl a => inl (inl a)
           | inr (inl b) => inl (inr b)
           | inr (inr a) => inr a
           end.
Definition sumSpA_inv : el ((A + B + C) S) -> el ((A + (B + C)) S) :=
  fun x => match x with
           | inl (inl a) => inl a
           | inl (inr b) => inr (inl b)
           | inr a => inr (inr a)
           end.
Let sumSpA_funK : cancel sumSpA_fun sumSpA_inv.
Proof. by case => [|[]]. Qed.
Let sumSpA_invK : cancel sumSpA_inv sumSpA_fun.
Proof. by case => [[]|]. Qed.
Fact sumSpA_fun_bij : bijective sumSpA_fun.
Proof. by exists sumSpA_inv. Qed.
Fact sumSpA_inv_bij : bijective sumSpA_inv.
Proof. by exists sumSpA_fun. Qed.
HB.instance Definition _ :=
  @BijHom.Build ((A + (B + C)) S) ((A + B + C) S) sumSpA_fun sumSpA_fun_bij.
HB.instance Definition _ :=
  @BijHom.Build ((A + B + C) S) ((A + (B + C)) S) sumSpA_inv sumSpA_inv_bij.

End Mor.
Definition sumSpA  : (A + (B + C)) ~~> (A + B + C) := sumSpA_fun.
Definition sumSpAV : (A + B + C) ~~> (A + (B + C)) := sumSpA_inv.

Fact sumSpA_natural : naturality (A + (B + C)) (A + B + C) sumSpA.
Proof. by move=> S T h [|[]]. Qed.
Fact sumSpAV_natural : naturality (A + B + C) (A + (B + C)) sumSpAV.
Proof. by move=> S T h [[]|]. Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (A + (B + C)) (A + B + C) sumSpA sumSpA_natural.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (A + B + C)( A + (B + C)) sumSpAV sumSpAV_natural.

Lemma sumSpAK : sumSpAV \v sumSpA =%= NId (A + (B + C)).
Proof. by move=> S [|[]]. Qed.
Lemma sumSpAVK : sumSpA \v sumSpAV =%= NId (A + B + C).
Proof. by move=> S [[]|]. Qed.

End SumSpeciesAssociative.


Section Restriction.

Variable (S T : Bij) (I : {set S}) (f : {hom S -> T}).

Fact restr_subproof (x : {x : S | x \in I}) : f (\val x) \in [set f x | x in I].
Proof. by case: x => x Px /=; apply: imset_f. Qed.
Definition restr (x : el ({x : S | x \in I} : Bij)) :
      el ({x : T | x \in [set f y | y in I]} : Bij) :=
  exist _ (f (\val x)) (restr_subproof x).

Fact restr_inv_spec (y : {x : T | x \in [set f y | y in I]}) :
  { x : {x : S | x \in I} | restr x == y }.
Proof.
case: y => /= [y Py].
case: (pickP (fun x : S => (x \in I) && (f x == y))) =>
      [x /andP [x_in_I /eqP eq] | Hfalse].
  by exists (exist _ x x_in_I); rewrite /restr /=; exact/eqP/val_inj.
exfalso; move: Py Hfalse => /imsetP[x x_in_I ->{y}] /(_ x).
by rewrite x_in_I eqxx.
Qed.
Definition restr_inv y := \val (restr_inv_spec y).
Let restrK : cancel restr restr_inv.
Proof.
move=> /= x; rewrite /restr /restr_inv /=.
case: (restr_inv_spec _) => x0 /= /eqP/(congr1 val)/=.
by move/(bij_inj (BijP f)) => eq; exact: val_inj.
Qed.
Let restrKV : cancel restr_inv restr.
Proof.
move=> y; apply val_inj; rewrite /restr_inv.
by case: (restr_inv_spec y) => /= x /eqP <-{y}.
Qed.
Fact restr_bij : bijective restr.
Proof. by exists restr_inv. Qed.
HB.instance Definition _ := BijHom.Build _ _ restr restr_bij.
Definition restr_hom :
  {hom[Bij] {x : S | x \in I} -> {x : T | x \in [set f y | y in I]}} := restr.

Lemma val_restrE x : \val (restr x) = f (\val x).
Proof. by []. Qed.

End Restriction.


Section EqCast.

Variable (T : Bij) (I J : {set T}) (eq : I = J).

Definition cast_TinSet (y : el (TinSet I)) : el (TinSet J) :=
  ecast X (TinSet X) eq y.
Definition cast_TinSetV (y : el (TinSet J)) : el (TinSet I) :=
  ecast X (TinSet X) (esym eq) y.

Lemma cast_TinSetE y : \val (cast_TinSet y) = \val y.
Proof. by rewrite /cast_TinSet; case: y => [x Hx] /=; case:_/eq. Qed.
Lemma cast_TinSetVE y : \val (cast_TinSetV y) = \val y.
Proof. by rewrite /cast_TinSetV; case: y => [x Hx] /=; case:_/(esym eq). Qed.
Lemma cast_TinSetK : cancel cast_TinSet cast_TinSetV.
Proof. by move=> x; apply: val_inj; rewrite cast_TinSetVE cast_TinSetE. Qed.
Lemma cast_TinSetVK : cancel cast_TinSetV cast_TinSet.
Proof. by move=> x; apply: val_inj; rewrite cast_TinSetE cast_TinSetVE. Qed.
Fact cast_TinSet_bij : bijective cast_TinSet.
Proof. exists cast_TinSetV; [exact: cast_TinSetK | exact: cast_TinSetVK]. Qed.
Fact cast_TinSetV_bij : bijective cast_TinSetV.
Proof. exists cast_TinSet; [exact: cast_TinSetVK | exact: cast_TinSetK]. Qed.
HB.instance Definition _ := BijHom.Build _ _ cast_TinSet cast_TinSet_bij.
HB.instance Definition _ := BijHom.Build _ _ cast_TinSetV cast_TinSetV_bij.

Definition cast_hom : {hom _ -> _} := cast_TinSet.
Definition cast_homV : {hom _ -> _} := cast_TinSetV.

Lemma Tagged_TinSet_castE (x : TinSet I) :
  Tagged (@TinSet T) x = Tagged (@TinSet T) (ecast X (TinSet X) eq x).
Proof. by move: x; subst I. Qed.

End EqCast.

Lemma Tagged_SpTinSet_castE (T : Bij) (I J : {set T}) (eq : I = J) (A : Species) x :
  Tagged (fun S => A (TinSet S)) ((A # cast_hom eq) x) =
    Tagged (fun S => A (TinSet S)) x.
Proof.
subst I => /=.
have /functor_ext_hom -> /= : cast_hom (erefl J) =1 idfun by [].
by rewrite functor_id_hom.
Qed.


Lemma restr_id (S : Bij) (I : {set S}) :
  restr_hom I [hom idfun] =1 cast_hom (esym (imset_id I)).
Proof. by move=> x /=; apply val_inj; rewrite cast_TinSetE. Qed.
Lemma restr_comp (S T U : Bij) (f : {hom S -> T}) (g : {hom T -> U}) (I : {set S}) :
  restr_hom _ g \o restr_hom I f
  =1 cast_hom (imset_comp g f I) \o restr_hom _ (g \o f).
Proof. by move => x /=; apply val_inj; rewrite cast_TinSetE !val_restrE. Qed.
Lemma restr_ext (S T : Bij) (f g : {hom S -> T}) (I : {set S}) (eq_fg : f =1 g) :
  restr_hom I f =1 cast_hom (eq_imset _ (fsym eq_fg)) \o (restr_hom I g).
Proof. by move => x /=; apply val_inj; rewrite !cast_TinSetE !val_restrE. Qed.


Section ProductSpecies.

Definition appSpSet (A : Species) {T : Bij} := fun (S : {set T}) => A (TinSet S).

Variable A B : Species.

Section Elements.
Variable (S : Bij).

Record prodSpType : predArgType := MkProdSp {
                      seta : {set S};
                      vala : appSpSet A seta;
                      setb : {set S};
                      valb : appSpSet B setb;
                      prodsp_dijs : seta == ~: setb
                    }.
Definition prodSpPair (x : prodSpType) : SpSet A S * SpSet B S :=
  (Tagged (appSpSet A) (vala x), Tagged (appSpSet B) (valb x)).
Definition from_auxType (y : SpSet A S * SpSet B S) : option prodSpType :=
  let: (existT a xa, existT b xb) := y in
  match boolP (a == ~: b) with
  | @AltTrue _ _ eq => Some (MkProdSp xa xb eq)
  | _ => None
  end.
Lemma prodSpPairK : pcancel prodSpPair from_auxType.
Proof.
move=> [a va b vb eq] /=.
case (boolP (a == ~: b)) => [eq'|]; last by rewrite eq.
by rewrite (bool_irrelevance eq eq').
Qed.
HB.instance Definition _ := Finite.copy prodSpType (pcan_type prodSpPairK).
Definition prodSpT : Bij := prodSpType.

Lemma eq_prodSpP (i j : prodSpT) :
  reflect
    (Tagged (appSpSet A) (vala i) = Tagged (appSpSet A) (vala j) /\
     Tagged (appSpSet B) (valb i) = Tagged (appSpSet B) (valb j))
     (i == j).
Proof.
rewrite /eq_op /= /prodSpPair /= xpair_eqE.
by apply (iffP andP) => [][]/eqP -> /eqP ->.
Qed.

End Elements.


Lemma prodSp_mor_subproof S T (f : {hom[Bij] S -> T}) (x : prodSpT S) :
  f @: seta x ==  ~: f @: setb x.
Proof. by rewrite (eqP (prodsp_dijs x)) (imsetCE _ (BijP f)). Qed.

Definition prodSp_fun S T (f : {hom[Bij] S -> T}) (x : el (prodSpT S : Bij))
  : el (prodSpT T : Bij)
  := MkProdSp ((A # restr_hom _ f) (vala x)) ((B # restr_hom _ f) (valb x))
       (prodSp_mor_subproof f x).
Lemma prodSp_fun_id S : prodSp_fun (S := S) [hom idfun] =1 idfun.
Proof.
move=> [a va b vb eq] /=; apply/eqP/eq_prodSpP; split.
- have /= -> := functor_ext_hom A _ _ (restr_id (I := a)).
  by rewrite /= Tagged_SpTinSet_castE.
- have /= -> := functor_ext_hom B _ _ (restr_id (I := b)).
  by rewrite /= Tagged_SpTinSet_castE.
Qed.
Lemma prodSp_fun_comp S T U (f : {hom[Bij] S -> T}) (g : {hom[Bij] T -> U}) :
  prodSp_fun g \o prodSp_fun f =1 prodSp_fun (g \o f).
Proof.
rewrite /prodSp_fun => [][a va b vb eq] /=; apply/eqP/eq_prodSpP; split.
- rewrite -[_ (_ va)]compapp -functor_o /=.
  have /= -> := functor_ext_hom A _ _ (restr_comp f g (I := a)).
  by rewrite functor_o /= Tagged_SpTinSet_castE.
- rewrite -[_ (_ vb)]compapp -functor_o /=.
  have /= -> := functor_ext_hom B _ _ (restr_comp f g (I := b)).
  by rewrite functor_o /= Tagged_SpTinSet_castE.
Qed.
Lemma prodSp_fun_ext S T (f g : {hom[Bij] S -> T}) :
  f =1 g -> prodSp_fun f =1 prodSp_fun g.
Proof.
rewrite /prodSp_fun => eqfg [a va b vb eq] /=; apply/eqP/eq_prodSpP; split.
- have /= -> := functor_ext_hom A _ _ (restr_ext eqfg).
  by rewrite functor_o /= Tagged_SpTinSet_castE.
- have /= -> := functor_ext_hom B _ _ (restr_ext eqfg).
  by rewrite functor_o /= Tagged_SpTinSet_castE.
Qed.

Lemma prodSp_fun_bij S T (f : {hom[Bij] S -> T}) : bijective (prodSp_fun f).
Proof.
exists (prodSp_fun (finv f)) => x; rewrite -[LHS]compapp prodSp_fun_comp.
- have /prodSp_fun_ext -> : finv f \o f =1 idfun by move=> y /=; rewrite finvK.
  by rewrite prodSp_fun_id.
- have /prodSp_fun_ext -> : f \o finv f =1 idfun by move=> y /=; rewrite finvKV.
  by rewrite prodSp_fun_id.
Qed.
HB.instance Definition _ S T (f : {hom[Bij] S -> T}) :=
  BijHom.Build (prodSpT S) (prodSpT T) (prodSp_fun f) (prodSp_fun_bij f).
Definition prodSp_mor S T (f : {hom[Bij] S -> T}) : {hom _ -> _} := prodSp_fun f.
Fact prodSp_ext : FunctorLaws.ext prodSp_mor.
Proof. exact: prodSp_fun_ext. Qed.
Fact prodSp_id : FunctorLaws.id prodSp_mor.
Proof. exact: prodSp_fun_id. Qed.
Fact prodSp_comp  : FunctorLaws.comp prodSp_mor.
Proof. by move=> S T U f g x; have /= <- := (prodSp_fun_comp g f x). Qed.

HB.instance Definition _ :=
  @isFunctor.Build Bij Bij prodSpT prodSp_mor prodSp_ext prodSp_id prodSp_comp.
Definition prodSp : Species := prodSpT.


Lemma imset_prodSpPair S :
  (@prodSpPair S) @: xpredT = [set p | tag p.1 == ~: tag p.2].
Proof.
apply/setP => /= [][[a vala] [b valb]]; rewrite !inE /=.
apply/imsetP/eqP => [[/= [a' vala' b' valb' eq _ ]] | /eqP eq].
  by move=> [/[swap] _ -> /[swap] _ ->]; apply/eqP.
by exists (MkProdSp vala valb eq).
Qed.

Lemma card_prodSp n :
  cardSp prodSp n = \sum_(i < n.+1) 'C(n, i) * (cardSp A i) * (cardSp B (n - i)).
Proof.
rewrite {1}/cardSp.
pose Pairs := (SpSet A 'I_n * SpSet B 'I_n)%type.
rewrite -(card_imset predT (pcan_inj (@prodSpPairK 'I_n))) imset_prodSpPair.
rewrite -sum1_card.
rewrite -[LHS]big_enum [LHS](partition_big (fun p => tag p.1) xpredT) //=.
have cardle (S : {set 'I_n}) : #|S| < n.+1.
  rewrite ltnS -[X in _ <= X](card_ord n).
  exact/subset_leq_card/subset_predT.
pose cardS S := Ordinal (cardle S).
rewrite -[LHS]big_enum [LHS](partition_big cardS xpredT) //=; apply eq_bigr => i _.
rewrite big_enum_cond /=.
under eq_bigl => S do rewrite -val_eqE /=.
rewrite {cardS cardle} -[X in 'C(X, i)](card_ord n) -card_draws.
rewrite -sum1_card !big_distrl /=.
apply esym; under eq_bigl => S do rewrite inE.
apply eq_bigr => S /eqP eq_card.
rewrite mul1n big_enum_cond /= sum1dep_card /=.
rewrite [[set _ | _ ]](_ : _ =
  setX [set p : (SpSet A 'I_n) | tag p == S]
       [set p : (SpSet B 'I_n) | tag p == ~: S]); first last.
  apply/setP => p; rewrite !inE andbC; case: eqP => //= ->.
  by rewrite eq_sym inv_eq //; exact: setCK.
rewrite [RHS]cardsX -!cardSp_set eq_card; congr (_ * (cardSp _ _)).
rewrite -[X in X - i]card_ord.
have:= (cardsCs S); rewrite eq_card => ->.
exact/subKn/subset_leq_card/subset_predT.
Qed.

End ProductSpecies.

Notation "f * g" := (prodSp f g) : species_scope.


Section ProdSpeciesCommutative.

Implicit Types (A B : Species).
Lemma prodSpC_subproof A B S (x : el ((A * B) S)) : setb x == ~: seta x.
Proof. by rewrite (eqP (prodsp_dijs x)) setCK. Qed.

Definition prodSpC_fun A B S : el ((A * B) S) -> el ((B * A) S)
  := fun x => MkProdSp (valb x) (vala x) (prodSpC_subproof x).

Lemma prodSpC_funK A B S : cancel (@prodSpC_fun A B S) (@prodSpC_fun B A S).
Proof.
move=> [a va b vb eq]; rewrite /prodSpC_fun /=.
by congr MkProdSp; apply: bool_irrelevance.
Qed.
Fact prodSpC_bij A B S : bijective (@prodSpC_fun A B S).
Proof. by exists (prodSpC_fun (S := S)); exact: prodSpC_funK. Qed.
HB.instance Definition _ A B S :=
  @BijHom.Build ((A * B) S) ((B * A) S) (@prodSpC_fun A B S) (@prodSpC_bij A B S).
Definition prodSpC A B : (A * B) ~~> (B * A) := @prodSpC_fun A B.

Fact prodSpC_natural A B : naturality (A * B) (B * A) (prodSpC A B).
Proof.
move=> S T h [a va b vb eq]; rewrite /= /prodSp_fun /prodSpC_fun /=.
by congr MkProdSp; apply: bool_irrelevance.
Qed.
HB.instance Definition _ A B :=
  @isNatural.Build Bij Bij (A * B) (B * A)
    (prodSpC A B) (@prodSpC_natural A B).

Lemma prodSpCK A B : prodSpC B A \v prodSpC A B =%= NId (A * B).
Proof.
move=> S [a va b vb eq]; rewrite /= /prodSpC_fun /=.
by congr MkProdSp; apply: bool_irrelevance.
Qed.

End ProdSpeciesCommutative.


Section ProdSpeciesZero.

Variable (A : Species).

Section Mor.
Variable (S : Bij).
Definition prodSp0_fun : el ((A * 0) S) -> el (0 S).
by move=> [a va [f []]].
Defined.
Definition prodSp0_inv : el (0 S) -> el ((A * 0) S).
by []. Defined.
Lemma prodSp0_funK : cancel prodSp0_fun prodSp0_inv.
Proof. by move=> [a va [f []]]. Qed.
Lemma prodSp0_invK : cancel prodSp0_inv prodSp0_fun.
Proof. by []. Qed.
Fact prodSp0_fun_bij : bijective prodSp0_fun.
Proof. exists prodSp0_inv; [exact: prodSp0_funK | exact: prodSp0_invK]. Qed.
Fact prodSp0_inv_bij : bijective prodSp0_inv.
Proof. exists prodSp0_fun; [exact: prodSp0_invK | exact: prodSp0_funK]. Qed.
HB.instance Definition _ :=
  @BijHom.Build ((A * 0) S) (0 S) prodSp0_fun prodSp0_fun_bij.
HB.instance Definition _ :=
  @BijHom.Build (0 S) ((A * 0) S) prodSp0_inv prodSp0_inv_bij.

End Mor.
Definition prodSp0  : A * 0 ~~> 0 := @prodSp0_fun.
Definition prodSp0V : 0 ~~> A * 0 := @prodSp0_inv.

Fact prodSp0_natural : naturality (A * 0) 0 prodSp0.
Proof. by move=> S T h []. Qed.
Fact prodSp0V_natural : naturality 0 (A * 0) prodSp0V.
Proof. by move=> S T h []. Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (A * 0) 0 prodSp0 prodSp0_natural.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij 0 (A * 0) prodSp0V prodSp0V_natural.

Definition prod0Sp : 0 * A ~> 0 := prodSp0 \v (prodSpC 0 A).
Definition Prod0SpV : 0 ~> 0 * A := (prodSpC A 0) \v prodSp0V.

End ProdSpeciesZero.


Section ProdSpeciesOne.

Lemma appSpSet1_card T (S : {set T}) : appSpSet 1 S -> #|S| = 0%N.
Proof.
rewrite /appSpSet /SpDelta /SpDelta_fun /= /SpDelta_fun card_TinSet.
by case eqP.
Qed.

Section Mor.
Variable (A : Species).
Variable (S : Bij).

Definition prodSp1_inv_def : el (A S) -> el ((A * 1) S).
move=> x.
pose a : A {x : S | x \in setT} := (A # toSetT S) x.
have b : 1 {x : S | x \in set0}.
  rewrite /SpDelta /= /SpDelta_fun card_TinSet cards0 eqxx.
  exact tt.
by apply: (MkProdSp a b _); rewrite setC0.
Defined.
Definition prodSp1_inv := locked prodSp1_inv_def.
Lemma prodSp1_inv_inj : injective prodSp1_inv.
Proof.
rewrite /prodSp1_inv; unlock.
have aux_lemma i : (A # toSetTV S) ((A # toSetT S) i) = i.
  rewrite -![(A # _) _]compapp -!functor_o.
  have /= ->:= functor_ext_hom A _ _ (@toSetTK S) i.
  by rewrite NIdE !functor_id /=.
move=> i j /eqP/eq_prodSpP [/[swap] _] /eqP.
rewrite !eq_Tagged => /eqP /(congr1 (A # toSetTV S)) /=.
by rewrite !aux_lemma.
Qed.
Lemma prodSp1_inv_bij : bijective prodSp1_inv.
Proof.
apply: (inj_card_bij prodSp1_inv_inj).
rewrite !cardSpE card_prodSp.
rewrite (bigD1 (Ordinal (ltnSn #|S|))) //= binn mul1n cardSp1 subnn eqxx muln1.
rewrite big1 ?addn0 // => [i]; rewrite -val_eqE /= => /negbTE neqi.
rewrite cardSp1 subn_eq0 leqNgt.
have:= ltn_ord i; rewrite ltnS leq_eqVlt neqi /= => -> /=.
by rewrite !muln0.
Qed.
HB.instance Definition _ :=
  @BijHom.Build (A S) ((A * 1) S) prodSp1_inv prodSp1_inv_bij.
Definition prodSp1_hom : {hom (A * 1) S -> A S} := inv_hom prodSp1_inv.
Lemma prodSp1_homK : cancel prodSp1_hom prodSp1_inv.
Proof. exact: inv_homK. Qed.
Lemma prodSp1_invK : cancel prodSp1_inv prodSp1_hom.
Proof. exact: isom_invK. Qed.
End Mor.
Definition prodSp1V (A : Species) : A ~~> A * 1 := @prodSp1_inv A.
Definition prodSp1 (A : Species) : A * 1 ~~> A := @prodSp1_hom A.

Lemma restr_hom_setTE (U V : Bij) (f : {hom U -> V}) :
  restr_hom setT f \o toSetT U
  =1 cast_TinSet (esym (imsetT (BijP f))) \o (toSetT V \o f).
Proof. by move=> x; apply val_inj; rewrite cast_TinSetE. Qed.

Fact prodSp1V_natural A : naturality A (A * 1) (prodSp1V A).
Proof.
move=> S T h x /=.
apply/eqP/eq_prodSpP; split => /=.
  rewrite /prodSp1_inv; unlock; rewrite /= -![(A # _) _]compapp -!functor_o /=.
  have /= -> := functor_ext_hom A _ _ (restr_hom_setTE h).
  by rewrite functor_o /= Tagged_SpTinSet_castE.
have eq0 : h @: (setb (prodSp1_inv x)) = setb (prodSp1_inv ((A # h) x)).
  by rewrite /prodSp1_inv; unlock; rewrite /= imset0.
have /= <- := Tagged_SpTinSet_castE eq0 (A := 1).
rewrite -[(1 # _) _]compapp -functor_o.
apply/eqP; rewrite eq_Tagged /=; apply/eqP.
apply SpDeltaE.
Qed.
Fact prodSp1_natural A : naturality (A * 1) A (prodSp1 A).
Proof. exact: (natural_inv (@prodSp1V_natural A)). Qed.

HB.instance Definition _ A :=
  @isNatural.Build Bij Bij A (A * 1) (@prodSp1V A) (@prodSp1V_natural A).
HB.instance Definition _ A :=
  @isNatural.Build Bij Bij (A * 1) A (@prodSp1 A) (@prodSp1_natural A).

Definition prod1Sp A : 1 * A ~> A := prodSp1 A \v prodSpC 1 A.
Definition Prod1SpV A : A ~> 1 * A := prodSpC A 1 \v prodSp1V A.

Lemma prodSp1K A : prodSp1V A \v prodSp1 A =%= NId (A * 1).
Proof. exact: prodSp1_homK. Qed.
Lemma prodSp1KV A : prodSp1 A \v prodSp1V A =%= NId A.
Proof. exact: prodSp1_invK. Qed.

End ProdSpeciesOne.


(** TODO associativity of product and distributivity over addition *)
