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

Variable (S T : finType)  (f : S -> T) (I : {set S}).

Lemma imsetCE : bijective f -> [set f y | y in ~: I] =  ~: [set f i | i in I].
Proof.
move=> f_bij.
apply/setP => y; rewrite inE.
(* apply/imsetP/(negPP imsetP) => [[x /[swap] ->{y}] |]. *)
apply/imsetP/idP => [[x /[swap] ->{y}] |].
  by rewrite inE; apply contra => /imsetP[z z_in_I/(bij_inj f_bij)->].
move: f_bij => [g fK gK] y_notin.
exists (g y); last by rewrite gK.
move: y_notin; rewrite inE; apply contra => gy_in_i.
by apply/imsetP; exists (g y); last by rewrite gK.
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


Section Card.

HB.instance Definition _ (S : Bij) :=
  BijHom.Build _ _ (@enum_rank S : el S -> el ('I_#|S| : Bij)) (@enum_rank_bij S).
Definition enum_rankBij (S : Bij) : {hom[Bij] S -> 'I_#|S|} :=
  @enum_rank S : el S -> el ('I_#|S| : Bij).

Definition cardSp (A : Species) (n : nat) := #|A 'I_n|.
Lemma cardSpE (A : Species) (S : Bij) : #|A S| = cardSp A #|S|.
Proof. exact: BijHom_eq_card (A # (@enum_rankBij S)). Qed.

End Card.


Definition Sp0_fun := fun _ : Bij => voidB.
Definition Sp0_mor (A B : Bij) (f : {hom[Bij] A -> B}) :
  {hom[Bij] voidB -> voidB} := idfun.
HB.instance Definition _ :=
  @isFunctor.Build Bij Bij Sp0_fun Sp0_mor
    (fun _ _ _ _ _ => frefl _) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition Sp0 : Species := Sp0_fun.
Notation "0" := Sp0 : species_scope.

Lemma cardSp0 n : cardSp 0 n = 0%N.
Proof. by rewrite /cardSp /= card_void. Qed.


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
  BijHom.Build (SumSp_fun S) (SumSp_fun T) (SumSp_mor f) (SumSp_mor_bij f).
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

Lemma card_sumSp A B n : cardSp (A + B) n = (cardSp A n + cardSp B n)%N.
Proof. by rewrite /SumSp /SumSp_fun /= /cardSp /= card_sum. Qed.


Section SumSpeciesCom.

Implicit Types (A B : Species).

Definition SumSpC_fun A B S : el ((A + B) S) -> el ((B + A) S) :=
  fun x => match x with inl a => inr a | inr b => inl b end.

Lemma SumSpC_funK A B S : cancel (@SumSpC_fun A B S) (@SumSpC_fun B A S).
Proof. by case. Qed.
Fact SumSpC_bij A B S : bijective (@SumSpC_fun A B S).
Proof. by exists (SumSpC_fun (S := S)); exact: SumSpC_funK. Qed.
HB.instance Definition _ A B S :=
  @BijHom.Build ((A + B) S) ((B + A) S) (@SumSpC_fun A B S) (@SumSpC_bij A B S).
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
  @BijHom.Build ((A + 0) S) (A S) SumSp0_fun SumSp0_fun_bij.
HB.instance Definition _ :=
  @BijHom.Build (A S) ((A + 0) S) SumSp0_inv SumSp0_inv_bij.

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
Definition Tin (X : {set T}) := el ({x : T | x \in X} : Bij).

Definition cast_Tin (y : Tin I) : Tin J := ecast X (Tin X) eq y.
Definition cast_TinV (y : Tin J) : Tin I := ecast X (Tin X) (esym eq) y.

Lemma cast_TinE y : \val (cast_Tin y) = \val y.
Proof. by rewrite /cast_Tin; case: y => [x Hx] /=; case:_/eq. Qed.
Lemma cast_TinVE y : \val (cast_TinV y) = \val y.
Proof. by rewrite /cast_TinV; case: y => [x Hx] /=; case:_/(esym eq). Qed.
Lemma cast_TinK : cancel cast_Tin cast_TinV.
Proof. by move=> x; apply: val_inj; rewrite cast_TinVE cast_TinE. Qed.
Lemma cast_TinVK : cancel cast_TinV cast_Tin.
Proof. by move=> x; apply: val_inj; rewrite cast_TinE cast_TinVE. Qed.
Fact cast_Tin_bij : bijective cast_Tin.
Proof. exists cast_TinV; [exact: cast_TinK | exact: cast_TinVK]. Qed.
Fact cast_TinV_bij : bijective cast_TinV.
Proof. exists cast_Tin; [exact: cast_TinVK | exact: cast_TinK]. Qed.
HB.instance Definition _ := BijHom.Build _ _ cast_Tin cast_Tin_bij.
HB.instance Definition _ := BijHom.Build _ _ cast_TinV cast_TinV_bij.

Definition cast_hom : {hom _ -> _} := cast_Tin.
Definition cast_homV : {hom _ -> _} := cast_TinV.

Lemma Tagged_Tin_castE (x : Tin I) :
  Tagged Tin x = Tagged Tin (ecast X (Tin X) eq x).
Proof. by move: x; subst I. Qed.

End EqCast.

Lemma Tagged_SpTin_castE (T : Bij) (I J : {set T}) (eq : I = J) (A : Species) x :
  Tagged (fun S => A (Tin S)) ((A # cast_hom eq) x) = Tagged (fun S => A (Tin S)) x.
Proof.
subst I => /=.
have /functor_ext_hom -> /= : cast_hom (erefl J) =1 idfun by [].
by rewrite functor_id_hom.
Qed.


Lemma restr_id (S : Bij) (I : {set S}) :
  restr_hom I [hom idfun] =1 cast_hom (esym (imset_id I)).
Proof. by move=> x /=; apply val_inj; rewrite cast_TinE. Qed.
Lemma restr_comp (S T U : Bij) (f : {hom S -> T}) (g : {hom T -> U}) (I : {set S}) :
  restr_hom _ g \o restr_hom I f
  =1 cast_hom (imset_comp g f I) \o restr_hom _ (g \o f).
Proof. by move => x /=; apply val_inj; rewrite cast_TinE !val_restrE. Qed.
Lemma restr_ext (S T : Bij) (f g : {hom S -> T}) (I : {set S}) (eq_fg : f =1 g) :
  restr_hom I f =1 cast_hom (eq_imset _ (fsym eq_fg)) \o (restr_hom I g).
Proof. by move => x /=; apply val_inj; rewrite !cast_TinE !val_restrE. Qed.


Section ProductSpecies.

Definition SpSet (A : Species) (S : Bij) : predArgType :=
  { I : {set S} & A { x : S | x \in I } }.

Variable A B : Species.

Section Elements.
Variable (S : Bij).

Record prodSpType : predArgType := MkProdSp {
                      seta : {set S};
                      vala : A {x : S | x \in seta};
                      setb : {set S};
                      valb : B {x : S | x \in setb};
                      prodsp_dijs : seta == ~: setb
                    }.
Definition to_auxType (x : prodSpType) : SpSet A S * SpSet B S :=
  (Tagged (i := (seta x)) _ (vala x), Tagged (i := (setb x)) _ (valb x)).
Definition from_auxType (y : SpSet A S * SpSet B S) : option prodSpType :=
  let: (existT a xa, existT b xb) := y in
  match boolP (a == ~: b) with
  | @AltTrue _ _ eq => Some (MkProdSp xa xb eq)
  | _ => None
  end.
Lemma to_auxTypeK : pcancel to_auxType from_auxType.
Proof.
move=> [a va b vb eq] /=.
case (boolP (a == ~: b)) => [eq'|]; last by rewrite eq.
by rewrite (bool_irrelevance eq eq').
Qed.
HB.instance Definition _ := Finite.copy prodSpType (pcan_type to_auxTypeK).
Definition prodSpT : Bij := prodSpType.

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
move=> [a va b vb eq] /=; rewrite /prodSp_fun /=.
apply/eqP; rewrite eqE /= /to_auxType /= {eq} -pair_eqE /=; apply/andP; split.
- have /= -> := functor_ext_hom A _ _ (restr_id (I := a)).
  by rewrite /= Tagged_SpTin_castE.
- have /= -> := functor_ext_hom B _ _ (restr_id (I := b)).
  by rewrite /= Tagged_SpTin_castE.
Qed.
Lemma prodSp_fun_comp S T U (f : {hom[Bij] S -> T}) (g : {hom[Bij] T -> U}) :
  prodSp_fun g \o prodSp_fun f =1 prodSp_fun (g \o f).
Proof.
rewrite /prodSp_fun => [][a va b vb eq] /=.
apply/eqP; rewrite eqE /= /to_auxType /= {eq} -pair_eqE /=; apply/andP; split.
- rewrite -[_ (_ va)]compapp -functor_o /=.
  have /= -> := functor_ext_hom A _ _ (restr_comp f g (I := a)).
  by rewrite functor_o /= Tagged_SpTin_castE.
- rewrite -[_ (_ vb)]compapp -functor_o /=.
  have /= -> := functor_ext_hom B _ _ (restr_comp f g (I := b)).
  by rewrite functor_o /= Tagged_SpTin_castE.
Qed.
Lemma prodSp_fun_ext S T (f g : {hom[Bij] S -> T}) :
  f =1 g -> prodSp_fun f =1 prodSp_fun g.
Proof.
rewrite /prodSp_fun => eqfg [a va b vb eq] /=.
apply/eqP; rewrite eqE /= /to_auxType /= {eq} -pair_eqE /=; apply/andP; split.
- have /= -> := functor_ext_hom A _ _ (restr_ext eqfg).
  by rewrite functor_o /= Tagged_SpTin_castE.
- have /= -> := functor_ext_hom B _ _ (restr_ext eqfg).
  by rewrite functor_o /= Tagged_SpTin_castE.
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

(*
Lemma card_ProdSp S : #|prodSp S| = 0%N.
Proof.
rewrite -(card_imset predT (pcan_inj (@to_auxTypeK S))).
pose P := [set 
rewrite /prodSp /prodSpT.
card_imset
rewrite card_tagged /= sumnE big_map big_enum /=.
 *)

End ProductSpecies.

