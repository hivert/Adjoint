From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup.

Require Import category species sum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Local Open Scope category_scope.

Declare Scope species_scope.
Delimit Scope category_scope with species.
Local Open Scope species_scope.


Section ProductSpecies.
Variable A B : Species.

Implicit Type (U V W : Bij).

Definition part2 U (Z X Y : {set U}) := (Z == X :|: Y) && [disjoint X & Y].
Lemma part2C U (Z X Y : {set U}) : part2 Z X Y = part2 Z Y X.
Proof. by rewrite /part2 setUC disjoint_sym. Qed.
Lemma part2_imset U V (Z X Y : {set U}) (f : U -> V) :
  injective f -> part2 (f @: Z) (f @: X) (f @: Y) = part2 Z X Y.
Proof.
move=> finj; rewrite /part2 -imsetU (inj_eq (imset_inj finj)).
by rewrite (imset_disjoint finj).
Qed.
Lemma part2TE U (X Y : {set U}) : part2 setT X Y = (X == ~: Y).
Proof.
rewrite /part2; apply/idP/eqP => [/andP[/eqP eqU dXY] | ->].
  rewrite -setTD eqU setDUl setDv setU0.
  apply/setP => x /[!inE]; rewrite andbC; case H : (x \in X) => //=.
  by move: dXY; rewrite disjoints_subset => /subsetP/(_ _ H) /[!inE] ->.
by rewrite setUC setUCr eqxx /= disjoint_sym -subsets_disjoint subxx.
Qed.

Definition prodSpT (U : Bij) : Bij :=
  { p : SpSet A U * SpSet B U | part2 setT (tag p.1) (tag p.2) }.

Lemma prodSp_mor_subproof U V (f : {hom U -> V}) (x : el (prodSpT U)) :
  part2 setT (tag ((SpSet A # f) (val x).1)) (tag ((SpSet B # f) (val x).2)).
Proof.
case: x => -/=[[a xa][b xb] /= Hp2].
by rewrite -(imsetT (BijP f)) part2_imset.
Qed.
Definition prodSp_mor U V (f : {hom U -> V})
  (x : el (prodSpT U)) : el (prodSpT V) :=
  exist _ ((SpSet A # f) (val x).1, (SpSet B # f) (val x).2)
    (prodSp_mor_subproof f x).

Lemma eq_prodSpP U (x y : prodSpT U) :
  (val x).1 = (val y).1 -> (val x).2 = (val y).2 -> x = y.
Proof.
case: x y => /= [[x1 x2] Hx][[y1 y2] Hy] /= eqx eqy; subst x1 x2.
by apply/eqP; rewrite /eq_op /=.
Qed.
Lemma eq_prodSpE U (x y : prodSpT U) :
  ((val x).1 == (val y).1) && ((val x).2 == (val y).2) = (x == y).
Proof. by apply/andP/eqP => [[/eqP + /eqP]|->//]; apply: eq_prodSpP. Qed.

Lemma prodSp_id : FunctorLaws.id prodSp_mor.
Proof.
rewrite /prodSp_mor => U /= -[[xa xb] /= Hp2].
by apply/eq_prodSpP; rewrite /= !functor_id.
Qed.
Lemma prodSp_comp : FunctorLaws.comp prodSp_mor.
Proof.
rewrite /prodSp_mor => U V W f g /= -[[xa xb] /= Hp2].
by apply/eq_prodSpP; rewrite /= !functor_o.
Qed.
Lemma prodSp_ext : FunctorLaws.ext prodSp_mor.
Proof.
rewrite /prodSp_mor => U V f g eqfg /= -[[xa xb] /= Hp2].
by apply/eq_prodSpP; rewrite /= !(functor_ext_hom (SpSet _) _ _ eqfg).
Qed.
Lemma prodSp_mor_bij U V (f : {hom U -> V}) : bijective (prodSp_mor f).
Proof. exact: (functor_bij prodSp_ext prodSp_id prodSp_comp). Qed.
HB.instance Definition _ U V (f : {hom U -> V}) :=
  BijHom.Build (prodSpT U) (prodSpT V) (prodSp_mor f) (prodSp_mor_bij f).
HB.instance Definition _ :=
  isFunctor.Build Bij Bij prodSpT prodSp_ext prodSp_id prodSp_comp.


Definition prodSp : Species := prodSpT.

Lemma card_prodSp n :
  cardSp prodSp n = \sum_(i < n.+1) 'C(n, i) * (cardSp A i) * (cardSp B (n - i)).
Proof.
rewrite {1}/cardSp; rewrite -(card_imset predT val_inj) /= imset_val_sub.
have cardle (E : {set 'I_n}) : #|E| < n.+1.
  rewrite ltnS -[X in _ <= X](card_ord n).
  exact/subset_leq_card/subset_predT.
pose cardS E := Ordinal (cardle E).
rewrite [LHS](card_preim (fun p => tag p.1)) /=.
rewrite [LHS](partition_big (fun E : {set 'I_n} => cardS E) xpredT) //=.
apply eq_bigr => i _.
rewrite -[X in 'C(X, i)](card_ord n) -card_draws -sum1_card !big_distrl /=.
apply: eq_big => [E | E /eqP/(congr1 val) /= eq_card].
  by rewrite inE -val_eqE /=.
rewrite [[set _ | _ ]](_ : _ =
  setX [set p : (SpSet A 'I_n) | tag p == E]
       [set p : (SpSet B 'I_n) | tag p == ~: E]); first last.
  apply/setP => -[a b]; rewrite !inE andbC; case: eqP => //= -> {a}.
  by rewrite part2C part2TE.
rewrite mul1n [LHS]cardsX -!card_SpSet eq_card; congr (_ * (cardSp _ _)).
rewrite -[X in X - i]card_ord.
have:= (cardsCs E); rewrite -eq_card => ->.
exact/esym/subKn/subset_leq_card/subset_predT.
Qed.


Lemma tag1_act_prodSp U (x : prodSp U) (s : {perm U}) :
  tag (\val (actSp _ _ x s)).1 = s @: (tag (\val x).1).
Proof. by case: x => [[[]]]. Qed.
Lemma tag2_act_prodSp U (x : prodSp U) (s : {perm U}) :
  tag (\val (actSp _ _ x s)).2 = s @: (tag (\val x).2).
Proof. by case: x => [[?[]]]. Qed.


Section ToPair.
Variables (n : nat) (i : 'I_n.+1).
Definition prodSpCTag := {x : prodSp 'I_n | #|tag (\val x).1| == i}.

Section Def.
Variable x : prodSpCTag.

Lemma card_tag1_prodSp : #|tag (\val (\val x)).1| == i.
Proof. by case: x => []. Qed.
Lemma card_tag2_prodSp : #|tag (\val (\val x)).2| == n - i.
Proof.
case: x => [[[a b] /= /[swap] /eqP taga]]; rewrite part2TE => /eqP.
move/(congr1 (fun c : {set _} => #|c|))/esym; rewrite {}taga => <-.
by rewrite cardsCs setCK -[X in _ == X - _](card_ord n) subKn // max_card.
Qed.
Definition toIsoPair : {set A 'I_i} * {set B 'I_(n - i)} :=
  ( isoclass (SpSetC2ord (exist _ (\val (val x)).1 card_tag1_prodSp)),
    isoclass (SpSetC2ord (exist _ (\val (val x)).2 card_tag2_prodSp)) ).
End Def.

Lemma toIsoPair_inj :
  {in [set x | \val x \in isoreprs prodSp 'I_n] &, injective toIsoPair}.
Proof.
move=> [x tx1][y ty1]; rewrite !inE /= => Hx Hy.
rewrite /toIsoPair => -[/eqP + /eqP]; rewrite !orbit_eq_mem.
repeat move : (card_tag1_prodSp _) => /= {}; move=> tx1' ty1'.
repeat move : (card_tag2_prodSp _) => /=; move=> tx2 ty2.
rewrite !isoclass_SpSetC2ord /= => /orbitP[/= s1 _].
rewrite /actSp_fun /= /SpSetC_mor /= => /(congr1 val) /= => eq1 {tx1' ty1'}.
move=> /orbitP[/= s2 _].
rewrite /actSp_fun /= /SpSetC_mor /= => /(congr1 val) /= => eq2.
apply val_inj => /=; apply/eqP; rewrite -(isoreprsE Hx Hy) {Hx Hy}.
rewrite orbit_sym.
apply/orbitP; rewrite /= /actSp_fun /= /prodSp_mor /=.
case: x y tx1 tx2 ty1 ty2 eq1 eq2.
move=> /= [[E1 x1][E2 x2] /= px] /=[] [[F1 y1][F2 y2] /= py] cE1 cF2 cF1 cE2.
rewrite eqSpSet => /= -[eqEF1 /(_ eqEF1)].
rewrite eq_Tagged /= hom_compE -functor_o /= => /eqP eq1.
rewrite eqSpSet => /= -[eqEF2 /(_ eqEF2)].
rewrite eq_Tagged /= hom_compE -functor_o /= => /eqP eq2.
have := px; rewrite part2TE => /eqP HE.
have := py; rewrite part2TE => /eqP HF.
exists (glue_perm HE HF eqEF1 eqEF2); first by rewrite inE.
apply val_inj => /=; apply/eqP; rewrite xpair_eqE; apply/andP; split.
- apply/eqP; rewrite eqSpSet /=; split => [|eqtag].
    rewrite -[RHS]eqEF1; apply eq_in_imset => x.
    by rewrite permE /= => ->.
  rewrite eq_Tagged /= hom_compE -functor_o; apply/eqP; rewrite -{}[RHS]eq1.
  apply: (functor_ext_hom A) => {}y /=.
  by apply: val_inj; rewrite /= !val_cast_TSet /= !permE /= TSetP.
- apply/eqP; rewrite eqSpSet /=; split => [|eqtag].
    rewrite -[RHS]eqEF2; apply eq_in_imset => x.
    by rewrite permE /= HF inE => ->.
  rewrite eq_Tagged /= hom_compE -functor_o; apply/eqP; rewrite -{}[RHS]eq2.
  apply: (functor_ext_hom B) => {}x /=.
  by apply: val_inj; rewrite /= !val_cast_TSet /= !permE /= HF inE TSetP.
Qed.


Lemma toIsoPairP (x1 x2 : prodSpCTag) :
  val x1 \in isoclass (val x2) -> toIsoPair x1 = toIsoPair x2.
Proof.
move=> H; rewrite /toIsoPair; unlock => /=.
apply/eqP; rewrite xpair_eqE !orbit_eq_mem !isoclass_SpSetC2ord.
move: H => /orbitP[/= s _ Heq]; apply/andP.
by split; apply/orbitP; exists s => //; apply val_inj; rewrite /= -{}Heq.
Qed.

End ToPair.

Lemma cardiso_prodSp n :
  cardiso prodSp n = \sum_(i < n.+1) (cardiso A i) * (cardiso B (n - i)).
Proof.
have csub_pf (E : {set 'I_n}) : #|E| < n.+1.
  rewrite ltnS -[X in _ <= X](card_ord n).
  exact/subset_leq_card/subset_predT.
pose csub E := Ordinal (csub_pf E).
rewrite -cardiso_ordE -card_isoreprE.
rewrite [LHS](card_preim (fun x => csub (tag (val x).1))); apply eq_bigr => i _.
rewrite -!cardiso_ordE -[RHS]cardsX.
transitivity #|[set x : prodSpCTag i | val x \in isoreprs prodSp 'I_n]|.
  rewrite -[RHS](card_imset _ (val_inj)); congr #|pred_of_set _|.
  apply/setP => p; rewrite inE.
  apply/idP/imsetP => [|[/= [q Hq] /[!inE] /= Hiso {p}->]].
    rewrite -[X in _ && X](inj_eq val_inj) /= => /andP [Hiso Htag].
    by exists (exist _ p Htag) => //= /[!inE].
  by rewrite Hiso /= -(inj_eq val_inj).
rewrite {csub csub_pf} -(card_in_imset (@toIsoPair_inj n i)).
congr #|pred_of_set _|; apply/setP => [/=[CA CB]] /[!inE] /=.
apply/imsetP/andP => [[/=[[[a b]/= p2] taga _]]| /=].
  by rewrite /toIsoPair /= => [[-> ->]]; split; apply: imset_f.
move=> [/imsetP[a _ {CA}->]/imsetP[b _ {CB}->]].
pose SA := [set j : 'I_n | j < i].
pose SB := [set j : 'I_n | j >= i].
have cSA : #|SA| = i by rewrite {SB}/SA cardltset // -ltnS.
have part2S : part2 setT SA SB.
  by rewrite part2TE /SA /SB; apply/eqP/setP => j; rewrite !inE -ltnNge.
have cSB : #|SB| = n - i.
  rewrite -cSA -[X in X - _](card_ord n) cardsCs /=.
  by move: part2S; rewrite part2TE => /eqP ->.
pose fA := cast_ord cSA \o cast_ord (card_TSet SA) \o @enum_rank (TSet SA).
pose fB := cast_ord cSB \o cast_ord (card_TSet SB) \o @enum_rank (TSet SB).
pose xA : SpSet A 'I_n := existT _ SA ((A # (finv fA)) a).
pose xB : SpSet B 'I_n := existT _ SB ((B # (finv fB)) b).
pose x : prodSp _ := exist _ (xA, xB) part2S.
have xpf : #|tag (sval x).1| == i by rewrite /= cSA.
pose xiso := @isorepr prodSp 'I_n x.
have xisopf : #|tag (sval xiso).1| == i.
  rewrite {}/xiso; have [s /= <-] := isorepr_ex x.
  by rewrite /actSp_fun /= (card_imset _ perm_inj) cSA.
exists (exist _ xiso xisopf); first by rewrite inE /=; exact: isorepr_mem.
have /toIsoPairP -> /= : (val (exist _ xiso xisopf : prodSpCTag _))
                           \in isoclass (val (exist _ x xpf : prodSpCTag _)).
  exact: isorepr_class.
rewrite {xiso xisopf} /toIsoPair /= /x /SpSetC2ord; unlock.
move: (card_tag1_prodSp _) => /= PF1.
move: (card_tag2_prodSp _) => /= PF2.
rewrite {x xpf xA xB part2S}/fA {}/fB !hom_compE -!functor_o /=.
set fA := (X in A # X); set fB := (X in B # X).
have /(functor_ext_hom A) -> : fA =1 idfun.
  move=> x; rewrite /fA /= finv_comp /= finvKV finv_comp /= finvKV.
  have /finvE <- : cast_ord (eqP PF1) =1 cast_ord cSA.
    by move=> y; apply val_inj.
  by rewrite finvKV.
rewrite functor_id.
have /(functor_ext_hom B) -> : fB =1 idfun.
  move=> x; rewrite /fB /= finv_comp /= finvKV finv_comp /= finvKV.
  have /finvE <- : cast_ord (eqP PF2) =1 cast_ord cSB.
    by move=> y; apply val_inj.
  by rewrite finvKV.
by rewrite functor_id.
Qed.

End ProductSpecies.

Notation "f * g" := (prodSp f g) : species_scope.


Section ProdSpeciesCommutative.

Implicit Types (A B : Species).
Fact prodSpC_subproof A B U (x : el ((A * B) U)) :
  part2 setT (tag (val x).2) (tag (val x).1).
Proof. by case: x => [[a b]/=]; rewrite part2C. Qed.
Definition prodSpC_fun A B U : el ((A * B) U) -> el ((B * A) U)
  := fun x => exist _ ((val x).2, (val x).1) (prodSpC_subproof x).

Lemma prodSpC_funK A B U : cancel (@prodSpC_fun A B U) (@prodSpC_fun B A U).
Proof. by move=> [[a b] eq]; apply val_inj. Qed.
Fact prodSpC_bij A B U : bijective (@prodSpC_fun A B U).
Proof. by exists (prodSpC_fun (U := U)); exact: prodSpC_funK. Qed.
HB.instance Definition _ A B U :=
  @BijHom.Build ((A * B) U) ((B * A) U) (@prodSpC_fun A B U) (@prodSpC_bij A B U).
Definition prodSpC A B : A * B ~~> B * A := @prodSpC_fun A B.

Fact prodSpC_natural A B : naturality (A * B) (B * A) (prodSpC A B).
Proof. by move=> U V h [[a b] eq]; apply val_inj. Qed.
HB.instance Definition _ A B :=
  @isNatural.Build Bij Bij (A * B) (B * A)
    (prodSpC A B) (@prodSpC_natural A B).

Lemma prodSpCK A B : prodSpC B A \v prodSpC A B =%= NId (A * B).
Proof.
Proof. by move=> U [[a b] eq]; apply val_inj. Qed.
Lemma prodSpC_invE A B : isoSpinv (prodSpC A B) =%= prodSpC B A.
Proof. by apply: eq_nattrans_sym; apply: isoSpinvrE; apply: prodSpCK. Qed.

End ProdSpeciesCommutative.


Section ProdSpeciesZero.

Variable (A : Species).

Section Mor.
Variable (U : Bij).
Definition prodSp0_fun : el ((A * 0) U) -> el (0 U).
by move=> [[a /= [f []]]]. Defined.
Definition prodSp0_inv : el (0 U) -> el ((A * 0) U).
by []. Defined.
Lemma prodSp0_funK : cancel prodSp0_fun prodSp0_inv.
Proof. by move=> [[a /= [f []]]]. Qed.
Lemma prodSp0_invK : cancel prodSp0_inv prodSp0_fun.
Proof. by []. Qed.
Fact prodSp0_fun_bij : bijective prodSp0_fun.
Proof. exists prodSp0_inv; [exact: prodSp0_funK | exact: prodSp0_invK]. Qed.
Fact prodSp0_inv_bij : bijective prodSp0_inv.
Proof. exists prodSp0_fun; [exact: prodSp0_invK | exact: prodSp0_funK]. Qed.
HB.instance Definition _ :=
  @BijHom.Build ((A * 0) U) (0 U) prodSp0_fun prodSp0_fun_bij.
HB.instance Definition _ :=
  @BijHom.Build (0 U) ((A * 0) U) prodSp0_inv prodSp0_inv_bij.

End Mor.
Definition prodSp0  : A * 0 ~~> 0 := @prodSp0_fun.

Fact prodSp0_natural : naturality (A * 0) 0 prodSp0.
Proof. by move=> U V h [[a /= [f []]]]. Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (A * 0) 0 prodSp0 prodSp0_natural.

Lemma prodSp0_invE : isoSpinv prodSp0 =%= prodSp0_inv.
Proof. by apply: eq_nattrans_sym; apply: isoSpinvrE => U; apply: prodSp0_funK. Qed.

Definition prod0Sp : 0 * A ~> 0 := prodSp0 \v (prodSpC 0 A).
Lemma prod0Sp_invE : isoSpinv prod0Sp =%= (prodSpC A 0) \v isoSpinv prodSp0.
Proof.
apply: (eq_nattrans_trans (isoSpinv_vcomp _ _)) => U x /=.
by rewrite prodSpC_invE.
Qed.

End ProdSpeciesZero.


Section ProdSpeciesOne.

Lemma appSpSet1_card V (S : {set V}) : 1 (TSet S) -> #|S| = 0%N.
Proof. by rewrite /deltaSp /= /ifSp card_TSet; case eqP. Qed.

Variable (A : Species).

Section Mor.
Variable (U : Bij).

Definition prodSp1_inv_def : el (A U) -> el ((A * 1) U).
move=> x.
pose a : A {x : U | x \in setT} := (A # toSetT U) x.
have b : 1 {x : U | x \in set0}.
  by rewrite /deltaSp /= /ifSp card_TSet cards0 eqxx; exact tt.
apply: (exist _ (existT _ [set: U] a, existT _ set0 b) _).
by rewrite /= part2TE setC0.
Defined.
Definition prodSp1_inv := locked prodSp1_inv_def.

Lemma prodSp1_inv_inj : injective prodSp1_inv.
Proof.
rewrite /prodSp1_inv; unlock.
move=> i j /= /(congr1 val) /= [] /eqP.
rewrite !eq_Tagged => /eqP /(congr1 (A # finv (toSetT U))) /=.
by rewrite !SpfinvK.
Qed.
Lemma prodSp1_inv_bij : bijective prodSp1_inv.
Proof.
apply: (inj_card_bij prodSp1_inv_inj).
rewrite !cardSpE card_prodSp.
rewrite (bigD1 (Ordinal (ltnSn #|U|))) //= binn mul1n cardSp1 subnn eqxx muln1.
rewrite big1 ?addn0 // => [i]; rewrite -val_eqE /= => /negbTE neqi.
rewrite cardSp1 subn_eq0 leqNgt.
have:= ltn_ord i; rewrite ltnS leq_eqVlt neqi /= => -> /=.
by rewrite !muln0.
Qed.
HB.instance Definition _ :=
  @BijHom.Build (A U) ((A * 1) U) prodSp1_inv prodSp1_inv_bij.
Definition prodSp1_hom : {hom (A * 1) U -> A U} := finv prodSp1_inv.
Lemma prodSp1_homK : cancel prodSp1_hom prodSp1_inv.
Proof. exact: finvKV. Qed.
Lemma prodSp1_invK : cancel prodSp1_inv prodSp1_hom.
Proof. exact: finvK. Qed.
End Mor.
Definition prodSp1 : A * 1 ~~> A := @prodSp1_hom.
Definition prodSp1V : A ~~> A * 1 := @prodSp1_inv.

Lemma restr_hom_setTE (U V : Bij) (f : {hom U -> V}) :
  restr_hom setT f \o toSetT U
  =1 cast_TSet (esym (imsetT (BijP f))) \o (toSetT V \o f).
Proof. by move=> x; apply val_inj; rewrite val_cast_TSet. Qed.

Fact prodSp1V_natural : naturality A (A * 1) prodSp1V.
Proof.
move=> U V h x /=; apply: eq_prodSpP.
  rewrite /= /prodSp1_inv; unlock; rewrite /prodSp1_inv_def /=.
  rewrite /= !hom_compE -!functor_o /=.
  have /= -> := functor_ext_hom A _ _ (restr_hom_setTE h).
  by rewrite functor_o /= -/(Tagged _ _) Tagged_SpTSet_castE.
rewrite /prodSp1_inv -!lock /= -!/(Tagged _ _).
move: (eq_rect_r _ _) => HL; move: (eq_rect_r _ _) => HR.
rewrite -(Tagged_SpTSet_castE (imset0 h) (A := 1)).
rewrite [(1 # _) _]hom_compE -functor_o.
apply/eqP; rewrite eq_Tagged /=; apply/eqP.
exact: deltaSpE.
Qed.
Fact prodSp1_natural : naturality (A * 1) A prodSp1.
Proof. exact: (natural_inv prodSp1V_natural). Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij A (A * 1) prodSp1V prodSp1V_natural.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (A * 1) A prodSp1 prodSp1_natural.

Lemma prodSp1_invE : isoSpinv prodSp1 =%= prodSp1V.
Proof. by apply: eq_nattrans_sym; apply: isoSpinvrE => U; apply: prodSp1_homK. Qed.

Definition prod1Sp : 1 * A ~> A := prodSp1 \v prodSpC 1 A.
Lemma prod1Sp_invE : isoSpinv prod1Sp =%= (prodSpC A 1) \v isoSpinv prodSp1.
Proof.
apply: (eq_nattrans_trans (isoSpinv_vcomp _ _)) => U x /=.
by rewrite prodSpC_invE.
Qed.

End ProdSpeciesOne.


Section ProdSumSpeciesDistributive.
Variables (A B C : Species).

Section Mor.
Variable (U : Bij).

Definition prodSpDl_fun : el ((A * (B + C)) U) -> el ((A * B + A * C) U).
case=>[/=[a][X [b|c]]] /= Hp2.
exact: (inl (exist _ (a, existT _ X b) _)).
exact: (inr (exist _ (a, existT _ X c) _)).
Defined.
Definition prodSpDl_inv : el ((A * B + A * C) U) -> el ((A * (B + C)) U).
case=>[[[a [/= S b]]]|[[a [/= S c]]]] /= Hp2.
by exists (a, (existT _ S (inl b))).
by exists (a, (existT _ S (inr c))).
Defined.
Definition prodSpDl_funK : cancel prodSpDl_fun prodSpDl_inv.
Proof. by case=> [/=[a][X [b|c]]]. Qed.
Definition prodSpDl_invK : cancel prodSpDl_inv prodSpDl_fun.
Proof. by case=> [] [[a [/= S b]]]. Qed.
Fact prodSpDl_fun_bij : bijective prodSpDl_fun.
Proof. by exists prodSpDl_inv; [exact: prodSpDl_funK | exact: prodSpDl_invK]. Qed.
Fact prodSpDl_inv_bij : bijective prodSpDl_inv.
Proof. by exists prodSpDl_fun; [exact: prodSpDl_invK | exact: prodSpDl_funK]. Qed.
HB.instance Definition _ :=
  @BijHom.Build ((A * (B + C)) U) ((A * B + A * C) U) prodSpDl_fun prodSpDl_fun_bij.
HB.instance Definition _ :=
  @BijHom.Build ((A * B + A * C) U) ((A * (B + C)) U) prodSpDl_inv prodSpDl_inv_bij.

End Mor.
Definition prodSpDl  : A * (B + C) ~~> A * B + A * C := prodSpDl_fun.
Definition prodSpDlV : A * B + A * C ~~> A * (B + C) := prodSpDl_inv.

Fact prodSpDl_natural : naturality (A * (B + C)) (A * B + A * C) prodSpDl.
Proof.
by move=> U V h [/=[a][X [b|c]]] /= Hp2; congr (_ _); apply eq_prodSpP.
Qed.
Fact prodSpDlV_natural : naturality (A * B + A * C) (A * (B + C)) prodSpDlV.
Proof.
by move=> U V h [] [[a [/= S b]]] Hp2; apply eq_prodSpP.
Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (A * (B + C)) (A * B + A * C) prodSpDl prodSpDl_natural.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (A * B + A * C) (A * (B + C)) prodSpDlV prodSpDlV_natural.

Lemma prodSpDl_invE : isoSpinv prodSpDl =%= prodSpDlV.
Proof. by apply/eq_nattrans_sym/isoSpinvrE => U; apply: prodSpDl_funK. Qed.

End ProdSumSpeciesDistributive.

Definition prodSpDr A B C : (B + C) * A ~> B * A + C * A :=
  sumSpTr (prodSpC A B) (prodSpC A C) \v prodSpDl A B C \v prodSpC (B + C) A.
Lemma prodSpDr_invE A B C :
  isoSpinv (prodSpDr A B C) =%=
    prodSpC A (B + C) \v prodSpDlV A B C \v sumSpTr (prodSpC B A) (prodSpC C A).
Proof.
move=> U x; rewrite isoSpinv_vcomp /= prodSpC_invE /= isoSpinv_vcomp /=.
rewrite prodSpDl_invE /= !sumSpTr_invE /=.
(* Missing congruence lemma for sumSpTr here *)
by case: x => [a|b] /=; rewrite prodSpC_invE.
Qed.


Section UpSpecies.

Variables (U : Bij) (S : {set U}).
Implicit Type (T : {set TSet S}).

Definition upT T := [set \val x | x in T].
Lemma upT_subset T : upT T \subset S.
Proof. by apply/subsetP => x /imsetP[/= [y yinS _] /= {x}->]. Qed.
Lemma upT_setU T1 T2 : upT (T1 :|: T2) = upT T1 :|: upT T2.
Proof.
apply/setP => x; rewrite !inE.
apply/imsetP/idP => /=[[y /[swap] {x}-> /= /[!inE]] |].
  by rewrite /upT -!(mem_imset _ _ val_inj).
move=> /orP[]/imsetP[/= y yinT {x}->]; exists y => // /[!inE] /[!yinT] //.
by rewrite orbT.
Qed.
Lemma upT_setC T : upT (~: T) = S :\: upT T.
Proof.
apply/setP => x; rewrite !inE.
apply/imsetP/idP => /=[[[y yinS /= /[swap] eqx /=]] | /andP[xninT xinS]].
  by rewrite {x}eqx inE -(mem_imset _ _ val_inj) /= -/(upT T) => ->.
exists (exist _ x xinS) => //.
by rewrite inE -(mem_imset _ _ val_inj).
Qed.
Lemma upT_setT : upT setT = S.
Proof. by rewrite -setC0 upT_setC /upT imset0 setD0. Qed.

Variable (T : {set TSet S}).
Fact up_subproof (x : TSet T) : \val (\val x) \in upT T.
Proof.
rewrite mem_imset; last exact: val_inj.
exact: TSetP.
Qed.
Definition up (x : el (TSet T)) : el (TSet (upT T)) :=
  exist _ (val (val x)) (up_subproof x).
Fact up_bij : bijective up.
Proof.
apply: inj_card_bij; first by move=> x y [] /val_inj/val_inj.
by rewrite !card_TSet card_imset //; apply: val_inj.
Qed.
HB.instance Definition _ :=
  @BijHom.Build (TSet T) (TSet (upT T)) up up_bij.
End UpSpecies.
Arguments up {U S T}.

Section UpSpeciesInSet.
Variable (A : Species) (U : Bij) (S : {set U}).

Definition upSpSet (x : SpSet A (TSet S)) : SpSet A U :=
  let (E, y) := x in (existT _ (upT E) ((A # up) y)).
Lemma tag_upSpSet x : tag (upSpSet x) = upT (tag x).
Proof. by rewrite /upSpSet; case: x. Qed.

End UpSpeciesInSet.

Lemma SpSet_up (A : Species) (U V : Bij) (h : {hom U -> V}) (E : {set U})
  (x : SpSet A (TSet E)) :
  (SpSet A # h) (upSpSet x) = upSpSet ((SpSet A # (restr_hom E h)) x).
Proof.
case: x => [SE xSE] /=.
apply eqSpSet => /=; split => [|eqtag].
  by rewrite /upT -!imset_comp; apply eq_imset.
rewrite eq_Tagged /=; apply/eqP.
rewrite [RHS]hom_compE [LHS]hom_compE -!functor_o hom_compE -!functor_o /=.
apply: (functor_ext_hom A) => {xSE}x /=.
by apply val_inj; rewrite /= val_cast_TSet /=.
Qed.


Section DownSpecies.

Variables (U : Bij) (S T : {set U}).
Hypothesis (TsubS : T \subset S).
Fact down_subproof (x : TSet T) : val x \in S.
Proof. exact/(subsetP TsubS)/TSetP. Qed.
Definition down_fun (x : TSet T) : (TSet S) :=
  exist _ (\val x) (down_subproof x).
Definition downT := [set down_fun x | x in [set: TSet T]].

Lemma downTK : upT downT = T.
Proof.
rewrite /upT /downT -imset_comp; apply/setP => u.
apply/imsetP/idP => [[[y yinT /=] _ {u}-> //] | uinT].
by exists (exist _ u uinT).
Qed.
Lemma down_fun_inj : injective down_fun.
Proof. by move=> [x px][y py] /= [eqxy]; apply: val_inj => /=. Qed.
Fact down_fun_in (x : TSet T) : down_fun x \in down_fun @: setT.
Proof. by rewrite (mem_imset _ _ down_fun_inj). Qed.
Definition down (x : el (TSet T)) : el (TSet downT) :=
  exist _ (down_fun x) (down_fun_in x).
Fact down_bij : bijective down.
Proof.
apply: inj_card_bij; first by move=> [x px] [y py] [eq]; apply val_inj.
rewrite card_TSet (card_imset _ down_fun_inj).
by rewrite card_TSet cardsT card_TSet.
Qed.
HB.instance Definition _ :=
  @BijHom.Build (TSet T) (TSet downT) down down_bij.
End DownSpecies.

Section DownSpeciesInSet.
Variable (A : Species) (U : Bij) (S : {set U}) (x : SpSet A U).
Hypothesis tX : tag x \subset S.

Definition downSpSet : SpSet A (TSet S).
case: x tX => [/= T y TsubS].
apply (existT _ (downT TsubS) ((A # (down TsubS)) y)).
Defined.
Lemma tag_downSpSet : tag downSpSet = downT tX.
Proof. by rewrite /downSpSet; case: x tX. Qed.
Lemma downSpSetK : upSpSet downSpSet = x.
Proof.
rewrite /upSpSet /downSpSet.
case: x tX => [/= E y] ty.
apply eqSpSet => /=; split => [|eqtag]; first exact: downTK.
rewrite eq_Tagged /=; apply/eqP.
do 2 rewrite hom_compE -functor_o /=.
rewrite -[RHS](@functor_id _ _ A) /=; apply: (functor_ext_hom A) => {}y.
by apply val_inj; rewrite val_cast_TSet.
Qed.

End DownSpeciesInSet.


Section ProdSpeciesA3.

Variable (A B C : Species).
Implicit Type (U V : Bij).

Definition part3 U (W X Y : {set U}) :=
  [&& (setT == W :|: X :|: Y),
    [disjoint W & X], [disjoint W & Y] & [disjoint X & Y] ].
Lemma part3C U (W X Y : {set U}) : part3 W X Y = part3 X Y W.
Proof.
rewrite /part3 -setUA setUC; congr (_ && _).
by rewrite andbA andbC ![[disjoint W & _]]disjoint_sym.
Qed.
Lemma part3_imset U V (W X Y : {set U}) (f : {hom U -> V}) :
  part3 (f @: W) (f @: X) (f @: Y) = part3 W X Y.
Proof.
have finj := Bij_injP f.
rewrite /part3 !(imset_disjoint finj).
rewrite -!imsetU -(inj_eq (imset_inj finj)).
by rewrite (imsetT (BijP f)).
Qed.
Lemma part23 U (W X Y Z : {set U}) :
  part2 setT W Z -> part2 Z X Y -> part3 W X Y.
Proof.
rewrite /part2 /part3 =>/andP[/eqP eqU dWZ] /andP[/eqP eqZ ->].
rewrite andbT -setUA -eqZ eqU eqxx /=.
by rewrite !(disjointWr _ dWZ) // eqZ ?subsetUr ?subsetUl.
Qed.

Definition prodSp3T U : Bij :=
  { p : SpSet A U * SpSet B U * SpSet C U |
    part3 (tag p.1.1) (tag p.1.2) (tag p.2) }.
Definition prodSp3_mor U V (f : {hom U -> V}) : el (prodSp3T U) -> el (prodSp3T V).
move=> /= [[[a b] c] /= p3].
exists ((SpSet A # f) a, (SpSet B # f) b, (SpSet C # f) c) => /=.
by rewrite /SpSet_mor /= !tag_SpSet part3_imset.
Defined.

Fact prodSp3_id : FunctorLaws.id prodSp3_mor.
Proof.
rewrite /prodSp3_mor => U /= [[[a b] c] /= p3]; apply: val_inj => /=.
by rewrite !functor_id.
Qed.
Fact prodSp3_ext : FunctorLaws.ext prodSp3_mor.
Proof.
rewrite /prodSp3_mor => U V f g H /= [[[a b] c] /= p3]; apply: val_inj => /=.
by rewrite !(functor_ext_hom _ _ _ H).
Qed.
Fact prodSp3_comp : FunctorLaws.comp prodSp3_mor.
rewrite /prodSp3_mor => U V W f g /= [[[a b] c] /= p3]; apply: val_inj => /=.
by rewrite !functor_o.
Qed.
Fact prodSp3_bij U V (f : {hom U -> V}) : bijective (prodSp3_mor f).
Proof. exact: (functor_bij prodSp3_ext prodSp3_id prodSp3_comp). Qed.
HB.instance Definition _ U V (f : {hom U -> V}) :=
  BijHom.Build (prodSp3T U) (prodSp3T V) (prodSp3_mor f) (prodSp3_bij f).
HB.instance Definition _ :=
  isFunctor.Build Bij Bij prodSp3T prodSp3_ext prodSp3_id prodSp3_comp.

Definition prodSp3 : Species := prodSp3T.


Section MorphA3.
Variable (U : Bij).

Definition prodSpA3_fun : el ((A * (B * C)) U) -> el (prodSp3 U).
move=> [[/= xA [/= V ]]] [[xSB xSC]] /= BC_SC UA_V.
exists (xA, upSpSet xSB, upSpSet xSC).
rewrite /= !tag_upSpSet; apply: (part23 UA_V).
by rewrite -{1}(upT_setT V) /upT (part2_imset _ _ _ val_inj).
Defined.
Definition prodSpA3_inv : el (prodSp3 U) -> el ((A * (B * C)) U).
move=> [/=[[a b]c] /=] p3.
have bc : (B * C)%species (TSet (tag b :|: tag c)).
  pose xb := downSpSet (subsetUl (tag b) (tag c)).
  pose xc := downSpSet (subsetUr (tag b) (tag c)).
  exists (xb, xc) => /=.
  rewrite -(part2_imset _ _ _ val_inj) /= /xb /xc !tag_downSpSet /=.
  rewrite /downT -!imset_comp !(eq_imset (g := val)) //.
  move: p3 => /and4P[/eqP SU dab dac dbc].
  by rewrite !imsetTE /= !imset_val_TSet /part2 eqxx /=.
exists (a, existT _ (tag b :|: tag c) bc) => /=.
move: p3 => /and4P[/eqP SU dab dac dbc].
rewrite /part2 setUA SU eqxx /=.
move: dab dac; rewrite !disjoints_subset => /subsetP ab /subsetP ac.
by apply/subsetP => x xa; rewrite setCU inE (ab _ xa) (ac _ xa).
Defined.

Fact prodSpA3K : cancel prodSpA3_fun prodSpA3_inv.
Proof.
move=> [[/= xA [/= V ]]] [[xSB xSC]] /= BC_V UA_V /=.
move: (eq_ind _ _ _ _ _) => H2.
apply val_inj => /=; apply/eqP; rewrite xpair_eqE eqxx /=.
have eqtag :
  [set x | (x \in tag (upSpSet xSB)) || (x \in tag (upSpSet xSC))] = V.
  rewrite !tag_upSpSet.
  move: BC_V => /andP[/eqP + _] => /(congr1 (@upT _ _)).
  rewrite upT_setU upT_setT=> {9}->.
  by apply/setP => x; rewrite !inE.
rewrite -!/(Tagged _ _) -(Tagged_SpTSet_castE eqtag (A := B * C)) eq_Tagged /=.
rewrite -(inj_eq val_inj) /= xpair_eqE /=; apply/andP.
split; apply/eqP; apply eqSpSet => /=; split.
- rewrite tag_SpSet tag_downSpSet /downT -imset_comp.
  case: xSB {H2} eqtag BC_V => /= SB _ eqtag _.
  apply/setP => u; apply/imsetP/idP => [[[u' u'in _ {u}->]] /= | uinSB].
    have:= u'in => /imsetP [/= [u uinV] Hin equ']; subst u'.
    move: Hin; congr (_ \in SB); apply: val_inj => /=.
    by rewrite val_cast_TSet.
  have Hupu : val u \in upT SB by rewrite /upT (mem_imset _ _ val_inj).
  exists (exist _ (val u) Hupu); first by rewrite inE.
  rewrite /=; apply val_inj => /=.
  by rewrite val_cast_TSet.
- case: xSB {H2} eqtag BC_V => /= SB b eqtag _ eqtag1.
  rewrite eq_Tagged /=; apply/eqP.
  repeat rewrite hom_compE -!functor_o /=.
  rewrite -[RHS](@functor_id _ _ B); apply: (functor_ext_hom B) => {}b /=.
  by repeat (apply val_inj; rewrite val_cast_TSet /=).
- rewrite tag_SpSet tag_downSpSet /downT -imset_comp.
  case: xSC {H2} eqtag BC_V => /= SC _ eqtag _.
  apply/setP => u; apply/imsetP/idP => [[[u' u'in _ {u}->]] /= | uinSB].
    have:= u'in => /imsetP [/= [u uinV] Hin equ']; subst u'.
    move: Hin; congr (_ \in SC); apply: val_inj => /=.
    by rewrite val_cast_TSet.
  have Hupu : val u \in upT SC by rewrite /upT (mem_imset _ _ val_inj).
  exists (exist _ (val u) Hupu); first by rewrite inE.
  rewrite /=; apply val_inj => /=.
  by rewrite val_cast_TSet.
- case: xSC {H2} eqtag BC_V => /= SC c eqtag _ eqtag1.
  rewrite eq_Tagged /=; apply/eqP.
  repeat rewrite hom_compE -!functor_o /=.
  rewrite -[RHS](@functor_id _ _ C); apply: (functor_ext_hom C) => {}c /=.
  by repeat (apply val_inj; rewrite val_cast_TSet /=).
Qed.
Fact prodSpA3KV : cancel prodSpA3_inv prodSpA3_fun.
Proof.
move=> [/=[[a b]c] /=] p3; move: (eq_ind_r _ _ _) => HL.
apply val_inj => /= {p3 HL}; apply/eqP.
by repeat (rewrite xpair_eqE; apply/andP; split) => //; rewrite downSpSetK.
Qed.
Fact prodSpA3_fun_bij : bijective prodSpA3_fun.
Proof. by exists prodSpA3_inv; [exact: prodSpA3K | exact: prodSpA3KV]. Qed.
HB.instance Definition _ :=
  @BijHom.Build ((A * (B * C)) U) (prodSp3 U) prodSpA3_fun prodSpA3_fun_bij.

End MorphA3.

Definition prodSpA3 : A * (B * C) ~~> prodSp3 := prodSpA3_fun.

Fact prodSpA3_natural : naturality (A * (B * C)) prodSp3 prodSpA3.
Proof.
move=> U V h [[/= xA [/= E ]]] [[xSB xSC]] /= BC_E UA_E /=.
apply: val_inj => /= {UA_E}; apply/eqP.
by rewrite !xpair_eqE !SpSet_up !eqxx.
Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (A * (B * C)) prodSp3 prodSpA3 prodSpA3_natural.

End ProdSpeciesA3.


Definition prodSpC3_fun (A B C : Species) (U : Bij) :
  el (prodSp3 C A B U) -> el (prodSp3 A B C U).
by move=> [[[c a] b] /= p3]; exists (a, b, c); rewrite -part3C.
Defined.

Lemma prodSpC3_cycle A B C (U : Bij) :
  prodSpC3_fun (U := U) \o prodSpC3_fun (U := U) \o @prodSpC3_fun A B C U =1 idfun.
Proof. by move=> [[[c a] b] /= H]; apply val_inj. Qed.

Section ProdCycleA3.
Variable (A B C : Species).

Fact prodSpC3_bij U : bijective (@prodSpC3_fun A B C U).
Proof.
by exists (prodSpC3_fun (U := U) \o prodSpC3_fun (U := U)) => x;
     apply: prodSpC3_cycle x.
Qed.
HB.instance Definition _ U :=
  BijHom.Build (prodSp3 C A B U) (prodSp3 A B C U)
    (@prodSpC3_fun A B C U) (prodSpC3_bij U).

Definition prodSpC3 : prodSp3 C A B ~~> prodSp3 A B C := @prodSpC3_fun A B C.

Fact prodSpC3_natural : naturality (prodSp3 C A B) (prodSp3 A B C) prodSpC3.
Proof. by move=> U V h [[[c a] b] /= H]; apply: val_inj. Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (prodSp3 C A B) (prodSp3 A B C)
    prodSpC3 prodSpC3_natural.

End ProdCycleA3.


Definition prodSpA (A B C : Species) : A * B * C ~> A * (B * C) :=
  isoSpinv (prodSpA3 _ _ _) \v prodSpC3 _ _ _ \v prodSpA3 _ _ _ \v prodSpC _ _.
