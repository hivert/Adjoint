From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup.

Require Import category species sum prod.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Local Open Scope category_scope.
Local Open Scope species_scope.


Section OMapHom.
Variables (U V : Bij) (f : {hom U -> V}).

Lemma omap_bij : bijective (omap f).
Proof. by exists (omap (finv f)) => [][x|]; rewrite //= ?finvK ?finvKV. Qed.
HB.instance Definition _ :=
  BijHom.Build (option U) (option V)
    (omap f : el (option U : Bij) -> el (option V : Bij)) (omap_bij).

End OMapHom.


Section DiffSpecies.
Variable A : Species.

Definition diffSpT (U : Bij) : Bij := A (option U).
Definition diffSp_mor U V (f : {hom U -> V}) : el (diffSpT U) -> el (diffSpT V) :=
  A # (omap f).

Lemma diffSp_ext : FunctorLaws.ext diffSp_mor.
Proof.
rewrite /diffSp_mor => U V f g eqfg.
by apply functor_ext_hom => [][x|]//=; rewrite eqfg.
Qed.
Lemma diffSp_id : FunctorLaws.id diffSp_mor.
Proof.
rewrite /diffSp_mor => U /= x.
have /(functor_ext_hom A) -> : omap (@idfun U) =1 idfun by move => [].
by rewrite functor_id.
Qed.
Lemma diffSp_comp : FunctorLaws.comp diffSp_mor.
Proof.
rewrite /diffSp_mor => U V W f g /= x.
by rewrite -functor_o; apply functor_ext_hom => [][|].
Qed.
HB.instance Definition _ :=
  isFunctor.Build Bij Bij diffSpT diffSp_ext diffSp_id diffSp_comp.

Definition diffSp : Species := diffSpT.

Lemma card_diffSp n : cardSp diffSp n = cardSp A n.+1.
Proof. by rewrite {1}/cardSp /= /diffSpT cardSpE card_option card_ord. Qed.

End DiffSpecies.


Section DiffSum.

Variables A B : Species.

(** (A + B)' U et (A' + B') U are convertible !!! *)
Lemma diffSumE U : (diffSp (A + B)) U = (diffSp A + diffSp B)%Sp U.
Proof. by []. Qed.

Definition diffSum : diffSp (A + B) ~~> (diffSp A + diffSp B)%Sp := fun => idfun.
Fact diffSum_natural :
  naturality (diffSp (A + B)) (diffSp A + diffSp B)%Sp diffSum.
Proof. by []. Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (diffSp (A + B)) (diffSp A + diffSp B)%Sp
    diffSum diffSum_natural.

End DiffSum.


Section DiffTSet.

Variable U : Bij.

Lemma Some_inj : injective (fun u : U => Some u).
Proof. by move=> u v []. Qed.
Lemma Some_eq_NoneF (u : U) : (Some u == None) = false.
Proof. by apply/negP => []. Qed.
Lemma None_in_SomeF (S : {set U}) : None \in [set Some u | u in S] = false.
Proof. by apply/negP => /imsetP[u _ ]. Qed.

Variable (S : {set U}).

Definition UIn : {set option U} := None |: [set Some u | u in S].
Lemma toUIn_subproof (x : option (TSet S)) : omap val x \in UIn.
Proof.
case: x => [[x xinS]|] /=; rewrite !inE ?eqxx //.
by rewrite (mem_imset _ _ Some_inj) xinS orbT.
Qed.
Definition toUIn (x : el (option (TSet S) : Bij)) : el (TSet UIn) :=
  exist _ (omap val x) (toUIn_subproof x).
Lemma toUIn_inj : injective toUIn.
Proof.
move=> [[x xinS]|][[y yinS]|] //= /(congr1 val) /= [eqxy].
by congr Some; apply: val_inj.
Qed.
Lemma toUIn_bij : bijective toUIn.
Proof.
apply (inj_card_bij toUIn_inj); rewrite card_option !card_TSet.
by rewrite cardsU1 None_in_SomeF add1n (card_imset _ Some_inj).
Qed.
HB.instance Definition _ :=
  @BijHom.Build (option (TSet S)) (TSet UIn) toUIn toUIn_bij.


Definition UOut : {set option U} := [set Some u | u in S].
Lemma toUOut_subproof (x : TSet S) : Some (val x) \in UOut.
Proof. by rewrite (mem_imset _ _ Some_inj) TSetP. Qed.
Definition toUOut (x : el (TSet S)) : el (TSet UOut) :=
  exist _ (Some (val x)) (toUOut_subproof x).
Lemma toUOut_inj : injective toUOut.
Proof. by move=> [x xinS][y yinS] // /(congr1 val) [eqxy]; exact: val_inj. Qed.
Lemma toUOut_bij : bijective toUOut.
Proof.
apply (inj_card_bij toUOut_inj); rewrite !card_TSet.
by rewrite (card_imset _ Some_inj).
Qed.
HB.instance Definition _ :=
  @BijHom.Build (TSet S) (TSet UOut) toUOut toUOut_bij.

End DiffTSet.

Section DiffProdLeft.

Context {A B : Species} {U : Bij}.

Section Defs.

Variable p : (diffSp A * B)%Sp U.
Let dpmap : SpSet A (option U) * SpSet B (option U) :=
  let: (existT Sx x, existT Sy y) := val p in
  ( existT _ (UIn  Sx) ((A # @toUIn  U Sx) x),
    existT _ (UOut Sy) ((B # @toUOut U Sy) y) ).
Fact dpmap_subproof : part2 setT (tag dpmap.1) (tag dpmap.2).
Proof.
rewrite /dpmap; case: p => [/= [[Sx x][Sy y]] /=] p2.
move: p2; rewrite !part2TE => /eqP ->.
apply/eqP/setP => [[u|]]; rewrite /UIn /UOut !inE.
  by rewrite !(mem_imset _ _ (@Some_inj U)) inE; case: (_ \in _).
by rewrite eqxx /= None_in_SomeF.
Qed.
Definition diffProdl : (diffSp (A * B)) U := exist _ dpmap dpmap_subproof.

Lemma diffProdlP : None \in tag (val diffProdl).1.
Proof.
rewrite /= /dpmap /=; case: p => [/= [[Sx x][Sy y]] /=] p2.
by rewrite /UIn !inE eqxx.
Qed.
Lemma diffProdlNP : None \notin tag (val diffProdl).2.
Proof.
rewrite /= /dpmap /=; case: p => [/= [[Sx x][Sy y]] /=] p2.
by rewrite /UOut None_in_SomeF.
Qed.

End Defs.

Lemma diffProdl_inj : injective diffProdl.
Proof.
rewrite /diffProdl => [][/= [[Ea xa] [Eb xb]] /= p2x].
move=>               [/= [[Fa ya] [Fb yb]] /= p2y] /eqP.
rewrite -eq_prodSpE => /= /andP[/eqP + /eqP]; rewrite !eqSpSet /=.
move=> [eqEFa] /(_ eqEFa); rewrite !eq_Tagged /= => /eqP.
rewrite hom_compE -functor_o /= => eqa.
move=> [eqEFb] /(_ eqEFb); rewrite !eq_Tagged /= => /eqP.
rewrite hom_compE -functor_o /= => eqb.
apply: val_inj => /= {p2x p2y}.
apply/eqP; rewrite xpair_eqE; apply/andP;
  split; apply/eqP; rewrite !eqSpSet /=; split.
- move: eqEFa {eqa}; rewrite /UIn => /setP eqa.
  apply/setP => u; move/(_ (Some u)) : eqa.
  by rewrite !inE !(mem_imset _ _ (@Some_inj U)) !Some_eq_NoneF /=.
- move=> eqtag; rewrite !eq_Tagged /=.
  apply/eqP/(Bij_injP (A # toUIn (S:=Fa))); rewrite -{}eqa /=.
  rewrite !hom_compE -functor_o; apply: functor_ext_hom => {}xa.
  apply val_inj; rewrite /= !val_cast_TSet /=.
  by case: xa => [xa|]; rewrite //= !val_cast_TSet.
- move: eqEFb {eqb}; rewrite /UIn => /setP eqb.
  apply/setP => u; move/(_ (Some u)) : eqb.
  by rewrite !(mem_imset _ _ (@Some_inj U)).
- move=> eqtag; rewrite !eq_Tagged /=.
  apply/eqP/(Bij_injP (B # toUOut (S:=Fb))); rewrite -{}eqb /=.
  rewrite !hom_compE -functor_o; apply: functor_ext_hom => {}xb.
  by apply val_inj; rewrite /= !val_cast_TSet.
Qed.

End DiffProdLeft.

Lemma diffProdl_natural (A B : Species) (U V : Bij) (f : {hom U -> V}) :
  diffSp (A * B) # f \o diffProdl =1 diffProdl \o (diffSp A * B) # f.
Proof.
move=> [/= [[Sx x][Sy y]] /= p2].
apply: val_inj => /=; apply/eqP; rewrite xpair_eqE; apply/andP;
split; apply/eqP; rewrite !eqSpSet /=; split.
- rewrite {Sy y p2} /UIn /= imsetU imset_set1 /=; congr (_ |: _).
  by rewrite -!imset_comp; apply eq_imset => u.
- move=> {Sy y p2} eqtag; rewrite !eq_Tagged /=; apply/eqP.
  rewrite [LHS]hom_compE -functor_o !hom_compE -!functor_o /=.
  apply: (functor_ext_hom A) => {}x /=.
  by apply val_inj; rewrite /= !val_cast_TSet /=; case: x.
- by rewrite {Sx x p2} /UOut /= -!imset_comp; apply eq_imset => u.
- move=> {Sx x p2} eqtag; rewrite !eq_Tagged /=; apply/eqP.
  rewrite [LHS]hom_compE -functor_o !hom_compE -!functor_o /=.
  apply: (functor_ext_hom B) => {}y /=.
  by apply val_inj; rewrite /= !val_cast_TSet /=; case: y.
Qed.

Section DiffProdRight.

Context {A B : Species} {U : Bij}.

Definition diffProdr : (A * diffSp B)%Sp U -> diffSp (A * B) U :=
  prodSpC (option U) \o diffProdl \o prodSpC U.
Lemma diffProdr_inj : injective diffProdr.
Proof. exact: inj_comp (inj_comp (Bij_injP _) diffProdl_inj) (Bij_injP _). Qed.
Lemma diffProdrNP p : None \notin tag (val (diffProdr p)).1.
Proof. exact: diffProdlNP (prodSpC _ p). Qed.
Lemma diffProdrP p : None \in tag (val (diffProdr p)).2.
Proof. exact: diffProdlP (prodSpC _ p). Qed.

End DiffProdRight.

Lemma diffProdr_natural (A B : Species) (U V : Bij) (f : {hom U -> V}) :
  diffSp (A * B) # f \o diffProdr =1 diffProdr \o (A * diffSp B) # f.
Proof.
rewrite /diffProdr => p.
have /= <- := natural prodSpC _ _ f p.
have /= <- := diffProdl_natural f _.
by move: diffProdl => [[a b] /= p2]; apply val_inj.
Qed.


Section DiffProd.

Variables (A B : Species).

Section Defs.

Variable U : Bij.

Definition diffProd_fun
  (x : el ((diffSp A * B + A * diffSp B) U)) : el (diffSp (A * B) U) :=
  match x with
  | inl p => diffProdl p
  | inr p => diffProdr p
  end.
Fact diffProd_inj : injective diffProd_fun.
Proof.
rewrite /diffProd_fun => [][]x []y.
- by move/diffProdl_inj ->.
- by move=> eq; have:= diffProdlNP x; rewrite {}eq diffProdrP.
- by move=> eq; have:= diffProdrNP x; rewrite {}eq diffProdlP.
- by move/diffProdr_inj ->.
Qed.
Fact diffProd_bij : bijective diffProd_fun.
Proof.
apply (inj_card_bij diffProd_inj).
rewrite leq_eqVlt; apply/orP; left; apply/eqP.
rewrite card_sum !cardSpE !card_prodSp card_diffSp card_prodSp.
rewrite big_nat_recl //= bin0 mul1n subn0.
under eq_bigr => i _ do rewrite binS !mulnDl subSS.
under [X in _ = (X + _)%N]eq_bigr => i _ do rewrite card_diffSp.
rewrite big_split /= addnA addnC; congr (_ + _)%N.
rewrite big_nat_recr //= bin_small // !mul0n addn0.
rewrite [RHS]big_nat_recl //= bin0 mul1n card_diffSp subn0; congr (_ + _)%N.
rewrite !big_nat; apply eq_bigr => /= i ltin.
by rewrite card_diffSp subnSK.
Qed.
HB.instance Definition _ :=
  BijHom.Build ((diffSp A * B + A * diffSp B) U) (diffSp (A * B) U)
    diffProd_fun diffProd_bij.

End Defs.

Definition diffProd :
  (diffSp A * B + A * diffSp B) ~~> diffSp (A * B) := diffProd_fun.

Fact diffProd_natural :
  naturality (diffSp A * B + A * diffSp B) (diffSp (A * B)) diffProd.
Proof.
by move=> U V f []; [exact: diffProdl_natural | exact: diffProdr_natural].
Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (diffSp A * B + A * diffSp B) (diffSp (A * B))
    diffProd diffProd_natural.

End DiffProd.
