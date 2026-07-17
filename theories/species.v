From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup.

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

Lemma imsetTE : [set f y | y in [set: S]] = [set f y | y in S].
Proof.
by apply/setP => x; apply/imsetP/imsetP => [][y _ {x}->]; exists y.
Qed.

Lemma iota_ltn a b : b <= a -> [seq i <- iota 0 a | i < b] = iota 0 b.
Proof.
move=> Hab.
rewrite -(subnKC Hab) iotaD add0n filter_cat.
rewrite -[RHS]cats0; congr (_ ++ _).
- rewrite (eq_in_filter (a2 := predT)) ?filter_predT //.
  by move=> i /=; rewrite mem_iota add0n /= => ->.
- rewrite (eq_in_filter (a2 := pred0)) ?filter_pred0 //.
  move=> i /=; rewrite mem_iota (subnKC Hab) => /andP[].
  by rewrite leqNgt => /negbTE.
Qed.

Lemma map_filter_comp (T1 T2: Type) (l : seq T1) (PP : pred T2) (F : T1 -> T2) :
  [seq F i | i <- l & PP (F i)] = [seq i | i <- map F l & PP i ].
Proof.
rewrite filter_map /= -map_comp.
have /eq_filter -> : (preim F [eta PP]) =1 (fun i => PP (F i)) by [].
by rewrite map_comp.
Qed.

End SSRCompl.

Lemma card_eq_imset_permP (U : finType) (E F : {set U}) :
  reflect (exists s : {perm U}, [set s x | x in E] = F) (#|E| == #|F|).
Proof.
apply (iffP eqP) => [eqcard | [s {F}<-]]; first last.
  by rewrite card_imset //; apply: perm_inj.
pose lset (X : {set U}) := enum X ++ enum (~: X).
have lset_uniq X : uniq (lset X).
  rewrite /lset cat_uniq !enum_uniq /= andbT.
  rewrite -all_predC; apply/allP => x /=.
  by rewrite !mem_enum inE.
have size_lset X : size (lset X) = #|U|.
  by rewrite /lset size_cat -!cardE cardsC.
have mem_lset X x : x \in lset X.
  by rewrite mem_cat !mem_enum inE; case: (x \in X).
have index_lset X Y x : index x (lset X) < size (lset Y).
  by rewrite size_lset -(size_lset X) index_mem mem_lset.
pose f x := nth x (lset F) (index x (lset E)).
have finj : injective f.
  rewrite /f => x y /(congr1 (fun i => index i (lset F))).
  rewrite !index_uniq // ?index_mem => /(congr1 (fun i => nth x (lset E) i)).
  by rewrite !nth_index.
exists (perm finj).
apply/eqP; rewrite -subset_leqif_cards.
  by rewrite -eqcard card_imset //;apply: perm_inj.
apply/subsetP => x /imsetP [y yinE {x}->].
rewrite permE /f /lset nth_cat index_cat mem_enum yinE.
have indEltF : index y (enum E) < size (enum F).
  by rewrite -cardE -eqcard {1}(cardE E) index_mem mem_enum.
by rewrite indEltF -mem_enum mem_nth.
Qed.


Section Cast.

Definition type_cast (A B : Type) (eqAB : A = B) x := ecast T T eqAB x.

Lemma type_castK A B (eqAB : A = B) :
  cancel (type_cast eqAB) (type_cast (esym eqAB)).
Proof. by move=> x; case:_/(eqAB). Qed.
Lemma type_castKV A B (eqAB : A = B) :
  cancel (type_cast (esym eqAB)) (type_cast eqAB).
Proof. by rewrite -{2}(esymK eqAB); apply: type_castK. Qed.

End Cast.


Section MapValSub.

Variables (T : finType) (P : pred T) (S : subFinType P).

Lemma imset_val_sub : [set val x | x in @predT S] = [set x : T | P x].
Proof.
apply/setP => xs; apply/imsetP/idP => [[x _ {xs}->]|] /[!inE]; first exact: valP.
by move=> Pxs; exists (Sub xs Pxs) => //; rewrite SubK.
Qed.

End MapValSub.


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

Lemma BijP (U V : Bij) (f : {hom U -> V}) : bijective f.
Proof. exact: (isHom_inhom f). Qed.
Hint Resolve BijP : core.

Section Homs.

Variable (U V : Bij) (f : {hom U -> V}).

Lemma hom_is_isom :
  { finv | bijective finv & (cancel finv f * cancel f finv)%type }.
Proof.
have:= isHom_inhom f; rewrite /inhom /= => f_bij.
pose ff := [ffun x : el U => f x : el V].
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
Definition finv : el V -> el U := let: exist2 finv P1 P2 := hom_is_isom in finv.

Lemma finv_bij : bijective finv.
Proof. by rewrite /finv; case: hom_is_isom. Qed.
HB.instance Definition _ := isHom.Build _ V U finv finv_bij.

Lemma finvK : cancel f finv.
Proof. by rewrite /finv; case: hom_is_isom => x _ []. Qed.
Lemma finvKV : cancel finv f.
Proof. by rewrite /finv; case: hom_is_isom => x _ []. Qed.

(* non forgetful inheritance detected.
HB.instance Definition _ :=
  isIsom.Build Bij U V f finv_bij finvK finvKV.
*)

End Homs.

Lemma finvI (U V : Bij) (f : {hom U -> V}) : finv (finv f) =1 f.
Proof.
move => x /=; apply (bij_inj (BijP (finv f))).
by rewrite finvKV [RHS]finvK.
Qed.
Lemma finv_id (U : Bij) : finv (@idfun U) =1 idfun.
Proof. by move=> x /=; apply (bij_inj (BijP idfun)); rewrite finvK. Qed.
Lemma finvE (U V : Bij) (f g : {hom U -> V}) :
  f =1 g -> finv f =1 finv g.
Proof. by move=> eq x; apply (bij_inj (BijP f)); rewrite finvKV eq finvKV. Qed.
Lemma finv_comp (U V W : Bij) (f : {hom U -> V}) (g : {hom V -> W}) :
  finv (g \o f) =1 (finv f) \o (finv g).
Proof.
move=> x /=.
apply (bij_inj (BijP f)); apply (bij_inj (BijP g)).
by rewrite -[LHS]compapp !finvKV.
Qed.

HB.factory Record BijHom (U V : Bij)
  (f : el U -> el V) := { finsetsbij_hom : bijective f }.
HB.builders Context (U V : Bij)
  (f : el U -> el V) of BijHom U V f.
HB.instance Definition _ := isHom.Build _ U V f finsetsbij_hom.
HB.instance Definition _ := isIsom.Build _ U V f (finv_bij f) (finvK f) (finvKV f).
HB.end.

Lemma BijHom_eq_card (U V : Bij) (f : {hom U -> V}) : #|U| = #|V|.
Proof. exact: (bij_eq_card (isHom_inhom f)). Qed.


Section FunctorBij.

Variable T : Bij -> Bij.
Variable F : forall (U V : Bij) (f : {hom U -> V}), el (T U) -> el (T V).
Hypothesis fext : FunctorLaws.ext F.
Hypothesis fid : FunctorLaws.id F.
Hypothesis fcomp : FunctorLaws.comp F.

Lemma functor_bij (U V : Bij) (f : {hom U -> V}) : bijective (F f).
Proof.
by exists (F (finv f)) => x;
  rewrite -(compapp (F _) (F _) x) -fcomp -[RHS]fid;
  apply fext => {}x; rewrite /= ?finvK ?finvKV.
Qed.

End FunctorBij.

Section TypeInSet.
Variable (U : Bij) (S : {set U}).

Definition TinSet : Bij := {x : U | x \in S} : Bij.
Lemma TinSetP (x : TinSet) : val x \in S.
Proof. by case: x. Qed.
Lemma imset_val_TinSet : [set \val x | x : TinSet] = S.
Proof.
apply/setP => x; apply/imsetP/idP => [[/= [y y_in_S] _ ->] // | x_in_S].
by exists (exist _ x x_in_S).
Qed.
Lemma card_TinSet : #|TinSet| = #|S|.
Proof.
by rewrite -[LHS](card_imset _ val_inj) imset_val_TinSet.
Qed.

End TypeInSet.


Section Restriction.

Variable (U V : Bij) (I : {set U}) (f : {hom U -> V}).

Fact restr_subproof (x : TinSet I) : f (\val x) \in (f @: I).
Proof. by case: x => x Px /=; apply: imset_f. Qed.
Definition restr (x : el (TinSet I)) : el (TinSet (f @: I)) :=
  exist _ (f (\val x)) (restr_subproof x).

Fact restr_inv_spec (y : TinSet (f @: I)) : { x : TinSet I | restr x == y }.
Proof.
case: y => /= [y Py].
case: (pickP (fun x : U => (x \in I) && (f x == y))) =>
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
Definition restr_hom : {hom[Bij] TinSet I -> TinSet (f @: I)} := restr.

Lemma val_restrE x : \val (restr x) = f (\val x).
Proof. by []. Qed.

End Restriction.


Definition voidB := (void : Bij).
Definition unitB := (unit : Bij).
Definition boolB := (bool : Bij).
Definition negbB : el boolB -> el boolB := negb.
HB.instance Definition _ := BijHom.Build boolB boolB negbB (inv_bij negbK).


Definition Species := {functor Bij -> Bij}.


Section SpeciesTheory.
Variable (A : Species) (U V : Bij) (f : {hom U -> V}).

Lemma SpfinvK : cancel (A # f) (A # (finv f)).
Proof.
move=> x.
have finvK : finv f \o f =1 idfun by apply: finvK.
by rewrite hom_compE -functor_o (functor_ext_hom _ _ _ finvK) functor_id.
Qed.
Lemma SpfinvKV : cancel (A # (finv f)) (A # f).
Proof.
move=> x.
have finvKV : f \o finv f =1 idfun by apply: finvKV.
by rewrite hom_compE -functor_o (functor_ext_hom _ _ _ finvKV) functor_id.
Qed.
Lemma SpfinvE : A # (finv f) =1 finv (A # f).
Proof.
move=> x; apply: (bij_inj (BijP (A # f))).
by rewrite SpfinvKV finvKV.
Qed.

HB.instance Definition _ :=
  BijHom.Build _ _ (@enum_rank U : el U -> el ('I_#|U| : Bij)) (@enum_rank_bij U).

Definition cardSp (n : nat) := #|A 'I_n|.
Lemma cardSpE : #|A U| = cardSp #|U|.
Proof. exact: BijHom_eq_card (A # (@enum_rank U)). Qed.

End SpeciesTheory.


Section Action.

Variable A : Species.
Implicit Types (U V : Bij).

Section Defs.

Variable U : Bij.
Implicit Type s : {perm U}.

Lemma perm_bij s : bijective s.
Proof. by exists (s^-1)%g; [exact: permK| exact: permKV]. Qed.
HB.instance Definition _ s := @BijHom.Build U U (s : el U -> U) (@perm_bij s).

Definition actSp_fun (x : el (A U)) (s : {perm U}) := (A # s) x.
Lemma actSp1 : actSp_fun^~ 1%g =1 id.
Proof.
rewrite /actSp_fun => /= x.
have /(functor_ext_hom A) -> : (1 : {perm U})%g =1 idfun by apply: perm1.
by rewrite functor_id.
Qed.
Lemma actSpM x : act_morph actSp_fun x.
Proof.
move=> /= s t.
rewrite /actSp_fun hom_compE -functor_o; apply: functor_ext_hom => {}x /=.
by rewrite permM.
Qed.
Canonical actSp := TotalAction actSp1 actSpM.

Lemma actSpP : [acts setT, on setT | actSp].
Proof.
apply/subsetP => /= s _; rewrite !inE /=.
by apply/subsetP => x _; rewrite !inE.
Qed.

Definition actSp_perm s := actSp^~ s.
Lemma actSp_bij s : bijective (actSp_perm s).
Proof. exact/injF_bij/act_inj. Qed.
HB.instance Definition _ s :=
  @BijHom.Build (A U) (A U) (actSp_perm s) (@actSp_bij s).

End Defs.


Section PermHom.
Variables (U : Bij) (f : {hom U -> U}).
Definition perm_hom := perm (bij_inj (BijP f)).
Lemma perm_homE : perm_hom =1 f.
Proof. exact: permE. Qed.
End PermHom.


Section Transport.

Variables (U V : Bij) (f : {hom U -> V}).

Definition perm_morph_fun (s : {perm U}) : {perm V} :=
  perm_hom (f \o s \o (finv f)).
Lemma perm_morph_subproof :
  {in setT &, {morph perm_morph_fun : x y / (x * y)%g}}.
Proof.
rewrite /perm_morph_fun => s t _ _ /=.
by apply/permP=> u /=; rewrite !perm_homE /= !permM /= !permE /= finvK.
Qed.
Canonical perm_morph := Morphism perm_morph_subproof.

Lemma perm_morphE (s : {perm U}) x : perm_morph s (f x) = f (s x).
Proof. by rewrite /= /perm_morph_fun perm_homE /= finvK. Qed.

End Transport.

Lemma perm_morph_ext U V (f g : {hom U -> V}) :
  f =1 g -> perm_morph f =1 perm_morph g.
Proof. by move=> eq /= s; apply/permP => v; rewrite !permE /= eq (finvE eq). Qed.
Lemma perm_morph_id U : perm_morph (@idfun U) =1 idfun :> (_ -> _).
Proof. by move => /= s; apply/permP => v; rewrite !permE /= finv_id. Qed.
Lemma perm_morph_comp W V U (f : {hom W -> V}) (g : {hom V -> U}) :
  perm_morph (g \o f) =1 perm_morph g \o perm_morph f.
Proof.
move=> /= s; apply/permP => v.
by rewrite !permE /= finv_comp -perm_morphE /= finvKV.
Qed.

Definition isoclass U (x : A U) : {set A U} := orbit (actSp U) setT x.
Definition isoclasses U : {set {set A U}} := [set isoclass x | x in [set: A U]].

Lemma morph_isoclass U V (f : {hom U -> V}) x :
  (A # f) @: isoclass x = isoclass ((A # f) x).
Proof.
(* TODO : this is very similar to transport_orbit, can it be merged ? *)
apply/setP=> u; apply/imsetP/orbitP => [[y /orbitP[/= s _ {y}<- {u}->]]|].
  exists (perm_morph f s); first by rewrite inE.
  rewrite /actSp_fun !hom_compE -!functor_o.
  by apply: (functor_ext_hom A) => {}x /=; rewrite perm_morphE.
move=> /=[s _ <-{u}].
exists (actSp _ x (perm_morph (finv f) s)).
  by apply/orbitP => /=; exists (perm_morph (finv f) s); first by rewrite inE.
rewrite /= /actSp_fun !hom_compE -!functor_o.
apply: (functor_ext_hom A) => {}x /=.
by rewrite /perm_morph_fun permE /= finvKV finvI.
Qed.

Lemma isoclassesE U V (f : {hom U -> V}) :
  [set (A # f) @: (S : {set _}) | S in isoclasses U] = isoclasses V.
Proof.
apply/setP => /= E.
apply/imsetP/imsetP => /=[[F /imsetP[u _ {F}-> {E}-> /=]] | [i _ {E}->]].
  exists ((A # f) u); first by rewrite inE.
  exact: morph_isoclass.
exists (orbit (actSp _) [set: {perm U}] ((A # finv f) i)).
  by apply/imsetP; exists ((A # finv f) i).
by rewrite morph_isoclass SpfinvKV.
Qed.
Lemma card_isoclassesE U V (f : {hom U -> V}) : #|isoclasses U| = #|isoclasses V|.
Proof.
rewrite -(isoclassesE f) [RHS]card_imset //.
exact: (imset_inj (bij_inj (BijP _))).
Qed.

Definition isotypes n := orbit_transversal (actSp 'I_n) setT setT.
Definition isotype U (x : A U) :=
  let ix := (A # @enum_rank U) x in
  transversal_repr ix (isotypes #|U|) (orbit (actSp 'I_#|U|) setT ix).
Definition cardiso n := #|isotypes n|.

Lemma isotypesP n : is_transversal (isotypes n) (isoclasses 'I_n) setT.
Proof. exact: (transversalP (orbit_partition (actSpP _))). Qed.
Lemma isotypesE n :
  {in (isotypes n) &, forall x y : A 'I_n, (y \in isoclass x) = (x == y)}.
Proof.
have [_ _ + _ x xin y yin] := orbit_transversalP (actSpP 'I_n).
by apply.
Qed.
Lemma isotypes_ex n (x : A 'I_n) :
  exists s : 'S_n, actSp 'I_n x s \in isotypes n.
Proof.
have [_ _ _ /(_ x) []] := orbit_transversalP (actSpP 'I_n).
  by rewrite inE.
by move=> /= s _ HS; exists s.
Qed.

Lemma cardisoE U : #|isoclasses U| = cardiso #|U|.
Proof.
by rewrite [RHS](card_transversal (isotypesP _)) (card_isoclassesE (@enum_rank U)).
Qed.
Lemma cardiso_ordE n : #|isoclasses 'I_n| = cardiso n.
Proof. by rewrite cardisoE card_ord. Qed.

Lemma isotype_mem U (x : A U) : isotype x \in isotypes #|U|.
Proof.
apply: (repr_mem_transversal (isotypesP _)); apply/imsetP.
by exists ((A # @enum_rank U) x).
Qed.
Lemma isotype_ex U (x : A U) :
  exists f : {hom U -> 'I_#|U|}, (A # f) x = isotype x.
Proof.
rewrite /isotype.
set ix := (A # @enum_rank U) x.
have [_ H] := orbit_transversalP (actSpP 'I_#|U|).
have /orbitP[/= s _] : isotype x \in orbit (actSp 'I_#|U|) setT ix.
  by apply: (repr_mem_pblock (isotypesP _)); apply/imsetP; exists ix.
rewrite /actSp_fun /isotype -/ix => <-.
by exists (s \o (@enum_rank U)); rewrite /ix functor_o.
Qed.

Lemma isotypeE U (x : A U) (f : {hom U -> 'I_#|U|}) :
  (A # f) x \in isotypes #|U| -> (A # f) x = isotype x.
Proof.
move=> H; apply/eqP; rewrite -isotypesE ?isotype_mem //.
have [g <-] := isotype_ex x.
apply/orbitP; exists (perm_hom (g \o (finv f))); first by rewrite inE.
rewrite /= /actSp_fun /=.
by rewrite (functor_ext_hom A _ _ (perm_homE _)) functor_o /= SpfinvK.
Qed.

Lemma isotypeP U V (x : A U) (y : A V) :
  reflect (exists f : {hom U -> V}, (A # f) x = y)
    (existT (fun n => A 'I_n) #|U| (isotype x) ==
     existT (fun n => A 'I_n) #|V| (isotype y)).
Proof.
apply (iffP idP) => [/eqP[eqcard]/eqP | [f eqy]].
  move: (isotype_ex x) (isotype_ex y) => [fx <-] [fy <-].
  move: fx fy; rewrite {}eqcard => fx fy.
  rewrite -!/(Tagged _ _) eq_Tagged /= => /eqP/(congr1 (A # (finv fy))).
  rewrite SpfinvK hom_compE -functor_o => <-.
  by exists (finv fy \o fx).
move: (isotype_ex y) (isotype_mem y) => [fy <-]; rewrite -{y}eqy.
rewrite hom_compE -functor_o /=.
by move: (BijHom_eq_card f) (X in A # X) x => {f fy V}<- f x /isotypeE ->.
Qed.

End Action.


Section NaturalTransport.

Lemma nattransp_orbit (A B : Species) (U : Bij) (f : A U -> B U) :
  (forall a (s : {perm U}), actSp B U (f a) s = f (actSp A U a s)) ->
  forall x : A U, f @: isoclass x = isoclass (f x).
Proof.
move=> fnat x.
apply/setP => b; apply/imsetP/orbitP => [[a' /orbitP[/= s _ {a'}<-{b}->]] |].
  exists s; first by rewrite inE.
  exact: fnat.
move=> [/= s _ {b}<-]; exists (actSp A _ x s).
  by apply/orbitP; exists s; first by rewrite inE.
exact: fnat.
Qed.

Variables (A B : Species) (U : Bij) (f : {hom A U -> B U}).
Hypothesis fnat : forall a (s : {perm U}), actSp B U (f a) s = f (actSp A U a s).

Lemma nattransp_isoclasses :
  [set f @: (C : {set _}) | C in isoclasses A U] = isoclasses B U.
Proof.
apply/setP => /= T.
apply/imsetP/imsetP => /=[[S /imsetP[a _ {S}-> {T}-> /=]] | [b _ {T}->]].
  exists (f a); first by rewrite inE.
  exact: nattransp_orbit.
exists (finv f @: orbit (actSp B U) setT b).
  apply/imsetP; exists (finv f b); first by rewrite inE.
  apply: nattransp_orbit => a s /=.
  by apply: (bij_inj (BijP f)); rewrite -fnat !finvKV.
apply/setP => b'; apply/orbitP/imsetP => [[/= s _ {b'}<-]|].
  exists (finv f (actSp_fun b s)); last by rewrite finvKV.
  rewrite (mem_imset _ _ (bij_inj (BijP _))).
  by apply/orbitP; exists s; first by rewrite inE.
move=> [a /imsetP[b'' /orbitP [/= s _ {b''}<- {a}-> {b'}->]]].
exists s; first by rewrite inE.
by rewrite finvKV.
Qed.

Lemma nattransp_cardiso : #|isoclasses A U| = #|isoclasses B U|.
Proof.
rewrite -nattransp_isoclasses [RHS]card_imset //.
exact/imset_inj/(bij_inj (BijP _)).
Qed.

End NaturalTransport.


Section IsoSpecies.

Variables (A B : Species) (F : A ~> B).

Definition isoSpinv : B ~~> A := fun U => finv (F U).
Lemma isoSpinv_natural : naturality B A isoSpinv.
Proof.
rewrite /isoSpinv => U V h x /=.
apply: (can_inj (finvKV (A # h))); rewrite finvK.
rewrite hom_compE -finv_comp.
apply: (bij_inj (BijP (F V \o A # h))).
by rewrite -[LHS](natural F U V h) [LHS]/= !finvKV.
Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij B A isoSpinv isoSpinv_natural.

Lemma isoSpK : isoSpinv \v F =%= NId A.
Proof. by move=> U x /=; rewrite finvK. Qed.
Lemma isoSpKV : F \v isoSpinv =%= NId B.
Proof. by move=> U x /=; rewrite finvKV. Qed.

Lemma isoSpinvrE (G : B ~~> A) :
  (forall U, (G U) \o (F U) =1 idfun) -> G =%= isoSpinv.
Proof.
move=> H U b; rewrite /isoSpinv.
by rewrite -{1}(finvKV (F U) b) hom_compE H.
Qed.
Lemma isoSpinvlE (G : B ~~> A) :
  (forall U, (F U) \o (G U) =1 idfun) -> G =%= isoSpinv.
Proof.
move=> H U b; rewrite /isoSpinv.
apply: (bij_inj (BijP (F U))).
by rewrite hom_compE H finvKV.
Qed.

Lemma card_SpE : cardSp A =1 cardSp B.
Proof. by move=> U; apply: BijHom_eq_card (F 'I_U). Qed.

Lemma cardiso_SpE : cardiso A =1 cardiso B.
Proof.
move=> n; rewrite -!cardiso_ordE.
pose ff := fun (S : {set A _}) => F 'I_n @: S.
rewrite -(card_imset (f := ff)); last exact/imset_inj/(bij_inj (BijP _)).
by rewrite nattransp_isoclasses // => a s; exact: (natural F).
Qed.

End IsoSpecies.

Lemma isoSpinvK (A B : Species) (F : A ~> B) : isoSpinv (isoSpinv F) =%= F.
Proof. by move=> U x; rewrite /isoSpinv /= /isoSpinv /= finvI.  Qed.
Lemma isoSpinv_vcomp (A B C : Species) (F : A ~> B) (G : B ~> C) :
  isoSpinv (G \v F) =%= (isoSpinv F) \v (isoSpinv G).
Proof. by move=> U x /=; rewrite finv_comp. Qed.


Section IdSpecies.

Definition idSp : Species := FId.
Lemma card_idSp n : cardSp idSp n = n.
Proof. exact: card_ord. Qed.

Lemma isoclass_idSp (U : Bij) (u : U) : isoclass (A := idSp) u = [set: U].
Proof.
apply/setP => /= v; rewrite !inE; apply/orbitP.
exists (tperm u v); first by rewrite inE.
by rewrite /actSp /= /actSp_fun /idSp /= tpermL.
Qed.

Lemma cardiso_idSp n : cardiso idSp n = (n != 0).
Proof.
rewrite -!cardiso_ordE.
case: n => [/=|n].
  by apply: eq_card0 => i /[!inE]; apply/imsetP => [][[]].
rewrite [RHS](_ : _ = 1%N) //=.
rewrite -[RHS](cards1 [set: idSp 'I_n.+1]); congr #|pred_of_set _|.
apply/setP => /= S; rewrite !inE.
apply/imsetP/eqP => [[i _ {S}->] | {S}->]; first by rewrite isoclass_idSp.
by exists ord0; rewrite ?inE // isoclass_idSp.
Qed.

End IdSpecies.


Section Cast.

Variable (U : Bij).
Implicit Types (I J : {set U}).

Definition cast_TinSet I J (eq : I = J) (y : el (TinSet I)) : el (TinSet J) :=
  ecast X (TinSet X) eq y.

Lemma val_cast_TinSet I J (eq : I = J) y : \val (cast_TinSet eq y) = \val y.
Proof. by rewrite /cast_TinSet; case: y => [x Hx] /=; case:_/eq. Qed.

Lemma cast_TinSetK I J (eqIJ : I = J) :
  cancel (cast_TinSet eqIJ) (cast_TinSet (esym eqIJ)).
Proof. by rewrite /cast_TinSet; subst J => /=. Qed.
Lemma cast_TinSetKV I J (eqIJ : I = J) :
  cancel (cast_TinSet (esym eqIJ)) (cast_TinSet eqIJ).
Proof. by rewrite /cast_TinSet; subst J => /=. Qed.
Fact cast_TinSet_bij I J (eqIJ : I = J) : bijective (cast_TinSet eqIJ).
Proof.
by exists (cast_TinSet (esym eqIJ)); [exact: cast_TinSetK | exact: cast_TinSetKV].
Qed.
HB.instance Definition _ I J (eqIJ : I = J) :=
  BijHom.Build _ _ (cast_TinSet eqIJ) (cast_TinSet_bij eqIJ).

Lemma cast_TinSetE I J (eq1 eq2 : I = J) : cast_TinSet eq1 =1 cast_TinSet eq2.
Proof. by move=> x; apply: val_inj; rewrite !val_cast_TinSet. Qed.
Lemma cast_TinSet_id I (eqI : I = I) : cast_TinSet eqI =1 idfun.
Proof. by move=> x; apply: val_inj; rewrite !val_cast_TinSet. Qed.
Lemma cast_TinSet_comp I J K (eqIJ : I = J) (eqJK : J = K) :
  cast_TinSet eqJK \o cast_TinSet eqIJ =1 cast_TinSet (etrans eqIJ eqJK).
Proof. by move=> x; apply: val_inj; rewrite !val_cast_TinSet. Qed.

Lemma Tagged_TinSet_castE I J (eqIJ : I = J) (x : TinSet I) :
  Tagged (@TinSet U) x = Tagged (@TinSet U) (ecast X (TinSet X) eqIJ x).
Proof. by move: x; subst I. Qed.

End Cast.

Lemma Tagged_SpTinSet_castE (V : Bij) (I J : {set V}) (eq : I = J) (A : Species) x :
  Tagged (fun U => A (TinSet U)) ((A # cast_TinSet eq) x) =
    Tagged (fun U => A (TinSet U)) x.
Proof.
subst I => /=.
have /functor_ext_hom -> /= : cast_TinSet (erefl J) =1 idfun by [].
by rewrite functor_id_hom.
Qed.

Lemma restr_id (U : Bij) (I : {set U}) :
  restr_hom I [hom idfun] =1 cast_TinSet (esym (imset_id I)).
Proof. by move=> x /=; apply val_inj; rewrite val_cast_TinSet. Qed.
Lemma restr_comp (U V W : Bij) (f : {hom U -> V}) (g : {hom V -> W}) (I : {set U}) :
  restr_hom _ g \o restr_hom I f
  =1 cast_TinSet (imset_comp g f I) \o restr_hom _ (g \o f).
Proof. by move => x /=; apply val_inj; rewrite val_cast_TinSet !val_restrE. Qed.
Lemma restr_ext (U V : Bij) (f g : {hom U -> V}) (I : {set U}) (eq_fg : f =1 g) :
  restr_hom I f =1 cast_TinSet (eq_imset _ (fsym eq_fg)) \o (restr_hom I g).
Proof. by move => x /=; apply val_inj; rewrite !val_cast_TinSet !val_restrE. Qed.


Section SpInSet.

Variable (A : Species).
Implicit Types (U V : Bij).

Definition SpInSet U : Bij := { I : {set U} & A (TinSet I) }.

Lemma eqSpInSet U (x y : SpInSet U) :
  x = y <->
    ((tag x = tag y) /\
       (let (E, xx) := x in let (F, yy) := y in forall eqtag : E = F,
          Tagged (fun G => A (TinSet G)) ((A # cast_TinSet eqtag) xx) ==
            Tagged (fun G => A (TinSet G)) yy)).
Proof.
split => [eqxy|].
  subst y; split => //.
  case: x => [E x] eqE /=; rewrite eq_Tagged /=; apply/eqP.
  rewrite -[RHS](@functor_id _ _ A) /=; apply: (functor_ext_hom A) => {}x.
  by apply val_inj; rewrite val_cast_TinSet.
case: x y => /= [E x][F y] /= [eqEF eq]; subst F; apply/eqP.
rewrite -!/(Tagged _ _) -(eqP (eq _)) eq_Tagged /=; apply/eqP.
rewrite -[LHS](@functor_id _ _ A) /=; apply: (functor_ext_hom A) => {eq}x.
by apply val_inj; rewrite val_cast_TinSet.
Qed.

Lemma card_SpInSet (V : Bij) (U : {set V}) :
  cardSp A #|U| = #|[set p : SpInSet V | tag p == U]|.
Proof.
rewrite -(card_TinSet U) -cardSpE.
pose totag (x : A (TinSet U)) : SpInSet V :=
  Tagged (fun U : {set V} => A (TinSet U)) x.
have totag_inj : injective totag.
  by rewrite /totag=> x y /eqP /[!eq_Tagged] /= /eqP.
rewrite -(card_imset _ totag_inj); congr #|pred_of_set _|.
apply/setP => /= x; apply/imsetP/idP => [[y _ {x}->] /[!inE] //| ].
move: x => [S x /[!inE] /= /eqP U_eq_S]; subst S.
by exists x.
Qed.

Definition SpInSet_mor U V (f : {hom U -> V}) (x : el (SpInSet U)) : SpInSet V :=
  let (S, v) := x in existT _ [set f u | u in S] ((A # restr_hom S f) v).

Fact SpInSet_id : FunctorLaws.id SpInSet_mor.
Proof.
rewrite /SpInSet_mor => U -[/= S x] /=; apply/eqP.
rewrite -!/(Tagged _ _) -(Tagged_SpTinSet_castE (imset_id _)) eq_Tagged.
rewrite (functor_ext_hom A _ _ (@restr_id _ S)) hom_compE -functor_o.
set Fid := (F in A # F).
suff /(functor_ext_hom A) -> : Fid =1 idfun by rewrite functor_id.
rewrite /Fid /= /cast_TinSet /= => {}x /=.
by rewrite -!/(cast_TinSet _ _) cast_TinSetKV.
Qed.
Fact SpInSet_ext : FunctorLaws.ext SpInSet_mor.
Proof.
rewrite /SpInSet_mor => U V f g H -[/= S x] /=.
rewrite -!/(Tagged _ _) (functor_ext_hom A _ _ (restr_ext H)).
rewrite -(Tagged_SpTinSet_castE (eq_imset _ H)) hom_compE -functor_o.
apply/eqP; rewrite -tag_eqE /tag_eq eqxx /=.
set F := (F in A # F).
suff /(functor_ext_hom A) -> : F =1 (restr_hom S g) by rewrite tagged_asE.
rewrite {}/F /= => {}x.
by apply: val_inj; rewrite !val_cast_TinSet.
Qed.
Fact SpInSet_comp : FunctorLaws.comp SpInSet_mor.
Proof.
rewrite /SpInSet_mor => U V W g f -[/= S x] /=; apply/eqP.
rewrite hom_compE -functor_o.
rewrite (functor_ext_hom A _ _ (restr_comp _ _ (I := S))) /=.
rewrite -!/(Tagged _ _) -(Tagged_SpTinSet_castE (imset_comp g f _)).
rewrite -tag_eqE /tag_eq /= eqxx /= tagged_asE.
rewrite hom_compE -functor_o; apply/eqP.
exact: (functor_ext_hom A).
Qed.
Fact SpInSet_bij U V (f : {hom U -> V}) : bijective (SpInSet_mor f).
Proof. exact: (functor_bij SpInSet_ext SpInSet_id SpInSet_comp). Qed.
HB.instance Definition _ U V (f : {hom U -> V}) :=
  BijHom.Build (SpInSet U) (SpInSet V)
    (SpInSet_mor f : el (SpInSet U) -> (SpInSet V)) (SpInSet_bij f).
HB.instance Definition _ := @isFunctor.Build Bij Bij SpInSet SpInSet_mor
                              SpInSet_ext SpInSet_id SpInSet_comp.

Lemma tag_SpInSet U V (f : {hom U -> V}) x : tag ((SpInSet # f) x) = f @: (tag x).
Proof. by case: x => [/= S x]. Qed.

End SpInSet.


Section Localization.

Definition setTB (U : Bij) : Bij := TinSet [set: U] : Bij.

Section Defs.
Variable (U : Bij).
Definition toSetT_fun (x : el U) : setTB U := exist _ x (in_setT x).
Definition toSetT_inv (x : el (setTB U)) : U := \val x.
Lemma toSetT_funK : cancel toSetT_fun toSetT_inv.
Proof. by []. Qed.
Lemma toSetT_invK : cancel toSetT_inv toSetT_fun.
Proof. by move=> [x pf]; apply val_inj. Qed.
Lemma toSetT_bij : bijective toSetT_fun.
Proof. by exists toSetT_inv; [exact: toSetT_funK | exact: toSetT_invK]. Qed.
Fact toSetT_inv_bij : bijective toSetT_inv.
Proof. by exists toSetT_fun; [exact: toSetT_invK | exact: toSetT_funK]. Qed.
HB.instance Definition _ :=
  @BijHom.Build U (setTB U) toSetT_fun toSetT_bij.
HB.instance Definition _ :=
  @BijHom.Build (setTB U) U toSetT_inv toSetT_inv_bij.

End Defs.

Definition setTB_mor (U V : Bij) (f : {hom U -> V}) : {hom setTB U -> setTB V} :=
  [hom @toSetT_fun V \o f \o @toSetT_inv U].
Fact setTB_ext : FunctorLaws.ext setTB_mor.
Proof. by move=> U V f g eq x; apply val_inj; rewrite /= eq. Qed.
Fact setTB_id : FunctorLaws.id setTB_mor.
Proof. by move=> U x; apply val_inj. Qed.
Fact setTB_comp  : FunctorLaws.comp setTB_mor.
Proof. by move=> /= U V W f g x; apply val_inj. Qed.
HB.instance Definition _ := @isFunctor.Build Bij Bij setTB setTB_mor
                              setTB_ext setTB_id setTB_comp.

Definition SpSetT : Species := setTB.

Definition toSetT : FId ~~> SpSetT := toSetT_fun.
Lemma toSetT_natural : naturality FId SpSetT toSetT.
Proof. by []. Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij FId SpSetT toSetT toSetT_natural.
Lemma toSetT_invE : isoSpinv toSetT =%= toSetT_inv.
Proof. by apply: eq_nattrans_sym; apply: isoSpinvrE => U; apply: toSetT_funK. Qed.

Lemma card_SpSetT n : cardSp SpSetT n = n.
Proof. by rewrite /cardSp (BijHom_eq_card (@toSetT_inv _)) card_ord. Qed.

Lemma cardiso_SpSetT n : cardiso SpSetT n = (n != 0).
Proof. by rewrite (cardiso_SpE (isoSpinv toSetT)) cardiso_idSp. Qed.

End Localization.


Section ZeroSpecies.

Definition Sp0_fun := fun _ : Bij => voidB.
Definition Sp0_mor (U V : Bij) (f : {hom U -> V}) : {hom voidB -> voidB} := idfun.
HB.instance Definition _ :=
  @isFunctor.Build Bij Bij Sp0_fun Sp0_mor
    (fun _ _ _ _ _ => frefl _) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition Sp0 : Species := Sp0_fun.

Lemma cardSp0 n : cardSp Sp0 n = 0%N.
Proof. by rewrite /cardSp /= card_void. Qed.

Lemma cardiso_Sp0 n : cardiso Sp0 n = 0.
Proof.
by rewrite -!cardiso_ordE; apply: eq_card0 => i /[!inE]; apply/imsetP => [][[]].
Qed.

End ZeroSpecies.
Notation "0" := Sp0 : species_scope.


Section SetSpecies.

Definition setSp_fun (U : Bij) := unitB.
Lemma setSp_funE (U V : Bij) (f : {hom U -> V}) :
  setSp_fun U = setSp_fun V.
Proof. by []. Qed.
Lemma setSp_fun_uniq (U : Bij) (x y : setSp_fun U) : x = y.
Proof. by move: x y; rewrite /setSp_fun => - [] []. Qed.
Definition setSp_mor (U V : Bij) (f : {hom U -> V}) :
  {hom setSp_fun U -> setSp_fun V} :=
  eq_rect _ (fun x => {hom x -> setSp_fun V}) idfun _ (esym (setSp_funE f)).
Fact setSp_ext : FunctorLaws.ext setSp_mor.
Proof. by move=> /= U V f g _ x; apply: setSp_fun_uniq. Qed.
Fact setSp_id : FunctorLaws.id setSp_mor.
Proof. move=> /= a x; apply: setSp_fun_uniq. Qed.
Fact setSp_comp  : FunctorLaws.comp setSp_mor.
Proof. by move=> /= a b c f g x; apply: setSp_fun_uniq. Qed.
HB.instance Definition _ := @isFunctor.Build Bij Bij setSp_fun setSp_mor
                              setSp_ext setSp_id setSp_comp.
Definition setSp : Species := setSp_fun.

Lemma card_setSp n : cardSp setSp n = 1%N.
Proof. by rewrite /cardSp /= /setSp_fun /= card_unit. Qed.

Lemma isoclass_setSp (U : Bij) (i : setSp U) : isoclass i = [set: unit].
Proof.
apply/setP => [[]] /[!inE]; apply/orbitP; exists 1%g; first by rewrite inE.
by case: (actSp _ _ _ _).
Qed.

Lemma cardiso_setSp n : cardiso setSp n = 1%N.
Proof.
rewrite -cardiso_ordE.
rewrite -[RHS](cards1 [set: setSp 'I_n.+1]); congr #|pred_of_set _|.
apply/setP => /= S; rewrite !inE /setSp_fun /unitB.
apply/imsetP/eqP => [[i _ {S}->] | {S}->]; first by rewrite isoclass_setSp.
by exists tt; rewrite ?inE // isoclass_setSp.
Qed.

End SetSpecies.


Section SubsetSpecies.

Definition subsetSp_fun (U : Bij) : Bij := {set U}.
Definition subsetSp_mor U V (f : {hom U -> V}) :
  el (subsetSp_fun U) -> el (subsetSp_fun V) := fun X => f @: X.

Lemma subsetSp_mor_bij U V (f : {hom U -> V}) : bijective (subsetSp_mor f).
Proof.
by exists (subsetSp_mor (finv f)) => X;
  rewrite /subsetSp_mor -imset_comp -[RHS]imset_id; apply: eq_imset;
  [exact: finvK | exact: finvKV].
Qed.
HB.instance Definition _ U V (f : {hom U -> V}) :=
  BijHom.Build (subsetSp_fun U) (subsetSp_fun V)
    (subsetSp_mor f) (subsetSp_mor_bij f).
Fact subsetSp_ext : FunctorLaws.ext subsetSp_mor.
Proof. by move=> U V f g eq X /=; rewrite /subsetSp_mor /=; apply: eq_imset. Qed.
Fact subsetSp_id : FunctorLaws.id subsetSp_mor.
Proof. by move=> U X; apply: imset_id. Qed.
Fact subsetSp_comp  : FunctorLaws.comp subsetSp_mor.
Proof. by move=> U V W f g X; rewrite /= /subsetSp_mor -imset_comp. Qed.
HB.instance Definition _ :=
  @isFunctor.Build Bij Bij subsetSp_fun subsetSp_mor
    subsetSp_ext subsetSp_id subsetSp_comp.
Definition subsetSp : Species := subsetSp_fun.

Lemma card_subsetSp0n n : cardSp subsetSp n = (2 ^ n)%N.
Proof.
by rewrite /cardSp -cardsT /subsetSp_fun -powersetT card_powerset cardsT card_ord.
Qed.

Lemma isoclass_subsetSpE (U : Bij) (F : {set U}) :
  isoclass (A := subsetSp) F = [set X : {set U} | #|X| == #|F|].
Proof.
apply/setP => E /[!inE]; apply/orbitP/eqP => [[/= s _ {E}<-] |].
  exact/card_imset/perm_inj.
by move/esym/eqP/card_eq_imset_permP => [s {E}<-]; exists s.
Qed.

Lemma cardiso_subsetSp n : cardiso subsetSp n = n.+1.
Proof.
have cardltset (u : 'I_n.+1) : #|[set k : 'I_n | k < u]| = u.
  rewrite cardE /enum_mem -enumT -(size_map \val).
  rewrite (eq_filter (a2 := (gtn u) \o \val)); last by move=> i /=; rewrite inE.
  rewrite /= map_filter_comp val_enum_ord iota_ltn -?(ltnS u) //.
  by rewrite map_id size_iota.
rewrite -cardiso_ordE.
have <- : #|[set [set X : {set 'I_n} | #|X| == k] | k : 'I_n.+1]| = n.+1.
  rewrite -[RHS]card_ord; apply card_imset => /= i j.
  move/setP => /(_ [set k : 'I_n | k < i]) /[!in_set].
  by rewrite !cardltset eqxx => /esym/eqP; apply: val_inj.
congr #|pred_of_set _|; apply/setP => /= E.
apply/imsetP/imsetP => /=[[F _ {E}->] | [u _ {E}->]].
  exists (inord #|F|); rewrite //= inordK ?isoclass_subsetSpE //.
  by rewrite ltnS -[X in _ <= X]card_ord -cardsT subset_leq_card.
exists [set k : 'I_n | k < u] => //.
by rewrite isoclass_subsetSpE cardltset.
Qed.

End SubsetSpecies.


Section ifSpecies.
Variable  (condn : pred nat) (A B : Species).
Implicit Type (U V W : Bij).

Let cond U := condn #|U|.
Lemma condP U V (f : {hom U -> V}) : cond V = cond U.
Proof. by rewrite /cond (BijHom_eq_card f). Qed.

Local Notation ifAB c V := (if c then A V else B V).
Definition ifSp U := ifAB (cond U) U.

Section Hom.
Variables (U V : Bij) (f : {hom U -> V}).

Definition ifSp_mor : el (ifSp U) -> el (ifSp V) :=
  match condP f in (_ = a) return ifAB a U -> ifAB (cond V) V
  with erefl => if cond V as b return ifAB b U -> ifAB b V
                then A # f else B # f
  end.
Definition ifSp_inv : el (ifSp V) -> el (ifSp U) :=
  match esym (condP f) in (_ = a) return ifAB a V -> ifAB (cond U) U
  with erefl => if cond U as b return ifAB b V -> ifAB b U
                then A # (finv f) else B # (finv f)
  end.

Lemma ifSp_morK : cancel ifSp_mor ifSp_inv.
Proof.
rewrite /ifSp_mor /ifSp_inv /ifSp; case:_/(condP f) => /=.
by case: (cond V) => x; rewrite SpfinvK.
Qed.
Lemma ifSp_invK : cancel ifSp_inv ifSp_mor.
Proof.
rewrite /ifSp_mor /ifSp_inv /ifSp; case:_/(condP f) => /=.
by case: (cond V) => x; rewrite SpfinvKV.
Qed.
Lemma ifSp_mor_bij : bijective ifSp_mor.
Proof. exists ifSp_inv; [exact: ifSp_morK | exact: ifSp_invK]. Qed.
Lemma ifSp_inv_bij : bijective ifSp_inv.
Proof. exists ifSp_mor; [exact: ifSp_invK | exact: ifSp_morK]. Qed.
HB.instance Definition _ :=
  @BijHom.Build (ifAB (cond U) U) (ifAB (cond V) V) ifSp_mor ifSp_mor_bij.
HB.instance Definition _ :=
  @BijHom.Build (ifAB (cond V) V) (ifAB (cond U) U) ifSp_inv ifSp_inv_bij.

End Hom.

Fact ifSp_id : FunctorLaws.id ifSp_mor.
Proof.
move=> U; rewrite /= /ifSp_mor  /ifSp.
by case: (cond U) (condP _) => /= C x /=;
  rewrite (eq_irrelevance C (erefl _)) functor_id.
Qed.
Fact ifSp_ext : FunctorLaws.ext ifSp_mor.
Proof.
move=> U V f g eqfg; rewrite /= /ifSp_mor /ifSp.
rewrite (eq_irrelevance (condP g) (condP f)).
by move: (cond U) (cond V) (condP f) => [] [] //= C x;
  rewrite (eq_irrelevance C (erefl _)); exact: functor_ext_hom.
Qed.
Fact ifSp_comp : FunctorLaws.comp ifSp_mor.
move=> U V W f g; rewrite /= /ifSp_mor /ifSp.
have -> : condP (ssrfun_comp__canonical__category_Hom f g) =
            etrans (condP f) (condP g).
  exact: eq_irrelevance.
move: (condP f) (condP g) (etrans _ _).
by move: (cond U) (cond V) (cond W) => [] [] [] //= C1 C2 CT x;
  rewrite (eq_irrelevance C1 (erefl _)) (eq_irrelevance C2 (erefl _))
    (eq_irrelevance CT (erefl _)) [LHS]functor_o.
Qed.

HB.instance Definition _ :=
  @isFunctor.Build Bij Bij ifSp ifSp_mor ifSp_ext ifSp_id ifSp_comp.

Lemma card_ifSp n :
  cardSp ifSp n = if (cond 'I_n) then cardSp A n else cardSp B n.
Proof. by rewrite /cardSp /= /ifSp; case: (cond _). Qed.

Lemma ifSpT U : cond U ->
  { f : {hom A U -> ifSp U} |
    forall (s : {hom U -> U}) (a : A U), f ((A # s) a) = (ifSp # s) (f a) }.
Proof.
rewrite /ifSp; rewrite /actSp /= /actSp_fun /= /ifSp_mor => Hcond.
move: (@condP U U) => C.
have eqC g : C g = erefl (cond U) by apply: eq_irrelevance.
move: C eqC; rewrite Hcond => C eqC /=.
by exists idfun => s a /=; rewrite eqC.
Qed.
Lemma ifSpF U : ~~ cond U ->
  { f : {hom B U -> ifSp U} |
    forall (b : B U) (s : {hom U -> U}), f ((B # s) b) = (ifSp # s) (f b) }.
Proof.
rewrite /ifSp; rewrite /actSp /= /actSp_fun /= /ifSp_mor => Hcond.
move: (@condP U U) => C.
have eqC g : C g = erefl (cond U) by apply: eq_irrelevance.
move: C eqC; rewrite (negPf Hcond) => C eqC /=.
by exists idfun => a s /=; rewrite eqC.
Qed.

Lemma cardiso_ifSp n :
  cardiso ifSp n = if (cond 'I_n) then cardiso A n else cardiso B n.
Proof.
case: (boolP (cond 'I_n)) => Hcond; rewrite -!cardiso_ordE.
- have [f Hf] := ifSpT Hcond.
  by rewrite -(nattransp_cardiso (f := f)) // => a s /=; rewrite Hf.
- have [f Hf] := ifSpF Hcond.
  by rewrite -(nattransp_cardiso (f := f)) // => a s /=; rewrite Hf.
Qed.

End ifSpecies.


Section DeltaSpecies.

Variable (cond : nat -> bool).
Definition deltaSp : Species := ifSp cond setSp 0.

Lemma card_deltaSp n : cardSp deltaSp n = cond n.
Proof. by rewrite card_ifSp cardSp0 card_setSp card_ord; case: cond. Qed.
Lemma cardiso_deltaSp n : cardiso deltaSp n = cond n.
Proof.
rewrite cardiso_ifSp card_ord.
by case: cond; rewrite ?cardiso_setSp ?cardiso_Sp0.
Qed.
Lemma deltaSpE U (x : deltaSp U) : all_equal_to x.
Proof. by apply: fintype_le1P; rewrite cardSpE card_deltaSp; case cond. Qed.

End DeltaSpecies.
Notation "1" := (deltaSp (fun n => n == 0%N)) : species_scope.
Notation "\X" := (deltaSp (fun n => n == 1%N)) : species_scope.

Lemma cardSp1 n : cardSp 1 n = (n == 0%N).
Proof. exact: card_deltaSp. Qed.
Lemma cardSpX n : cardSp \X n = (n == 1%N).
Proof. exact: card_deltaSp. Qed.

Lemma cardiso_Sp1 n : cardiso 1 n = (n == 0%N).
Proof. exact: cardiso_deltaSp. Qed.
Lemma cardiso_SpX n : cardiso \X n = (n == 1%N).
Proof. exact: cardiso_deltaSp. Qed.


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
  @isFunctor.Build Bij Bij sumSp_fun sumSp_mor sumSp_ext sumSp_id sumSp_comp.
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
- left; apply/imsetP; exists (orbit (actSp A  'I_n) setT a).
    by apply/imsetP; exists a.
  by rewrite -[LHS]nattransp_orbit.
- right; apply/imsetP; exists (orbit (actSp B  'I_n) setT b).
    by apply/imsetP; exists b.
  by rewrite -[LHS]nattransp_orbit.
- by exists (inl x) => //; rewrite -[RHS]nattransp_orbit.
- by exists (inr x) => //; rewrite -[RHS]nattransp_orbit.
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
Definition sumSpC A B : (A + B) ~~> (B + A) := @sumSpC_fun A B.

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
Definition sumSpA  : (A + (B + C)) ~~> (A + B + C) := sumSpA_fun.
Definition sumSpAV : (A + B + C) ~~> (A + (B + C)) := sumSpA_inv.

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

Definition sumSpTr : (A1 + B1) ~~> (A2 + B2) := @sumSpTr_fun.
Fact sumSpTr_natural : naturality (A1 + B1) (A2 + B2) sumSpTr.
Proof. by move=> U V h [a|b] /=; rewrite !hom_compE natural. Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (A1 + B1) (A2 + B2) sumSpTr sumSpTr_natural.

End SumNatTransf.

Lemma sumSpTr_invE (A1 A2 B1 B2 : Species) (tA : A1 ~> A2) (tB : B1 ~> B2) :
  isoSpinv (sumSpTr tA tB) =%= sumSpTr (isoSpinv tA) (isoSpinv tB).
Proof. by apply: eq_nattrans_sym; apply: isoSpinvrE => U [] x /= /[!finvK]. Qed.


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
  { p : SpInSet A U * SpInSet B U | part2 setT (tag p.1) (tag p.2) }.

Lemma prodSp_mor_subproof U V (f : {hom U -> V}) (x : el (prodSpT U)) :
  part2 setT (tag ((SpInSet A # f) (val x).1)) (tag ((SpInSet B # f) (val x).2)).
Proof.
case: x => -/=[[a xa][b xb] /= Hp2].
by rewrite -(imsetT (BijP f)) part2_imset //; exact: (bij_inj (BijP f)).
Qed.
Definition prodSp_mor U V (f : {hom U -> V})
  (x : el (prodSpT U)) : el (prodSpT V) :=
  exist _ ((SpInSet A # f) (val x).1, (SpInSet B # f) (val x).2)
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
by apply/eq_prodSpP; rewrite /= !(functor_ext_hom (SpInSet _) _ _ eqfg).
Qed.
Lemma prodSp_mor_bij U V (f : {hom U -> V}) : bijective (prodSp_mor f).
Proof. exact: (functor_bij prodSp_ext prodSp_id prodSp_comp). Qed.
HB.instance Definition _ U V (f : {hom U -> V}) :=
  BijHom.Build (prodSpT U) (prodSpT V) (prodSp_mor f) (prodSp_mor_bij f).
HB.instance Definition _ :=
  @isFunctor.Build Bij Bij prodSpT prodSp_mor prodSp_ext prodSp_id prodSp_comp.


Definition prodSp : Species := prodSpT.


Lemma card_prodSp n :
  cardSp prodSp n = \sum_(i < n.+1) 'C(n, i) * (cardSp A i) * (cardSp B (n - i)).
Proof.
rewrite {1}/cardSp; rewrite -(card_imset predT val_inj) /= imset_val_sub.
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
  setX [set p : (SpInSet A 'I_n) | tag p == S]
       [set p : (SpInSet B 'I_n) | tag p == ~: S]); first last.
  apply/setP => -[a b]; rewrite !inE andbC; case: eqP => //= -> {a}.
  by rewrite part2C part2TE.
rewrite [RHS]cardsX -!card_SpInSet eq_card; congr (_ * (cardSp _ _)).
rewrite -[X in X - i]card_ord.
have:= (cardsCs S); rewrite eq_card => ->.
exact/subKn/subset_leq_card/subset_predT.
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
Definition prodSpC A B : (A * B) ~~> (B * A) := @prodSpC_fun A B.

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

Lemma appSpSet1_card V (S : {set V}) : 1 (TinSet S) -> #|S| = 0%N.
Proof. by rewrite /deltaSp /= /ifSp card_TinSet; case eqP. Qed.

Variable (A : Species).

Section Mor.
Variable (U : Bij).

Definition prodSp1_inv_def : el (A U) -> el ((A * 1) U).
move=> x.
pose a : A {x : U | x \in setT} := (A # toSetT U) x.
have b : 1 {x : U | x \in set0}.
  by rewrite /deltaSp /= /ifSp card_TinSet cards0 eqxx; exact tt.
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
  =1 cast_TinSet (esym (imsetT (BijP f))) \o (toSetT V \o f).
Proof. by move=> x; apply val_inj; rewrite val_cast_TinSet. Qed.

Fact prodSp1V_natural : naturality A (A * 1) prodSp1V.
Proof.
move=> U V h x /=; apply: eq_prodSpP.
  rewrite /= /prodSp1_inv; unlock; rewrite /prodSp1_inv_def /=.
  rewrite /= !hom_compE -!functor_o /=.
  have /= -> := functor_ext_hom A _ _ (restr_hom_setTE h).
  by rewrite functor_o /= -/(Tagged _ _) Tagged_SpTinSet_castE.
rewrite /prodSp1_inv -!lock /= -!/(Tagged _ _).
move: (eq_rect_r _ _) => HL; move: (eq_rect_r _ _) => HR.
rewrite -(Tagged_SpTinSet_castE (imset0 h) (A := 1)).
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
(* Eval hnf in prodSpDl_inv. *)
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
Definition prodSpDl  : (A * (B + C)) ~~> (A * B + A * C) := prodSpDl_fun.
Definition prodSpDlV : (A * B + A * C) ~~> (A * (B + C)) := prodSpDl_inv.

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
Implicit Type (T : {set TinSet S}).

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

Variable (T : {set TinSet S}).
Let up_fun (x : TinSet T) := \val (\val x).
Fact up_funP (x : TinSet T) : (up_fun x) \in upT T.
Proof.
rewrite /up_fun mem_imset; last exact: val_inj.
exact: TinSetP.
Qed.
Definition up (x : el (TinSet T)) : el (TinSet (upT T)) :=
  exist _ (up_fun x) (up_funP x).
Fact up_bij : bijective up.
Proof.
apply: inj_card_bij; first by move=> x y [] /val_inj/val_inj.
by rewrite !card_TinSet card_imset //; apply: val_inj.
Qed.
HB.instance Definition _ :=
  @BijHom.Build (TinSet T) (TinSet (upT T)) up up_bij.
Definition upSp (A : Species) : {hom A (TinSet T) -> A (TinSet (upT T))} := A # up.
End UpSpecies.

Section UpSpeciesInSet.
Variable (A : Species) (U : Bij) (S : {set U}).

Definition upSpInSet (x : SpInSet A (TinSet S)) : SpInSet A U :=
  let (E, y) := x in (existT _ (upT E) (upSp _ _ y)).
Lemma tag_upSpInSet x : tag (upSpInSet x) = upT (tag x).
Proof. by rewrite /upSpInSet; case: x. Qed.

End UpSpeciesInSet.


Section DownSpecies.

Variables (U : Bij) (S T : {set U}).
Hypothesis (TsubS : T \subset S).
Fact down_subproof (x : TinSet T) : val x \in S.
Proof. exact/(subsetP TsubS)/TinSetP. Qed.
Definition down_fun (x : TinSet T) : (TinSet S) :=
  exist _ (\val x) (down_subproof x).
Definition downT := [set down_fun x | x in [set: TinSet T]].

Lemma downTK : upT downT = T.
Proof.
rewrite /upT /downT -imset_comp; apply/setP => u.
apply/imsetP/idP => [[[y yinT /=] _ {u}-> //] | uinT].
by exists (exist _ u uinT).
Qed.
Lemma down_fun_inj : injective down_fun.
Proof. by move=> [x px][y py] /= [eqxy]; apply: val_inj => /=. Qed.
Fact down_fun_in (x : TinSet T) : down_fun x \in down_fun @: setT.
Proof. by rewrite (mem_imset _ _ down_fun_inj). Qed.
Definition down (x : el (TinSet T)) : el (TinSet downT) :=
  exist _ (down_fun x) (down_fun_in x).
Fact down_bij : bijective down.
Proof.
apply: inj_card_bij; first by move=> [x px] [y py] [eq]; apply val_inj.
rewrite card_TinSet (card_imset _ down_fun_inj).
by rewrite card_TinSet cardsT card_TinSet.
Qed.
HB.instance Definition _ :=
  @BijHom.Build (TinSet T) (TinSet downT) down down_bij.
Definition downSp (A : Species) : {hom A (TinSet T) -> A (TinSet downT)} := A # down.

End DownSpecies.

Section DownSpeciesInSet.
Variable (A : Species) (U : Bij) (S : {set U}) (x : SpInSet A U).
Hypothesis tX : tag x \subset S.

Definition downSpInSet : SpInSet A (TinSet S).
case: x tX => [/= T y TsubS].
apply (existT _ (downT TsubS) (downSp TsubS A y)).
Defined.
Lemma tag_downSpInSet : tag downSpInSet = downT tX.
Proof. by rewrite /downSpInSet; case: x tX. Qed.
Lemma downSpInSetK : upSpInSet downSpInSet = x.
Proof.
rewrite /upSpInSet /downSpInSet.
case: x tX => [/= E y] ty.
apply eqSpInSet => /=; split => [|eqtag]; first exact: downTK.
rewrite eq_Tagged /= /upSp /downSp; apply/eqP.
do 2 rewrite hom_compE -functor_o /=.
rewrite -[RHS](@functor_id _ _ A) /=; apply: (functor_ext_hom A) => {}y.
by apply val_inj; rewrite val_cast_TinSet.
Qed.

End DownSpeciesInSet.

Lemma SpInSet_up (A : Species) (U V : Bij) (h : {hom U -> V}) (E : {set U})
  (x : SpInSet A (TinSet E)) :
  (SpInSet A # h) (upSpInSet x) = upSpInSet ((SpInSet A # (restr_hom E h)) x).
Proof.
case: x => [SE xSE] /=.
apply eqSpInSet => /=; split => [|eqtag].
  by rewrite /upT -!imset_comp; apply eq_imset.
rewrite eq_Tagged /= /upSp /=; apply/eqP.
rewrite [RHS]hom_compE [LHS]hom_compE -!functor_o hom_compE -!functor_o /=.
apply: (functor_ext_hom A) => {xSE}x /=.
by apply val_inj; rewrite /= val_cast_TinSet /=.
Qed.


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
have finj := bij_inj (BijP f).
rewrite /part3 !(imset_disjoint finj).
by rewrite -!imsetU -(inj_eq (imset_inj finj)) (imsetT (BijP f)).
Qed.
Lemma part23 U (W X Y Z : {set U}) :
  part2 setT W Z -> part2 Z X Y -> part3 W X Y.
Proof.
rewrite /part2 /part3 =>/andP[/eqP eqU dWZ] /andP[/eqP eqZ ->].
rewrite andbT -setUA -eqZ eqU eqxx /=.
by rewrite !(disjointWr _ dWZ) // eqZ ?subsetUr ?subsetUl.
Qed.

Definition prodSp3T U : Bij :=
  { p : SpInSet A U * SpInSet B U * SpInSet C U |
    part3 (tag p.1.1) (tag p.1.2) (tag p.2) }.
Definition prodSp3_mor U V (f : {hom U -> V}) : el (prodSp3T U) -> el (prodSp3T V).
move=> /= [[[a b] c] /= p3].
exists ((SpInSet A # f) a, (SpInSet B # f) b, (SpInSet C # f) c) => /=.
by rewrite /SpInSet_mor /= !tag_SpInSet part3_imset.
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
HB.instance Definition _ := @isFunctor.Build Bij Bij prodSp3T prodSp3_mor
                              prodSp3_ext prodSp3_id prodSp3_comp.

Definition prodSp3 : Species := prodSp3T.


Section MorphA3.
Variable (U : Bij).

Definition prodSpA3_fun : el ((A * (B * C)) U) -> el (prodSp3 U).
move=> [[/= xA [/= V ]]] [[xSB xSC]] /= BC_SC UA_V.
exists (xA, upSpInSet xSB, upSpInSet xSC).
rewrite /= !tag_upSpInSet; apply: (part23 UA_V).
by rewrite -{1}(upT_setT V) /upT (part2_imset _ _ _ val_inj).
Defined.
Definition prodSpA3_inv : el (prodSp3 U) -> el ((A * (B * C)) U).
move=> [/=[[a b]c] /=] p3.
have bc : (B * C)%species (TinSet (tag b :|: tag c)).
  pose xb := downSpInSet (subsetUl (tag b) (tag c)).
  pose xc := downSpInSet (subsetUr (tag b) (tag c)).
  exists (xb, xc) => /=.
  rewrite -(part2_imset _ _ _ val_inj) /= /xb /xc !tag_downSpInSet /=.
  rewrite /downT -!imset_comp !(eq_imset (g := val)) //.
  move: p3 => /and4P[/eqP SU dab dac dbc].
  by rewrite !imsetTE /= !imset_val_TinSet /part2 eqxx /=.
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
  [set x | (x \in tag (upSpInSet xSB)) || (x \in tag (upSpInSet xSC))] = V.
  rewrite !tag_upSpInSet.
  move: BC_V => /andP[/eqP + _] => /(congr1 (@upT _ _)).
  rewrite upT_setU upT_setT=> {9}->.
  by apply/setP => x; rewrite !inE.
rewrite -!/(Tagged _ _) -(Tagged_SpTinSet_castE eqtag (A := B * C)) eq_Tagged /=.
rewrite -(inj_eq val_inj) /= xpair_eqE /=; apply/andP.
split; apply/eqP; apply eqSpInSet => /=; split.
- rewrite tag_SpInSet tag_downSpInSet /downT -imset_comp.
  case: xSB {H2} eqtag BC_V => /= SB _ eqtag _.
  apply/setP => u; apply/imsetP/idP => [[[u' u'in _ {u}->]] /= | uinSB].
    have:= u'in => /imsetP [/= [u uinV] Hin equ']; subst u'.
    move: Hin; congr (_ \in SB); apply: val_inj => /=.
    by rewrite val_cast_TinSet.
  have Hupu : val u \in upT SB by rewrite /upT (mem_imset _ _ val_inj).
  exists (exist _ (val u) Hupu); first by rewrite inE.
  rewrite /=; apply val_inj => /=.
  by rewrite val_cast_TinSet.
- case: xSB {H2} eqtag BC_V => /= SB b eqtag _ eqtag1.
  rewrite eq_Tagged /=; apply/eqP.
  repeat rewrite hom_compE -!functor_o /=.
  rewrite -[RHS](@functor_id _ _ B); apply: (functor_ext_hom B) => {}b /=.
  by repeat (apply val_inj; rewrite val_cast_TinSet /=).
- rewrite tag_SpInSet tag_downSpInSet /downT -imset_comp.
  case: xSC {H2} eqtag BC_V => /= SC _ eqtag _.
  apply/setP => u; apply/imsetP/idP => [[[u' u'in _ {u}->]] /= | uinSB].
    have:= u'in => /imsetP [/= [u uinV] Hin equ']; subst u'.
    move: Hin; congr (_ \in SC); apply: val_inj => /=.
    by rewrite val_cast_TinSet.
  have Hupu : val u \in upT SC by rewrite /upT (mem_imset _ _ val_inj).
  exists (exist _ (val u) Hupu); first by rewrite inE.
  rewrite /=; apply val_inj => /=.
  by rewrite val_cast_TinSet.
- case: xSC {H2} eqtag BC_V => /= SC c eqtag _ eqtag1.
  rewrite eq_Tagged /=; apply/eqP.
  repeat rewrite hom_compE -!functor_o /=.
  rewrite -[RHS](@functor_id _ _ C); apply: (functor_ext_hom C) => {}c /=.
  by repeat (apply val_inj; rewrite val_cast_TinSet /=).
Qed.
Fact prodSpA3KV : cancel prodSpA3_inv prodSpA3_fun.
Proof.
move=> [/=[[a b]c] /=] p3; move: (eq_ind_r _ _ _) => HL.
apply val_inj => /= {p3 HL}; apply/eqP.
by repeat (rewrite xpair_eqE; apply/andP; split) => //; rewrite downSpInSetK.
Qed.
Fact prodSpA3_fun_bij : bijective prodSpA3_fun.
Proof. by exists prodSpA3_inv; [exact: prodSpA3K | exact: prodSpA3KV]. Qed.
HB.instance Definition _ :=
  @BijHom.Build ((A * (B * C)) U) (prodSp3 U) prodSpA3_fun prodSpA3_fun_bij.

End MorphA3.

Definition prodSpA3 : (A * (B * C)) ~~> prodSp3 := prodSpA3_fun.

Fact prodSpA3_natural : naturality (A * (B * C)) prodSp3 prodSpA3.
Proof.
move=> U V h [[/= xA [/= E ]]] [[xSB xSC]] /= BC_E UA_E /=.
apply: val_inj => /= {UA_E}; apply/eqP.
by rewrite !xpair_eqE !SpInSet_up !eqxx.
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

Definition prodSpC3 : (prodSp3 C A B) ~~> (prodSp3 A B C) := @prodSpC3_fun A B C.

Fact prodSpC3_natural : naturality (prodSp3 C A B) (prodSp3 A B C) prodSpC3.
Proof. by move=> U V h [[[c a] b] /= H]; apply: val_inj. Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (prodSp3 C A B) (prodSp3 A B C)
    prodSpC3 prodSpC3_natural.

End ProdCycleA3.


Definition prodSpA (A B C : Species) : (A * B * C) ~> A * (B * C) :=
  isoSpinv (prodSpA3 _ _ _) \v prodSpC3 _ _ _ \v prodSpA3 _ _ _ \v prodSpC _ _.
