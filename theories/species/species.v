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
move=> [g fK gK].
by apply/setP => y; rewrite -(gK y) !(mem_imset, inE) //; apply: can_inj.
Qed.

Lemma imsetT : bijective f -> [set f y | y in [set: S]] = [set: T].
Proof.
move=> [g fK gK]; apply/setP => i; rewrite inE; apply/imsetP.
by exists (g i).
Qed.

Lemma imsetTE : [set f y | y in [set: S]] = [set f y | y in S].
Proof.
by apply/setP => x; apply/imsetP/imsetP => [][y _ {x}->]; exists y.
Qed.

Lemma iota_ltn a b : b <= a -> [seq i <- iota 0 a | i < b] = iota 0 b.
Proof.
elim: a b => [|a IHa] b; first by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt => /orP[/eqP ->|].
  rewrite -[RHS] filter_predT; apply: eq_in_filter => i.
  by rewrite mem_iota /= add0n => ->.
rewrite ltnS => /[dup] /IHa <- leba.
by rewrite -addn1 iotaD add0n filter_cat /= ltnNge leba /= cats0.
Qed.

Lemma map_filter_comp (T1 T2: Type) (l : seq T1) (PP : pred T2) (F : T1 -> T2) :
  [seq F i | i <- l & PP (F i)] = [seq i | i <- map F l & PP i ].
Proof.
rewrite filter_map /= -map_comp.
have /eq_filter -> : preim F [eta PP] =1 fun i => PP (F i) by [].
by rewrite map_comp.
Qed.

Lemma cardltset a b : b <= a -> #|[set k : 'I_a | k < b]| = b.
Proof.
move=> leba.
rewrite cardE /enum_mem -enumT -(size_map \val).
rewrite (eq_filter (a2 := gtn b \o \val)); last by move=> i /=; rewrite inE.
rewrite /= map_filter_comp val_enum_ord iota_ltn -?(ltnS u) //.
by rewrite map_id size_iota.
Qed.

End SSRCompl.

Lemma card_preim (I J : finType) (f : I -> J) (E : {set I}) :
  #|E| = \sum_(j : J) #|[set x in E | f x == j]|.
Proof.
rewrite -sum1_card (partition_big f xpredT) //=; apply eq_bigr => j _.
by rewrite -sum1_card; apply eq_bigl => i /[!inE].
Qed.

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

Section PermExtd.

Variables (U V : finType) (f : U -> V) (finj : injective f) (s : {perm U}).

Definition perm_extd_fun :=
  [fun v => if [pick u | f u == v] is Some u then f (s u) else v].
Lemma perm_extd_inj : injective perm_extd_fun.
Proof.
move=> v1 v2 /=.
case: pickP => [u1 /eqP {v1}<- | nou1]; case: pickP => [u2 /eqP {v2}<- | nou2] //.
- by move/finj/perm_inj ->.
- by move/eqP; rewrite nou2.
- by move/esym/eqP; rewrite nou1.
Qed.
Definition perm_extd : {perm V} := perm perm_extd_inj.
Lemma perm_extdP u : perm_extd (f u) = f (s u).
Proof.
rewrite permE /=; case: pickP => [u' /eqP /finj -> // | /(_ u)].
by rewrite eqxx.
Qed.
Lemma perm_extd_out v : (v \notin f @: setT) -> perm_extd v = v.
Proof.
rewrite permE /=; case: pickP => [u /eqP <-|//].
by rewrite mem_imset // inE.
Qed.
End PermExtd.


Section PermGlue.
Variable (U : finType) (E1 E2 F1 F2 : {set U}) (s1 s2 : {perm U}).
Hypothesis HE : E1 = ~: E2.
Hypothesis HF : F1 = ~: F2.
Hypothesis eqEF1 : [set s1 u | u in F1] = E1.
Hypothesis eqEF2 : [set s2 u | u in F2] = E2.
Definition glue_perm_fun := [fun u => if u \in F1 then s1 u else s2 u].
Lemma glue_perm_inj : injective glue_perm_fun.
Proof.
move=> u1 u2 /=.
case: (boolP (u1 \in F1)) => uin1; case: (boolP (u2 \in F1)) => uin2.
- by move/perm_inj.
- move=> eq; exfalso.
  have : s1 u1 \in E1 by rewrite -eqEF1 mem_imset //; exact: perm_inj.
  rewrite {}eq HE inE.
  suff -> : s2 u2 \in E2 by [].
  rewrite -eqEF2 mem_imset //; last exact: perm_inj.
  by move: uin2; rewrite HF inE negbK.
- move=> eq; exfalso.
  have : s1 u2 \in E1 by rewrite -eqEF1 mem_imset //; exact: perm_inj.
  rewrite -{}eq HE inE.
  suff -> : s2 u1 \in E2 by [].
  rewrite -eqEF2 mem_imset //; last exact: perm_inj.
  by move: uin1; rewrite HF inE negbK.
- by move/perm_inj.
Qed.
Definition glue_perm : {perm U} := perm glue_perm_inj.

End PermGlue.


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
Lemma Bij_injP (U V : Bij) (f : {hom U -> V}) : injective f.
Proof. exact: bij_inj (BijP f). Qed.
Arguments Bij_injP {U V} (f).
Hint Resolve BijP Bij_injP : core.


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
move => x /=; apply: (Bij_injP (finv f)).
by rewrite finvKV [RHS]finvK.
Qed.
Lemma finv_id (U : Bij) : finv (@idfun U) =1 idfun.
Proof.
by move=> x /=; apply (Bij_injP idfun); rewrite finvK. Qed.
Lemma finvE (U V : Bij) (f g : {hom U -> V}) :
  f =1 g -> finv f =1 finv g.
Proof. by move=> eq x; apply (Bij_injP f); rewrite finvKV eq finvKV. Qed.
Lemma finv_comp (U V W : Bij) (f : {hom U -> V}) (g : {hom V -> W}) :
  finv (g \o f) =1 (finv f) \o (finv g).
Proof.
move=> x /=.
apply (Bij_injP f); apply (Bij_injP g).
by rewrite -[LHS]compapp !finvKV.
Qed.

HB.factory Record BijHom (U V : Bij)
  (f : el U -> el V) := { finsetsbij_hom : bijective f }.
HB.builders Context (U V : Bij)
  (f : el U -> el V) of BijHom U V f.
HB.instance Definition _ := isHom.Build _ U V f finsetsbij_hom.
HB.instance Definition _ := isIsom.Build _ U V f (finv_bij f) (finvK f) (finvKV f).
HB.end.

Lemma Bij_eq_card (U V : Bij) (f : {hom U -> V}) : #|U| = #|V|.
Proof. exact: (bij_eq_card (isHom_inhom f)). Qed.

Lemma cast_ord_bij i j (eq : i = j) : bijective (cast_ord eq).
Proof. by exists (cast_ord (esym eq)) => x; rewrite ?cast_ordK ?cast_ordKV. Qed.
HB.instance Definition _ i j (eq : i = j) :=
  @BijHom.Build 'I_i 'I_j (cast_ord eq : el ('I_i : Bij) -> el ('I_j : Bij))
    (cast_ord_bij eq).


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

Definition TSet : Bij := {x : U | x \in S} : Bij.
Lemma TSetP (x : TSet) : val x \in S.
Proof. by case: x. Qed.
Lemma imset_val_TSet : [set \val x | x : TSet] = S.
Proof.
apply/setP => x; apply/imsetP/idP => [[/= [y y_in_S] _ ->] // | x_in_S].
by exists (exist _ x x_in_S).
Qed.
Lemma card_TSet : #|TSet| = #|S|.
Proof.
by rewrite -[LHS](card_imset _ val_inj) imset_val_TSet.
Qed.

End TypeInSet.


Section Restriction.

Variable (U V : Bij) (I : {set U}) (f : {hom U -> V}).

Fact restr_subproof (x : TSet I) : f (\val x) \in (f @: I).
Proof. by case: x => x Px /=; apply: imset_f. Qed.
Definition restr (x : el (TSet I)) : el (TSet (f @: I)) :=
  exist _ (f (\val x)) (restr_subproof x).

Fact restr_inv_spec (y : TSet (f @: I)) : { x : TSet I | restr x == y }.
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
by move/Bij_injP; exact: val_inj.
Qed.
Let restrKV : cancel restr_inv restr.
Proof.
move=> y; apply val_inj; rewrite /restr_inv.
by case: (restr_inv_spec y) => /= x /eqP <-{y}.
Qed.
Fact restr_bij : bijective restr.
Proof. by exists restr_inv. Qed.
HB.instance Definition _ := BijHom.Build _ _ restr restr_bij.
Definition restr_hom : {hom[Bij] TSet I -> TSet (f @: I)} := restr.

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
move=> x; apply: (Bij_injP (A # f)).
by rewrite SpfinvKV finvKV.
Qed.

HB.instance Definition _ :=
  BijHom.Build _ _ (@enum_rank U : el U -> el ('I_#|U| : Bij)) (@enum_rank_bij U).

Definition cardSp (n : nat) := #|A 'I_n|.
Lemma cardSpE : #|A U| = cardSp #|U|.
Proof. exact: Bij_eq_card (A # (@enum_rank U)). Qed.

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
Definition perm_hom := perm (Bij_injP f).
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

Notation isoclass x := (orbit (actSp _) setT x).
Definition isoclasses U : {set {set A U}} := [set isoclass x | x in [set: A U]].

Lemma mem_isoclass U (f : {hom U -> U}) x : (A # f) x \in isoclass x.
Proof. by rewrite -(functor_ext_hom A _ _ (perm_homE f)) /=; apply: mem_orbit. Qed.

Lemma morph_isoclass U V (f : {hom U -> V}) x :
  (A # f) @: isoclass x = isoclass ((A # f) x).
Proof.
(* TODO : this is very similar to nattransp_isoclass, can it be merged ? *)
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

Lemma isoclass_morph U V (f g : {hom U -> V}) x :
  (A # f) x \in isoclass ((A # g) x).
Proof.
rewrite -morph_isoclass; apply/imsetP.
exists ((A # ((finv g) \o f)) x); first exact: mem_isoclass.
by rewrite functor_o /= SpfinvKV.
Qed.

Lemma imset_isoclasses U V (f : {hom U -> V}) :
  [set (A # f) @: (S : {set _}) | S in isoclasses U] = isoclasses V.
Proof.
apply/setP => /= E.
apply/imsetP/imsetP => /=[[F /imsetP[u _ {F}-> {E}-> /=]] | [i _ {E}->]].
  exists ((A # f) u); first by rewrite inE.
  exact: morph_isoclass.
exists (orbit (actSp _) [set: {perm U}] ((A # finv f) i)); first exact: imset_f.
by rewrite morph_isoclass SpfinvKV.
Qed.
Lemma card_isoclassesE U V (f : {hom U -> V}) : #|isoclasses U| = #|isoclasses V|.
Proof.
rewrite -(imset_isoclasses f) [RHS]card_imset //.
exact: (imset_inj (Bij_injP _)).
Qed.

Definition isoreprs U := orbit_transversal (actSp U) setT setT.
Definition isorepr U (x : A U) :=
  transversal_repr x (isoreprs U) (orbit (actSp U) setT x).

Definition isotype U (x : A U) := isorepr ((A # @enum_rank U) x).
Definition cardiso n := #|isoreprs 'I_n|.

Lemma isotypesP U : is_transversal (isoreprs U) (isoclasses U) setT.
Proof. exact: (transversalP (orbit_partition (actSpP _))). Qed.
Lemma isorepr_class U (x : A U) : isorepr x \in isoclass x.
Proof. by apply: (repr_mem_pblock (isotypesP U)); exact: imset_f. Qed.
Lemma isoreprsE U :
  {in (isoreprs U) &, forall x y : A U, (y \in isoclass x) = (x == y)}.
Proof.
have [_ _ + _ x xin y yin] := orbit_transversalP (actSpP U).
by apply.
Qed.
Lemma isoreprs_ex U (x : A U) : exists s : {perm U}, actSp U x s \in isoreprs U.
Proof.
have [_ _ _ /(_ x) []] := orbit_transversalP (actSpP U).
  by rewrite inE.
by move=> /= s _ HS; exists s.
Qed.
Lemma isorepr_mem U (x : A U) : isorepr x \in isoreprs U.
Proof.
apply: (repr_mem_transversal (isotypesP _)); rewrite -/(isoclass x).
exact: imset_f.
Qed.
Lemma isorepr_ex U (x : A U) : exists s : {perm U}, actSp U x s = isorepr x.
Proof.
have [s /isoreprsE/(_ (isorepr_mem x)) Heq] := isoreprs_ex x.
exists s; apply/eqP; rewrite -{}Heq.
apply: (orbit_trans (isorepr_class x)).
apply/orbitP; exists (s^-1)%g => //.
by rewrite actK.
Qed.

Lemma card_isoreprE U : #|isoreprs U| = #|isoclasses U|.
Proof. exact (card_transversal (isotypesP U)). Qed.
Lemma cardisoE U : #|isoclasses U| = cardiso #|U|.
Proof. by rewrite /cardiso card_isoreprE (card_isoclassesE (@enum_rank U)). Qed.
Lemma cardiso_ordE n : #|isoclasses 'I_n| = cardiso n.
Proof. by rewrite cardisoE card_ord. Qed.

Lemma isotype_mem U (x : A U) : isotype x \in isoreprs 'I_#|U|.
Proof. exact: isorepr_mem. Qed.
Lemma isotype_ex U (x : A U) :
  exists f : {hom U -> 'I_#|U|}, (A # f) x = isotype x.
Proof.
rewrite /isotype.
set ix := (A # @enum_rank U) x.
have [_ H] := orbit_transversalP (actSpP 'I_#|U|).
have /orbitP[/= s _] : isotype x \in orbit (actSp 'I_#|U|) setT ix.
  by apply: (repr_mem_pblock (isotypesP _)); exact: imset_f.
rewrite /actSp_fun /isotype -/ix => <-.
by exists (s \o (@enum_rank U)); rewrite /ix functor_o.
Qed.

Lemma isotypeE U (x : A U) (f : {hom U -> 'I_#|U|}) :
  (A # f) x \in isoreprs 'I_#|U| -> (A # f) x = isotype x.
Proof.
move=> H; apply/eqP; rewrite -isoreprsE ?isotype_mem //.
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
by move: (Bij_eq_card f) (X in A # X) x => {f fy V}<- f x /isotypeE ->.
Qed.

End Action.
Notation isoclass x := (orbit (actSp _ _) setT x).


Section NaturalTransport.

Lemma nattransp_isoclass (A B : Species) (U : Bij) (f : A U -> B U) :
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
  exact: nattransp_isoclass.
exists (finv f @: orbit (actSp B U) setT b).
  apply/imsetP; exists (finv f b); first by rewrite inE.
  apply: nattransp_isoclass => a s /=.
  by apply: (Bij_injP f); rewrite -fnat !finvKV.
apply/setP => b'; apply/orbitP/imsetP => [[/= s _ {b'}<-]|].
  exists (finv f (actSp_fun b s)); last by rewrite finvKV.
  rewrite mem_imset //.
  by apply/orbitP; exists s; first by rewrite inE.
move=> [a /imsetP[b'' /orbitP [/= s _ {b''}<- {a}-> {b'}->]]].
exists s; first by rewrite inE.
by rewrite finvKV.
Qed.

Lemma nattransp_cardiso : #|isoclasses A U| = #|isoclasses B U|.
Proof.
rewrite -nattransp_isoclasses [RHS]card_imset //.
exact : imset_inj.
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
apply: (Bij_injP (F V \o A # h)).
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
apply: (Bij_injP (F U)).
by rewrite hom_compE H finvKV.
Qed.

Lemma card_SpE : cardSp A =1 cardSp B.
Proof. by move=> U; apply: Bij_eq_card (F 'I_U). Qed.

Lemma cardiso_SpE : cardiso A =1 cardiso B.
Proof.
move=> n; rewrite -!cardiso_ordE.
pose ff := fun (S : {set A _}) => F 'I_n @: S.
rewrite -(card_imset (f := ff)); last exact: imset_inj.
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

Lemma isoclass_idSp (U : Bij) (u : U) : isoclass (u : idSp U) = [set: U].
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

Definition cast_TSet I J (eq : I = J) (y : el (TSet I)) : el (TSet J) :=
  ecast X (TSet X) eq y.

Lemma val_cast_TSet I J (eq : I = J) y : \val (cast_TSet eq y) = \val y.
Proof. by rewrite /cast_TSet; case: y => [x Hx] /=; case:_/eq. Qed.

Lemma cast_TSetK I J (eqIJ : I = J) :
  cancel (cast_TSet eqIJ) (cast_TSet (esym eqIJ)).
Proof. by rewrite /cast_TSet; subst J => /=. Qed.
Lemma cast_TSetKV I J (eqIJ : I = J) :
  cancel (cast_TSet (esym eqIJ)) (cast_TSet eqIJ).
Proof. by rewrite /cast_TSet; subst J => /=. Qed.
Fact cast_TSet_bij I J (eqIJ : I = J) : bijective (cast_TSet eqIJ).
Proof.
by exists (cast_TSet (esym eqIJ)); [exact: cast_TSetK | exact: cast_TSetKV].
Qed.
HB.instance Definition _ I J (eqIJ : I = J) :=
  BijHom.Build _ _ (cast_TSet eqIJ) (cast_TSet_bij eqIJ).

Lemma cast_TSetE I J (eq1 eq2 : I = J) : cast_TSet eq1 =1 cast_TSet eq2.
Proof. by move=> x; apply: val_inj; rewrite !val_cast_TSet. Qed.
Lemma cast_TSet_id I (eqI : I = I) : cast_TSet eqI =1 idfun.
Proof. by move=> x; apply: val_inj; rewrite !val_cast_TSet. Qed.
Lemma cast_TSet_comp I J K (eqIJ : I = J) (eqJK : J = K) :
  cast_TSet eqJK \o cast_TSet eqIJ =1 cast_TSet (etrans eqIJ eqJK).
Proof. by move=> x; apply: val_inj; rewrite !val_cast_TSet. Qed.

Lemma Tagged_TSet_castE I J (eqIJ : I = J) (x : TSet I) :
  Tagged (@TSet U) x = Tagged (@TSet U) (ecast X (TSet X) eqIJ x).
Proof. by move: x; subst I. Qed.

End Cast.

Lemma Tagged_SpTSet_castE (V : Bij) (I J : {set V}) (eq : I = J) (A : Species) x :
  Tagged (fun U => A (TSet U)) ((A # cast_TSet eq) x) =
    Tagged (fun U => A (TSet U)) x.
Proof.
subst I => /=.
have /functor_ext_hom -> /= : cast_TSet (erefl J) =1 idfun by [].
by rewrite functor_id_hom.
Qed.

Lemma restr_id (U : Bij) (I : {set U}) :
  restr_hom I [hom idfun] =1 cast_TSet (esym (imset_id I)).
Proof. by move=> x /=; apply val_inj; rewrite val_cast_TSet. Qed.
Lemma restr_comp (U V W : Bij) (f : {hom U -> V}) (g : {hom V -> W}) (I : {set U}) :
  restr_hom _ g \o restr_hom I f
  =1 cast_TSet (imset_comp g f I) \o restr_hom _ (g \o f).
Proof. by move => x /=; apply val_inj; rewrite val_cast_TSet !val_restrE. Qed.
Lemma restr_ext (U V : Bij) (f g : {hom U -> V}) (I : {set U}) (eq_fg : f =1 g) :
  restr_hom I f =1 cast_TSet (eq_imset _ (fsym eq_fg)) \o (restr_hom I g).
Proof. by move => x /=; apply val_inj; rewrite !val_cast_TSet !val_restrE. Qed.


Section SpSet.

Variable (A : Species).
Implicit Types (U V : Bij).

Definition SpSet U : Bij := { I : {set U} & A (TSet I) }.

Lemma eqSpSet U (x y : SpSet U) :
  x = y <->
    ((tag x = tag y) /\
       (let (E, xx) := x in let (F, yy) := y in forall eqtag : E = F,
          Tagged (fun G => A (TSet G)) ((A # cast_TSet eqtag) xx) ==
            Tagged (fun G => A (TSet G)) yy)).
Proof.
split => [eqxy|].
  subst y; split => //.
  case: x => [E x] eqE /=; rewrite eq_Tagged /=; apply/eqP.
  rewrite -[RHS](@functor_id _ _ A) /=; apply: (functor_ext_hom A) => {}x.
  by apply val_inj; rewrite val_cast_TSet.
case: x y => /= [E x][F y] /= [eqEF eq]; subst F; apply/eqP.
rewrite -!/(Tagged _ _) -(eqP (eq _)) eq_Tagged /=; apply/eqP.
rewrite -[LHS](@functor_id _ _ A) /=; apply: (functor_ext_hom A) => {eq}x.
by apply val_inj; rewrite val_cast_TSet.
Qed.

Lemma card_SpSet (V : Bij) (U : {set V}) :
  cardSp A #|U| = #|[set p : SpSet V | tag p == U]|.
Proof.
rewrite -(card_TSet U) -cardSpE.
pose totag (x : A (TSet U)) : SpSet V :=
  Tagged (fun U : {set V} => A (TSet U)) x.
have totag_inj : injective totag.
  by rewrite /totag=> x y /eqP /[!eq_Tagged] /= /eqP.
rewrite -(card_imset _ totag_inj); congr #|pred_of_set _|.
apply/setP => /= x; apply/imsetP/idP => [[y _ {x}->] /[!inE] //| ].
move: x => [S x /[!inE] /= /eqP U_eq_S]; subst S.
by exists x.
Qed.

Definition SpSet_mor U V (f : {hom U -> V}) (x : el (SpSet U)) : SpSet V :=
  let (S, v) := x in existT _ [set f u | u in S] ((A # restr_hom S f) v).

Fact SpSet_id : FunctorLaws.id SpSet_mor.
Proof.
rewrite /SpSet_mor => U -[/= S x] /=; apply/eqP.
rewrite -!/(Tagged _ _) -(Tagged_SpTSet_castE (imset_id _)) eq_Tagged.
rewrite (functor_ext_hom A _ _ (@restr_id _ S)) hom_compE -functor_o.
set Fid := (F in A # F).
suff /(functor_ext_hom A) -> : Fid =1 idfun by rewrite functor_id.
rewrite /Fid /= /cast_TSet /= => {}x /=.
by rewrite -!/(cast_TSet _ _) cast_TSetKV.
Qed.
Fact SpSet_ext : FunctorLaws.ext SpSet_mor.
Proof.
rewrite /SpSet_mor => U V f g H -[/= S x] /=.
rewrite -!/(Tagged _ _) (functor_ext_hom A _ _ (restr_ext H)).
rewrite -(Tagged_SpTSet_castE (eq_imset _ H)) hom_compE -functor_o.
apply/eqP; rewrite -tag_eqE /tag_eq eqxx /=.
set F := (F in A # F).
suff /(functor_ext_hom A) -> : F =1 (restr_hom S g) by rewrite tagged_asE.
rewrite {}/F /= => {}x.
by apply: val_inj; rewrite !val_cast_TSet.
Qed.
Fact SpSet_comp : FunctorLaws.comp SpSet_mor.
Proof.
rewrite /SpSet_mor => U V W g f -[/= S x] /=; apply/eqP.
rewrite hom_compE -functor_o.
rewrite (functor_ext_hom A _ _ (restr_comp _ _ (I := S))) /=.
rewrite -!/(Tagged _ _) -(Tagged_SpTSet_castE (imset_comp g f _)).
rewrite -tag_eqE /tag_eq /= eqxx /= tagged_asE.
rewrite hom_compE -functor_o; apply/eqP.
exact: (functor_ext_hom A).
Qed.
Fact SpSet_bij U V (f : {hom U -> V}) : bijective (SpSet_mor f).
Proof. exact: (functor_bij SpSet_ext SpSet_id SpSet_comp). Qed.
HB.instance Definition _ U V (f : {hom U -> V}) :=
  BijHom.Build (SpSet U) (SpSet V)
    (SpSet_mor f : el (SpSet U) -> (SpSet V)) (SpSet_bij f).
HB.instance Definition _ :=
  isFunctor.Build Bij Bij SpSet SpSet_ext SpSet_id SpSet_comp.

Lemma tag_SpSet U V (f : {hom U -> V}) x : tag ((SpSet # f) x) = f @: (tag x).
Proof. by case: x => [/= S x]. Qed.

Variable c : nat.

Definition SpSetC U : Bij := { x : SpSet U | #|tag x| == c }.
Lemma SpSetCP U (x : SpSetC U) : #|tag (val x)| = c.
Proof. by case: x => x /= /eqP. Qed.

Definition SpSetC_mor_subproof U V (f : {hom U -> V}) (x : el (SpSetC U)) :
  #|tag ((SpSet # f) (\val x))| == c.
Proof.
case: x => [x /= /eqP tx].
by rewrite tag_SpSet card_imset ?tx.
Qed.
Definition SpSetC_mor U V (f : {hom U -> V}) (x : el (SpSetC U)) : SpSetC V :=
  exist _ ((SpSet # f) (\val x)) (SpSetC_mor_subproof f x).

Fact SpSetC_ext : FunctorLaws.ext SpSetC_mor.
Proof.
move=> U V f g H x; apply val_inj => /=.
exact: (functor_ext_hom SpSet _ _ H).
Qed.
Fact SpSetC_id : FunctorLaws.id SpSetC_mor.
Proof. by move=> U x; apply val_inj; rewrite /= functor_id. Qed.
Fact SpSetC_comp : FunctorLaws.comp SpSetC_mor.
Proof.
move=> U V W g f x; apply val_inj => /=.
exact: (functor_o (F := SpSet) g f).
Qed.
Fact SpSetC_bij U V (f : {hom U -> V}) : bijective (SpSetC_mor f).
Proof. exact: (functor_bij SpSetC_ext SpSetC_id SpSetC_comp). Qed.
HB.instance Definition _ U V (f : {hom U -> V}) :=
  BijHom.Build (SpSetC U) (SpSetC V)
    (SpSetC_mor f : el (SpSetC U) -> (SpSetC V)) (SpSetC_bij f).
HB.instance Definition _ :=
  isFunctor.Build Bij Bij SpSetC SpSetC_ext SpSetC_id SpSetC_comp.

Definition SpSetC2ord U : SpSetC U -> A 'I_c := locked
  (fun x => match x with
    (exist (existT E a) cardEc) =>
      (A # (cast_ord (eqP cardEc) \o
              cast_ord (card_TSet E) \o
              @enum_rank (TSet E))) a
  end).
Lemma isoclass_SpSetC2ord U (x y : SpSetC U) :
  (SpSetC2ord x \in isoclass (SpSetC2ord y)) = (x \in isoclass y).
Proof.
apply/idP/idP; first last.
  move/orbitP => [/= s _ {x}<-]; case: y => [[E y] /= p].
  by rewrite /SpSetC2ord -!lock /= hom_compE -functor_o isoclass_morph.
move/orbitP => [/= s _]; rewrite /actSp_fun.
rewrite /SpSetC2ord; unlock.
case Hx : x => [[/= E xE] pE] /=; case Hy : y => [[/= F yF] pF] /=.
rewrite hom_compE -functor_o.
move: (X in (A # X) xE) (X in (A # X) yF) => /= f g Heq.
have {} Heq : xE = (A # (finv f \o g)) yF by rewrite functor_o /= Heq SpfinvK.
subst xE; rewrite -Hx -Hy.
have := pE; rewrite -{1}(eqP pF) => /card_eq_imset_permP[t eqF].
suff: (actSp _ _ x t) \in isoclass y.
  apply orbit_trans; rewrite orbit_sym.
  by apply/orbitP; exists t => // /[!inE].
rewrite -(mem_imset _ _ val_inj) /= /SpSet_mor {x}Hx /= {pE}.
rewrite hom_compE -functor_o /=.
rewrite -/(Tagged _ _) -(Tagged_SpTSet_castE eqF) /Tagged hom_compE -functor_o /=.
move: (X in A # X) => {g eqF E s t}f.
rewrite /orbit -imset_comp.
rewrite (eq_imset (g := fun s => (actSp SpSet U (val y)) s)) //.
rewrite {}Hy /= {pF} -/(orbit _ _ _).
apply/orbitP; exists (perm_extd val_inj (perm_hom f)); first by rewrite inE.
rewrite /actSp /= /actSp_fun /= /SpSetC_mor /=.
rewrite eqSpSet; split => /= [|eqtag].
  apply/setP => u; apply/imsetP/idP => [[u' u'inF {u}->] | uinF].
    by rewrite permE /=; case: pickP => [/= u _ |]; first exact: TSetP.
  exists (val ((finv f) (exist _ u uinF))); first exact: TSetP.
  by rewrite /= perm_extdP permE /= finvKV.
rewrite eq_Tagged /= hom_compE -functor_o; apply/eqP.
apply: (functor_ext_hom A) => {}y /=.
by apply val_inj; rewrite val_cast_TSet val_restrE /= perm_extdP permE.
Qed.

End SpSet.


Section Localization.

Definition setTB (U : Bij) : Bij := TSet [set: U] : Bij.

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
HB.instance Definition _ :=
  isFunctor.Build Bij Bij setTB setTB_ext setTB_id setTB_comp.

Definition SpSetT : Species := setTB.

Definition toSetT : FId ~~> SpSetT := toSetT_fun.
Lemma toSetT_natural : naturality FId SpSetT toSetT.
Proof. by []. Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij FId SpSetT toSetT toSetT_natural.
Lemma toSetT_invE : isoSpinv toSetT =%= toSetT_inv.
Proof. by apply: eq_nattrans_sym; apply: isoSpinvrE => U; apply: toSetT_funK. Qed.

Lemma card_SpSetT n : cardSp SpSetT n = n.
Proof. by rewrite /cardSp (Bij_eq_card (@toSetT_inv _)) card_ord. Qed.

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
HB.instance Definition _ :=
  isFunctor.Build Bij Bij setSp_fun setSp_ext setSp_id setSp_comp.
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
  isFunctor.Build Bij Bij subsetSp_fun subsetSp_ext subsetSp_id subsetSp_comp.
Definition subsetSp : Species := subsetSp_fun.

Lemma card_subsetSp0n n : cardSp subsetSp n = (2 ^ n)%N.
Proof.
by rewrite /cardSp -cardsT /subsetSp_fun -powersetT card_powerset cardsT card_ord.
Qed.

Lemma isoclass_subsetSpE (U : Bij) (F : {set U}) :
  isoclass (F : subsetSp U) = [set X : {set U} | #|X| == #|F|].
Proof.
apply/setP => E /[!inE]; apply/orbitP/eqP => [[/= s _ {E}<-] |].
  exact/card_imset/perm_inj.
by move/esym/eqP/card_eq_imset_permP => [s {E}<-]; exists s.
Qed.

Lemma cardiso_subsetSp n : cardiso subsetSp n = n.+1.
Proof.
rewrite -cardiso_ordE.
have <- : #|[set [set X : {set 'I_n} | #|X| == k] | k : 'I_n.+1]| = n.+1.
  rewrite -[RHS]card_ord; apply card_imset => /= i j.
  move/setP => /(_ [set k : 'I_n | k < i]) /[!in_set].
  rewrite !cardltset -?(ltnS i n) // eqxx => /esym/eqP; apply: val_inj.
congr #|pred_of_set _|; apply/setP => /= E.
apply/imsetP/imsetP => /=[[F _ {E}->] | [u _ {E}->]].
  exists (inord #|F|); rewrite //= inordK ?isoclass_subsetSpE //.
  by rewrite ltnS -[X in _ <= X]card_ord -cardsT subset_leq_card.
exists [set k : 'I_n | k < u] => //.
by rewrite isoclass_subsetSpE cardltset // -ltnS.
Qed.

End SubsetSpecies.


Section ifSpecies.
Variable  (condn : pred nat) (A B : Species).
Implicit Type (U V W : Bij).

Let cond U := condn #|U|.
Lemma condP U V (f : {hom U -> V}) : cond V = cond U.
Proof. by rewrite /cond (Bij_eq_card f). Qed.

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
  isFunctor.Build Bij Bij ifSp ifSp_ext ifSp_id ifSp_comp.

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
