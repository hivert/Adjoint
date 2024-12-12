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


Definition voidB := (void : Bij).
Definition unitB := (unit : Bij).
Definition boolB := (bool : Bij).

Definition negbB : el boolB -> el boolB := negb.

HB.instance Definition _ :=
  BijHom.Build boolB boolB negbB (inv_bij negbK).


Definition Species := {functor Bij -> Bij}.


Section SpFInv.
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

End SpFInv.


Section Cardinality.

Definition TinSet (V : Bij) (S : {set V}) : Bij := {x : V | x \in S} : Bij.

Lemma card_TinSet (V : Bij) (S : {set V}) : #|TinSet S| = #|S|.
Proof.
rewrite -[LHS](card_imset _ val_inj); congr #|pred_of_set _|.
apply/setP => x; apply/imsetP/idP => [[/= [y y_in_S] _ ->] // | x_in_S].
by exists (exist _ x x_in_S).
Qed.

HB.instance Definition _ (U : Bij) :=
  BijHom.Build _ _ (@enum_rank U : el U -> el ('I_#|U| : Bij)) (@enum_rank_bij U).

Definition cardSp (A : Species) (n : nat) := #|A 'I_n|.
Lemma cardSpE (A : Species) (U : Bij) : #|A U| = cardSp A #|U|.
Proof. exact: BijHom_eq_card (A # (@enum_rank U)). Qed.

Definition SpSet (A : Species) (U : Bij) : predArgType :=
  { I : {set U} & A (TinSet I) }.
Lemma cardSp_set (A : Species) (V : Bij) (U : {set V}) :
  cardSp A #|U| = #|[set p : SpSet A V | tag p == U]|.
Proof.
rewrite -(card_TinSet U) -cardSpE.
pose totag (x : A (TinSet U)) : SpSet A V :=
  Tagged (fun U : {set V} => A (TinSet U)) x.
have totag_inj : injective totag.
  by rewrite /totag=> x y /eqP /[!eq_Tagged] /= /eqP.
rewrite -(card_imset _ totag_inj); congr #|pred_of_set _|.
apply/setP => /= x; apply/imsetP/idP => [[y _ {x}->] /[!inE] //| ].
move: x => [S x /[!inE] /= /eqP U_eq_S]; subst S.
by exists x.
Qed.

End Cardinality.


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
  rewrite -/(Tagged (fun n => A 'I_n) ((A # fx) x))
          -/(Tagged (fun n => A 'I_n) ((A # fy) y)).
  rewrite eq_Tagged /= => /eqP/(congr1 (A # (finv fy))).
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
Definition Sp0_mor (S V : Bij) (f : {hom S -> V}) : {hom voidB -> voidB} := idfun.
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

Definition setSp_fun (S : Bij) := unitB.
Lemma setSp_funE (S V : Bij) (f : {hom S -> V}) :
  setSp_fun S = setSp_fun V.
Proof. by []. Qed.
Lemma setSp_fun_uniq (S : Bij) (x y : setSp_fun S) : x = y.
Proof. by move: x y; rewrite /setSp_fun => - [] []. Qed.
Definition setSp_mor (S V : Bij) (f : {hom S -> V}) :
  {hom setSp_fun S -> setSp_fun V} :=
  eq_rect _ (fun x => {hom x -> setSp_fun V}) idfun _ (esym (setSp_funE f)).
Fact setSp_ext : FunctorLaws.ext setSp_mor.
Proof. by move=> /= S V f g _ x; apply: setSp_fun_uniq. Qed.
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

Definition subsetSp_fun (S : Bij) : Bij := {set S}.
Definition subsetSp_mor S V (f : {hom S -> V}) :
  el (subsetSp_fun S) -> el (subsetSp_fun V) := fun X => f @: X.

Lemma subsetSp_mor_bij S V (f : {hom S -> V}) : bijective (subsetSp_mor f).
Proof.
by exists (subsetSp_mor (finv f)) => X;
  rewrite /subsetSp_mor -imset_comp -[RHS]imset_id; apply: eq_imset;
  [exact: finvK | exact: finvKV].
Qed.
HB.instance Definition _ S V (f : {hom S -> V}) :=
  BijHom.Build (subsetSp_fun S) (subsetSp_fun V)
    (subsetSp_mor f) (subsetSp_mor_bij f).
Fact subsetSp_ext : FunctorLaws.ext subsetSp_mor.
Proof. by move=> S V f g eq X /=; rewrite /subsetSp_mor /=; apply: eq_imset. Qed.
Fact subsetSp_id : FunctorLaws.id subsetSp_mor.
Proof. by move=> S X; apply: imset_id. Qed.
Fact subsetSp_comp  : FunctorLaws.comp subsetSp_mor.
Proof. by move=> S V U f g X; rewrite /= /subsetSp_mor -imset_comp. Qed.
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

Definition sumSp_fun S : Bij := (A S + B S)%type.
Definition sumSp_mor S V (f : {hom S -> V}) :
  el (sumSp_fun S) -> el (sumSp_fun V) :=
  fun x => match x with
           | inl a => inl ((A # f) a)
           | inr b => inr ((B # f) b)
           end.
Lemma sumSp_mor_bij S V (f : {hom S -> V}) : bijective (sumSp_mor f).
Proof.
by exists (sumSp_mor (finv f)); case => [a|b] /=; rewrite ?SpfinvK ?SpfinvKV.
Qed.
HB.instance Definition _ S V (f : {hom S -> V}) :=
  BijHom.Build (sumSp_fun S) (sumSp_fun V) (sumSp_mor f) (sumSp_mor_bij f).
Fact sumSp_ext : FunctorLaws.ext sumSp_mor.
Proof. by move=> S V f g eq [a|b] /=; congr (_ _); apply: functor_ext_hom. Qed.
Fact sumSp_id : FunctorLaws.id sumSp_mor.
Proof. by move=> S [a|b] /=; rewrite functor_id. Qed.
Fact sumSp_comp  : FunctorLaws.comp sumSp_mor.
Proof. by move=> S V U f g [a|b]; rewrite /= functor_o. Qed.
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
Proof. by move=> S V h []. Qed.
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
Fact sumSp0_funK : cancel sumSp0_fun sumSp0_inv.
Proof. by case => [|[]]. Qed.
Fact sumSp0_invK : cancel sumSp0_inv sumSp0_fun.
Proof. by []. Qed.
Fact sumSp0_fun_bij : bijective sumSp0_fun.
Proof. by exists sumSp0_inv; [exact: sumSp0_funK | exact: sumSp0_invK]. Qed.
Fact sumSp0_inv_bij : bijective sumSp0_inv.
Proof. by exists sumSp0_fun; [exact: sumSp0_invK | exact: sumSp0_funK]. Qed.
HB.instance Definition _ :=
  @BijHom.Build ((A + 0) S) (A S) sumSp0_fun sumSp0_fun_bij.
HB.instance Definition _ :=
  @BijHom.Build (A S) ((A + 0) S) sumSp0_inv sumSp0_inv_bij.

End Mor.
Definition sumSp0  : A + 0 ~~> A := @sumSp0_fun.

Fact sumSp0_natural : naturality (A + 0) A sumSp0.
Proof. by move=> S V h []. Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (A + 0) A sumSp0 sumSp0_natural.

Lemma sumSp0_invE : isoSpinv sumSp0 =%= sumSp0_inv.
Proof. by apply: eq_nattrans_sym; apply: isoSpinvrE => U; apply: sumSp0_funK. Qed.

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
Fact sumSpA_funK : cancel sumSpA_fun sumSpA_inv.
Proof. by case => [|[]]. Qed.
Fact sumSpA_invK : cancel sumSpA_inv sumSpA_fun.
Proof. by case => [[]|]. Qed.
Fact sumSpA_fun_bij : bijective sumSpA_fun.
Proof. by exists sumSpA_inv; [exact sumSpA_funK | exact: sumSpA_invK]. Qed.
Fact sumSpA_inv_bij : bijective sumSpA_inv.
Proof. by exists sumSpA_fun; [exact sumSpA_invK | exact: sumSpA_funK]. Qed.
HB.instance Definition _ :=
  @BijHom.Build ((A + (B + C)) S) ((A + B + C) S) sumSpA_fun sumSpA_fun_bij.
HB.instance Definition _ :=
  @BijHom.Build ((A + B + C) S) ((A + (B + C)) S) sumSpA_inv sumSpA_inv_bij.

End Mor.
Definition sumSpA  : (A + (B + C)) ~~> (A + B + C) := sumSpA_fun.
Definition sumSpAV : (A + B + C) ~~> (A + (B + C)) := sumSpA_inv.

Fact sumSpA_natural : naturality (A + (B + C)) (A + B + C) sumSpA.
Proof. by move=> S V h [|[]]. Qed.
Fact sumSpAV_natural : naturality (A + B + C) (A + (B + C)) sumSpAV.
Proof. by move=> S V h [[]|]. Qed.
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
Proof. by move=> S V h [a|b] /=; rewrite !hom_compE natural. Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (A1 + B1) (A2 + B2) sumSpTr sumSpTr_natural.

End SumNatTransf.

Lemma sumSpTr_invE (A1 A2 B1 B2 : Species) (tA : A1 ~> A2) (tB : B1 ~> B2) :
  isoSpinv (sumSpTr tA tB) =%= sumSpTr (isoSpinv tA) (isoSpinv tB).
Proof. by apply: eq_nattrans_sym; apply: isoSpinvrE => U [] x /= /[!finvK]. Qed.


Section Restriction.

Variable (S V : Bij) (I : {set S}) (f : {hom S -> V}).

Fact restr_subproof (x : {x : S | x \in I}) : f (\val x) \in [set f x | x in I].
Proof. by case: x => x Px /=; apply: imset_f. Qed.
Definition restr (x : el ({x : S | x \in I} : Bij)) :
      el ({x : V | x \in [set f y | y in I]} : Bij) :=
  exist _ (f (\val x)) (restr_subproof x).

Fact restr_inv_spec (y : {x : V | x \in [set f y | y in I]}) :
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
  {hom[Bij] {x : S | x \in I} -> {x : V | x \in [set f y | y in I]}} := restr.

Lemma val_restrE x : \val (restr x) = f (\val x).
Proof. by []. Qed.

End Restriction.


Section EqCast.

Variable (V : Bij) (I J : {set V}) (eq : I = J).

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
  Tagged (@TinSet V) x = Tagged (@TinSet V) (ecast X (TinSet X) eq x).
Proof. by move: x; subst I. Qed.

End EqCast.

Lemma Tagged_SpTinSet_castE (V : Bij) (I J : {set V}) (eq : I = J) (A : Species) x :
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
Lemma restr_comp (S V U : Bij) (f : {hom S -> V}) (g : {hom V -> U}) (I : {set S}) :
  restr_hom _ g \o restr_hom I f
  =1 cast_hom (imset_comp g f I) \o restr_hom _ (g \o f).
Proof. by move => x /=; apply val_inj; rewrite cast_TinSetE !val_restrE. Qed.
Lemma restr_ext (S V : Bij) (f g : {hom S -> V}) (I : {set S}) (eq_fg : f =1 g) :
  restr_hom I f =1 cast_hom (eq_imset _ (fsym eq_fg)) \o (restr_hom I g).
Proof. by move => x /=; apply val_inj; rewrite !cast_TinSetE !val_restrE. Qed.


Section ProductSpecies.

Definition appSpSet (A : Species) {V : Bij} := fun (S : {set V}) => A (TinSet S).

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


Lemma prodSp_mor_subproof S V (f : {hom S -> V}) (x : prodSpT S) :
  f @: seta x ==  ~: f @: setb x.
Proof. by rewrite (eqP (prodsp_dijs x)) (imsetCE _ (BijP f)). Qed.

Definition prodSp_fun S V (f : {hom S -> V}) (x : el (prodSpT S : Bij))
  : el (prodSpT V : Bij)
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
Lemma prodSp_fun_comp S V U (f : {hom S -> V}) (g : {hom V -> U}) :
  prodSp_fun g \o prodSp_fun f =1 prodSp_fun (g \o f).
Proof.
rewrite /prodSp_fun => [][a va b vb eq] /=; apply/eqP/eq_prodSpP; split.
- rewrite hom_compE -functor_o /=.
  have /= -> := functor_ext_hom A _ _ (restr_comp f g (I := a)).
  by rewrite functor_o /= Tagged_SpTinSet_castE.
- rewrite !hom_compE -!functor_o /=.
  have /= -> := functor_ext_hom B _ _ (restr_comp f g (I := b)).
  by rewrite functor_o /= Tagged_SpTinSet_castE.
Qed.
Lemma prodSp_fun_ext S V (f g : {hom S -> V}) :
  f =1 g -> prodSp_fun f =1 prodSp_fun g.
Proof.
rewrite /prodSp_fun => eqfg [a va b vb eq] /=; apply/eqP/eq_prodSpP; split.
- have /= -> := functor_ext_hom A _ _ (restr_ext eqfg).
  by rewrite functor_o /= Tagged_SpTinSet_castE.
- have /= -> := functor_ext_hom B _ _ (restr_ext eqfg).
  by rewrite functor_o /= Tagged_SpTinSet_castE.
Qed.

Lemma prodSp_fun_bij S V (f : {hom S -> V}) : bijective (prodSp_fun f).
Proof.
exists (prodSp_fun (finv f)) => x; rewrite -[LHS]compapp prodSp_fun_comp.
- have /prodSp_fun_ext -> : finv f \o f =1 idfun by move=> y /=; rewrite finvK.
  by rewrite prodSp_fun_id.
- have /prodSp_fun_ext -> : f \o finv f =1 idfun by move=> y /=; rewrite finvKV.
  by rewrite prodSp_fun_id.
Qed.
HB.instance Definition _ S V (f : {hom S -> V}) :=
  BijHom.Build (prodSpT S) (prodSpT V) (prodSp_fun f) (prodSp_fun_bij f).
Definition prodSp_mor S V (f : {hom S -> V}) : {hom _ -> _} := prodSp_fun f.
Fact prodSp_ext : FunctorLaws.ext prodSp_mor.
Proof. exact: prodSp_fun_ext. Qed.
Fact prodSp_id : FunctorLaws.id prodSp_mor.
Proof. exact: prodSp_fun_id. Qed.
Fact prodSp_comp  : FunctorLaws.comp prodSp_mor.
Proof. by move=> S V U f g x; have /= <- := (prodSp_fun_comp g f x). Qed.

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
move=> S V h [a va b vb eq]; rewrite /= /prodSp_fun /prodSpC_fun /=.
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
Lemma prodSpC_invE A B : isoSpinv (prodSpC A B) =%= prodSpC B A.
Proof. by apply: eq_nattrans_sym; apply: isoSpinvrE; apply: prodSpCK. Qed.

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

Fact prodSp0_natural : naturality (A * 0) 0 prodSp0.
Proof. by move=> S V h []. Qed.
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

Lemma appSpSet1_card V (S : {set V}) : appSpSet 1 S -> #|S| = 0%N.
Proof. by rewrite /appSpSet /deltaSp /= /ifSp card_TinSet; case eqP. Qed.

Variable (A : Species).

Section Mor.
Variable (S : Bij).

Definition prodSp1_inv_def : el (A S) -> el ((A * 1) S).
move=> x.
pose a : A {x : S | x \in setT} := (A # toSetT S) x.
have b : 1 {x : S | x \in set0}.
  rewrite /deltaSp /= /ifSp card_TinSet cards0 eqxx.
  exact tt.
by apply: (MkProdSp a b _); rewrite setC0.
Defined.
Definition prodSp1_inv := locked prodSp1_inv_def.
Lemma prodSp1_inv_inj : injective prodSp1_inv.
Proof.
rewrite /prodSp1_inv; unlock.
move=> i j /eqP/eq_prodSpP [/[swap] _] /eqP.
rewrite !eq_Tagged => /eqP /(congr1 (A # finv (toSetT S))) /=.
by rewrite !SpfinvK.
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
Definition prodSp1_hom : {hom (A * 1) S -> A S} := finv prodSp1_inv.
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
Proof. by move=> x; apply val_inj; rewrite cast_TinSetE. Qed.

Fact prodSp1V_natural : naturality A (A * 1) prodSp1V.
Proof.
move=> S V h x /=.
apply/eqP/eq_prodSpP; split => /=.
  rewrite /prodSp1_inv; unlock; rewrite /= !hom_compE -!functor_o /=.
  have /= -> := functor_ext_hom A _ _ (restr_hom_setTE h).
  by rewrite functor_o /= Tagged_SpTinSet_castE.
have eq0 : h @: (setb (prodSp1_inv x)) = setb (prodSp1_inv ((A # h) x)).
  by rewrite /prodSp1_inv; unlock; rewrite /= imset0.
have /= <- := Tagged_SpTinSet_castE eq0 (A := 1).
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
Variable (S : Bij).

Definition prodSpDl_fun : el ((A * (B + C)) S) -> el ((A * B + A * C) S) :=
  fun x => match valb x with
           | inl b => inl (MkProdSp (vala x) b (prodsp_dijs x))
           | inr c => inr (MkProdSp (vala x) c (prodsp_dijs x))
           end.
Definition prodSpDl_inv : el ((A * B + A * C) S) -> el ((A * (B + C)) S).
refine
  (fun x => match x with
           | inl b => MkProdSp (vala b) _ (prodsp_dijs b)
           | inr c => MkProdSp (vala c) _ (prodsp_dijs c)
           end).
exact (inl (valb b)).
exact (inr (valb c)).
Defined.

Definition prodSpDl_funK : cancel prodSpDl_fun prodSpDl_inv.
Proof. by case => [a Aa b []]. Qed.
Definition prodSpDl_invK : cancel prodSpDl_inv prodSpDl_fun.
Proof. by case => [][]/=. Qed.
Fact prodSpDl_fun_bij : bijective prodSpDl_fun.
Proof. by exists prodSpDl_inv; [exact: prodSpDl_funK | exact: prodSpDl_invK]. Qed.
Fact prodSpDl_inv_bij : bijective prodSpDl_inv.
Proof. by exists prodSpDl_fun; [exact: prodSpDl_invK | exact: prodSpDl_funK]. Qed.
HB.instance Definition _ :=
  @BijHom.Build ((A * (B + C)) S) ((A * B + A * C) S) prodSpDl_fun prodSpDl_fun_bij.
HB.instance Definition _ :=
  @BijHom.Build ((A * B + A * C) S) ((A * (B + C)) S) prodSpDl_inv prodSpDl_inv_bij.

End Mor.
Definition prodSpDl  : (A * (B + C)) ~~> (A * B + A * C) := prodSpDl_fun.
Definition prodSpDlV : (A * B + A * C) ~~> (A * (B + C)) := prodSpDl_inv.

Fact prodSpDl_natural : naturality (A * (B + C)) (A * B + A * C) prodSpDl.
Proof.
move=> S V h [a Aa b [] Xb eqXb]; rewrite /= /prodSp_fun /=;
  congr (_ _); by apply/eqP/eq_prodSpP.
Qed.
Fact prodSpDlV_natural : naturality (A * B + A * C) (A * (B + C)) prodSpDlV.
Proof.
by move=> S V h [][a Aa b Xb eqXb]; rewrite /prodSp_fun /=; apply/eqP/eq_prodSpP.
Qed.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (A * (B + C)) (A * B + A * C) prodSpDl prodSpDl_natural.
HB.instance Definition _ :=
  @isNatural.Build Bij Bij (A * B + A * C) (A * (B + C)) prodSpDlV prodSpDlV_natural.

Lemma prodSpDl_invE : isoSpinv prodSpDl =%= prodSpDlV.
Proof. by apply: eq_nattrans_sym; apply: isoSpinvrE => U; apply: prodSpDl_funK. Qed.

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

(** TODO associativity of product *)
