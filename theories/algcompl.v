From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finfun bigop.
From mathcomp Require Import ssralg ssrint finmap multiset.

Require Import category examples.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "'{' 'mmorphism' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'mmorphism'  U  ->  V }").

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope category_scope.

Declare Scope monoid_scope.
Delimit Scope monoid_scope with M.
Local Open Scope monoid_scope.


HB.mixin Record isMonoid V := {
  one : V;
  mul : V -> V -> V;
  mulmA : associative mul;
  mul1m : left_id one mul;
  mulm1 : right_id one mul;
}.

#[short(type="monoidType")]
HB.structure Definition Monoid := {V of isMonoid V & Choice V}.

Bind Scope monoid_scope with Monoid.sort.

Local Notation "1" := (@one _) : monoid_scope.
Local Notation "1%M" := (@one _) : monoid_scope.
Local Notation "*%M" := (@mul _) : function_scope.

#[export]
HB.instance Definition _ (V : monoidType) :=
  Monoid.isLaw.Build V 1 *%M mulmA mul1m mulm1.

Definition exp M x n := iterop n (@mul M) x (@one M).
Arguments exp : simpl never.
Definition comm M x y := @mul M x y = mul y x.

Notation "x * y" := (mul x y) : monoid_scope.
Notation "x ^+ n" := (exp x n) : monoid_scope.

Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%M/1%M]_(i <- r | P%B) F%M) : monoid_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%M/1%M]_(i <- r) F%M) : monoid_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%M/1%M]_(m <= i < n | P%B) F%M) : monoid_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%M/1%M]_(m <= i < n) F%M) : monoid_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%M/1%M]_(i | P%B) F%M) : monoid_scope.
Notation "\prod_ i F" :=
  (\big[*%M/1%M]_i F%M) : monoid_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%M/1%M]_(i : t | P%B) F%M) (only parsing) : monoid_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%M/1%M]_(i : t) F%M) (only parsing) : monoid_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%M/1%M]_(i < n | P%B) F%M) : monoid_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%M/1%M]_(i < n) F%M) : monoid_scope.
Notation "\prod_ ( i 'in' A | P ) F" :=
  (\big[*%M/1%M]_(i in A | P%B) F%M) : monoid_scope.
Notation "\prod_ ( i 'in' A ) F" :=
  (\big[*%M/1%M]_(i in A) F%M) : monoid_scope.

Section MonoidTheory.

Variable M : monoidType.
Implicit Types x y : M.

Lemma expm0 x : x ^+ 0 = 1. Proof. by []. Qed.
Lemma expm1 x : x ^+ 1 = x. Proof. by []. Qed.
Lemma expm2 x : x ^+ 2 = x * x. Proof. by []. Qed.

Lemma expmS x n : x ^+ n.+1 = x * x ^+ n.
Proof. by case: n => //; rewrite mulm1. Qed.

Lemma expm1n n : 1 ^+ n = 1 :> M.
Proof. by elim: n => // n IHn; rewrite expmS mul1m. Qed.

Lemma expmD x m n : x ^+ (m + n) = x ^+ m * x ^+ n.
Proof. by elim: m => [|m IHm]; rewrite ?mul1m // !expmS -mulmA -IHm. Qed.

Lemma expmSm x n : x ^+ n.+1 = x ^+ n * x.
Proof. by rewrite -addn1 expmD expm1. Qed.

Lemma expm_sum x (I : Type) (s : seq I) (P : pred I) F :
  x ^+ (\sum_(i <- s | P i) F i) = \prod_(i <- s | P i) x ^+ F i :> M.
Proof. exact: (big_morph _ (expmD _)). Qed.

Lemma commm_sym x y : comm x y -> comm y x. Proof. by []. Qed.
Lemma commm_refl x : comm x x. Proof. by []. Qed.

Lemma commm1 x : comm x 1.
Proof. by rewrite /comm mulm1 mul1m. Qed.

Lemma commmM x y z : comm x y -> comm x z -> comm x (y * z).
Proof. by move=> com_xy; rewrite /comm mulmA com_xy -!mulmA => ->. Qed.

Lemma commm_prod (I : Type) (s : seq I) (P : pred I) (F : I -> M) x :
  (forall i, P i -> comm x (F i)) -> comm x (\prod_(i <- s | P i) F i).
Proof. exact: (big_ind _ (commm1 x) (@commmM x)). Qed.

Lemma commmX x y n : comm x y -> comm x (y ^+ n).
Proof.
rewrite /comm => com_xy.
by elim: n => [|n IHn]; rewrite ?commm1 // expmS commmM.
Qed.

Lemma expmMn_comm x y n : comm x y -> (x * y) ^+ n = x ^+ n * y ^+ n.
Proof.
move=> com_xy; elim: n => /= [|n IHn]; first by rewrite mulm1.
by rewrite !expmS IHn !mulmA; congr (_ * _); rewrite -!mulmA -commmX.
Qed.

Lemma expmM x m n : x ^+ (m * n) = x ^+ m ^+ n.
Proof.
elim: m => [|m IHm]; first by rewrite expm1n.
by rewrite mulSn expmD IHm expmS expmMn_comm //; apply: commmX.
Qed.

Lemma expmAC x m n : (x ^+ m) ^+ n = (x ^+ n) ^+ m.
Proof. by rewrite -!expmM mulnC. Qed.

Lemma iter_mulm n x y : iter n ( *%M x) y = x ^+ n * y.
Proof. by elim: n => [|n ih]; rewrite ?expm0 ?mul1m //= ih expmS -mulmA. Qed.

Lemma iter_mulm_1 n x : iter n ( *%M x) 1 = x ^+ n.
Proof. by rewrite iter_mulm mulm1. Qed.

End MonoidTheory.



HB.mixin Record Monoid_hasCommutativeMul M of Monoid M := {
  mulmC : commutative (@mul M)
}.
#[short(type="comMonoidType")]
HB.structure Definition ComMonoid :=
  {M of Monoid M & Monoid_hasCommutativeMul M}.

Bind Scope monoid_scope with ComMonoid.sort.

HB.factory Record isComMonoid V & Choice V := {
  one : V;
  mul : V -> V -> V;
  mulmA : associative mul;
  mul1m : left_id one mul;
  mulmC : commutative mul
}.
HB.builders Context V of isComMonoid V.
Let mulm1_fromC : right_id one mul.
Proof. by move=> x; rewrite mulmC mul1m. Qed.
HB.instance Definition _ := isMonoid.Build V mulmA mul1m mulm1_fromC.
HB.instance Definition _ := Monoid_hasCommutativeMul.Build V mulmC.
HB.end.


Definition monmorphism (R S : monoidType) (f : R -> S) : Prop :=
  {morph f : x y / x * y} * (f 1 = 1).

HB.mixin Record isMonMorphism (R S : monoidType) (f : R -> S) := {
  monmorphism_subproof : monmorphism f
}.

HB.structure Definition MonMorphism (R S : monoidType) :=
  {f of isMonMorphism R S f}.

Module MonMorphismExports.
Notation "{ 'mmorphism' U -> V }" := (MonMorphism.type U%type V%type)
  : type_scope.
End MonMorphismExports.
HB.export MonMorphismExports.


Section MonMorphismTheory.

Section Properties.

Variables (R S : monoidType) (f : {mmorphism R -> S}).

Lemma mmorphismMP : monmorphism f. Proof. exact: monmorphism_subproof. Qed.
Lemma mmorph1 : f 1 = 1. Proof. by case: mmorphismMP. Qed.
Lemma mmorphM : {morph f: x y  / x * y}. Proof. by case: mmorphismMP. Qed.

Lemma mmorph_prod I r (P : pred I) E :
  f (\prod_(i <- r | P i) E i) = \prod_(i <- r | P i) f (E i).
Proof. exact: (big_morph f mmorphM mmorph1). Qed.

Lemma mmorphXn n : {morph f : x / x ^+ n}.
Proof. by elim: n => [|n IHn] x; rewrite ?mmorph1 // !expmS mmorphM IHn. Qed.

Lemma can2_mmorphism f' : cancel f f' -> cancel f' f -> monmorphism f'.
Proof.
move=> fK f'K.
by split=> [x y|]; apply: (canLR fK); rewrite /= (mmorphM, mmorph1) ?f'K.
Qed.

End Properties.

Section Projections.

Variables (R S T : monoidType).
Variables (f : {mmorphism S -> T}) (g : {mmorphism R -> S}).

Fact idfun_is_monmorphism : monmorphism (@idfun R).
Proof. by []. Qed.
#[export]
HB.instance Definition _ := isMonMorphism.Build R R idfun
  idfun_is_monmorphism.

Fact comp_is_monmorphism : monmorphism (f \o g).
Proof. by split=> [x y|] /=; rewrite ?mmorph1 ?mmorphM. Qed.
#[export]
HB.instance Definition _ := isMonMorphism.Build R T (f \o g)
  comp_is_monmorphism.

End Projections.

End MonMorphismTheory.


Record multMon (R : semiRingType) := Mk { mval :> R; _ : true; }.
HB.instance Definition _ R := [isSub of multMon R for @mval R].
HB.instance Definition _ R := [Equality of multMon R by <:].
HB.instance Definition _ R := [Choice of multMon R by <:].

Coercion to_multMon (R : semiRingType) (x : R) := Mk x is_true_true.

Module Monoid_of_SemiRing.

Section CanonicalSR.

Variable R : semiRingType.
Implicit Type (x y : multMon R).

Let one : multMon R := 1%R.
Let mul x y : multMon R := (x * y)%R.
Fact mulmA : associative mul.
Proof. move=> x y z; apply val_inj; exact: mulrA. Qed.
Fact mul1m : left_id one mul.
Proof. move=> x; apply val_inj; exact: mul1r. Qed.
Fact mulm1 : right_id one mul.
Proof. move=> x; apply val_inj; exact: mulr1. Qed.
#[export]
HB.instance Definition _ := isMonoid.Build (multMon R) mulmA mul1m mulm1.

End CanonicalSR.

Section CanonicalCSR.

Variable R : comSemiRingType.
Implicit Type (x y : multMon R).

Fact mulmC : commutative (@mul (multMon R)).
Proof. move=> x y; apply val_inj; exact: mulrC. Qed.
#[export]
HB.instance Definition _ :=
  Monoid_hasCommutativeMul.Build (multMon R) mulmC.

End CanonicalCSR.

Module Exports.
HB.reexport Monoid_of_SemiRing.
Notation multMon R := (multMon R).

Section Theory.

Variable R : semiRingType.
Implicit Type (x y : multMon R).

Lemma monE : (1%M : multMon R) = 1%R. Proof. by []. Qed.
Lemma monME x y : (x * y)%M = (x * y)%R. Proof. by []. Qed.
Lemma tomonE (x : R) : (to_multMon x) = x. Proof. by []. Qed.

End Theory.
End Exports.
End Monoid_of_SemiRing.
HB.export Monoid_of_SemiRing.Exports.


Section Functoriality.

Variable (R S : semiRingType) (f : {rmorphism R -> S}).

Definition multmor (r : multMon R) : multMon S := to_multMon (f (val r)).
Fact multmor_monmorphism : monmorphism multmor.
Proof.
split; last by rewrite /multmor !monE /= rmorph1.
by move=> x y; rewrite /multmor !monME rmorphM.
Qed.
HB.instance Definition _ :=
  isMonMorphism.Build (multMon R) (multMon S) multmor multmor_monmorphism.

End Functoriality.


(* Monoid ************************************************************)

Fact comp_is_monmorphism_fun (a b c : monoidType) (f : a -> b) (g : b -> c) :
  monmorphism f -> monmorphism g -> monmorphism (g \o f).
Proof. by move=> fM gM; split => [x y|]; rewrite /= fM gM. Qed.
HB.instance Definition _ :=
  isCategory.Build monoidType (fun T : monoidType => T)
    monmorphism idfun_is_monmorphism comp_is_monmorphism_fun.
Notation Monoids := [the category of monoidType].
#[warning="-uniform-inheritance"]
Coercion mmorphism_of_Monoids a b (f : {hom[Monoids] a -> b}) : {mmorphism a -> b} :=
  HB.pack (Hom.sort f) (isMonMorphism.Build _ _ _ (isHom_inhom f)).
Lemma mmorphism_of_MonoidsE a b (f : {hom[Monoids] a -> b}) :
  @mmorphism_of_Monoids a b f = f :> (_ -> _).
Proof. by []. Qed.

Module ForgetMonoids_to_Sets.

Section Morphism.
Variable (a b : Monoids) (f : {hom[Monoids] a -> b}).
Definition forget (T : Monoids) : Sets := T.
HB.instance Definition _ :=
  @isHom.Build Sets a b (f : (a : Sets) -> b) I.
Definition forget_mor : {hom[Sets] a -> b} := f : a -> b.
End Morphism.
HB.instance Definition _ :=
  @isFunctor.Build Monoids Sets forget forget_mor
    (fun _ _ _ _ => id) (fun _ => frefl _) (fun _ _ _ _ _ => frefl _).
Definition functor : {functor Monoids -> Sets} := forget.

End ForgetMonoids_to_Sets.

Definition forget_Monoids_to_Sets := ForgetMonoids_to_Sets.functor.
Lemma forget_Monoids_to_SetsE a b (f : {hom[Monoids] a -> b}) :
  forget_Monoids_to_Sets # f = f :> (_ -> _).
Proof. by []. Qed.


Definition freeMonoid (a : Sets) := seq a.
HB.instance Definition _ (a : Sets) := Choice.on (freeMonoid a).
HB.instance Definition _ (a : Sets) :=
  isMonoid.Build (freeMonoid a) (@catA a) (@cat0s a) (@cats0 a).

Notation "{ 'freemon' T }" := (freeMonoid T)
                                (at level 0, format "{ 'freemon'  T }").
Notation "[fm x ]" := ([:: x] : {freemon _})
                        (at level 0, format "[fm  x ]").

Lemma freeMonoidE (a : Sets) (x : freeMonoid a) : x = \prod_(i <- x) [fm i].
Proof.
by elim: x => [| s s0 {1}->]; rewrite ?big_nil // big_cons [RHS]cat1s.
Qed.


Section FreeMonoid.

Variables (a b c : Sets) (f : {hom[Sets] a -> b}).

Definition hom_freeMonoid (m : {freemon a}) : {freemon b} :=
  [seq f i | i <- m].

Lemma hom_freeMonoid1 x : hom_freeMonoid [fm x] = [fm f x].
Proof. by []. Qed.
Lemma hom_freeMonoidE (s : {freemon a}) :
  hom_freeMonoid s = \prod_(i <- s) [fm f i].
Proof. by elim: s => [//=| s0 s /= ->]; rewrite ?big_nil ?big_cons. Qed.
Lemma hom_freeMonoid_monmorphism : monmorphism hom_freeMonoid.
Proof. by rewrite /hom_freeMonoid; split => [/= x y| //]; rewrite map_cat. Qed.

End FreeMonoid.

HB.instance Definition _ (a b : Sets) (f : {hom[Sets] a -> b}) :=
  @isHom.Build Monoids {freemon a} {freemon b}
    (hom_freeMonoid f : [the Monoids of {freemon a}] -> {freemon b})
    (hom_freeMonoid_monmorphism f).
Definition freeMonoid_mor (a b : Sets) (f : {hom[Sets] a -> b})
  : {hom[Monoids] {freemon a} -> {freemon b}} := hom_freeMonoid f.

Fact freeMonoid_ext : FunctorLaws.ext freeMonoid_mor.
Proof. by move=> /= a b f g eq y; rewrite /hom_freeMonoid; exact: eq_map. Qed.
Fact freeMonoid_id : FunctorLaws.id freeMonoid_mor.
Proof. by move=> /= a x /=; rewrite /hom_freeMonoid /= map_id. Qed.
Fact freeMonoid_comp  : FunctorLaws.comp freeMonoid_mor.
Proof. by move=> /= a b c f g x; rewrite /hom_freeMonoid /= map_comp. Qed.

Definition functor_freeMon T : Monoids := {freemon T}.
HB.instance Definition _ :=
  @isFunctor.Build Sets Monoids
    functor_freeMon freeMonoid_mor freeMonoid_ext freeMonoid_id freeMonoid_comp.

Section Adjoint.

Implicit Types (a : Sets) (T : Monoids).

Let eta_fun a (x : a) := [fm x].
Definition eta : FId ~~> forget_Monoids_to_Sets \o functor_freeMon := eta_fun.
Fact eta_natural : naturality FId (forget_Monoids_to_Sets \o functor_freeMon) eta.
Proof. by move=> /= a b h x /=; rewrite /eta_fun FIdf. Qed.
HB.instance Definition _ :=
  @isNatural.Build Sets Sets FId
    (forget_Monoids_to_Sets \o functor_freeMon) eta eta_natural.

Let eps_fun T (m : (functor_freeMon \o forget_Monoids_to_Sets) T) : T :=
      \prod_(i <- m : {freemon _}) i.
Fact eps_fun_monmorphism T : monmorphism (@eps_fun T).
Proof. by rewrite /eps_fun; split => [s t |]; rewrite ?big_nil ?big_cat. Qed.
HB.instance Definition _ T :=
  isHom.Build Monoids ((functor_freeMon \o forget_Monoids_to_Sets) T) (FId T)
    (@eps_fun T) (@eps_fun_monmorphism T).
Definition eps : functor_freeMon \o forget_Monoids_to_Sets ~~> FId := eps_fun.
Fact eps_natural : naturality (functor_freeMon \o forget_Monoids_to_Sets) FId eps.
Proof.
move=> /= a b h x /=.
rewrite -!mmorphism_of_MonoidsE [LHS]mmorph_prod /=.
by rewrite FIdf /eps_fun /= /hom_freeMonoid big_map.
Qed.
HB.instance Definition _ :=
  @isNatural.Build Monoids Monoids
    (functor_freeMon \o forget_Monoids_to_Sets) FId eps eps_natural.

Fact triL : TriangularLaws.left eta eps.
Proof.
move=> /= a x.
rewrite -!mmorphism_of_MonoidsE /=.
rewrite /eta_fun /= /eps_fun /hom_freeMonoid.
by rewrite big_map [RHS]freeMonoidE.
Qed.
Fact triR : TriangularLaws.right eta eps.
Proof. by move=> /= M m; rewrite /eta_fun /= /eps_fun big_cons big_nil mulm1. Qed.

Let F : {functor Sets -> Monoids} := functor_freeMon.
Let G : {functor Monoids -> Sets} := forget_Monoids_to_Sets.

Definition adj_functor_freeMon_forget : F -| G :=
  AdjointFunctors.mk triL triR.

End Adjoint.


Section UniversalProperty.

Variables (A : choiceType) (M : monoidType) (f : A -> M).

Definition univmap_fm : {mmorphism {freemon A} -> M} :=
  eps M \o functor_freeMon # f : {hom _ -> M}.

Lemma univmap_fmP a : univmap_fm [fm a] = f a.
Proof.
rewrite /univmap_fm -[[fm a]]/(eta A a) /=.
exact: triR.
Qed.

Lemma univmap_fm_uniq (g : {mmorphism {freemon A} -> M}) :
  (forall a : A, g [fm a] = f a) -> g =1 univmap_fm.
Proof.
move=> eq m.
rewrite (freeMonoidE m) !mmorph_prod; apply eq_bigr => i _.
by rewrite eq univmap_fmP.
Qed.

End UniversalProperty.


(* Full subcategory of Monoid *)
HB.instance Definition _ :=
  isCategory.Build comMonoidType (fun T : comMonoidType => T)
    (@inhom Monoids) (@idfun_inhom Monoids) (@funcomp_inhom Monoids).
Notation ComMonoids := [the category of comMonoidType].
#[warning="-uniform-inheritance"]
Coercion mmorphism_of_ComMonoids a b (f : {hom[ComMonoids] a -> b}) :
  {mmorphism a -> b} :=
  HB.pack (Hom.sort f) (isMonMorphism.Build _ _ _ (isHom_inhom f)).
Lemma mmorphism_of_ComMonoidsE a b (f : {hom[ComMonoids] a -> b}) :
  @mmorphism_of_ComMonoids a b f = f :> (_ -> _).
Proof. by []. Qed.


(** Equivalence ComMonoid NModule ***********************************)
Definition NMod_of_ComMonoid_type (M : ComMonoids) : Type := M.
HB.lock Definition nmod_of_commonoid (M : ComMonoids) (x : M)
  : (NMod_of_ComMonoid_type M) := x.
Canonical nmod_of_commonoid_unlock := Unlockable nmod_of_commonoid.unlock.
HB.lock Definition nmod_of_commonoid_inv M (x : NMod_of_ComMonoid_type M) : M := x.
Canonical nmod_of_commonoid_inv_unlock := Unlockable nmod_of_commonoid_inv.unlock.

Lemma nmod_of_commonoidK M :
  cancel (@nmod_of_commonoid M) (@nmod_of_commonoid_inv M).
Proof. by rewrite !unlock. Qed.
Lemma nmod_of_commonoid_invK M :
  cancel (@nmod_of_commonoid_inv M) (@nmod_of_commonoid M).
Proof. by rewrite !unlock. Qed.

Section Defs.

Variable M : ComMonoids.
Local Notation nmodM := (NMod_of_ComMonoid_type M).
HB.instance Definition _ := Choice.on nmodM.

Let zeronm := @nmod_of_commonoid M 1%M.
Let addnm (x y : nmodM) :=
  nmod_of_commonoid (nmod_of_commonoid_inv x * nmod_of_commonoid_inv y).
Fact addnmA : associative addnm.
Proof. by move=> x y z; rewrite /addnm !unlock mulmA. Qed.
Fact addnmC : commutative addnm.
Proof. by move=> x y; rewrite /addnm !unlock mulmC. Qed.
Fact add0nm : left_id zeronm addnm.
Proof. by move=> x; rewrite /addnm /zeronm !unlock mul1m. Qed.
HB.instance Definition _ := GRing.isNmodule.Build nmodM addnmA addnmC add0nm.
Definition NMod_of_ComMonoid : NModules := nmodM.

Lemma nmod_of_commonoid1 : 0%R = nmod_of_commonoid 1 :> nmodM.
Proof. by []. Qed.
Lemma nmod_of_commonoidM :
  {morph @nmod_of_commonoid M : x y / (x * y)%M >-> (x + y)%R}.
Proof. by move=> x y; rewrite /GRing.add /= /addnm !nmod_of_commonoidK. Qed.

End Defs.

Section Functor_on_Hom.

Variables (M N : ComMonoids) (f : {hom[ComMonoids] M -> N}).
Let nmod_of_commonoid_mor : (NMod_of_ComMonoid M) -> (NMod_of_ComMonoid N) :=
  (@nmod_of_commonoid N) \o f \o (@nmod_of_commonoid_inv M).

Fact nmod_of_commonoid_mor_is_additive : semi_additive nmod_of_commonoid_mor.
Proof.
rewrite /nmod_of_commonoid_mor; split => /= [|x y /=].
  rewrite nmod_of_commonoid1 nmod_of_commonoidK.
  by rewrite -(mmorphism_of_ComMonoidsE f) mmorph1.
rewrite -nmod_of_commonoidM -(mmorphism_of_ComMonoidsE f) -mmorphM; congr (_ (f _)).
apply (can_inj (@nmod_of_commonoidK _)).
by rewrite nmod_of_commonoidM !nmod_of_commonoid_invK.
Qed.
HB.instance Definition _ :=
  isHom.Build NModules (NMod_of_ComMonoid M) (NMod_of_ComMonoid N)
    nmod_of_commonoid_mor nmod_of_commonoid_mor_is_additive.
Definition NMod_of_ComMonoid_mor
  : {hom[NModules] NMod_of_ComMonoid M -> NMod_of_ComMonoid N}
  := nmod_of_commonoid_mor.

End Functor_on_Hom.

Fact NMod_of_ComMonoid_ext : FunctorLaws.ext NMod_of_ComMonoid_mor.
Proof. by move=> /= a b f g eq y; rewrite /= eq. Qed.
Fact NMod_of_ComMonoid_id : FunctorLaws.id NMod_of_ComMonoid_mor.
Proof. by move=> /= a x /=; rewrite /hom_mset /= nmod_of_commonoid_invK. Qed.
Fact NMod_of_ComMonoid_comp  : FunctorLaws.comp NMod_of_ComMonoid_mor.
Proof. by move=> /= a b c f g x /=; rewrite nmod_of_commonoidK. Qed.
HB.instance Definition _ :=
  @isFunctor.Build ComMonoids NModules NMod_of_ComMonoid NMod_of_ComMonoid_mor
    NMod_of_ComMonoid_ext NMod_of_ComMonoid_id NMod_of_ComMonoid_comp.


Definition ComMonoid_of_NMod_type (M : NModules) : Type := M.
HB.lock Definition commonoid_of_nmod (M : NModules) (x : M)
  : (ComMonoid_of_NMod_type M) := x.
Canonical commonoid_of_nmod_unlock := Unlockable commonoid_of_nmod.unlock.
HB.lock Definition commonoid_of_nmod_inv M (x : ComMonoid_of_NMod_type M) : M := x.
Canonical commonoid_of_nmod_inv_unlock := Unlockable commonoid_of_nmod_inv.unlock.

Lemma commonoid_of_nmodK M :
  cancel (@commonoid_of_nmod M) (@commonoid_of_nmod_inv M).
Proof. by rewrite !unlock. Qed.
Lemma commonoid_of_nmod_invK M :
  cancel (@commonoid_of_nmod_inv M) (@commonoid_of_nmod M).
Proof. by rewrite !unlock. Qed.

Section Defs.

Variable M : NModules.
Local Notation cmonM := (ComMonoid_of_NMod_type M).
HB.instance Definition _ := Choice.on cmonM.

Let onecm := @commonoid_of_nmod M 0%R.
Let mulcm (x y : cmonM) :=
  commonoid_of_nmod (commonoid_of_nmod_inv x + commonoid_of_nmod_inv y).
Fact mulcmA : associative mulcm.
Proof. by move=> x y z; rewrite /mulcm !unlock addrA. Qed.
Fact mulcmC : commutative mulcm.
Proof. by move=> x y; rewrite /mulcm !unlock addrC. Qed.
Fact mul1cm : left_id onecm mulcm.
Proof. by move=> x; rewrite /mulcm /onecm !unlock add0r. Qed.
HB.instance Definition _ := isComMonoid.Build cmonM mulcmA mul1cm mulcmC.
Definition ComMonoid_of_NMod : ComMonoids := cmonM.

Lemma commonoid_of_nmod0 : 1%M = commonoid_of_nmod 0%R :> cmonM.
Proof. by []. Qed.
Lemma commonoid_of_nmodD :
  {morph @commonoid_of_nmod M : x y / (x + y)%R >-> (x * y)%M}.
Proof. by move=> x y; rewrite /mul /= /mulcm !commonoid_of_nmodK. Qed.

End Defs.

Section Functor_on_Hom.

Variables (M N : NModules) (f : {hom[NModules] M -> N}).
Let commonoid_of_nmod_mor : (ComMonoid_of_NMod M) -> (ComMonoid_of_NMod N) :=
  (@commonoid_of_nmod N) \o f \o (@commonoid_of_nmod_inv M).

Fact commonoid_of_nmod_mor_monmorphism : monmorphism commonoid_of_nmod_mor.
Proof.
rewrite /commonoid_of_nmod_mor; split => /= [x y /=|].
  rewrite -commonoid_of_nmodD -(additive_of_NmodE f) -raddfD; congr (_ (f _)).
  apply (can_inj (@commonoid_of_nmodK _)).
  by rewrite commonoid_of_nmodD !commonoid_of_nmod_invK.
rewrite commonoid_of_nmod0 commonoid_of_nmodK.
by rewrite -(additive_of_NmodE f) raddf0.
Qed.
HB.instance Definition _ :=
  isHom.Build ComMonoids (ComMonoid_of_NMod M) (ComMonoid_of_NMod N)
    commonoid_of_nmod_mor commonoid_of_nmod_mor_monmorphism.
Definition ComMonoid_of_NMod_mor
  : {hom[ComMonoids] ComMonoid_of_NMod M -> ComMonoid_of_NMod N}
  := commonoid_of_nmod_mor.

End Functor_on_Hom.

Fact ComMonoid_of_NMod_ext : FunctorLaws.ext ComMonoid_of_NMod_mor.
Proof. by move=> /= a b f g eq y; rewrite /= eq. Qed.
Fact ComMonoid_of_NMod_id : FunctorLaws.id ComMonoid_of_NMod_mor.
Proof. by move=> /= a x /=; rewrite /hom_mset /= commonoid_of_nmod_invK. Qed.
Fact ComMonoid_of_NMod_comp  : FunctorLaws.comp ComMonoid_of_NMod_mor.
Proof. by move=> /= a b c f g x /=; rewrite commonoid_of_nmodK. Qed.
HB.instance Definition _ :=
  @isFunctor.Build NModules ComMonoids ComMonoid_of_NMod ComMonoid_of_NMod_mor
    ComMonoid_of_NMod_ext ComMonoid_of_NMod_id ComMonoid_of_NMod_comp.

(** Doesn't seems to be provable
Lemma CM_id : ComMonoid_of_NMod \O NMod_of_ComMonoid =#= FId.
 *)

Local Notation CM := (ComMonoid_of_NMod \O NMod_of_ComMonoid).
Local Notation MC := (NMod_of_ComMonoid \O ComMonoid_of_NMod).

(** Build natural isom *)
Section IsoCM.

Variable M : ComMonoids.
Definition isoCM_map : CM M -> FId M :=
  (@nmod_of_commonoid_inv _) \o (@commonoid_of_nmod_inv (NMod_of_ComMonoid M)).
Definition isoCM_inv : FId M -> CM M :=
  (@commonoid_of_nmod _) \o (@nmod_of_commonoid M).

Fact isoCM_mapK : cancel isoCM_map isoCM_inv.
Proof.
rewrite /isoCM_map {}/isoCM_inv => x /=.
by rewrite !(nmod_of_commonoid_invK, commonoid_of_nmod_invK).
Qed.
Fact isoCM_invK : cancel isoCM_inv isoCM_map.
Proof.
rewrite /isoCM_map {}/isoCM_inv => x /=.
by rewrite !(nmod_of_commonoidK, commonoid_of_nmodK).
Qed.
Fact isoCM_monmorphism : monmorphism isoCM_map.
Proof.
split => [x y |].
  rewrite -{1}(isoCM_mapK x) -{1}(isoCM_mapK y).
  move: (isoCM_map x) (isoCM_map y) => {}x {}y.
  rewrite /isoCM_map /= {1}/mul /= {1}/GRing.add /=.
  rewrite nmod_of_commonoidM commonoid_of_nmodD.
  by rewrite !(nmod_of_commonoidK, commonoid_of_nmodK).
rewrite commonoid_of_nmod0 nmod_of_commonoid1 /isoCM_map /=.
by rewrite !(nmod_of_commonoidK, commonoid_of_nmodK).
Qed.
HB.instance Definition _ :=
  isHom.Build ComMonoids (CM M) M isoCM_map isoCM_monmorphism.

Fact isoCM_inv_monmorphism : monmorphism isoCM_inv.
Proof.
rewrite /isoCM_inv; split => [x y |] /=.
  by rewrite nmod_of_commonoidM commonoid_of_nmodD.
by rewrite commonoid_of_nmod0 nmod_of_commonoid1.
Qed.
HB.instance Definition _ :=
  isIsom.Build ComMonoids (CM M) M isoCM_map
    isoCM_inv_monmorphism isoCM_mapK isoCM_invK.

End IsoCM.

Section IsoCMTrans.

Let isoCM_hom : CM ~~> FId := isoCM_map.
Fact natural_isoCM : naturality CM FId isoCM_hom.
Proof.
move=> a b h x.
rewrite -(isoCM_mapK x); move: (isoCM_map x) => /= {}x.
rewrite /isoCM_inv /isoCM_map /=.
by rewrite !(nmod_of_commonoidK, commonoid_of_nmodK) FIdf.
Qed.
HB.instance Definition _ :=
  isNatural.Build ComMonoids ComMonoids CM FId isoCM_hom natural_isoCM.
Definition isoCM : CM ~> FId := isoCM_hom.

End IsoCMTrans.



Section IsoMC.

Variable M : NModules.
Definition isoMC_map : MC M -> FId M :=
  (@commonoid_of_nmod_inv _) \o (@nmod_of_commonoid_inv (ComMonoid_of_NMod M)).
Definition isoMC_inv : FId M -> MC M :=
  (@nmod_of_commonoid _) \o (@commonoid_of_nmod M).

Fact isoMC_mapK : cancel isoMC_map isoMC_inv.
Proof.
rewrite /isoMC_map {}/isoMC_inv => x /=.
by rewrite !(nmod_of_commonoid_invK, commonoid_of_nmod_invK).
Qed.
Fact isoMC_invK : cancel isoMC_inv isoMC_map.
Proof.
rewrite /isoMC_map {}/isoMC_inv => x /=.
by rewrite !(nmod_of_commonoidK, commonoid_of_nmodK).
Qed.
Fact isoMC_additive : semi_additive isoMC_map.
Proof.
split => [| x y].
  rewrite nmod_of_commonoid1 commonoid_of_nmod0 /isoMC_map /=.
  by rewrite !(nmod_of_commonoidK, commonoid_of_nmodK).
rewrite -{1}(isoMC_mapK x) -{1}(isoMC_mapK y).
move: (isoMC_map x) (isoMC_map y) => {}x {}y.
rewrite /isoMC_map /= {1}/GRing.add /= {1}/mul /=.
rewrite commonoid_of_nmodD nmod_of_commonoidM.
by rewrite !(nmod_of_commonoidK, commonoid_of_nmodK).
Qed.
HB.instance Definition _ :=
  isHom.Build NModules (MC M) M isoMC_map isoMC_additive.

Fact isoMC_inv_additive : semi_additive isoMC_inv.
Proof.
rewrite /isoMC_inv; split => [| x y] /=.
  by rewrite nmod_of_commonoid1 commonoid_of_nmod0.
by rewrite commonoid_of_nmodD nmod_of_commonoidM.
Qed.
HB.instance Definition _ :=
  isIsom.Build NModules (MC M) M isoMC_map
    isoMC_inv_additive isoMC_mapK isoMC_invK.

End IsoMC.

Section IsoMCTrans.

Let isoMC_hom : MC ~~> FId := isoMC_map.
Fact natural_isoMC : naturality MC FId isoMC_hom.
Proof.
move=> a b h x.
rewrite -(isoMC_mapK x); move: (isoMC_map x) => /= {}x.
rewrite /isoMC_inv /isoMC_map /=.
by rewrite !(nmod_of_commonoidK, commonoid_of_nmodK) FIdf.
Qed.
HB.instance Definition _ :=
  isNatural.Build NModules NModules MC FId isoMC_hom natural_isoMC.
Definition isoMC : MC ~> FId := isoMC_hom.

End IsoMCTrans.


Definition Equiv_ComMonoids_NModules :
  equivalence_category NMod_of_ComMonoid ComMonoid_of_NMod :=
  EquivalenceCategory natural_isoMC natural_isoCM.
