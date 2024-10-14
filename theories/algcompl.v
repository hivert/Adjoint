From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finfun bigop.
From mathcomp Require Import ssralg ssrint.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "'{' 'mmorphism' U '->' V '}'"
  (at level 0, U at level 98, V at level 99,
   format "{ 'mmorphism'  U  ->  V }").

Import GRing.Theory.

Local Open Scope ring_scope.

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

Notation "1" := (@one _) : monoid_scope.
Notation "1%M" := (@one _) : monoid_scope.
Notation "*%M" := (@mul _) : function_scope.

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
