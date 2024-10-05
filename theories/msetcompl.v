From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finfun bigop.
From mathcomp Require Import ssralg ssrint finmap multiset.

Require Import category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope mset_scope.

HB.instance Definition _ (S : choiceType) := Choice.on {mset S}.
HB.instance Definition _ (S : choiceType) :=
  GRing.isNmodule.Build {mset S} msetDA msetDC mset0D.

Section MsetComplement.

Variable (K : choiceType).
Implicit Types (a b c : K) (A B C D : {mset K}) (s : seq K).

Lemma mset1E a b : [mset a] b = (a == b).
Proof. by rewrite fsfunE /= in_fset1 eq_sym; case eqP. Qed.

Definition mset_head h a A := let: tt := h in A a.
Local Notation coefm a := (mset_head tt a).

Fact coefm_is_additive a : semi_additive (coefm a).
Proof.
split; rewrite /mset_head /= ?mset0E // => A B.
rewrite fsfunE inE.
by case: (boolP (a \in finsupp A)); case: (boolP (a \in finsupp B));
  rewrite !msuppE //= => /mset_eq0P -> /mset_eq0P ->.
Qed.
HB.instance Definition _ a :=
  GRing.isSemiAdditive.Build {mset K} nat _ (coefm_is_additive a).

Lemma msetDE A B a : (A + B) a = A a + B a.
Proof. exact: (raddfD (coefm a)). Qed.
Lemma msetMn A n a : (A *+ n) a = (A a) *+ n.
Proof. exact: (raddfMn (coefm a)). Qed.
Lemma mset_sum I (r : seq I) (s : pred I) (F : I -> {mset K}) a :
  (\sum_(i <- r | s i) F i) a = \sum_(i <- r | s i) (F i) a.
Proof. exact: (raddf_sum (coefm a)). Qed.


Lemma msetE A : \sum_(i <- A) [mset i] = A.
Proof.
apply msetP => u /=; rewrite !mset_sum !sum_mset.
case: (boolP (u \in finsupp A)) => uS.
  rewrite (big_fsetD1 u uS) /= mset1E eqxx muln1.
  rewrite big_seq big1 ?addn0 // => v; rewrite !inE mset1E.
  by case eqP => //=; rewrite muln0.
have:= uS; rewrite msuppE -mset_eq0 => /eqP ->.
rewrite big_seq big1 // => v.
rewrite mset1E; case: (altP (_ =P _)) => [->|]; last by rewrite muln0.
by rewrite (negbTE uS).
Qed.

Lemma additive_msetE (M : nmodType) (f g : {additive {mset K} -> M}) :
  (forall x : K, f [mset x] = g [mset x]) -> f =1 g.
Proof. by move=> eq x; rewrite -(msetE x) !raddf_sum; apply: eq_bigr. Qed.

Section Widen.

Variables (R : Type) (idx : R) (op : Monoid.com_law idx).
Implicit Types (X Y : {mset K}) (P : pred K) (F : K -> R).

Lemma finsupp_widen X (S : {fset K}) F :
  (forall i, i \notin finsupp X -> F i = idx) ->
  {subset finsupp X <= S} ->
  (\big[op/idx]_(i <- S) F i) = (\big[op/idx]_(i <- finsupp X) F i).
Proof.
move=> H sub.
rewrite [LHS](bigID (fun i => i \in finsupp X)) /=.
rewrite [X in (op _ X)]big1 // Monoid.mulm1.
apply: eq_fbig_cond => // i; rewrite !inE /= andbT.
by case: (boolP (i \in finsupp X)); rewrite /= ?andbF ?andbT // => /sub ->.
Qed.

Lemma finsupp_widenD X Y F :
  (forall i, i \notin finsupp X -> F i = idx) ->
  (\big[op/idx]_(i <- finsupp (X + Y)%R) F i) = (\big[op/idx]_(i <- finsupp X) F i).
Proof. by move/finsupp_widen; apply=> x; rewrite !msuppE in_msetD => ->. Qed.


End Widen.

Variables (R : Type) (idx : R) (op : Monoid.com_law idx).
Implicit Types (X Y : {mset K}) (P : pred K) (F : K -> R).

Lemma perm_enum_mseqD X Y : perm_eq (enum_mset (X + Y)) (X ++ Y).
Proof.
rewrite unlock; apply/permP => i.
rewrite count_cat !count_flatten !sumnE !big_map -natrDE.
have cnotin (Z : {mset K}) j : j \notin finsupp Z -> count i (nseq (Z j) j) = 0.
  by rewrite count_nseq msuppE -mset_eq0 => /eqP -> /[!muln0].
rewrite -(@finsupp_widenD nat 0 _ X Y _ (cnotin X)) //=.
rewrite -(@finsupp_widenD nat 0 _ Y X _ (cnotin Y)) //= [Y + X]msetDC.
rewrite -[RHS]big_split /=; apply eq_bigr => j _.
by rewrite msetDE nseqD count_cat.
Qed.

Lemma big_msetD X Y P F:
  \big[op/idx]_(i <- (X + Y : {mset K}) | P i) F i =
    op (\big[op/idx]_(i <- X | P i) F i) (\big[op/idx]_(i <- Y | P i) F i).
Proof. by rewrite -big_cat; apply: (perm_big _ (perm_enum_mseqD X Y)). Qed.

End MsetComplement.