From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype finfun bigop.
From mathcomp Require Import ssralg ssrint finmap multiset.

Require Import category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Section FSFunComplement.

Variables (K : choiceType) (R : eqType) (z : R) (M : Type).
Variables (idx : M) (op : Monoid.com_law idx).
Implicit Types (X Y : {fsfun K -> R with z}) (P : pred K) (F : K -> M).

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

End FSFunComplement.

Local Open Scope fset_scope.
Local Open Scope ring_scope.

Definition freeLmod (R : nmodType) (T : choiceType) :=
  {fsfun T -> R with 0%R}.
Definition freeLmod_of (R : nmodType) (T : choiceType) of phant T :=
  @freeLmod R T.
Notation "{ 'freemod' R [ T ] }" := (freeLmod R T).

Identity Coercion fm_fm_of : freeLmod_of >-> freeLmod.

Fact fm_key : unit. Proof. exact: tt. Qed.

Notation "[ 'fm[' key ] x 'in' aT => F ]" :=
  ([fsfun[key] x in aT => F] : {freemod _[_]})
  (at level 0, x ident, only parsing).
Notation "[ 'fm' x 'in' aT => F ]" :=
  ([fsfun[fm_key] x in aT => F] : {freemod _[_]})
  (at level 0, x ident, format "[ 'fm'  x  'in'  aT  =>  F ]").
Notation "[ 'fm' i => j ]" := [fm x in [fset i]%fset => j]
  (at level 0, format "[ 'fm'  i  =>  j ]").

Lemma fm1E (R : nmodType) (T : choiceType) (i j : T) (r : R) :
  [fm i => r] j = if j == i then r else 0.
Proof. by rewrite !fsfunE in_fset1. Qed.

HB.instance Definition _ (R : nmodType) (T : choiceType) :=
  Choice.on {freemod R[T]}.

Section OnNModule.

Variables (R : nmodType) (T : choiceType).
Implicit Types (a b c : R) (f g h : {freemod R[T]}) (x y z : T).

Fact addfm_key : unit. Proof. exact: tt. Qed.
Definition addfm f g : {freemod R[T]} :=
  [fm[addfm_key] x in finsupp f `|` finsupp g => f x + g x].

Lemma addfmE f g x : addfm f g x = f x + g x.
Proof.
rewrite fsfun_fun in_fsetU.
case: (finsuppP f); case: (finsuppP g) => _ _ //=.
by rewrite addr0.
Qed.

Fact addfmA : associative addfm.
Proof. by move=> f g h; apply/fsfunP => x; rewrite !addfmE addrA. Qed.
Fact addfmC : commutative addfm.
Proof. by move=> f g; apply/fsfunP => x; rewrite !addfmE addrC. Qed.
Fact add0fm : left_id [fsfun with 0] addfm.
Proof. by move=> f; apply/fsfunP => x; rewrite addfmE /= fsfun0E add0r. Qed.
HB.instance Definition _ :=
  GRing.isNmodule.Build {freemod R[T]} addfmA addfmC add0fm.

Definition fmeval_head (k : unit) x f := let: tt := k in f x.
Local Notation fmeval x := (fmeval_head tt x).

Fact fmeval_is_additive x : semi_additive (fmeval x).
Proof.
split; rewrite /fmeval_head /= ?fsfunE // => f g.
rewrite fsfunE inE.
case: (boolP (x \in finsupp f)); case: (boolP (x \in finsupp g)) => //=.
by move=> /fsfun_dflt -> /fsfun_dflt ->; rewrite addr0.
Qed.
HB.instance Definition _ x :=
  GRing.isSemiAdditive.Build {freemod R[T]} R _ (fmeval_is_additive x).

Lemma fmDE f g x : (f + g) x = f x + g x.
Proof. exact: (raddfD (fmeval x)). Qed.
Lemma fmMn f n x : (f *+ n) x = (f x) *+ n.
Proof. exact: (raddfMn (fmeval x)). Qed.
Lemma fm_sum I (r : seq I) (s : pred I) (F : I -> {freemod R[T]}) x :
  (\sum_(i <- r | s i) F i) x = \sum_(i <- r | s i) (F i) x.
Proof. exact: (raddf_sum (fmeval x)). Qed.

Lemma fmE f : \sum_(i <- finsupp f) [fm i => f i] = f.
Proof.
apply/fsfunP => x; rewrite fm_sum.
case: (boolP (x \in finsupp f)) => [x_in_f | /[dup] x_notin_f /fsfun_dflt ->].
  rewrite (big_fsetD1 x x_in_f) /= fm1E eqxx.
  rewrite big_seq big1 ?addr0 // => y; rewrite fm1E !inE.
  by rewrite eq_sym => /andP[/negbTE ->].
rewrite big_seq big1 // => y; rewrite fm1E.
by case: eqP => // <-; rewrite (negbTE x_notin_f).
Qed.

End OnNModule.


Section OnZModule.

Variables (R : zmodType) (T : choiceType).
Implicit Types (a b c : R) (f g h : {freemod R[T]}) (x y z : T).

Fact oppfm_key : unit. Proof. exact: tt. Qed.
Definition oppfm f : {freemod R[T]} :=
  [fm[oppfm_key] x in finsupp f => (-f x)%R].

Lemma oppfmE f x : oppfm f x = (-(f x))%R.
Proof. by rewrite fsfun_fun; case: (finsuppP f) => //=; rewrite oppr0. Qed.

Fact addNfm : left_inverse 0%R oppfm (+%R)%R.
Proof.
by move=> f; apply/fsfunP => x; rewrite addfmE oppfmE addNr fsfun0E.
Qed.
HB.instance Definition _ :=
  GRing.Nmodule_isZmodule.Build {freemod R[T]} addNfm.

End OnZModule.


Section OnRing.

Variables (R : ringType) (T : choiceType).
Implicit Types (a b c : R) (f g h : {freemod R[T]}) (x y z : T).

Fact scalefm_key : unit. Proof. exact: tt. Qed.
Definition scalefm c f : {freemod R[T]} :=
  [fm[scalefm_key] x in finsupp f => (c * f x)%R].

Lemma scalefmE c f x : scalefm c f x = (c * f x).
Proof. by rewrite fsfun_fun; case: (finsuppP f); rewrite //= mulr0. Qed.

Fact scalefmA a b  f : scalefm a (scalefm b f) = scalefm (a * b) f.
Proof. by apply/fsfunP => x; rewrite !scalefmE mulrA. Qed.
Fact scale1fm : left_id 1%R scalefm.
Proof. by move=> f; apply/fsfunP => x; rewrite !scalefmE mul1r. Qed.
Fact scalefmDr : right_distributive scalefm +%R.
Proof.
move=> a f g; apply/fsfunP => x.
by rewrite !(addfmE, scalefmE) /= mulrDr.
Qed.
Fact scalefmDl f : {morph scalefm^~ f: a b / (a + b)%R}.
Proof.
move=> a b; apply/fsfunP => x.
by rewrite !(addfmE, scalefmE) /= mulrDl.
Qed.

HB.instance Definition _ :=
  GRing.Zmodule_isLmodule.Build R {freemod R[T]}
    scalefmA scale1fm scalefmDr scalefmDl.

Lemma finsupp_fm1 x : finsupp ([fm x => 1] : {freemod R[T]}) = [fset x].
Proof.
apply/fsetP => y; rewrite !inE mem_finsupp fm1E.
by case: (y == x); rewrite ?eqxx ?oner_neq0.
Qed.

Lemma fm1ZE x c : [fm x => c] = c *: [fm x => 1].
Proof.
apply/fsfunP => y; rewrite scalefmE !fm1E.
by case: (y == x); rewrite ?mulr0 ?mulr1.
Qed.

Lemma linear_fmE (M : lmodType R) (f g : {linear {freemod R[T]} -> M}) :
  (forall x : T, f [fm x => 1] = g [fm x => 1]) -> f =1 g.
Proof.
move=> eqfg m; rewrite -(fmE m) !linear_sum; apply eq_bigr=> x _.
by rewrite fm1ZE !linearZ /= eqfg.
Qed.

End OnRing.

Local Close Scope fset_scope.


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
by rewrite -(@fmDE nat K A B a) !fsfunE.
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
rewrite -[RHS]fmE; apply msetP => u /=; rewrite mset_sum sum_mset fm_sum.
apply: eq_bigr => v _.
rewrite mset1E fsfunE inE eq_sym.
by case: eqP => _; rewrite ?muln1 ?muln0.
Qed.

Lemma additive_msetE (M : nmodType) (f g : {additive {mset K} -> M}) :
  (forall x : K, f [mset x] = g [mset x]) -> f =1 g.
Proof. by move=> eq x; rewrite -(msetE x) !raddf_sum; apply: eq_bigr. Qed.

Section WidenMset.

Variables (M : Type) (idx : M) (op : Monoid.com_law idx).
Implicit Types (X Y : {mset K}) (P : pred K) (F : K -> M).

Lemma finsupp_widenD (X Y : {mset K}) F :
  (forall i, i \notin finsupp X -> F i = idx) ->
  (\big[op/idx]_(i <- finsupp (X + Y)%R) F i) = (\big[op/idx]_(i <- finsupp X) F i).
Proof. by move/(finsupp_widen op); apply=> x; rewrite !msuppE in_msetD => ->. Qed.

End WidenMset.

Lemma perm_enum_mseqD (X Y : {mset K}) : perm_eq (enum_mset (X `+` Y)) (X ++ Y).
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

Variables (M : Type) (idx : M) (op : Monoid.com_law idx).
Implicit Types (X Y : {mset K}) (P : pred K) (F : K -> M).

Lemma big_msetD X Y P F:
  \big[op/idx]_(i <- (X + Y : {mset K}) | P i) F i =
    op (\big[op/idx]_(i <- X | P i) F i) (\big[op/idx]_(i <- Y | P i) F i).
Proof. by rewrite -big_cat; apply: (perm_big _ (perm_enum_mseqD X Y)). Qed.

End MsetComplement.



