From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup.

Require Import category species sum prod diff.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set SsrOldRewriteGoalsOrder.  (* change to Unset and remove the line when requiring MathComp >= 2.6 *)

Local Open Scope category_scope.
Local Open Scope species_scope.


Section CheckSpecies.

Variables (A B C : Species) (n : nat) (cond : nat -> bool).

Check A + B : Species.
Check 0 : Species.
Check @sumSpAV A B C : (A + B) + C ~> A + (B + C).
Check @sumSpC A B : A + B ~> B + A.
Check @sumSp0 A : A + 0 ~> A.
Check @sum0Sp A : 0 + A ~> A.

Check A * B : Species.
Check 1 : Species.
Check @prodSpC A B : A * B ~> B * A.
Check @prodSpA A B C : (A * B) * C ~> A * (B * C).
Check @prodSp1 A : A * 1 ~> A.
Check @prod1Sp A : 1 * A ~> A.

Check @prodSpDl A B C : A * (B + C) ~> A * B + A * C.
Check @prodSpDr A B C : (B + C) * A ~> B * A + C * A.

Check ∂ : Species -> Species.
Check @diffSum A B : ∂ (A + B) ~> ∂ A + ∂ B.
Check @diffProdV A B : ∂ (A * B) ~> ∂ A * B + A * ∂ B.



Check cardSp0 n : cardSp 0 n = 0%N.
Check cardiso_Sp0 n :cardiso 0 n = 0%N.

Check cardSp1 n : cardSp 1 n = (n == 0%N).
Check cardiso_Sp1 n : cardiso 1 n = (n == 0%N).

Check \X : Species.
Check cardSpX n : cardSp \X n = (n == 1%N).
Check cardiso_SpX n : cardiso \X n = (n == 1%N).

Check card_sumSp A B n : cardSp (A + B) n = (cardSp A n + cardSp B n)%N.
Check cardiso_sumSp A B n : cardiso (A + B) n = (cardiso A n + cardiso B n)%N.

Check card_prodSp A B n :
  cardSp (A * B) n =
    \sum_(0 <= i < n.+1) 'C(n, i) * cardSp A i * cardSp B (n - i).
Check cardiso_prodSp A B n :
  cardiso (A * B) n = \sum_(0 <= i < n.+1) cardiso A i * cardiso B (n - i).

Check setSp : Species.
Check card_setSp n : cardSp setSp n = 1%N.
Check cardiso_setSp n : cardiso setSp n = 1%N.

Check subsetSp : Species.
Check card_subsetSp0n n : cardSp subsetSp n = 2 ^ n.
Check cardiso_subsetSp n : cardiso subsetSp n = n.+1.

Check deltaSp cond : Species.
Check card_deltaSp cond n : cardSp (deltaSp cond) n = cond n.
Check cardiso_deltaSp cond n : cardiso (deltaSp cond) n = cond n.

Check card_diffSp A n : cardSp (∂ A) n = cardSp A n.+1.

End CheckSpecies.

