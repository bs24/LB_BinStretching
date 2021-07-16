Require Import Lia List Arith.
Import Nat ListNotations.

Scheme Equality for list.
Hint Resolve leb_correct leb_complete beq_nat_true beq_nat_eq beq_nat_refl : export core.

Require   MSets.
Require Import Coq.Structures.Orders.
Require Import NArith.
Require Import PArith.Pnat.

Open Scope bool_scope.


Notation "a &&& b" := (if a then b else false)
 (at level 40, left associativity).
Notation "a ||| b" := (if a then true else b)
 (at level 50, left associativity).


(** Preliminaries **)
(*
Goal: define a (binary search tree)-based dictionnary for pairs of natural lists 
We first need to define a total order on natural lists, with relevant lemmas.
*)

Definition elt := N.


Inductive Listlt: list elt ->  list elt -> Prop:=
| Empty l x   : Listlt [] (x::l)
| Lt x r y s  :  (x < y)%N -> Listlt (x::r) (y::s)
| Cons x r  s :  Listlt r s -> Listlt (x::r) (x::s)
.


Lemma Listlt_trans: forall b a c,  Listlt a b -> Listlt b c -> Listlt a c.
Proof.
intro; induction b; intros; inversion H; simpl.
    - inversion H0; constructor.
    - inversion H0; apply Lt.
           eapply N.lt_trans; eauto.
           auto.
    - inversion H0. apply Lt; auto. apply Cons; auto.
Qed.


Ltac n_lt H := let c:= fresh H in
inversion H as [c]; rewrite  nat_of_Ncompare in c; rewrite <- nat_compare_lt in c; try lia.
Hint Rewrite N.eqb_eq.
Hint Resolve N.eqb_eq : export core.


Lemma Listlt_neq: forall a b, Listlt a b -> a <> b.
Proof.
intro; induction a; intros; intro; inversion H; try congruence.
all: rewrite <- H2 in H0; inversion H0; subst.
  n_lt H4.
apply IHa with s; auto.
Qed.

Definition List_eq (a:list elt) (b:list elt) := a=b.



Lemma beq_nat_nat (n:elt) (m:elt):  n=m -> (n =? m)%N = true .
Proof. intros. rewrite H. now autorewrite with core.
Qed.
Lemma beq_aux: forall x y : elt, (x =? y)%N = true -> x = y.
intros. apply N.eqb_eq; auto.
Qed.
Lemma List_eq_dec: forall l l':list elt, {l = l'} + {l <> l'}.
Proof.
intros.
edestruct (list_eq_dec N N.eqb  (beq_aux) beq_nat_nat l l');
intuition.
Qed.
Lemma List_str_order : StrictOrder Listlt.
Proof.
split; repeat intro. now apply Listlt_neq in H. 
eapply Listlt_trans; eauto.
Qed.
Lemma Listlt_compat : Proper (List_eq ==> List_eq ==> iff) Listlt.
Proof.
apply proper_sym_impl_iff_2; auto with *.
Qed.

Fixpoint compare l l' := match l,l' with
| [], []   => Datatypes.Eq
| [], x::r => Datatypes.Lt
| x::r, [] => Datatypes.Gt
| x::r, y::s => match (x?=y)%N with
                | Datatypes.Lt => Datatypes.Lt
                | Datatypes.Gt => Datatypes.Gt
                | Datatypes.Eq => compare r s
                end
end.

Lemma compare_spec :
     forall x y : list elt, CompareSpec (x = y) (Listlt x y) (Listlt y x) (compare x y).
Proof.
  intro; induction x; intros; simpl. induction y; simpl.
  + auto.
  + repeat constructor.
  + induction y.
    - repeat constructor.
    - remember (a?=a0)%N as c. symmetry in Heqc.
      destruct c.
      * rewrite N2Nat.inj_compare in Heqc.
        apply compare_eq_iff in Heqc. apply N2Nat.inj_iff in Heqc; subst.
        destruct IHx with y.
        all: repeat constructor; congruence.
      * repeat constructor. auto.
      * repeat constructor. apply N.compare_gt_iff in Heqc. auto.
Qed.


Module List_as_OT <: OrderedType.
  Definition t:=list elt.
  Definition eq:= List_eq.
  Definition lt := Listlt.
  Definition compare := compare.
  Definition compare_spec := compare_spec.
  Definition eq_dec := List_eq_dec.
  Instance eq_equiva : Equivalence List_eq.
  Proof. split; congruence.  Qed.
  Definition eq_equiv := eq_equiva.
  Definition lt_strorder := List_str_order.
  Definition lt_compat := Listlt_compat.
End List_as_OT.


Module RKEY := OrdersEx.PairOrderedType (List_as_OT) (List_as_OT).

(* Module representing a list of integers dictionnary *)
Module M :=  MSetAVL.Make RKEY .





(*************************************************)


(** Start of the main section **)

Section OnlineBinStretching.


(* Set Default Proof Using "Type". 
 *)
(* the element sizes have the type elt, which represent a binary integer.
As unary integers as easier to manipulate in the proofs, we define functions with
both unary and binary integers (the latter end by *N). The goal is the following:
 - enable the user to run a function checking a tree with binary integers for performance
 - define a unary integer counterpart to the function
 - prove that both functions give the same result
 - prove that if the unary function returns true (which we do not run), then the final property holds
*)

(* m = number of bins | t = target height | g = guarantee height *)
Variables m : nat.
Variables t g: nat.
Hypothesis Posm: m>0.


(** * Types, small functions and properties **)

(* list of elements in one bin *)
Definition BinExtended := list nat.
(* height of each bin *)
Definition BinLoads := list nat.
(* which elements are in each bin *)
Definition BinsExtended:= list BinExtended.


(* sum of the elements of a bin *)
Fixpoint BinSum B := match B with
| nil  => 0
| x::s => (x + BinSum s)
end.


(* return the height of the maximum bin, where bins are described by elements *)

Fixpoint MaxBinSum P := match P with
| nil  => 0
| x::s => max (BinSum x) (MaxBinSum s)
end.


(* return the height of the maximum bin, where bins are described by height *)
Fixpoint MaxBinValue (S: BinLoads) := match S with
| nil  => 0
| x::s => max x (MaxBinValue s)
end.


(* add the element e to the bin b; bins are described by height *)

Fixpoint AddToBin (S: BinLoads) (e: nat) (b: nat) := match S, b with
| nil  , b     => [e]
| x::s , 0     => (x+e)::s
| x::s , (S k) => x::(AddToBin s e k)
end.


(* checks that all elements of l are contained in P *) 
Definition CompletePacking (l: list nat) (P: BinsExtended):= forall e, 
count_occ Nat.eq_dec l e <= count_occ Nat.eq_dec (concat P) e.

(* checks the validity of a packing: completeness, number of bins, height *)
Definition SolutionPacking (l:list nat) (P: BinsExtended)  :=
CompletePacking l P /\  length P = m /\ (MaxBinSum P <= g).

(* checks that the list contains only zeros *)
Definition Iszero l := (forall e, In e l -> e=0) /\ length l <= m.


(** * Main property we want to prove **)

(* first, the inductive property *)
(**
-   l  = list of elements
-   St = current state of bins
-   X = decreasing parameter to help in the induction
*)


Inductive OnlineInfeasible_simpl: nat -> list nat -> BinLoads -> Prop :=
| Overflow_simpl X l St: (* one bin is too high and a valid packing exists *)
            (t <= MaxBinValue St)
         -> (exists P, SolutionPacking l P)
         -> OnlineInfeasible_simpl X l St

| Deadend_simpl X l St: (* if we add the element e to any bin, we get an infeasible state *)
            length St <= m
         -> (exists e, forall b, (b < m) -> OnlineInfeasible_simpl X ((S e)::l) (AddToBin St (S e) b))
         -> OnlineInfeasible_simpl (S X) l St
.


(**  **************** This is the final property     **************)

Definition Lower_bound := exists s, Iszero s  /\  OnlineInfeasible_simpl (m*g+2) [] s.





(** add an initial case to help the induction **)

Inductive OnlineInfeasible: nat -> list nat -> BinLoads -> Prop :=
| Overflow X l St: 
            t <= MaxBinValue St
         -> (exists P, SolutionPacking l P)
         -> OnlineInfeasible X l St

| NoMorePieces l St: 
            (exists P, SolutionPacking l P)
         -> OnlineInfeasible 0 l St

| Deadend X l St:
            length St <= m
         -> (exists e, forall b, (b < m) -> OnlineInfeasible X ((S e)::l) (AddToBin St (S e) b))
         -> OnlineInfeasible (S X) l St
.


Open Scope bool_scope.
Open Scope nat_scope.


(* Preliminary results on binary integers *)


Lemma Nnat_s: forall a, (N_of_nat a <? N_of_nat (S a))%N = true.
Proof.
induction a.
  simpl. auto.
simpl.
apply N.ltb_lt.
apply Pos.lt_succ_diag_r.
Qed.

Lemma Nnat_ltle: forall b a, (a <? b)%N = true -> (a <=? b)%N = true.
Proof.
intros.
assert (N.compare (0+a) b = (a ?= b)%N). auto.
induction (N.compare a b); simpl in H0;
 unfold N.leb; rewrite H0; intuition.
unfold N.ltb in H; rewrite H0 in H; auto.
Qed.



Lemma Nnat_order_plus: forall a b,  (N_of_nat a <? N_of_nat (S(b+a)))%N = true.
Proof.
intros.
induction b.
+ simpl. apply Nnat_s.
+ 
  rewrite plus_Sn_m.
  apply N.ltb_lt. apply N.ltb_lt in IHb.
  etransitivity. apply IHb.
  apply N.ltb_lt.
  apply Nnat_s.
Qed.

Lemma Nnat_sorder:  forall a b,  (a<?b)  = (N_of_nat a <? N_of_nat b)%N.
Proof.

intros. destruct (lt_eq_lt_dec a b). destruct s.
+ transitivity true.
    now apply ltb_lt.
  assert (a<=b). auto with arith.
  apply le_plus_minus in H.
  revert H; generalize (b-a); intros.
  destruct n. lia.
  subst. rewrite <- plus_n_Sm.
  rewrite plus_comm.
  symmetry; apply Nnat_order_plus.
+ subst.
  transitivity false.
    apply ltb_irrefl.
  symmetry; apply N.ltb_irrefl.
+ subst.
  transitivity false.
  - apply Bool.not_true_iff_false; intro.  
    apply ltb_lt in H; lia.
  - symmetry; apply Bool.not_true_iff_false; intro.  
    assert ((N.of_nat b <? N.of_nat a)%N = true).
    * assert (b<=a). auto with arith.
      apply le_plus_minus in H0.
      revert H0; generalize (a-b); intros.
      destruct n. lia.
      subst. rewrite <- plus_n_Sm.
      rewrite plus_comm.
      apply Nnat_order_plus.
    * apply N.ltb_lt in H. apply N.ltb_lt in H0.
      apply N.compare_lt_iff in H. apply N.compare_lt_iff in H0.
      rewrite N.compare_antisym in H.
      rewrite H0 in H.
      simpl in H.
      inversion H.
Qed.


Lemma Nnat_order:  forall a b,  (a<=?b)  = (N_of_nat a <=? N_of_nat b)%N.
Proof.

intros.
destruct (lt_eq_lt_dec a b). destruct s.
+ transitivity true.
    apply leb_le; auto with arith.
  symmetry; apply Nnat_ltle.
  rewrite <- Nnat_sorder.
  apply leb_le; auto with arith.
+ subst.
  transitivity true.
    apply leb_refl.
  symmetry; apply N.leb_refl.
+ transitivity false.
  - apply Bool.not_true_iff_false; intro.  
    apply leb_le in H; lia.
  - symmetry; apply Bool.not_true_iff_false; intro.
    assert (b<=a). auto with arith.
    assert ((N.of_nat b <? N.of_nat a)%N = true).
    * rewrite <- Nnat_sorder. apply ltb_lt; auto with arith.
    * apply N.leb_le in H. apply N.ltb_lt in H1.
      apply N.compare_le_iff in H. apply N.compare_lt_iff in H1.
      rewrite N.compare_antisym in H.
      rewrite H1 in H.
      simpl in H.
      intuition.
      
Qed.




Hint Resolve Nnat_order : Nnat.


(* functions to translate binary integer lists to unary integer lists 
and preliminary lemmas on list translations  *)

Definition List_toN := map N_of_nat .
Definition LList_toN := map (map N_of_nat) .
Definition List_ofN := map nat_of_N .
Definition LList_ofN := map (map nat_of_N) .

Hint Rewrite Nat2N.inj_double Nat2N.inj_succ_double
 Nat2N.inj_succ Nat2N.inj_add Nat2N.inj_mul Nat2N.inj_sub
 Nat2N.inj_pred Nat2N.inj_div2 Nat2N.inj_max Nat2N.inj_min
 Nat2N.id
 : Nnat.


Lemma List_iff: forall l, List_toN (List_ofN l) = l.
Proof.
intro. induction l; auto. simpl.
rewrite IHl; autorewrite with Nnat.
auto.
Qed.
Lemma List_ofto: forall l, List_ofN (List_toN l) = l.
Proof.
intro. induction l; auto. simpl.
rewrite IHl; autorewrite with Nnat.
auto.
Qed.
Lemma List_toof: forall l, List_toN (List_ofN l) = l.
Proof.
intro. induction l; auto. simpl.
rewrite IHl; autorewrite with Nnat.
auto.
Qed.

Lemma InListN: forall l x, In x (List_ofN l) -> In (N_of_nat x) l.
Proof.
intros.
rewrite <- List_iff. 
apply in_map; auto.
Qed.

Lemma List_inj: forall l l', l<>l' -> List_ofN l <> List_ofN l'.
Proof.
intros; intro.
pose proof (List_iff l).
rewrite H0 in H1.
rewrite List_iff in H1.
intuition.
Qed.

Lemma List_concat: forall a b, List_ofN (a ++ b) = (List_ofN a) ++ (List_ofN b).
Proof.
induction a; intros.
  auto.
simpl in *.
rewrite IHa; auto.
Qed.


Lemma Count_occN_eq: forall l a, count_occ N.eq_dec l a = count_occ eq_dec (List_ofN l) (nat_of_N a).
Proof.
induction l; intros.
  simpl; auto.
simpl.
destruct N.eq_dec; destruct eq_dec; subst; intuition.
apply Nnat.nat_of_N_inj in e; intuition.
Qed.
Hint Rewrite Count_occN_eq : Nnat.

Lemma ConcatN_eq: forall P, concat (LList_ofN P) =  List_ofN (concat P).
Proof.
induction P; intros.
  simpl; auto.
simpl. rewrite IHP.
induction a; simpl; auto.
rewrite IHa; auto.
Qed.
Hint Rewrite ConcatN_eq : Nnat.


(* Binary version of the primitive functions, and their equivalence proofs *)



Definition BinExtendedN := list elt.
Definition BinLoadsN := list elt.
Definition BinsExtendedN:= list BinExtendedN.

Fixpoint BinSumN B := match B with
| nil  => 0%N
| x::s => (x + BinSumN s)%N
end.

Lemma BinSumN_eq : forall S, N_of_nat (BinSum (List_ofN S)) = BinSumN S.
Proof.
intro; induction S; simpl; auto.
rewrite <- IHS.
autorewrite with Nnat.  auto.
Qed.
Hint Rewrite BinSumN_eq List_iff : Nnat.


Fixpoint MaxBinSumN P := match P with
| nil  => 0%N
| x::s => N.max (BinSumN x) (MaxBinSumN s)
end.

Lemma MaxBinSumN_eq : forall S, N_of_nat (MaxBinSum (LList_ofN S)) = MaxBinSumN S.
Proof.
intro; induction S; simpl; auto.
rewrite <- IHS.
autorewrite with Nnat.  auto.
Qed.
Hint Rewrite MaxBinSumN_eq : Nnat.


Fixpoint MaxBinValueN S := match S with
| nil  => 0%N
| x::s => N.max x (MaxBinValueN s)
end.

Lemma MaxBinValueN_eq : forall S, N_of_nat (MaxBinValue (List_ofN S)) = MaxBinValueN S.
Proof.
intro; induction S; simpl; auto.
rewrite <- IHS.
autorewrite with Nnat.  auto.
Qed.
Hint Rewrite MaxBinValueN_eq : Nnat.


Fixpoint AddToBinN S (e: elt) (b: nat) := match S, b with
| nil  , b     => [e]
| x::s , 0     => (x+e)%N::s
| x::s , (S k) => x::(AddToBinN s e k)
end.

Lemma AddToBinN_eq : forall b e S, List_toN (AddToBin (List_ofN S) (nat_of_N e) b ) = AddToBinN S e b.
Proof.
induction b; intros.
+ induction S;  simpl; autorewrite with Nnat;  auto.
+ induction S;  simpl; autorewrite with Nnat;  auto.
  rewrite IHb; auto.
Qed.
Hint Rewrite AddToBinN_eq : Nnat.



(* Some auxiliary functions *)

(* take the first non-sorted element in the list and put it at the front *)
Fixpoint BubbleSort l := match l with
| nil  =>  nil
| x::s => match (BubbleSort s) with
          | nil  => [x]
          | a::t => if (a <=? x) then x::a::t else a::x::t
          end
end.

Fixpoint BubbleSortN l := match l with
| nil  =>  nil
| x::s => match (BubbleSortN s) with
          | nil  => [x]
          | a::t => if (a <=? x)%N then x::a::t else a::x::t
          end
end.


Lemma BubbleSortN_eq: forall l, BubbleSortN l = List_toN (BubbleSort (List_ofN l)).
Proof.
intros; induction l.
  simpl; auto.
simpl BubbleSortN.
rewrite IHl.

simpl List_ofN.
simpl BubbleSort.
destruct (BubbleSort (List_ofN l)).
  simpl; autorewrite with Nnat; auto.
simpl.
assert (a = N.of_nat (N.to_nat a)); autorewrite with Nnat; auto.
rewrite H.
generalize (N.to_nat a); intros.
rewrite <- Nnat_order.
autorewrite with Nnat; auto.
destruct (n <=? n0); 
autorewrite with Nnat; auto.
Qed.
Hint Resolve BubbleSortN_eq : Nnat.


(* verify the CompletePacking property *)
Fixpoint CompletePacking_b (l: list nat) (P: list nat):= match l with
| nil  => true
| x::s => (count_occ Nat.eq_dec l x <=? count_occ Nat.eq_dec (P) x) &&& CompletePacking_b s P
end.

Fixpoint CompletePacking_bN (l: list elt) (P: list (elt)):= match l with
| nil  => true
| x::s => (count_occ N.eq_dec l x <=? count_occ N.eq_dec (P) x) &&& CompletePacking_bN s P
end.


Lemma CompletePacking_b_eq : forall l P, CompletePacking_bN l P = true -> CompletePacking_b (List_ofN l) (List_ofN P) = true.
Proof.
induction l; intros.
  simpl; auto.
simpl.
destruct eq_dec; intuition.
simpl in H.
destruct N.eq_dec; intuition.
symmetry in H; apply Bool.andb_true_eq in H; destruct H.
apply Bool.andb_true_iff; split; auto; symmetry.
autorewrite with Nnat in *. auto.
Qed.


(* binary versions of the parameters *)
Definition Nt := Eval vm_compute in N_of_nat t.
Definition Ng := Eval vm_compute in N_of_nat g.

(* verify the SolutionPacking property *)
Definition SolutionPacking_b  (l:list nat) (P: BinsExtended)  :=
(CompletePacking_b l (concat P)) &&&  (length P =? m) &&& (MaxBinSum P <=? g).

Definition SolutionPacking_bN  (l:list elt) (P: list (list elt))  :=
(CompletePacking_bN l (concat P)) &&&  (length P =? m) &&& (MaxBinSumN P <=? Ng)%N.


Lemma SolutionPacking_b_eq : forall l P, SolutionPacking_bN l P = true -> SolutionPacking_b (List_ofN l) (LList_ofN P) = true.
Proof.
intros.
symmetry in H; apply Bool.andb_true_eq in H; destruct H.
apply Bool.andb_true_eq in H; destruct H.
apply Bool.andb_true_iff; split; try apply Bool.andb_true_iff; try split.
+ rewrite ConcatN_eq; apply CompletePacking_b_eq; auto.
+ unfold LList_ofN. rewrite map_length; auto.
+ rewrite Nnat_order. autorewrite with Nnat; auto.
Qed.


(* verify the MaxBinTooHigh property *)
Definition idb (x:bool) := x.
Definition MaxBinTooHighN  St := ( Nt <=? MaxBinValueN St)%N.
Definition MaxBinTooHigh  St := (t <=? MaxBinValue St).

Lemma MaxBinTooHighN_eq: forall St, MaxBinTooHighN St = MaxBinTooHigh (List_ofN St).
Proof.
intros; unfold MaxBinTooHighN in *; unfold MaxBinTooHigh.
rewrite <- MaxBinValueN_eq.
rewrite Nnat_order.
autorewrite with Nnat in *; auto.
Qed.
Hint Rewrite MaxBinTooHighN_eq: Nnat.


(* A faster version on sorted lists *)

Definition FirstBinTooHigh St := match St with
| []   => false
| x::r => (t <=? x)
end.

Definition FirstBinTooHighN St := match St with
| []   => false
| x::r => (Nt <=? x)%N
end.

Lemma FirstBinTooHigh_eq: forall St, FirstBinTooHighN St = FirstBinTooHigh (List_ofN St).
Proof.
intros; destruct St; simpl; auto.
rewrite Nnat_order.
autorewrite with Nnat; auto.
Qed.



(* Reformulate decidability results on lists *)

Lemma list_bl {A eq_A} (A_bl : forall x y : A, eq_A x y = true -> x = y) {x y}
: list_beq A eq_A x y = true -> x = y.
Proof. now apply internal_list_dec_bl. Qed.

Lemma list_lb {A eq_A} (A_bl : forall x y : A, x=y -> eq_A x y = true ) {x y}
: x=y -> list_beq A eq_A x y = true .
Proof. apply internal_list_dec_lb. auto. Qed.

Lemma list_lbF {A eq_A} (A_bl : forall x y : A, eq_A x y = true -> x = y) {x y}
: x<>y -> list_beq A eq_A x y = false .
Proof. 
intros.
apply Bool.not_true_is_false; intro.
apply H.
 eapply list_bl; eauto.
Qed.



(** ** Lemmas related to Packings ***)

Lemma CompletePackBool: forall l P, true = CompletePacking_b l (concat P) <-> CompletePacking l P.
Proof.
intros; induction l; unfold CompletePacking;split; intros;auto.
{
  destruct (Nat.eq_decidable a e).

    rewrite H0; rewrite H0 in H; clear H0.
    rewrite count_occ_cons_eq;auto.
    inversion H.
    apply Bool.andb_true_eq in H1; destruct H1.
    destruct Nat.eq_dec; auto.

  rewrite count_occ_cons_neq;auto.
  apply IHl.
  apply Bool.andb_true_eq in H; destruct H; auto.
}

simpl;  destruct (eq_dec); intuition.
   symmetry; apply Bool.andb_true_iff; split.
   eapply leb_correct.
   erewrite <- count_occ_cons_eq; eauto.
symmetry; apply H1; intro.
eapply le_trans.
2: eapply H. 
destruct (Nat.eq_dec a e0).
    rewrite count_occ_cons_eq; auto.
    rewrite count_occ_cons_neq; auto.
Qed.

Lemma SolPackbool: forall l P, true = SolutionPacking_b l P  <-> SolutionPacking l P.
Proof.

split.
+ intros.
  unfold SolutionPacking_b in H.
  apply Bool.andb_true_eq in H; destruct H.
  apply Bool.andb_true_eq in H; destruct H.
  split; intros.
    apply CompletePackBool;auto.
  split; auto.
+ intros.
  unfold SolutionPacking_b; symmetry.
  destruct H. destruct H0.
  apply Bool.andb_true_iff; split; auto.
    apply Bool.andb_true_iff; split.
     symmetry; apply CompletePackBool; auto.
    subst; auto.
Qed.

Lemma SolPackCountocc: forall l l' P, 
(forall x, count_occ Nat.eq_dec l x  = count_occ Nat.eq_dec l' x) ->
SolutionPacking l P -> SolutionPacking l' P .
Proof.
intros.
destruct H0. destruct H1.
split; auto.
 intro;auto.
specialize  (H0 e).
  rewrite <- H;  auto.
Qed.

Lemma SolPackCountocc_ex: forall l l', 
(forall x, count_occ Nat.eq_dec l x  = count_occ Nat.eq_dec l' x) ->
(exists P, SolutionPacking l P) -> (exists P, SolutionPacking l' P ).
Proof.
intros. destruct H0. exists x. eapply SolPackCountocc; auto.
Qed.



Lemma Packing_included: forall l e P, SolutionPacking (e::l) P ->  SolutionPacking l P.
Proof.
intros l.
induction l; intros. 
  split.
    intro;auto.
    inversion H; auto.
    
inversion H.
split; auto.  intro.
destruct (Nat.eq_decidable e e0).
  apply le_Sn_le; erewrite <- count_occ_cons_eq; eauto.
erewrite <- count_occ_cons_neq; eauto.
Qed.

Lemma Packing_concat: forall a b P, SolutionPacking (a++b) P -> SolutionPacking b P.
Proof.
induction a; intros.
  auto.
eapply IHa. eapply Packing_included. eapply H.
Qed.


Lemma Countocc_exch: forall a x b e, count_occ Nat.eq_dec (x::a++b) e = count_occ Nat.eq_dec (a++x::b) e.
Proof.
induction a; intros.
  auto.
simpl.
  destruct (Nat.eq_dec a e); destruct (Nat.eq_dec x e); subst; auto.
 + rewrite <- IHa. rewrite count_occ_cons_eq; auto.
 + rewrite <- IHa. rewrite count_occ_cons_neq; auto.
 + rewrite <- IHa. rewrite count_occ_cons_eq; auto.
 + rewrite <- IHa. rewrite count_occ_cons_neq; auto.
 Qed.


Lemma Packing_exch: forall a x b P, SolutionPacking (x::a++b) P -> SolutionPacking (a++x::b) P.
Proof.
intros; unfold SolutionPacking in *.
repeat split; intuition.
unfold CompletePacking in *; intros.
rewrite <- Countocc_exch.
auto.
Qed.


(** ** Count_occ ***)

Lemma Countocc_cons: forall s s' a,
(forall x, count_occ Nat.eq_dec s x  = count_occ Nat.eq_dec s' x) ->
(forall x, count_occ Nat.eq_dec (a::s) x  = count_occ Nat.eq_dec (a::s') x).
Proof.
intros.
destruct (Nat.eq_dec a x); subst.
rewrite count_occ_cons_eq; auto.
rewrite count_occ_cons_eq; auto.
rewrite count_occ_cons_neq; auto.
rewrite count_occ_cons_neq; auto.
Qed.

Lemma Countocc_sound: forall s s',
(forall x, count_occ Nat.eq_dec s x  = count_occ Nat.eq_dec s' x) ->
(forall x, In x s <-> In x s').
Proof.
intros; split; intros; eapply count_occ_In; 
[rewrite <- H | rewrite H] ; 
eapply count_occ_In ; auto.
Qed.

Lemma BubSort_countocc: forall s i , 
          count_occ Nat.eq_dec (BubbleSort s) i = count_occ Nat.eq_dec s i.
Proof.
intro;induction s; intros; auto.
destruct (Nat.eq_decidable a i).
{
  rewrite H; clear H.
  rewrite count_occ_cons_eq; auto.
  rewrite <- IHs; simpl.
  destruct (BubbleSort s); simpl.
    destruct (Nat.eq_dec i i); intuition.
  destruct Nat.eq_dec; auto; subst.
    rewrite Nat.leb_refl.
    rewrite count_occ_cons_eq;auto;
    rewrite count_occ_cons_eq; auto.
  destruct (n <=? i).
    rewrite count_occ_cons_eq;auto;
    rewrite count_occ_cons_neq; auto.
  rewrite count_occ_cons_neq;auto;
  rewrite count_occ_cons_eq; auto.
}

rewrite count_occ_cons_neq; auto.
rewrite <- IHs.
simpl.
destruct (BubbleSort s); simpl.
  destruct Nat.eq_dec; intuition.
destruct (n <=? a);
destruct Nat.eq_dec.
      rewrite count_occ_cons_neq; auto;
      rewrite count_occ_cons_eq;auto.
    rewrite count_occ_cons_neq;auto;
    rewrite count_occ_cons_neq; auto.
  rewrite count_occ_cons_eq;auto;
  rewrite count_occ_cons_neq; auto.
rewrite count_occ_cons_neq;auto;
rewrite count_occ_cons_neq; auto.
Qed.

(* remove first occurence of a in s; only used in proofs *)
Fixpoint sa (s: list nat ) (a:nat) := match s with
| [] => []
| x::s => if Nat.eq_dec x a then s else x:: (sa s a) end.

Lemma sa_length: forall s a, In a s -> length s = S(length (sa s a)).
Proof.
intro; induction s; intros. destruct H.
simpl; apply eq_S.
destruct (Nat.eq_dec a a0); auto.
simpl; apply IHs.
destruct H; intuition.
Qed.

Lemma sa_countocc_eq: forall s a, In a s -> count_occ Nat.eq_dec s a = S (count_occ Nat.eq_dec (sa s a) a).
Proof.
intro; induction s; intros. destruct H.
simpl; destruct (Nat.eq_dec a a0); auto.
rewrite count_occ_cons_neq;auto.
apply IHs.
destruct H; intuition.
Qed.

Lemma sa_countocc_neq: forall s a b, In a s -> a<>b -> count_occ Nat.eq_dec s b = count_occ Nat.eq_dec (sa s a) b.
Proof.

intro; induction s; intros. destruct H.
simpl.
destruct (Nat.eq_dec a b); intuition.
{
  destruct (Nat.eq_dec a a0); intuition.
  rewrite e.
  rewrite count_occ_cons_eq;auto.
  apply eq_S.
  apply IHs; auto.
  destruct H; intuition.
}
destruct (Nat.eq_dec a a0); intuition.
rewrite count_occ_cons_neq;auto.
apply IHs; auto.
destruct H; intuition.
Qed.

Lemma sa_cons_neq: forall s a b, b<>a -> sa (b::s) a = b :: (sa s a).
Proof.
intros.
simpl; destruct (Nat.eq_dec b a); intuition.
Qed.

Lemma Countocc_length: forall s s',
(forall x, count_occ Nat.eq_dec s x  = count_occ Nat.eq_dec s' x) ->
(length s = length s').
Proof.

intro; induction s; intros; simpl; destruct s'; simpl; intuition.
{
  specialize (H n); simpl in H.
  destruct (Nat.eq_dec); intuition.
}{
  specialize (H a); simpl in H.
  destruct (Nat.eq_dec); intuition.
}
apply eq_S; destruct (Nat.eq_dec a n).
{
  apply IHs; intros.
  specialize (H x); simpl in H.
  destruct (Nat.eq_dec);
  destruct (Nat.eq_dec);intuition.
}

assert (length s = length (sa (n::s') a)).
{
  apply IHs; intros.
  destruct (Nat.eq_dec a x); subst.
    specialize (H x).
    apply eq_add_S.
    rewrite <- sa_countocc_eq.
      rewrite count_occ_cons_eq in H; auto.
    eapply count_occ_In.
    rewrite <- H.
    rewrite count_occ_cons_eq; lia.
  rewrite <- sa_countocc_neq; auto.
    specialize (H x).
    rewrite count_occ_cons_neq in H; auto.
  eapply count_occ_In.
  rewrite <- H.
  rewrite count_occ_cons_eq; lia.
}

simpl in H0.
destruct (Nat.eq_dec); intuition.
simpl in H0; rewrite H0.
symmetry; apply sa_length.
eapply count_occ_In.
erewrite <- count_occ_cons_neq.
  rewrite <- H.
  rewrite count_occ_cons_eq; lia.
intuition.
Qed.

(** ** MaxBinValue ***)

Lemma MaxBinValue_ge: forall s e, In e s -> e <= MaxBinValue s.
Proof.

intros; induction s.
  apply in_nil in H; destruct H.
destruct (Nat.eq_dec e a).
  rewrite e0; auto. apply le_max_l.
apply in_inv in H.
destruct H; intuition.
eapply Nat.le_trans.
  apply H0; eapply H.
simpl; auto with arith.
Qed.

Lemma MaxBinValue_in: forall x s, In (MaxBinValue (x::s)) (x::s).
Proof.
intros x s. induction s; simpl in *.
  left; rewrite max_0_r; auto.
destruct (Max.max_dec a (MaxBinValue s)); rewrite e.
  destruct (Max.max_dec x a); auto.
intuition.
Qed.

Lemma MaxBinValue_order: forall s s', (forall x, In x s <-> In x s') ->
MaxBinValue s = MaxBinValue s'.
Proof.
intro.
induction s; intros.
  destruct s'; simpl; auto.
  destruct (H n). eapply in_nil in H1; intuition.

apply Nat.le_antisymm.
  apply MaxBinValue_ge. apply H. apply MaxBinValue_in.
destruct s'.
  auto with arith.
apply MaxBinValue_ge. apply H. apply MaxBinValue_in.
Qed.


Lemma BubSortMaxValue: forall s , MaxBinValue (BubbleSort s) = MaxBinValue s.
Proof.
intros.
apply MaxBinValue_order.
apply Countocc_sound.
apply BubSort_countocc.
Qed.


Lemma FirstBin_MaxBin: forall St, FirstBinTooHigh St = true  -> MaxBinTooHigh St = true.
Proof.
intros; destruct St; simpl in *; intuition.
unfold MaxBinTooHigh.
apply leb_complete in H; apply leb_correct.
eapply le_trans. apply H.
apply MaxBinValue_ge.
intuition.
Qed.


(** ** AddToBin ***)

Lemma AddToBin_cons: forall x s e b, AddToBin (x::s) e (S b) = x::(AddToBin s e b).
Proof.
intro; induction s; intros; auto.
Qed.

Lemma AddToBin_length:  forall s b e, b<m -> (length s) <= m -> length (AddToBin s e b) <= m .
Proof.
intros s; revert m Posm.
induction s; intros;simpl. lia.
simpl in H0.
destruct b; simpl; auto.
destruct m; auto.
  lia.
apply le_n_S.
apply IHs; lia.
Qed.

Lemma AddToBin_countocc_one: forall s  b e a,
nth_error s b = Some a -> e<>0 ->
count_occ Nat.eq_dec (AddToBin s e b) (a+e) = S(count_occ Nat.eq_dec s (a+e)).
Proof.

intro; induction s; intros.
  eapply nth_error_In in H; inversion H.
induction b;simpl.
  destruct (Nat.eq_dec (a+e) (a0+e)); intuition;
  destruct (Nat.eq_dec (a) (a0+e)); intuition;
  simpl in H; inversion H; intuition.
destruct (Nat.eq_dec (a) (a0+e)); intuition.
Qed.

Lemma AddToBin_countocc_minus: forall s  b e a,
nth_error s b = Some a -> e<>0 ->
(count_occ Nat.eq_dec (AddToBin s e b) (a)) = (count_occ Nat.eq_dec s (a))-1.
Proof.

intro; induction s; intros.
  eapply nth_error_In in H; inversion H.
induction b;simpl.
  destruct (Nat.eq_dec (a+e) (a0)); intuition;
  destruct (Nat.eq_dec (a) (a0)); intuition;
  simpl in H; inversion H; intuition.
destruct (Nat.eq_dec (a) (a0)); intuition.
rewrite IHs; auto.
assert(count_occ Nat.eq_dec s a0 >0).
  simpl in H; apply count_occ_In; eapply nth_error_In; eauto.
lia.
Qed.

Lemma AddToBin_countocc_neq: forall s  b e a x,
nth_error s b = Some a -> x <> a+e -> x <> a ->
count_occ Nat.eq_dec (AddToBin s e b) (x) = (count_occ Nat.eq_dec s (x)).
Proof.

intro; induction s; intros.
  eapply nth_error_In in H. inversion H.
induction b; simpl; simpl in H.
  destruct (Nat.eq_dec (a+e) (x)); intuition;
  destruct (Nat.eq_dec (a) (x)); intuition; inversion H; intuition.
destruct (Nat.eq_dec (a) (x)); intuition.
apply eq_S; eapply IHs; eauto.
eapply IHs; eauto.
Qed.

Lemma AddToBin_countocc_0: forall s  b , nth_error s b <> None -> AddToBin s 0 b = s.
intro; induction s; intros.
Proof.

apply nth_error_Some in H.
  simpl in H; lia.
simpl; destruct b.
  assert (a+0=a); auto.
  rewrite H0; auto.
rewrite IHs; auto.
Qed.

Lemma  AddToBin_overflow: forall s b e,
length s <= b -> AddToBin s e b = s++[e].
Proof.
intro; induction s; intros; simpl; auto.
destruct b.
  inversion H.
rewrite IHs; intuition.
Qed.


Lemma AddToBin_countocc_in: forall s s' b,
(forall x, count_occ Nat.eq_dec s x  = count_occ Nat.eq_dec s' x) ->
b<length s -> exists b', (b'< length s') /\  
(forall x e, count_occ Nat.eq_dec (AddToBin s e b) x 
           = count_occ Nat.eq_dec (AddToBin s' e b') x).
Proof.


intros s; induction s; intros.
  inversion H0.
destruct b.
{
  induction s'.
    simpl in H; specialize (H a).
    destruct (Nat.eq_dec a a); lia.
  destruct (Nat.eq_dec a a0).
  {
    subst; exists 0.
    split.
      simpl; auto with arith.
    intros;simpl.
    specialize (H x); simpl in H.
    destruct (Nat.eq_dec a0 x);
    try apply eq_add_S in H;
    rewrite H; auto.
  }
  (* a <> a0 *)
  assert (exists p, nth_error  s' p = Some a).
    apply In_nth_error; eapply count_occ_In.
    simpl in H; specialize (H a).
    destruct (Nat.eq_dec a a);
    destruct (Nat.eq_dec a0 a);
    try erewrite <- H; try lia.  

  destruct H1.
  exists (S x); split.
    assert (Some a <> None) by try congruence.
    rewrite <- H1 in H2.
    apply nth_error_Some in H2; simpl; lia.

  intros; simpl.
  destruct (Nat.eq_dec (a+e) x0).
  {
    destruct (Nat.eq_dec a0 x0); subst.
      rewrite <- count_occ_cons_neq with (x:=a); try lia.
      rewrite H.
      apply eq_S.
      rewrite count_occ_cons_eq; auto.
      erewrite AddToBin_countocc_one; intuition.

    destruct e.

      rewrite AddToBin_countocc_0; [|congruence].
        erewrite <- count_occ_cons_eq; auto.
        rewrite <- plus_n_O.
        rewrite H.
        apply count_occ_cons_neq; auto.

    erewrite AddToBin_countocc_one; intuition.
    apply eq_S.
    erewrite <- count_occ_cons_neq.
      symmetry;erewrite <- count_occ_cons_neq. 
        eauto.
      all: intuition. 
   }
  
  (* a+e <> x0 *)
  destruct (Nat.eq_dec a0 x0); subst.
  {
    destruct e.
      rewrite AddToBin_countocc_0; try congruence.
      erewrite <- count_occ_cons_eq; auto.
      erewrite <- count_occ_cons_neq; intuition.

    erewrite AddToBin_countocc_neq.
      erewrite <- count_occ_cons_eq; auto.
      erewrite <- count_occ_cons_neq; intuition.
    eauto. all: intuition.
  }
  
  (* a0 <> x0 *)
  destruct (Nat.eq_dec x0 a); subst.
  {
    assert (e>0) by lia.
    erewrite AddToBin_countocc_minus; intuition.
    apply eq_add_S.
    erewrite <- count_occ_cons_eq; try trivial.
    rewrite H.
    erewrite count_occ_cons_neq; intuition.
    assert (count_occ Nat.eq_dec s' a >0); try lia.
      apply count_occ_In; eapply nth_error_In; eauto.
  }
  erewrite AddToBin_countocc_neq.
    erewrite <- count_occ_cons_neq.
      symmetry; erewrite <- count_occ_cons_neq; intuition.
    all: eauto.
}


(* b>0 **)

destruct s'.
  simpl in H; specialize (H a).
  destruct (Nat.eq_dec); lia.

simpl in H0; destruct (Nat.eq_dec a n); subst.
{
  assert (forall x : nat, count_occ Nat.eq_dec s x = count_occ Nat.eq_dec s' x).
  {
    intros.
    destruct (Nat.eq_dec n x); subst.
      apply eq_add_S.
      erewrite <- count_occ_cons_eq.
      erewrite <- count_occ_cons_eq.
      all: auto.

    erewrite <- count_occ_cons_neq.
    symmetry; erewrite <- count_occ_cons_neq. 
    all: auto.
  }

  apply IHs with s' b in H1; auto with arith.
  destruct H1.
  exists (S x).
  split; simpl; intuition.
  destruct (Nat.eq_dec); intuition.
}



(* a <> n *)

assert (forall x : nat, count_occ Nat.eq_dec s x = count_occ Nat.eq_dec (sa (n::s') a) x).

{
  intros.
  destruct (Nat.eq_dec n x); subst.
  {
    apply eq_add_S.
    erewrite <- count_occ_cons_neq with (x:=a); auto.
      rewrite sa_cons_neq; auto.
      rewrite H .
      simpl. destruct (Nat.eq_dec); auto.
        rewrite <- sa_countocc_neq; auto.
        eapply count_occ_In.
        erewrite <- count_occ_cons_neq with (x:=x); auto.
          rewrite <- H. simpl. destruct (Nat.eq_dec); lia.
  }

  destruct (Nat.eq_dec a x); subst.
  {
    apply eq_add_S.
    erewrite <- count_occ_cons_eq; auto.
      rewrite sa_cons_neq; auto.
      rewrite H .
      simpl. destruct (Nat.eq_dec);  intuition.
      rewrite <- sa_countocc_eq; auto.
      eapply count_occ_In.
      erewrite <- count_occ_cons_neq.
      rewrite <- H. simpl. destruct (Nat.eq_dec); lia.
    auto.
  }

  erewrite <- count_occ_cons_neq.
    rewrite sa_cons_neq; auto.
    rewrite H .
    simpl. destruct (Nat.eq_dec);  intuition.
    rewrite <- sa_countocc_neq; auto.
    eapply count_occ_In.
    erewrite <- count_occ_cons_neq.
    rewrite <- H. simpl. destruct (Nat.eq_dec); lia.
  all: auto.
}

apply IHs with (sa (n::s') a) b in H1; auto with arith.
do 2 destruct H1.
revert H1; induction x; intros.
{
  exists 0.
  split.
    simpl; auto with arith.
  intros.
  rewrite AddToBin_cons; simpl.
  rewrite H2.
  rewrite sa_cons_neq; auto.
  simpl; destruct (Nat.eq_dec).

  {
    destruct (Nat.eq_dec);
      subst;
      rewrite <- sa_countocc_eq; auto;
      eapply count_occ_In;
      erewrite <- count_occ_cons_neq.
       1,3: rewrite <- H; simpl; destruct (Nat.eq_dec); lia.
       all: intuition.
  }

  rewrite <- sa_countocc_neq; auto.
  eapply count_occ_In.
  erewrite <- count_occ_cons_neq.
    rewrite <- H; simpl; destruct (Nat.eq_dec); lia.
    intuition.
}


  (** induction x *)

clear IHx.
assert (nth_error s b <> None).
  apply nth_error_Some; lia.
assert (exists c, nth_error s b = Some c).
  destruct (nth_error s b); auto. 
  exists n1; auto. destruct H3; auto.

destruct H4.
assert (exists c, nth_error (n::s') c = Some x0). 
  eapply nth_error_In in H4.
  eapply count_occ_In in H4.
  eapply In_nth_error.
  eapply count_occ_In.
  erewrite <- H. 
  simpl; destruct (Nat.eq_dec); eauto.

destruct H5.
exists x1.
split.
  apply nth_error_Some.
  subst; congruence.

intros.
destruct (Nat.eq_dec x0 x2); destruct (Nat.eq_dec (x0+e) x2); subst.

  assert (e=0);subst. destruct e; auto; lia.
  repeat rewrite AddToBin_countocc_0. 
    auto. congruence. simpl; congruence.

  erewrite AddToBin_countocc_minus; intuition.
  erewrite AddToBin_countocc_minus; intuition.

  erewrite AddToBin_countocc_one; intuition.
  erewrite AddToBin_countocc_one; intuition.

rewrite AddToBin_countocc_neq with (a:=x0); auto.
rewrite AddToBin_countocc_neq with (a:=x0); auto.
Qed.



(* BinSum *)

Lemma BinSum_sa: forall l a, In a l -> BinSum l = a + BinSum (sa l a).
Proof.

intro; induction l; intros; simpl.
  auto.
destruct eq_dec; simpl.
  auto.
apply in_inv in H.
destruct H; auto.
eapply IHl in H.
lia.
Qed.

Lemma Countocc_binsum: forall l l', 
(forall e, count_occ Nat.eq_dec l e <= count_occ Nat.eq_dec l' e) ->
BinSum l <= BinSum l'.
Proof.

intro; induction l; intros.
  simpl; auto.
simpl.
specialize (IHl (sa l' a)).
assert (In a l').
{
  eapply count_occ_In with eq_dec.
  specialize (H a). simpl in H. destruct eq_dec; try intuition.
}
pose proof H0.
apply BinSum_sa in H0. rewrite H0.
apply plus_le_compat_l.
apply IHl; intros.
specialize (H e).
destruct (Nat.eq_dec a e).
{
  subst.
  apply le_S_n.
  rewrite <- sa_countocc_eq; auto.
  simpl in H.
  destruct eq_dec; auto. 
}
{
  rewrite <- sa_countocc_neq; auto.
  erewrite <- count_occ_cons_neq; eauto.
}
Qed.

Lemma MaxBinSum_ntimes: forall l, BinSum (concat l) <= (length l)*(MaxBinSum l).
Proof.

intro; induction l.
  simpl; auto.
simpl.
apply Nat.le_trans with (BinSum a + length l * MaxBinSum l).
  induction a; simpl; lia.
assert (BinSum a <= max (BinSum a) (MaxBinSum l)).
apply Max.le_max_l.
assert (MaxBinSum l <= max (BinSum a) (MaxBinSum l)).
apply Max.le_max_r.
eapply mult_le_compat_l in H0.
eapply plus_le_compat; eauto.
Qed.


Lemma SolPack_BinSum: forall l P, SolutionPacking l P -> BinSum l <= m* g.
Proof.

intros. destruct H. destruct H0.
apply Nat.le_trans with (BinSum (concat P)).
  apply Countocc_binsum; auto.
etransitivity.
  apply MaxBinSum_ntimes.
  subst.
  eapply mult_le_compat_l; auto.
Qed.



Lemma OnlineInfeasible_length: forall X l St, OnlineInfeasible X l St -> (BinSum l) <= m*g.
Proof using All.
intro; induction X; intros.
{
  inversion H.
    destruct H1; eapply SolPack_BinSum; eauto.
    destruct H0; eapply SolPack_BinSum; eauto.
}
{
  inversion H.
    destruct H1; eapply SolPack_BinSum; eauto.
  destruct H2.
  specialize (H2 0).
  apply H2 in Posm.
  apply IHX in Posm.
  simpl in Posm.
  lia.
}
Qed.


(* OnlineInfeasible *)

Lemma OnlineInfeasible_equiv: forall X l St, (X > m*g+1 - BinSum l) -> (OnlineInfeasible X l St) -> OnlineInfeasible_simpl X l St.
Proof using All.
intro; induction X; intros.
  inversion H.
inversion H0.
  econstructor; auto.
apply Deadend_simpl; auto.
destruct H3. exists x; intros.
apply H3 in H6.
eapply IHX; auto.
simpl.
apply OnlineInfeasible_length in H0.
lia.
Qed.


Lemma OnlineInfeasible_rev: forall X l St, (OnlineInfeasible_simpl X l St) -> OnlineInfeasible X l St.
Proof.
intro; induction X; intros.
  inversion H.
  econstructor; auto.
inversion H.
  econstructor; auto.
apply Deadend; auto.
destruct H2. exists x; intros.
apply H2 in H5; auto.
Qed.


Lemma OI_countocc: forall X l s s', 
(forall x, count_occ Nat.eq_dec s x = count_occ Nat.eq_dec  s' x) ->
OnlineInfeasible X l s' -> OnlineInfeasible X l s. 
Proof.

intros X; induction X; intros.
  apply NoMorePieces;inversion H0; auto.

inversion H0.
{
  apply Overflow; auto.
    assert (MaxBinValue s = MaxBinValue s'); try lia.
      apply MaxBinValue_order; apply Countocc_sound; auto.
}

destruct H1; auto. clear l0 St H4 H5.
assert (length s = length s'). eapply Countocc_length; auto.
assert (length s <= m). rewrite H1; auto.

apply Deadend; auto.
destruct H3.
exists x; intros.

assert(count_occ_app: forall s0 x e, count_occ Nat.eq_dec (s0++[x]) e = 
       count_occ Nat.eq_dec s0 e + count_occ Nat.eq_dec [x] e).
{
  intro; induction s0; intros; simpl; auto.
  simpl in IHs0.
  destruct (Nat.eq_dec a e); destruct (Nat.eq_dec x e);simpl;
  rewrite IHs0;destruct (Nat.eq_dec x e); intuition.
}

destruct (le_lt_dec  (length s) b).
{
  pose proof l0.
  eapply AddToBin_overflow  in l0.
  erewrite l0.
  specialize (H3 b).
  rewrite AddToBin_overflow in H3; intuition.
    eapply IHX with  (s'++[S x]); auto.
    intro; rewrite count_occ_app; rewrite count_occ_app; simpl.
    rewrite H; auto.
}

eapply AddToBin_countocc_in with s s' b in H; auto.
do 2 destruct H.
eapply IHX; [ eauto | apply H3; lia ].
Qed.



Lemma OI_countocc_list: forall X l s l', 
(forall x, count_occ Nat.eq_dec l x = count_occ Nat.eq_dec  l' x) ->
OnlineInfeasible X l' s -> OnlineInfeasible X l s.
Proof.
intro; induction X; intros.
{
  apply NoMorePieces.
  eapply SolPackCountocc_ex with (l:=l'); auto.
  inversion H0; auto.
}

inversion H0.
{
  eapply Overflow; auto.
  eapply SolPackCountocc_ex with (l:=l'); auto.
}
{
  eapply Deadend; auto.
  destruct H3.
  exists x; intros.
  eapply IHX; intros.
    apply Countocc_cons; apply H.
  eauto.
}
Qed. 
 


(** * Definition of a tree, witness of a solution **)



(* 
meaning of 
- nodeI St e F: under the bin heights given by St, adding the element e to any bin either exceeds the height or leads to a state described in F, or is present in a companion record.
- nodeL St el P: under the bin heights given by St, adding the elements el leads to one high bin. P is a valid packing of the elements which lead to this state. 

forest is a list of trees and of states of bins (heights).
*)
Inductive tree  :=
  | nodeI : BinLoads -> nat  -> forest -> tree
  | nodeL : BinLoads -> list nat -> BinsExtended -> tree

with forest :=
  | leaf :  forest
  | cons : tree -> forest -> forest
.

(* shorter names as they will be used in the input files *)
Inductive treeN  :=
  | nd : BinLoadsN -> elt  -> forestN -> treeN
  | lf : BinLoadsN -> list elt -> BinsExtendedN -> treeN

with forestN :=
  | leafN :  forestN
  | consN : treeN -> forestN -> forestN
.


(* induction scheme *)
Scheme tree_forest_ind := Induction for tree Sort Prop
with forest_tree_ind   := Induction for forest Sort Prop.
Combined Scheme tree_forest_mutind from tree_forest_ind, forest_tree_ind.

Scheme tree_forestN_ind := Induction for treeN Sort Prop
with forest_treeN_ind   := Induction for forestN Sort Prop.
Combined Scheme tree_forestN_mutind from tree_forestN_ind, forest_treeN_ind.




(** ** Functions defined on a tree **)

(* Record: list of couples (list of elements,tree). The state of the tree corresponds to the elements of the list. Each tree can point to records of this list. *)
Inductive record := rec: list nat ->  tree -> record.
Definition Record := list record.

Inductive recordN := recN: list elt ->  treeN -> recordN.
Definition RecordN := list recordN.

Fixpoint to_tree_nat T := match T with
| nd St e F   => nodeI (List_ofN St) (nat_of_N e) (to_forest_nat F)
| lf St el P  => nodeL (List_ofN St) (List_ofN el) (LList_ofN P)
end
with
to_forest_nat F := match F with
| leafN => leaf
| consN T F => cons (to_tree_nat T) (to_forest_nat F)
end.

Fixpoint to_Record_nat R:= match R with
| nil => nil
| (recN L T)::X => (rec (List_ofN L) (to_tree_nat T))::(to_Record_nat X)
end.




Definition GetState T := match T with
| nodeI St _ _ => St
| nodeL St _ _ => St
end.
Definition GetStateN T := match T with
| nd St _ _ => St
| lf St _ _ => St
end.


Lemma GetStateN_eq : forall T, GetStateN T = List_toN (GetState (to_tree_nat T)).
Proof.
destruct T; simpl; intros;
autorewrite with Nnat; auto.
Qed.

Lemma GetStateN2_eq: forall x,  GetState (to_tree_nat x) = List_ofN (GetStateN x).
Proof.
intros. destruct x; simpl; auto.
Qed.


Definition GetElt T := match T with
| nodeI _ e _ => e
| nodeL _ (e::r) _ => e
| nodeL _ [] _ => 0
end.
Definition GetEltN T := match T with
| nd _ e _ => e
| lf _ (e::r) _ => e
| lf _ [] _ => 0%N
end.


Lemma GetEltN_eq : forall T, GetEltN T = N_of_nat (GetElt (to_tree_nat T)).
Proof.
destruct T; simpl; intros.
autorewrite with Nnat; auto.
destruct l; simpl; autorewrite with Nnat; auto.
Qed.
Hint Rewrite GetStateN_eq GetStateN2_eq GetEltN_eq : Nnat.

(* checks that St belongs to a tree in F *)
Fixpoint StateInForest_b (St: BinLoads) (F: forest) := match F with
| leaf       => false
| cons T F'  => (list_beq nat Nat.eqb (GetState T)  St) ||| StateInForest_b St F'
end.

Fixpoint StateInForest_bN (St: BinLoadsN) (F: forestN) := match F with
| leafN      => false
| consN T F' => (list_beq N N.eqb (GetStateN T)  St) ||| StateInForest_bN St F'
end.

Lemma List_beqN_eq: forall l l', list_beq N N.eqb l l' = list_beq nat Nat.eqb (List_ofN l) (List_ofN l').
Proof.
intros.
destruct (List_eq_dec l l').
+ pose proof e.
  eapply list_lb in e; try now apply N.eqb_eq.
  subst.
  unfold elt in e.
  rewrite e.
  symmetry.
  apply list_lb; try now apply eqb_eq. 
  auto.
+ etransitivity.
  eapply list_lbF in n; eauto; apply N.eqb_eq.
  apply List_inj in n.
  eapply list_lbF in n; eauto.
Qed.


Lemma StateInForest_b_eq: forall F St, StateInForest_bN St F = StateInForest_b (List_ofN St) (to_forest_nat F).
Proof.
induction F; intros; simpl; auto; rewrite <- IHF.
+ autorewrite with Nnat. rewrite List_ofto.
  rewrite List_beqN_eq. rewrite List_ofto; auto.
Qed.


(* Insert an element while keeping the list sorted *)
Fixpoint Insert_sorted x l : list nat :=
  match l with
  | nil => [x]
  | a::s => if (x <? a) then a::(Insert_sorted x s) else x::l
  end.
Fixpoint Insert_sortedN x l : list elt :=
  match l with
  | nil => [x]
  | a::s => if (x <? a)%N then a::(Insert_sortedN x s) else x::l
  end.


Lemma Insert_sorted_eq: forall l x, Insert_sortedN x l = List_toN (Insert_sorted (nat_of_N x) (List_ofN l)).
Proof.
induction l; intros.
  simpl; autorewrite with Nnat; auto. 
simpl.

rewrite  Nnat_sorder.
assert (forall y,  y= N.of_nat (N.to_nat y)); intros; autorewrite with Nnat; auto.
rewrite IHl.
destruct ((x<?a)%N).
all: simpl; autorewrite with Nnat; auto.
Qed.



Lemma Insert_countocc: forall l e x,  count_occ Nat.eq_dec  (Insert_sorted e l) x = count_occ Nat.eq_dec (e::l)  x.
Proof.
intro; induction l; intros; auto.
simpl. simpl in IHl.
destruct eq_dec; destruct eq_dec; destruct (e<?a); subst;
simpl; destruct eq_dec; intuition;
 try rewrite IHl; destruct eq_dec; intuition.
Qed.


(* Checks that any way to add the elements of el to the state St leads to a high bin *)

Fixpoint CheckEndTree (St: BinLoads) (el:list nat)   := match el with
| []   => FirstBinTooHigh St
| 0::r => false
| (S e)::r => (forallb (fun b => let S := BubbleSort (AddToBin St (S e) b) in
                        FirstBinTooHigh S ||| CheckEndTree S r )
                       (seq 0 m))
end.

Fixpoint CheckEndTreeN (St: BinLoadsN) (el:list elt)   := match el with
| []   => FirstBinTooHighN St
| (0%N)::r => false
| (N.pos e)::r => (forallb (fun b =>  let S := BubbleSortN (AddToBinN St (N.pos e) b) in
                   FirstBinTooHighN S ||| CheckEndTreeN S r ) 
                   (seq 0 m))
end.

Lemma CheckEndTree_OI: (forall el l St, (true = CheckEndTree St el ) 
            -> (length St <= m) 
            -> (exists P, SolutionPacking (el++l) P)
            -> forall X, OnlineInfeasible X l St).
Proof using All.
induction el; intros.
{
  apply Overflow; auto.
  apply leb_complete.
  apply FirstBin_MaxBin.
  auto.
}
destruct a; simpl in H.
  inversion H.
destruct X.
  apply NoMorePieces.
+ destruct H1. exists x.
  eapply Packing_concat; eauto.
+ eapply Deadend; auto.
  exists (a).
  intros.
  symmetry in H; eapply forallb_forall in H.
  {
    apply Bool.orb_true_iff in H; destruct H.
    + apply Overflow. 
      {
        apply FirstBin_MaxBin in H.
        rewrite <- BubSortMaxValue.
        eauto.
      }
      destruct H1.
      apply Packing_exch in H1. apply Packing_concat in H1. eauto.
    + eapply OI_countocc.
        intros; symmetry; apply BubSort_countocc.
      eapply IHel; auto.
        erewrite Countocc_length.
          apply AddToBin_length.
            apply H2.
             apply H0.
          apply BubSort_countocc.
      destruct H1.
      apply Packing_exch in H1.
      eauto.
  }
  apply in_seq; auto.
Qed.

Lemma CheckEndTree_eq: forall l St, CheckEndTreeN St l = true -> CheckEndTree (List_ofN St) (List_ofN l) = true.
Proof.
induction l; intros.
+ simpl in *. rewrite <- FirstBinTooHigh_eq; auto.
+ destruct a; simpl in *; auto.
  
  assert (nat_of_N (N.pos p) = Pos.to_nat p); auto.
  pose proof (Pos2Nat.is_pos p).
  destruct (Pos.to_nat p); intuition.
  rewrite <- H0.
  eapply forallb_forall; intros.
  eapply forallb_forall in H.
  -  rewrite FirstBinTooHigh_eq in H.
     rewrite BubbleSortN_eq in H. rewrite <- AddToBinN_eq in H.
     repeat rewrite List_ofto in H.
     apply Bool.orb_true_iff in H; apply Bool.orb_true_iff; destruct H.
     * left.  eauto.
     * right. eapply IHl in H.  rewrite List_ofto in H. eauto.
  - auto.
Qed.

(** * Main Function **)

(** 
  Arguments:
  - set of trees on which the function returns true (stored as a binary search tree for efficient queries)
  - current list of elements, sorted by largest element first
  - tree

  Behavior: 
   - on a leaf: check the packing is correct and the next states are infeasible 
   - on a node: check that adding e to any bin leads either to an infeasible state or a tree in the forest or in R 
                      && check that the trees in the forest return true.
                if there is no explicit child (i.e., all children are in R), check that there is a child node 
                      (when adding the element to the smallest bin) on which this function returns true, so there is a packing respecting g.
*)


Fixpoint CheckTree (R: M.t)  (l:list nat)  (T:tree) := match T with
| nodeI _ 0 _ => false
| nodeL _ [] _ => false

| nodeL St el P => 
  CheckEndTree St el &&& SolutionPacking_b  (el++l) P

| nodeI St (S e) F => let l' := Insert_sorted (S e) l in
  (forallb (fun b => let St' :=  BubbleSort (AddToBin St (S e) b) in
                 (FirstBinTooHigh St')
                 ||| (StateInForest_b St' F)
                 ||| (M.mem (List_toN St', List_toN l') R))
          (seq 0 m))
&&& 
(
(match F with
| leaf => M.mem (List_toN (BubbleSort (AddToBin St (S e) (m-1))), List_toN l') R
| _    => true
end)
&&&
CheckForest R l' F 
)
end
with
CheckForest (R: M.t)  (l: list nat)  (F: forest) := match F with
| leaf      => true
| cons T F' => (CheckTree R l T) &&& (CheckForest R l F')
end.





Fixpoint CheckTreeN (R: M.t)  (l:list elt)  (T:treeN) := match T with
| nd _ 0%N _ => false
| lf _ [] _ => false

| lf St el P => 
  CheckEndTreeN St (el) &&& SolutionPacking_bN  (el++l) P

| nd St (N.pos e) F =>  let l' := Insert_sortedN (N.pos e) l in
  (forallb
  (fun b => let St' :=  BubbleSortN (AddToBinN St (N.pos e) b) in
                 (FirstBinTooHighN St') 
                 ||| (StateInForest_bN St' F)
                 ||| (M.mem (St', l') R)
                 )
       (seq 0 m))
&&& (
(match F with
| leafN => M.mem ((BubbleSortN (AddToBinN St (N.pos e) (m-1))),  l') R
| _    => true
end)
&&&
CheckForestN R l' F 
)
end
with
CheckForestN (R: M.t)  (l: list elt)  (F: forestN) := match F with
| leafN      => true
| consN T F' => (CheckTreeN R l T) &&& (CheckForestN R l F')
end.



(* Check that each record in the list is true assuming the elements in R return true.
Each record can only use the records located sooner in the list.
Note that we will reverse the list before calling this function in the theorem Lower_bound_record. 
So in the list given to the theorem, the records can use the ones located later in the list. *)
Fixpoint CheckRecord (R:M.t) (L:Record) := match L with
| [] => (true, R)
| (rec l T):: L' => if (CheckTree R l T &&& (length (GetState T) <=? m)) then
                        CheckRecord ( M.add (List_toN (GetState T), List_toN l) R) L' 
                    else
                         (false, M.empty)
end.

Fixpoint CheckRecordN (R:M.t) (L:RecordN) := match L with
| [] => (true,R)
| (recN l T):: L' => if (CheckTreeN R l T &&& (length (GetStateN T) <=? m)) then 
                        CheckRecordN ( M.add (GetStateN T,l) R) L' 
                     else
                        (false,M.empty)
end.


Arguments CheckEndTree  : simpl never.
Arguments CheckEndTreeN : simpl never.
Arguments StateInForest_b : simpl never.
Arguments StateInForest_bN : simpl never.
Arguments CheckForest : simpl never.
Arguments CheckForestN : simpl never.
Arguments to_forest_nat : simpl never.


Lemma CheckTreeForest_eq:
(forall T l R, true = CheckTreeN R l T
            -> true = CheckTree R (List_ofN l) (to_tree_nat T) )
/\
(forall F l R, true = CheckForestN R l F
            -> true = CheckForest R (List_ofN l) (to_forest_nat F) ).
Proof.
apply tree_forestN_mutind; intros.
{
  destruct e; intuition.
  assert (nat_of_N (N.pos p) = Pos.to_nat p); auto.
  pose proof (Pos2Nat.is_pos p).

  simpl; simpl in H0; destruct (Pos.to_nat p); try lia;
       apply Bool.andb_true_eq in H0; destruct H0; rewrite <- H1.
  symmetry; apply Bool.andb_true_iff; split.
  apply forallb_forall; intros. 
  symmetry in H0; eapply forallb_forall in H0.
  2: eauto.
  rewrite FirstBinTooHigh_eq in H0; repeat rewrite BubbleSortN_eq in H0;
        rewrite <- AddToBinN_eq in H0; rewrite  StateInForest_b_eq in H0;
        repeat rewrite List_ofto in H0; repeat rewrite List_toof in H4;
        rewrite Insert_sorted_eq in H0.
  auto.
  apply Bool.andb_true_eq in H3; destruct H3.
  apply Bool.andb_true_iff; split.
  + destruct f; simpl; auto.
    rewrite <- AddToBinN_eq in H3.
    rewrite  BubbleSortN_eq in H3.
    rewrite  Insert_sorted_eq in H3.
    rewrite List_ofto in H3.
    auto.
  + apply H in H4;
        rewrite Insert_sorted_eq in H4;
        rewrite List_ofto in H4;
        auto.
}
{
  destruct l.
     simpl; auto.
  simpl; simpl in H.
  apply Bool.andb_true_eq in H; destruct H.
  symmetry in H0; eapply SolutionPacking_b_eq in H0.
  symmetry in H; apply CheckEndTree_eq in H.
  symmetry; apply Bool.andb_true_iff.
  simpl in H0; rewrite List_concat in H0.
  intuition.
}
{ auto. }
{
  apply Bool.andb_true_eq in H1; destruct H1.
  symmetry; apply <- Bool.andb_true_iff; split; symmetry; auto.
}
Qed.



Lemma CheckRecord_eq: forall L R R', (true,R') = CheckRecordN R L -> (true,R') = CheckRecord R (to_Record_nat L). 
Proof.
intro; induction L; intros.
  simpl; auto.
destruct a; simpl in *.
case_eq (CheckTreeN R l t0 &&& (length (GetStateN t0) <=? m)); intros; rewrite H0 in H;
case_eq (CheckTree R (List_ofN l) (to_tree_nat t0) &&& (length (GetState (to_tree_nat t0)) <=? m)); intros; intuition.
+ eapply IHL.
  rewrite GetStateN_eq in H. rewrite List_iff; auto.
+ symmetry in H0; apply Bool.andb_true_eq in H0; destruct H0.
  apply (proj1 CheckTreeForest_eq) in H0; rewrite <- H0 in H1.
  rewrite GetStateN_eq in H2. unfold List_toN in H2. rewrite map_length in H2. rewrite <- H2 in H1.
  simpl in H1. inversion H1.
+ inversion H.
Qed.


 


(** * Correctness of CheckTree **) 



Ltac existpackinc H :=  match type of H with
           | ex (fun x => _) => let c:= fresh x in
    destruct H as [c]; eapply Packing_included in H; exists c; auto
end.
 

(* if CheckTree returns true and the records are consistent, there exists a packing containing the new element *)
Lemma CheckTreeForest_Packing:
(forall T l R, true = CheckTree R l T
            -> (forall St l', M.mem (List_toN St, List_toN l') R = true  -> exists P, SolutionPacking l' P)
            -> exists P, SolutionPacking ((GetElt T)::l) P )
/\
(forall F l R, true = CheckForest R l F
            -> F <> leaf 
            -> (forall St l', M.mem (List_toN St,List_toN l') R = true  -> exists P, SolutionPacking l' P)
            -> exists P, SolutionPacking l P ).
Proof.
apply tree_forest_mutind; intros; try congruence.
{
  destruct n.
    inversion H0.
  destruct f.
  + simpl in H0.
    apply Bool.andb_true_eq in H0; destruct H0.
    apply Bool.andb_true_eq in H2; destruct H2.
    symmetry in H2. apply H1 in H2.
    simpl.
    eapply SolPackCountocc_ex;[ apply Insert_countocc|auto].
  + simpl in H0; apply Bool.andb_true_eq in H0.
    eapply SolPackCountocc_ex; [eapply Insert_countocc|].
    eapply H; intuition; try congruence; eauto.
}{
  destruct l; simpl in H.
    inversion H.
   exists b0; simpl.
   eapply Packing_concat.
   apply Packing_exch.
   apply SolPackbool.
   apply Bool.andb_true_eq in H; intuition; eauto.
}{
  simpl in H1; apply Bool.andb_true_eq in H1; destruct H1.
  apply H in H1; auto; existpackinc H1.
}
Qed.


(* if CheckTree returns true and the records are consistent, we can prove OnlineInfeasible *)
Lemma CheckTree_OnlineInfeasible: 
(forall T l R, (true = CheckTree R l T ) 
            -> (forall St l', M.mem (List_toN St,List_toN l') R = true  -> forall X, OnlineInfeasible X l' St)
            -> (length (GetState T) <= m) 
            -> forall X, OnlineInfeasible X l (GetState T))
/\
(forall F s l R, (true = CheckForest R l (F) )
              -> (forall St l', true = M.mem (List_toN St,List_toN l') R  -> forall X, OnlineInfeasible X l' St)
              -> (true = StateInForest_b s F) 
              -> (length s <= m) 
              -> forall X, OnlineInfeasible X l s ).
Proof using All.
apply tree_forest_mutind; intros; try now inversion H1.

destruct X.
{
  apply NoMorePieces; auto.
  eapply CheckTreeForest_Packing in H0.
    existpackinc H0.
  intros; apply H1 with (X:=0) in H4; inversion H4; auto.
}

{
  destruct n.
    inversion H0.
  
   assert (IH: forall b1, b1<m -> 0=0 -> idb  (FirstBinTooHigh (BubbleSort (AddToBin b (S n) b1)) || StateInForest_b (BubbleSort (AddToBin b (S n) b1)) (f)
  || M.mem    (List_toN (BubbleSort (AddToBin b (S n) b1)),
              List_toN (Insert_sorted (S n) l)) R) = true
          -> OnlineInfeasible X ((S n) :: l) (AddToBin b (S n) b1)).
    {
      pose proof H2.
      intros;  apply Bool.orb_true_iff in H6; destruct H6. 
      apply Bool.orb_true_iff in H6; destruct H6.  {
          apply Overflow.
          {
            rewrite <- BubSortMaxValue.
            now apply FirstBin_MaxBin in H6; auto.
          }
          apply CheckTreeForest_Packing in H0;auto;intros.
          apply H1 with (X:=O)in H8; inversion H8; auto.
        }{
          eapply OI_countocc.
            intro; rewrite <- BubSort_countocc;  auto.
          eapply OI_countocc_list.
            intro; symmetry; eapply Insert_countocc.
          eapply H.
            + simpl in H0.
              destruct f; try congruence;
              apply Bool.andb_true_eq in H0;
              destruct H0; try apply Insert_countocc; eauto; intuition.
            + eauto.
            + auto.
            + erewrite Countocc_length.
                eapply AddToBin_length; eauto.
              eapply BubSort_countocc.
        }{
          eapply OI_countocc.
          intros; rewrite BubSort_countocc; auto.
          eapply OI_countocc_list.
          intros; rewrite Insert_countocc; auto.
          eapply H1; eauto.
       }  }

    
  all: eapply Deadend; auto; exists n; simpl; intros.
  all: inversion H0; apply Bool.andb_true_eq in H5; destruct H5; symmetry in H4;
       eapply forallb_forall in H4.
  2: apply in_seq; split; [lia | eapply H3].
  apply IH; intuition; inversion H6.
}
{
  destruct l.
    inversion H.
  simpl. unfold CheckTree in H. apply Bool.andb_true_eq in H.
  destruct H.
  apply SolPackbool in H2.
  eapply CheckEndTree_OI; eauto.
}  
{
  simpl in H3; symmetry in H3; apply Bool.orb_true_iff in H3.
  simpl in H1; apply Bool.andb_true_eq in H1; destruct H1.
  destruct H3.
    apply list_bl in H3; auto; subst.
      eapply H; intuition; eauto; congruence.
  eapply H0; intuition; eauto.
}
Qed.

(** * Wrappers to use the main results above **)

(* if CheckRecord is true and the records assumed are consistent, we get OnlineInfeasible for any state in the record *)
Lemma CheckRecord_OI: forall R1 R0 Map MapR  l T, (true,MapR) = CheckRecord Map ((R0++R1))  
                             -> In (rec l T) (R1)
                             -> (forall St l', M.mem (List_toN St, List_toN l') Map = true  
                                         -> forall X, OnlineInfeasible X l' St
                                )
                             -> forall X, OnlineInfeasible X l (GetState T).
Proof using All.
destruct CheckTree_OnlineInfeasible. clear H0.
intro; induction R1. intros; inversion H1.

destruct a;
intro; induction R0; intros;
pose proof H0; [| destruct a];
simpl in H0.

{
  case_eq (CheckTree Map l t0 &&& (length (GetState t0) <=? m)); intros;
  rewrite H4 in H0; symmetry in H4; try apply Bool.andb_true_eq in H4.
  + destruct H4.
    inversion H1.
    - inversion H6; subst; eauto.
    - eapply IHR1  with (R0:=[rec l t0]); eauto.
  + inversion H0.
}

{ 
  case_eq (CheckTree Map l1 t1 &&& (length (GetState t1) <=? m)); intros;
  rewrite H4 in H0.
  +  
    inversion H3.
    rewrite H4 in H6.
    eapply IHR0; eauto.
    clear  IHR1 IHR0.
    intros.
    apply M.mem_spec in H5; apply M.add_spec in H5.
    destruct H5.
      - inversion H5.
        inversion H7.
        inversion H8.
        pose proof (List_ofto St). rewrite H10 in H9. rewrite List_ofto in H9.
        pose proof (List_ofto l'). rewrite H11 in H12. rewrite List_ofto in H12. subst.
        symmetry in H4; apply Bool.andb_true_eq in H4; destruct H4.
        eapply H; eauto.
      - eapply H2.
        now apply M.mem_spec in H5.
  + inversion H0.

}
Qed.

Lemma CheckRecord_Map: forall R Map MapR b, (b,MapR) = CheckRecord Map ((R))  
                             -> (forall St l', M.mem (List_toN St, List_toN l') Map = true  
                                         -> forall X, OnlineInfeasible X l' St
                                )
                             -> (forall St l', M.mem (List_toN St, List_toN l') MapR = true  
                                         -> forall X, OnlineInfeasible X l' St
                                ).
Proof using All.
intro; induction R; intros.
   inversion H. subst; auto.
inversion H; destruct a.
case_eq (CheckTree Map l t0 &&& (length (GetState t0) <=? m)); intros; rewrite H2 in H3.
symmetry in H2; apply Bool.andb_true_eq in H2; destruct H2.
- eapply IHR. 1,3: eauto. intros.
  apply M.mem_spec in H5; apply M.add_spec in H5. destruct H5.
  + inversion H5. inversion H6; inversion H7.
    pose proof (List_ofto St0). rewrite H9 in H8. rewrite List_ofto in H8.
    pose proof (List_ofto l'0). rewrite H10 in H11. rewrite List_ofto in H11. subst.
    eapply (proj1 CheckTree_OnlineInfeasible); eauto.
  + apply H0.
    apply M.mem_spec; auto.
- inversion H3; subst.
  now apply M.mem_spec in H1.
Qed.
  
  
Lemma CheckRecord_MapN: forall b R Map MapR, (b,MapR) = CheckRecordN Map ((R))  
                             -> (forall St l', M.mem (List_toN St, List_toN l') Map = true  
                                         -> forall X, OnlineInfeasible X l' St
                                )
                             -> (forall St l', M.mem (List_toN St, List_toN l') MapR = true  
                                         -> forall X, OnlineInfeasible X l' St
                                ).
Proof using All.
intro. destruct b. intros; eapply CheckRecord_Map; try apply CheckRecord_eq; eauto.
induction R; intros.
  simpl in H; inversion H.
simpl in H; inversion H; destruct a.
case_eq (CheckTreeN Map l t0 &&& (length (GetStateN t0) <=? m)); intros; rewrite H2 in H3.
+ eapply IHR. 1,3: eauto. intros.
  apply M.mem_spec in H4; apply M.add_spec in H4. destruct H4.
  * inversion H4. inversion H6; inversion H5. simpl in H7.
    symmetry in H2; apply Bool.andb_true_eq in H2; destruct H2.
    eapply (proj1 CheckTreeForest_eq) in H2.
    eapply (proj1 CheckTree_OnlineInfeasible) in H2.
    - rewrite  GetStateN2_eq in H2.
      rewrite <- H7 in H2. rewrite <- H9 in H2. do 2 rewrite List_ofto in H2.
      eauto.
    - auto.
    - rewrite GetStateN_eq in H8.
      unfold List_toN in H8.
      rewrite map_length in H8.
      auto.
  * apply H0.
    apply M.mem_spec; auto.
+ inversion H3; subst.
  now apply M.mem_spec in H1.
Qed.




Definition Iszero_bN l := (length(l) <=? m) &&& forallb (fun x => (nat_of_N x=?0)) l.
Definition Iszero_b l := (length(l) <=? m) &&& forallb (fun x => (x=?0)) l.

Lemma Iszero_sound : forall l, true = Iszero_b l -> Iszero l.
Proof.
intros; apply Bool.andb_true_eq in H; destruct H.
split; auto; symmetry in H0.
intros; eapply forallb_forall in H0; eauto.
Qed.

Lemma Iszero_b_eq: forall l, true = Iszero_bN l -> true = Iszero_b (List_ofN l).
Proof.
intros.
intros; apply Bool.andb_true_eq in H; destruct H.
symmetry; apply Bool.andb_true_iff; split; symmetry.
+ unfold List_ofN.
  rewrite map_length; auto.
+ symmetry; eapply forallb_forall; intros.
  apply InListN in H1.

  symmetry in H0; eapply forallb_forall in H0.
    assert ( x = N.to_nat (N.of_nat x)). autorewrite with Nnat; auto.
    rewrite H2.
    eauto.
  auto.
Qed.

(** Theorems to use with a witness tree **)


Theorem Lower_bound_tree: (exists T, (true= CheckTree M.empty [] T) /\ true = Iszero_b (GetState T)) -> Lower_bound.
Proof using All.
destruct CheckTree_OnlineInfeasible; intro.
do 2 destruct H1. exists (GetState x).
apply Iszero_sound in H2; intros; split; intros; auto.
eapply OnlineInfeasible_equiv; simpl.
rewrite <- minus_n_O; auto with arith.
eapply H in H1;  [eauto | intros; inversion H3 | destruct H2; intuition ].
Qed. 



Theorem Lower_bound_record: (exists T R, ((true)= fst (CheckRecord M.empty  (rev ([rec [] T]++R)))) /\true = Iszero_b (GetState T)) -> Lower_bound.
Proof using All.
intro; do 3 destruct H.
exists (GetState x); intros.
apply Iszero_sound in H0;
simpl; intuition; eauto.
eapply OnlineInfeasible_equiv; simpl.
  rewrite <- minus_n_O; lia.
eapply CheckRecord_OI. 
  symmetry. rewrite H. eapply surjective_pairing.
  simpl. intuition.
intros. apply M.mem_spec in H1. inversion H1.
Qed.

Theorem Lower_bound_recordN: (exists T R,((true) = fst (CheckRecordN M.empty (rev ([recN [] T]++R)))) /\ true = Iszero_bN (GetStateN T)) -> Lower_bound.
Proof using All.
intros. do 3 destruct H.
apply Lower_bound_record.
exists (to_tree_nat x). exists (to_Record_nat x0). split.
+ assert (to_Record_nat  ( ([recN [] x] ++ x0)) = ( ([rec [] (to_tree_nat x)] ++ to_Record_nat x0))); auto.
  rewrite <- H1.
  assert (forall (a:bool*M.t), true = fst a -> exists b, (true,b) = a) as RH. intros; destruct a. exists t0. rewrite H2. auto.
  apply RH in H; destruct H.
  apply CheckRecord_eq in H.
  assert (forall l, to_Record_nat l = map (fun x => match x with |(recN St T) => rec (List_ofN St) (to_tree_nat T) end) l).
  {
    induction l; simpl; auto.
    destruct a. rewrite IHl. auto.
  }
  rewrite H2. rewrite <- map_rev. rewrite <- H2.
  rewrite <- H.
  auto.
+ rewrite GetStateN_eq in H0.
  apply Iszero_b_eq in H0.
  autorewrite with Nnat.
  auto.
Qed.


Theorem OI_recordN: forall l St, (exists T R,((true) = fst (CheckRecordN M.empty ((R++[recN l T])))  /\ St = GetStateN T)) -> forall X, OnlineInfeasible X (List_ofN l) (List_ofN St).
Proof using All.
intros. do 3 destruct H. subst.
rewrite GetStateN_eq. rewrite List_ofto.
eapply CheckRecord_OI with (R0:=[]).
+ 
 erewrite CheckRecord_eq.
   simpl. eauto.
 rewrite surjective_pairing.
 rewrite <- H. eauto.
+ clear H. induction x0; simpl; auto.
  destruct a.
  apply in_cons. auto.
+ intros. inversion H0.
Qed.


(* Results used in the research paper *)
Theorem OI_length: forall X l St, OnlineInfeasible_simpl X l St -> (BinSum l) <= m*g.
Proof.
intros.
eapply OnlineInfeasible_length.
apply OnlineInfeasible_rev.
eauto. 
Qed.

Lemma OI_Succ: forall X l St, OnlineInfeasible_simpl X l St -> OnlineInfeasible_simpl (S X) l St.
Proof.
induction X; intros.
+ inversion H. apply Overflow_simpl; auto.
+ inversion H. apply Overflow_simpl; auto.
  apply Deadend_simpl; auto.
  destruct H2; exists x.
  intros. apply IHX.
  auto.
Qed.



End OnlineBinStretching.




Module BinNotations.
Notation "[[ ]]" := leafN (format "[[ ]]") .
Notation "[[ x ]]" := (consN x leafN) .
Notation "[[ x ; y ; .. ; z ]]" :=  (consN x (consN y .. (consN z leafN) ..)).
End BinNotations.

Import BinNotations.


Require Export Nat List NArith.
Export BinNotations Nat ListNotations.
Print Assumptions Lower_bound_recordN.

