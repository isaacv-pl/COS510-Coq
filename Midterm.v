Require Import Omega.
Require Export List.
Import ListNotations.
Import Bool.

(* BEGIN This stuff is just the [bdestruct] tactic (and associated lemmas)
    exactly as in vfa/Perm.v, reproduced here for your convenience *)
Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof. intros x y. apply iff_reflect. symmetry.  apply Nat.eqb_eq. Qed.
Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof. intros x y. apply iff_reflect. symmetry. apply Nat.ltb_lt. Qed.
Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof. intros x y. apply iff_reflect. symmetry. apply Nat.leb_le. Qed.
Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.
Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].
(* END of [bdestruct] reproduced from Perm.v *)

(**  PART ONE  **)

Fixpoint nth {U: Type} (n: nat) (l: list U) (default: U) : U :=
 match l with
 | nil => default
 | x::xs => match n with O => x | S n' => nth n' xs default end
 end.

(** **** Exercise: 1 star, standard (nth_nil)  *)
Lemma nth_nil: forall U n d, nth n (@nil U) d = d.
  intros. induction n.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (nth_over)  *)
Lemma nth_over: forall U n (al: list U) d, n >= length al -> nth n al d = d.
  intros. revert al H. induction n; intros.
  - destruct al.
    + simpl. reflexivity.
    + simpl in H. omega.
  - destruct al.
    + apply nth_nil.
    + simpl. apply IHn. simpl in H. omega.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (nth_app1)  *)
Lemma nth_app1: forall U n (al bl: list U) d,
  n < length al ->
  nth n al d = nth n (al++bl) d.
  intros. revert al H. induction n; intros.
  - simpl. destruct al, bl; try reflexivity; try simpl in H; try omega.
  - destruct al, bl; try reflexivity; try simpl in H; try omega.
    + Search (_ ++ []). rewrite app_nil_r. reflexivity.
    + apply IHn. omega.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (nth_app2)  *)
Lemma nth_app2: forall U n (al bl: list U) d,
  nth n bl d = nth (length al + n) (al++bl) d.
  intros. revert bl n. induction al; intros.
  - simpl. auto.
  - simpl. apply IHal.
Qed.
(** [] *)

(** PART TWO *)

(** We introduce here a representation of the integers, that is,
   negative and positive numbers.   This isn't the representation
   that the Coq standard library uses, but it will work fine for this
   exercise. *)

Inductive int : Type := Neg (n: nat) | Pos (n: nat).

Definition minus_two := Neg (S O).
Definition minus_one := Neg O.
Definition zero := Pos O.
Definition one := Pos (S O).
Definition two := Pos (S (S O)).

Definition add (i j: int) :=
 match i, j with
 | Neg a, Pos b => if Nat.ltb a b then Pos (b-(S a)) else Neg (a-b)
 | Neg a, Neg b => Neg (S (a+b))
 | Pos b, Neg a => if Nat.ltb a b then Pos (b-(S a)) else Neg (a-b)
 | Pos a, Pos b => Pos (a+b)
 end.

(** **** Exercise: 1 star, standard (negate)  *)
(* Define the [negate] function so that [int_add_negate] is provable. *)
Definition negate (i: int) : int :=
  match i with
  | Neg a => (Pos (S a))
  | Pos a => match a with
            | O => i
            | (S b) => (Neg b)
            end
  end.

Lemma int_add_negate:  forall i, add i (negate i) = zero.
Proof.
  intros. destruct i.
  - simpl. bdestruct (n<? S n).
    + assert (n - n = O). { omega. } rewrite H0. reflexivity.
    + omega.
  - simpl. destruct n.
    + reflexivity.
    + bdestruct (n <? S n). simpl. assert (n - n = O). { omega. } rewrite H0. auto.
      omega.
Qed.
(** [] *)

(** PART THREE **)

(* Suppose you write a program to simulate a Turing machine.
  Let's examine what the TAPE module would look like.
  The tape is an infinite sequence extending in both directions.
  Each "square" of the tape contains a "symbol".  
  There is a "tape head" pointing at one square of the tape.
  One can read or write the symbol under the tape head.
  One can move the tape head left or right.
  The "empty" tape is initialized to infinite copies of the "default"
   symbol, which we will call "A".
*)

Inductive symbol := A | B | C | D.

(* This module-type describes this "tape" interface *)
Module Type TAPE.
  Parameter T : Type.
  Parameter empty : T.
  Parameter read : T -> symbol.
  Parameter write: T -> symbol -> T.
  Parameter left : T -> T.
  Parameter right : T -> T.
End TAPE.

(* Here's a simple implementation of the module-type,
   not very efficient because every call to [write] or [left] or [right]
   maps one more layer of [fun] around the tape, so then
   [read] will take linear time in the number of previous operations. *)
   
Module Simple <: TAPE.
  Definition T := int -> symbol.
  Definition empty (i: int) := A.
  Definition read (t: T) : symbol := t zero.
  Definition write (t: T) (s: symbol) : T := 
      fun i => match i with Pos O => s | _ => t i end.
  Definition left (t: T) : T  :=
      fun i => t (add i minus_one).
  Definition right(t: T) : T  :=
      fun i => t (add i one).

  (* TEST CODE *)
  Fixpoint leftN (t: T) (n: nat) : T :=
    match n with O => t | S n' => leftN (left t) n' end.
  Fixpoint rightN (t: T) (n: nat) : T :=
    match n with O => t | S n' => leftN (right t) n' end.
  Fixpoint showN (t: T) (n: nat) : list symbol :=
    match n with O => nil | S n' => read t :: showN (right t) n' end.

  Definition show (t: T) : list symbol := showN (leftN t 5) 10.

  Definition t1 := write (right (right (write empty B))) D.

  Compute show t1.
End Simple.

(* Here's an efficient implementation of tapes, in which every
   operation takes constant time. *)
Module Fast <: TAPE.
  Definition T : Type := list symbol * list symbol.
  Definition empty : T := (nil,nil).
  Definition read (t: T) : symbol := 
           match t with (l,x::r) => x | _ => A end.
  Definition write (t: T) (s: symbol) : T := 
           match t with (l,x::r) => (l,s::r) | (l,nil) => (l,s::nil) end.
  Definition left (t: T) : T  :=
      match t with (x::xs,r) => (xs,x::r)  | (nil,r) => (nil,A::r) end.
  Definition right(t: T) : T  :=
      match t with (l,x::xs) => (x::l,xs)  | (l,nil) => (A::l,nil) end.

  (* TEST CODE *)
  Fixpoint leftN (t: T) (n: nat) : T :=
    match n with O => t | S n' => leftN (left t) n' end.
  Fixpoint rightN (t: T) (n: nat) : T :=
    match n with O => t | S n' => leftN (right t) n' end.
  Fixpoint showN (t: T) (n: nat) : list symbol :=
    match n with O => nil | S n' => read t :: showN (right t) n' end.

  Definition show (t: T) : list symbol := showN (leftN t 5) 10.

  Definition t1 := write (right (right (write empty B))) D.
  
  Compute show t1.
End Fast.

(** Now we will prove that the two implementations are indistinguishable
   by any client program that respects the abstraction.  Here's how. *)
Search rev.
(** **** Exercise: 2 stars, standard (relate)  *)
(* Define the [relate] relation so that the lemmas below are provable.
    Hint:  use the [nth] function... *)
Definition relate (f: Fast.T) (s: Simple.T) : Prop :=
  forall (n: int),
  match f with
  | (a, b) =>  match n with
              | Pos p => nth p b A = s n
              | Neg m => nth m a A = s n
              end
  end.
       
(*  match f with
  | (a, b) => forall (n: int), match n with
                            | Pos p => nth p b A = s
                            | Neg m => nth m a A = s
                            end
  end.*)
(** [] *)

(** **** Exercise: 1 star, standard (relate_empty)  *)
Lemma relate_empty: relate Fast.empty Simple.empty.
  simpl. unfold relate. induction n.
  - simpl. apply nth_nil.
  - apply nth_nil.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (relate_read)  *)
Lemma relate_read: forall f s, relate f s -> Fast.read f = Simple.read s.
  intros. unfold relate in H. destruct f. apply H with (n:= zero).
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (relate_write)  *)
Lemma relate_write: forall f s x, relate f s -> relate (Fast.write f x) (Simple.write s x).
  intros. unfold relate in H. destruct f. unfold relate. unfold Fast.write.
  destruct l0.
  - intros. destruct n.
    + simpl. apply H with (n:= Neg n).
    + simpl. destruct n.
      *  auto.
      * simpl. rewrite H with (n:= Pos (S n)). apply nth_nil.
  - intros. destruct n.
    + simpl. apply H with (n:= Neg n).
    + simpl. destruct n.
      * auto.
      * simpl. rewrite H with (n:= Pos (S n)). reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (relate_left)  *)
Lemma relate_left: forall f s, relate f s -> relate (Fast.left f) (Simple.left s).
  intros. unfold relate. unfold relate in H. destruct f. intros. unfold Fast.left.
  destruct l.
  - unfold Simple.left. remember (add n minus_one) as nug. destruct n.
    +  rewrite nth_nil. specialize H with (nug). destruct nug.
       * rewrite nth_nil in H. apply H.
       * assert (False).
         {
         induction n.
         - simpl in Heqnug. discriminate.
         - simpl in Heqnug. rewrite <- plus_n_O in Heqnug. discriminate.
         } destruct H0.
    + specialize H with nug. destruct nug.
      * rewrite <- H. destruct n eqn:En.
        **  simpl. rewrite nth_nil. auto.
        ** assert (False).
           {
           induction n1.
           + discriminate.
           + discriminate.
           } destruct H0.
      * rewrite <- H. induction n.
        ** simpl. simpl in Heqnug. discriminate.
        ** simpl. injection Heqnug. intros.
           assert (HH: n - 0 = n).
           {
           induction n.
           - reflexivity.
           - reflexivity.
           } rewrite HH in H0. rewrite H0. auto.
  - unfold Simple.left. remember (add n minus_one) as nug. destruct n.
    + specialize H with (nug). destruct nug.
      * rewrite <- H. assert (n0 = (S n)).
        {
        simpl in Heqnug. injection Heqnug. intros. rewrite <- plus_n_O in H0.
        apply H0.
        } rewrite H0. simpl. auto.
      * discriminate.
    + specialize H with (nug). destruct nug.
      * destruct n.
        ** simpl in Heqnug. injection Heqnug. intros. rewrite <- H.
           rewrite H0. simpl. auto.
        ** simpl in Heqnug. discriminate.
      * destruct n.
        ** simpl in Heqnug. discriminate.
        ** simpl in Heqnug. rewrite <- H. simpl.
           assert (HH: n - 0 = n).
           {
           induction n.
           - reflexivity.
           - reflexivity.
           } rewrite HH in Heqnug. injection Heqnug. intros. rewrite H0. auto.
Qed.
(** [] *)

Lemma minus_zero : forall n, n - 0 = n.
Proof.
  induction n.
  - reflexivity.
  - reflexivity.
Qed.

(** **** Exercise: 3 stars, standard (relate_right)  *)
Lemma relate_right: forall f s, relate f s -> relate (Fast.right f) (Simple.right s).
  intros.  unfold relate in H. unfold relate. intros. destruct f.  unfold Fast.right.
  destruct l0.
  - unfold Simple.right. remember (add n one) as nug. destruct n.
    + specialize H with nug. destruct nug.
      * destruct n.
        ** simpl in Heqnug. discriminate.
        ** simpl. simpl in Heqnug. rewrite minus_zero in Heqnug.
           injection Heqnug. intros. rewrite <- H.  rewrite H0. reflexivity.
      *  destruct n; simpl in Heqnug; try discriminate.
         ** injection Heqnug. intros. rewrite <- H. rewrite H0. simpl. reflexivity.
    + specialize H with nug. destruct nug.
      * destruct n; simpl in Heqnug; try discriminate.
      * destruct n; simpl in Heqnug; try discriminate.
        ** rewrite <- H. simpl. rewrite nth_nil. auto.
        ** rewrite <- H. simpl. rewrite nth_nil. auto.
  - unfold Simple.right. remember (add n one) as nug. destruct n.
    + specialize H with nug. destruct nug.
      * destruct n; simpl in Heqnug; try discriminate. rewrite minus_zero in Heqnug.
        rewrite <- H. simpl. injection Heqnug. intros. rewrite H0. auto.
      *  destruct n; simpl in Heqnug; try discriminate. injection Heqnug. intros.
         rewrite <- H. rewrite H0. simpl. auto.
    + specialize H with nug. destruct nug.
      * destruct n; simpl in Heqnug; try discriminate.
      * destruct n; simpl in Heqnug.
        ** injection Heqnug; intros; rewrite <- H; rewrite H0; auto.
        ** rewrite plus_comm in Heqnug. simpl in Heqnug. injection Heqnug.
           intros. rewrite <- H. rewrite H0. simpl. auto.
Qed.
(** [] *)

(** The following [Opaque] commands discourage Coq from unfolding these
   definitions.  The point is that all the remaining theorems can be proved
   without unfolding these definitions, just using the relate_* axioms that you've
   already proved. *)
Opaque Fast.empty Fast.read Fast.write Fast.left Fast.right.
Opaque Simple.empty Simple.read Simple.write Simple.left Simple.right.
Opaque relate.

(* Now that we have proved that Fast and Simple are equivalent implementations
   of Turing-machine tapes, we can prove the following consequence of that fact: *)
Lemma relate_leftN : forall f s j, relate f s ->
                             relate (Fast.leftN f j) (Simple.leftN s j).
Proof.
  intros. revert f s H. induction j.
  - simpl. intros. apply H.
  - simpl. intros. apply relate_left in H. apply IHj in H.
    apply H.
Qed.

Lemma relate_showN : forall f s i, relate f s ->
                              Fast.showN f i = Simple.showN s i.
Proof.
  intros. revert f s H. induction i.
  - intros.  simpl. auto.
  - simpl. intros. assert (Hright: (relate (Fast.right f) (Simple.right s))).
    { apply relate_right in H. apply H. }
    assert (HRead: Fast.read f = Simple.read s).
    { apply relate_read in H. apply H. }
    apply IHi in Hright. rewrite HRead. rewrite Hright. auto.
Qed.

(** **** Exercise: 3 stars, standard (relate_show)  *)
Lemma relate_show:  forall f s, relate f s -> Fast.show f = Simple.show s.
Proof.
intros.
unfold Fast.show, Simple.show.
set (i:=10). clearbody i.
set (j:=5). clearbody j.
(* Finish this proof.  Do not unfold any of the Opaque definitions.
   Instead, use the Lemmas that you proved about [relate].  Feel free
   to write some auxiliary lemmas to support the proof of this Lemma. *)
revert f s H j. induction i.
- simpl. auto.
- intros. assert (HH: relate (Fast.leftN f j) (Simple.leftN s j)).
  {apply relate_leftN with (j:= j) in H. apply H. }
  apply relate_showN with (i:= (S i)) in HH. apply HH.
Qed.

(** [] *)
(* Wed Mar 11 12:25:43 EDT 2020 *)
