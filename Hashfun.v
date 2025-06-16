(** * Hashfun: Functional model of hash tables *)

(** ** This C program, [hash.c], implements a hash table with
   external chaining.  See https://www.cs.princeton.edu/~appel/HashTables.pdf
   for an introduction to hash tables.  *)

(** 

#include <stddef.h>

extern void * malloc (size_t n);
extern void exit(int n);
extern size_t strlen(const char *str);
extern char *strcpy(char *dest, const char *src);
extern int strcmp(const char *str1, const char *str2);

unsigned int hash (char *s) {
  unsigned int n=0;
  unsigned int i=0;
  int c=s[i];
  while (c) {
    n = n*65599u+(unsigned)c;
    i++;
    c=s[i];
  }
  return n;
}

struct cell {
  char *key;
  unsigned int count;
  struct cell *next;
};

enum {N = 109};

struct hashtable {
  struct cell *buckets[N];
};

char *copy_string (char *s) {
  int i,n = strlen(s)+1;
  char *p = malloc(n);
  if (!p) exit(1);
  strcpy(p,s);
  return p;
}

struct hashtable *new_table (void) {
  int i;
  struct hashtable *p = (struct hashtable * )malloc(sizeof(struct hashtable));
  if (!p) exit(1);
  for (i=0; i<N; i++) p->buckets[i]=NULL;
  return p;
}  

struct cell *new_cell (char *key, int count, struct cell *next) {
  struct cell *p = (struct cell * )malloc(sizeof(struct cell));
  if (!p) exit(1);
  p->key = copy_string(key);
  p->count = count;
  p->next = next;
  return p;
}

unsigned int get (struct hashtable *table, char *s) {
  unsigned int h = hash(s);
  unsigned int b = h % N;
  struct cell *p = table->buckets[b];
  while (p) {
    if (strcmp(p->key, s)==0)
      return p->count;
    p=p->next;
  }
  return 0;
}

void incr_list (struct cell **r0, char *s) {
  struct cell *p, **r;
  for(r=r0; ; r=&p->next) {
    p = *r;
    if (!p) {
      *r = new_cell(s,1,NULL);
      return;
    }
    if (strcmp(p->key, s)==0) {
      p->count++;
      return;
    }
  }
}  

void incr (struct hashtable *table, char *s) {
  unsigned int h = hash(s);
  unsigned int b = h % N;
  incr_list (& table->buckets[b], s);
}
*)

(* ================================================================= *)
(** ** A functional model *)

(** Before we prove the C program correct, we write a functional
 program that models its behavior as closely as possible.  
 The functional program won't be (average) constant time per access,
 like the C program, because it takes linear time to get the nth
 element of a list, while the C program can subscript an array in
 constant time.  But we are not worried about the execution time
 of the functional program; only that it serve as a model
 for specifying the C program. *)

Require Import VST.floyd.functional_base.

Instance EqDec_string: EqDec (list byte) := list_eq_dec Byte.eq_dec. 

Fixpoint hashfun_aux (h: Z) (s: list byte) : Z :=
 match s with
 | nil => h
 | c :: s' =>
      hashfun_aux ((h * 65599 + Byte.signed c) mod Int.modulus) s'
end.

Definition hashfun (s: list byte) := hashfun_aux 0 s.

Definition hashtable_contents := list (list (list byte * Z)).

Definition N := 109.
Lemma N_eq : N = 109. 
Proof. reflexivity. Qed.
Hint Rewrite N_eq : rep_omega.
Global Opaque N.

Definition empty_table : hashtable_contents :=
  list_repeat (Z.to_nat N) nil.

Fixpoint list_get (s: list byte) (al: list (list byte * Z)) : Z :=
  match al with
 | (k,i) :: al' => if eq_dec s k then i else list_get s al'
 | nil => 0
 end.

Fixpoint list_incr (s: list byte) (al: list (list byte * Z))
              :  list (list byte * Z) :=
  match al with
 | (k,i) :: al' => if eq_dec s k 
                      then (k, i +1)::al'
                      else (k,i)::list_incr s al'
 | nil => (s, 1)::nil
 end.

Definition hashtable_get  (s: list byte) (contents: hashtable_contents) : Z :=
  list_get s (Znth (hashfun s mod (Zlength contents)) contents).

Definition hashtable_incr (s: list byte) (contents: hashtable_contents)
                      : hashtable_contents :=
  let h := hashfun s mod (Zlength contents)
  in let al := Znth h contents
  in upd_Znth h contents (list_incr s al).

(** **** Exercise: 2 stars, standard (hashfun_inrange)  *)
Lemma hashfun_inrange: forall s, 0 <= hashfun s <= Int.max_unsigned.
Proof.
  assert(Int.max_unsigned + 1 <= Int.modulus). unfold Int.max_unsigned. rep_omega.
  unfold hashfun.
  destruct s.
  { unfold hashfun. simpl. rep_omega. }
  unfold hashfun. simpl.
  remember  (Byte.signed i) as b.
  remember (b mod Int.modulus) as a.
  clear Heqb.
  revert i b a Heqa.
  induction s; intros.
  - simpl. subst. assert(0 <= (b mod Int.modulus) < Int.modulus).
    apply Z.mod_pos_bound. rep_omega. rep_omega.
  -  simpl. remember (((a0 * 65599 + Byte.signed a) mod Int.modulus) ) as a'.
     apply IHs with (b:= (a0 * 65599 + Byte.signed a)).
     exact i. apply Heqa'.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (hashfun_get_unfold)  *)
Lemma hashtable_get_unfold:
 forall sigma (cts: list (list (list byte * Z) * val)),
 hashtable_get sigma (map fst cts) =
  list_get sigma (Znth (hashfun sigma mod (Zlength cts)) (map fst cts)).
Proof.
  intros. induction sigma.
  - unfold hashtable_get. rewrite Zlength_map. auto.
  - unfold hashtable_get. rewrite Zlength_map. auto.
Qed.
(** [] *)

Lemma zlt_obv: forall a b,
     a <= b -> a <= b + 1.
Proof.
 intros. omega.
Qed.

Lemma zlt_obv2: forall a b,
     a < b -> a + 1 <= b.
Proof.
  intros. omega.
Qed.
(* cts =
  upd_Znth (hashfun k mod Zlength cts) cts
    (list_incr k (Znth (hashfun k mod Zlength cts) cts))*)
(** **** Exercise: 2 stars, standard (Zlength_hashtable_incr)  *)
Lemma Zlength_hashtable_incr:
 forall sigma cts, 
      0 < Zlength cts -> 
      Zlength (hashtable_incr sigma cts) = Zlength cts.
Proof.
  intros.  revert cts H. unfold hashtable_incr. unfold upd_Znth.
  induction sigma; intros.
  - simpl. rewrite Zlength_cons. rewrite Zlength_sublist.
    omega. rep_omega. rep_omega.
  - assert(forall b, 0 <= b mod Zlength cts < (Zlength cts)). intros. apply Z.mod_pos_bound. omega.
    assert(forall c, 0 <= c mod Zlength cts + 1 <= (Zlength cts)). intros. specialize H0 with c.
    destruct H0. split. apply zlt_obv. apply H0. omega.
    rewrite Zlength_app. rewrite Zlength_cons.
    rewrite Zlength_sublist. rewrite Z.sub_0_r.
    replace  (Z.succ (Zlength (sublist (hashfun (a :: sigma) mod Zlength cts + 1) (Zlength cts) cts))) with
        ((Zlength (sublist (hashfun (a :: sigma) mod Zlength cts + 1) (Zlength cts) cts)) + 1).
    Search (_ + _). rewrite Z.add_comm. rewrite Zlength_sublist. omega.
    apply H1. omega.
    omega. split.  omega. apply H0. Search (_ < _ -> _ <= _). apply Z.lt_le_incl.
    apply H0.
Qed.

Hint Rewrite Zlength_hashtable_incr using list_solve : sublist.
(** [] *)

(** **** Exercise: 3 stars, standard (hashfun_snoc)  *)

Lemma Int_repr_eq_mod:
   forall a,  Int.repr (a mod Int.modulus) = Int.repr a.
Proof.
Print Int.eqm.  (* This is a hint about how to prove the lemma *)
Search Int.eqm. (* This is a hint about how to prove the lemma *)
intros.
apply Int.eqm_samerepr.
unfold Int.eqm.
apply int_modm_mod_elim.
apply Zbits.eqmod_refl.
Qed.

(*induction a.
- Search (0 mod _). rewrite Zmod_0_l. auto.
- Search Int.eqm. apply Int.eqm_samerepr.
  Search Int.eqm. assert (0 <= Z.pos p mod Int.modulus < Int.modulus).
  apply Z.mod_pos_bound. rep_omega.*)
(** Use [Int_repr_eq_mod] in the proof of [hashfun_snoc]. *)
Lemma sublist_nil'':
 forall A (s e : Z), sublist s e (@nil A) = nil.
Proof.
  intros. unfold sublist. rewrite skipn_nil. rewrite firstn_nil. auto.
Qed.

(*Lemma hashfun_aux_list:
   hashfun_aux h l ++ l' = *)
Lemma hashfun_aux_sublist: forall (i:Z) (x y : list byte),
    hashfun_aux i (x ++ y) = hashfun_aux (hashfun_aux i x) y.
Proof.
  intros i x.
  revert i.
  induction x; intros.
  - reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Lemma hashfun_snoc:
  forall sigma h lo i,
    0 <= lo ->
    lo <= i < Zlength sigma ->
  Int.repr (hashfun_aux h (sublist lo (i + 1) sigma)) =
  Int.repr (hashfun_aux h (sublist lo i sigma) * 65599 + Byte.signed (Znth i sigma)).
Proof.
  intros. rewrite sublist_split with (mid:= i). rewrite hashfun_aux_sublist.
  rewrite sublist_len_1. simpl. apply Int_repr_eq_mod.
  rep_omega. rep_omega. rep_omega.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Functional model satisfies the high-level specification *)

(** The purpose of a hash table is to implement a finite mapping,
  (a finite function) from keys to values.  We claim that the
  functional model ([empty_table, hashtable_get, hashtable_incr])
  correctly implements the appropriate operations on the abstract
  data type of finite functions.

  We formalize that statement by defining a Module Type: *)

Module Type COUNT_TABLE.
 Parameter table: Type.
 Parameter key : Type.
 Parameter empty: table.
 Parameter get: key -> table -> Z.
 Parameter incr: key -> table -> table.
 Axiom gempty: forall k,   (* get-empty *)
       get k empty = 0.
 Axiom gss: forall k t,      (* get-set-same *)
      get k (incr k t) = 1+(get k t).
 Axiom gso: forall j k t,    (* get-set-other *)
      j <> k -> get j (incr k t) = get j t.
End COUNT_TABLE.

(** This means:  in any [Module] that satisfies this [Module Type],
   there's a type [table] of count-tables,
   and operators [empty], [get], [set] that satisfy the axioms
   [gempty], [gss], and [gso]. *)
  
(* ----------------------------------------------------------------- *)
(** *** A "reference" implementation of COUNT_TABLE *)

(** **** Exercise: 2 stars, standard (FunTable) 

     It's easy to make a slow implementation of [COUNT_TABLE], using functions. *)

Module FunTable <: COUNT_TABLE.
 Definition table: Type := nat -> Z.
 Definition key : Type := nat.
 Definition empty: table := fun k => 0.
 Definition get (k: key) (t: table) : Z := t k.
 Definition incr (k: key) (t: table) : table :=
    fun k' => if Nat.eqb k' k then 1 + t k' else t k'.
 Lemma gempty: forall k,  get k empty = 0.
   intros. unfold get. unfold empty. auto.
 Qed.

 Lemma gss: forall k t,  get k (incr k t) = 1+(get k t).
   intros. unfold get. unfold incr. destruct (k =? k)%nat eqn:Heqk.
   -  auto.
   - apply Nat.eqb_neq in Heqk. assert(k = k). auto.
     unfold not in Heqk. apply Heqk in H. inversion H.
 Qed.

 Lemma gso: forall j k t,  j <> k -> get j (incr k t) = get j t.
   intros. unfold not in H. unfold get. unfold incr. destruct (j =? k)%nat eqn:Heq.
   - apply beq_nat_true in Heq. apply H in Heq.
     inversion Heq.
   - auto.
 Qed.

End FunTable.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Demonstration that hash tables implement COUNT_TABLE *)

(** **** Exercise: 3 stars, standard (IntHashTable) 

     Now we make a "fast" implementation using hash tables.  We
  put "fast" in quotes because, unlike the imperative implementation,
 the purely functional implementation takes linear time, not constant time,
 to select the the i'th bucket.  That is, [Znth i al] takes time proportional to [i].
 But that is no problem, because we are not using [hashtable_get] and
 [hashtable_incr] as our real implementation; they are serving as the 
 _functional model_ of the fast implementation in C.  *)
Lemma map_fst_incr_inv: forall k k0 cts,
    k <> k0 -> In k0 (map fst cts) -> In k0 (map fst (list_incr k cts)).
Proof.
  intros.
  induction cts.
  - simpl in *. contradiction.
  - simpl. destruct a as [k1 i].
    destruct (eq_dec k k1).
    + simpl. subst k1.
      Search (map _ (_ :: _)).
      rewrite map_cons in H0. simpl in H0. destruct H0.
      * contradiction.
      * right. apply H0.
    + simpl. simpl in H0. destruct H0.
      * subst. left. reflexivity.
      * right. apply IHcts. apply H0.
Qed.

Lemma step_in_list_incr: forall k0 k x xs,
    fst x <> k0 -> In k0 (map fst (list_incr k (x :: xs))) ->
    In k0 (map fst (list_incr k xs)).
Proof.
  intros.
  unfold list_incr in H0. destruct x as [k1 i].
  destruct (eq_dec k k1).
  - destruct H0. contradiction. subst k1.
    apply map_fst_incr_inv. apply H. apply H0.
  - simpl in H0. destruct H0. contradiction. simpl in H0.
    apply H0.
Qed.

Lemma list_norepet_inv_list_incr: forall (k : list byte) (cts: list (list byte * Z)),
    list_norepet (map fst cts) -> list_norepet (map fst (list_incr k cts)).
Proof.
  intros.
  induction cts.
  - simpl in *. apply list_norepet_cons. intro. contradiction. apply H.
  - simpl in *. destruct a as [k0 i]. destruct (eq_dec k k0).
    + simpl in *. apply H.
    + inversion H; clear H; subst; simpl.
      apply list_norepet_cons.
      * intro. apply H2. clear H2. clear - n H.
        induction cts.
        ** simpl in *. destruct H; contradiction.
        ** simpl. destruct (eq_dec (fst a) k0).
           *** left. apply e.
           *** right. apply IHcts. clear IHcts.
               apply step_in_list_incr with (x:=a).
               apply n0. apply H.
      * apply IHcts. apply H3.
Qed.

Lemma forall_map_Znth_incr: forall (i:Z) k (cts: hashtable_contents),
    Zlength cts = N ->
    0 <= i < N ->
    Forall (fun s : list byte => hashfun s mod N = i) (map fst (Znth i cts)) ->
    Forall (fun s : list byte => hashfun s mod N = i)
           (map fst (Znth i (hashtable_incr k cts))).
Proof.
  intros.
  unfold hashtable_incr.
  remember (hashfun k mod Zlength cts) as j.
  destruct (zeq i j).
  - subst. rewrite upd_Znth_same. 2: { apply Z.mod_pos_bound. rep_omega. }
    remember (hashfun k mod Zlength cts) as j.
    induction (Znth j cts) as [| z zs].
    + simpl. apply Forall_cons. subst. rewrite H. auto. apply Forall_nil.
    + simpl in *. destruct z as [k0 i].
      destruct (eq_dec k k0).
      * simpl in *. apply H1.
      * simpl in *. apply Forall_cons.
        ** subst. inversion H1. subst. apply H4.
        ** apply IHzs. inversion H1. subst. apply H5.
  - subst. rewrite upd_Znth_diff. apply H1. rewrite H. assumption.
    apply Z.mod_pos_bound. rep_omega. apply n.
Qed.

Module IntHashTable <: COUNT_TABLE.
 Definition hashtable_invariant (cts: hashtable_contents) : Prop :=
  Zlength cts = N /\
  forall i, 0 <= i < N ->
             list_norepet (map fst (Znth i cts))
             /\ Forall (fun s => hashfun s mod N = i) (map fst (Znth i cts)).
 Definition table := sig hashtable_invariant.
 Definition key := list byte.

 Lemma empty_invariant: hashtable_invariant empty_table.
 Proof.
   unfold hashtable_invariant. unfold empty_table. split.
   - apply Zlength_list_repeat. rep_omega.
   - intros. split.
     + rewrite Znth_list_repeat_inrange.
       apply list_map_norepet.  apply list_norepet_nil.
       intros. auto. auto.
     +  rewrite Znth_list_repeat_inrange. simpl.
       auto. apply H.
 Qed.

 Lemma succ_plus: forall a,
      Z.succ(a) = a + 1.
 Proof.
   intros. rep_omega.
 Qed.

Lemma incr_invariant: forall k cts, hashtable_invariant cts -> hashtable_invariant (hashtable_incr k cts).
Proof.
  split.
  - rewrite Zlength_hashtable_incr; inversion H; rep_omega.
  - intros. split.
    + unfold hashtable_incr. remember (hashfun k mod Zlength cts) as j.
      inversion H; clear H.
      destruct (zeq i j).
      * subst i. remember (Znth j cts) as al. rewrite upd_Znth_same.
        apply list_norepet_inv_list_incr. subst.
        apply H2. apply H0. rep_omega.
      * rewrite upd_Znth_diff. apply H2. apply H0. rep_omega.
        rewrite Heqj. apply Z.mod_pos_bound. rep_omega. apply n.
    + apply forall_map_Znth_incr.
      * inversion H. apply H1.
      * apply H0.
      * inversion H. apply H2. apply H0.
Qed.


 Definition empty : table := exist _ _ empty_invariant.
 Definition get : key -> table -> Z := fun k tbl => hashtable_get k (proj1_sig tbl).
 Definition incr : key -> table -> table := 
       fun k tbl => exist _ _ (incr_invariant k _ (proj2_sig tbl)).

 Theorem gempty: forall k, get k empty = 0.
 Proof.
   intros. unfold get. unfold hashtable_get. unfold proj1_sig.
   simpl. unfold empty_table. Search Zlength. rewrite Znth_list_repeat_inrange.
   unfold list_get. auto. Search Zlength. rewrite Zlength_list_repeat.
   apply Z.mod_pos_bound. rep_omega. rep_omega.
Qed.

Lemma list_get_ind: forall k a l,
    list_get k (list_incr k l) = 1 + list_get k l ->
    list_get k (list_incr k (a :: l)) = 1 + list_get k (a :: l).
Proof.
  intros.
  unfold list_incr. fold list_incr.
  destruct a as [k0 i].
  destruct (eq_dec k k0) eqn:E.
  - unfold list_get. rewrite E. apply Z.add_comm.
  - unfold list_get. rewrite E. fold list_get. apply H.
Qed.

 Theorem gss: forall k t,  get k (incr k t) =  1 + (get k t).
 Proof.
   intros. unfold get. unfold proj1_sig. destruct t. unfold incr.
   unfold proj1_sig. unfold hashtable_get. unfold hashtable_incr.
   remember (hashfun k mod Zlength x) as j.
   remember (hashfun k mod Zlength (upd_Znth j x (list_incr k (Znth j x)))) as i.
   assert (H: i = j).
   { subst. f_equal. apply upd_Znth_Zlength. apply Z.mod_pos_bound.
     inversion h. rep_omega. }
   rewrite H. rewrite upd_Znth_same.
   2: { destruct x. inversion h; discriminate H0.
        rewrite Heqj. apply Z.mod_pos_bound. subst. rewrite Zlength_cons. rep_omega. }
   subst i. clear H. induction (Znth j x).
   { simpl. destruct eq_dec. auto. contradiction. }
   apply list_get_ind. apply IHl.
 Qed.

 Lemma lgo: forall j k ll,
  j <> k -> list_get j (list_incr k ll) = list_get j ll.
Proof.
  intros.
  induction ll as [| x xs ].
  - simpl. destruct (eq_dec j k). contradiction. reflexivity.
  - simpl. destruct x as [k0 i]. destruct (eq_dec k k0), (eq_dec j k0) eqn:E.
    + simpl. subst. rewrite E. destruct H. reflexivity.
    + simpl. rewrite E. reflexivity.
    + simpl. rewrite E. reflexivity.
    + simpl. rewrite E. subst. simpl. apply IHxs.
Qed.

Lemma lgo': forall j' j k' k cts,
  j' <> k' ->
  k' = hashfun k mod Zlength cts ->
  j' = hashfun j mod Zlength cts ->
  Znth j' (upd_Znth k' cts (list_incr k (Znth k' cts))) = Znth j' cts.
Proof.
  intros.
  destruct cts as [| x xs ].
  - apply upd_Znth_diff.
    + subst. destruct H. repeat rewrite Zmod_0_r. reflexivity.
    + subst. destruct H. repeat rewrite Zmod_0_r. auto.
    + apply H.
  - apply upd_Znth_diff.
    + subst. apply Z.mod_pos_bound. rewrite Zlength_cons. rep_omega.
    + subst. apply Z.mod_pos_bound. rewrite Zlength_cons. rep_omega.
    + apply H.
Qed.

 Theorem gso: forall j k t,    (* get-set-other *)
      j <> k -> get j (incr k t) = get j t.
 Proof.
    intros. unfold get. unfold proj1_sig. destruct t. unfold incr. unfold proj1_sig.
   unfold hashtable_get. unfold hashtable_incr.
   remember (upd_Znth (hashfun k mod Zlength x) x
                      (list_incr k (Znth (hashfun k mod Zlength x) x))) as i.
   assert (H': Zlength i = Zlength x).
   { subst. apply upd_Znth_Zlength. apply Z.mod_pos_bound.
     destruct x. inversion h; discriminate H0. rewrite Zlength_cons. rep_omega. }
   rewrite H'. clear H'.
   destruct (zeq (hashfun j mod Zlength x) (hashfun k mod Zlength x)) eqn: Ejk.
   - inversion h; clear h; subst.
     rewrite e. rewrite upd_Znth_same.
     2: { apply Z.mod_pos_bound. rep_omega. }
     Search list_incr. Search eq_dec. Search Znth.
     remember (hashfun k mod Zlength x) as i.
     specialize H1 with i.
     destruct H1.
     { split. subst. apply Z.mod_pos_bound. rep_omega. subst. rewrite <- H0.
       apply Z.mod_pos_bound. rep_omega. }
     apply lgo. apply H.
   - f_equal.
     remember (hashfun j mod Zlength x) as q.
     remember (hashfun k mod Zlength x) as p.
     subst i.
     eapply lgo'.
     apply n. apply Heqp. apply Heqq.
Qed.
(** [] *)

End IntHashTable.

(* 2020-04-22 08:26:23 (UTC-04) *)
