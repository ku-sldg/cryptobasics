(**

Author: Perry Alexander and Alessandro Coglio

This file contains a Coq model of "perfect" crypto adapted from a PVS
model [6] developed by Alessandro Coglio.

By perfect crypto we mean functions that provide absolute instead of
high-probability guarantees for cryptographic properties.  Specifically:

- Keys cannot be guessed.  Encryption and decrytption, signing and
  verifying signatures only works if the appropriate key is known.
- Hashes are collision-free, injective functions

The model incudes:

- Structured data that includes explicit uses of crypto functions
- Analysis functions for structured data (decryption)
- Synthesis functions for structured data (encryption)

This approach is used in the inductive approach to verifying cryptographic
protocols [1] as well as in the model checking of cryptographic progocols
[2].  The analysis and synthesis functions on structured data correspond
to the Dolev-Yao attacker model [3].  The inductive approach to verifying
cryptographic protocols [1] was originally developed for the Isabelle/HOL
theorem prover.  This Coq theory is similar to [4] and derived from a PVS
model [6].

References:

[1] Lawrence Paulson,
    "The Inductive Approach to Verifying Cryptographic Protocols",
    Journal of Computer Security, 6 (1998), pages 85-128.

[2] David Basin, Cas Cremers, Catherine Meadows,
    "Model Checking Security Protocols",
    Chapter 24 of Handbook of Model Checking (Springer), to appear.

[3] Danny Dolev, Andrew Yao,
    "On the Security of Public Key Protocols",
    IEEE Transactions on Information Theory, Vol. IT-29, No. 2, 1983.

[4] Lawrence Paulson,
    "HOL/Auth/Message" theory in the Isabelle 2013-2 library
    (http://isabelle.in.tum.de).

[5] Veronique Cortier, Stephanie Delaune, Pascal Lafourcade,
    "A Survey of Algebraic Properties Used in Cryptographic Protocols",
     Journal of Computer Security, 14-1 (2006), pages 1-43.

[6] PVS model here

*)

Require Import Relations.
Require Import Omega.
Require Import ZArith.
Require Export List.
Require Export Lists.ListTactics.

Inductive key : Type :=
| symmetric : nat -> key
| private : nat -> key
| public : nat -> key.

Variables k k1 k2: key.

Definition kinverse(k:key) : key :=
  match k with
    | symmetric _ => k
    | private k' => (public k')
    | public k' => (private k')
  end.

Lemma kinverse_injective: forall k1 k2, kinverse k1 = kinverse k2 -> k1 = k2.
Proof.
  intros.
  destruct k3,k4; inversion H; reflexivity.
Qed.

Hint Resolve kinverse_injective.

Lemma kinverse_inverse : forall k, kinverse (kinverse k) = k.
Proof.
  intros. destruct k0; cbv; reflexivity.
Qed.

Hint Resolve kinverse_inverse.

Lemma kinverse_surjective : forall k2, exists k1, kinverse k1 = k2.
Proof.
  intros k3. exists (kinverse k3). auto.
Qed.

Hint Resolve kinverse_surjective.

Lemma kinverse_bijective :
  (forall k1 k2, kinverse k1 = kinverse k2 -> k1 = k2)
  /\ (forall k2, exists k1, kinverse k1 = k2).
Proof.
  split; auto.
Qed.

Definition basic := nat.

Inductive data(T:Type) : Type :=
| value : T -> data T
| kval : key -> data T
| kapply : key -> data T -> data T
| hash : data T -> data T
| pair : data T -> data T -> data T.

Arguments value {T} _.
Arguments kval {T} _.
Arguments kapply {T} _ _.
Arguments hash {T} _.
Arguments pair {T} _ _.

Definition sign(T:Type)(d:data T)(k:key):data T :=
  pair d (kapply k (hash d)).

Definition check(T:Type)(d:data T)(k:key):Prop :=
  match d with
  | pair d' s' => match s' with
                 | kapply k' s'' => k = kinverse k' /\ s'' = hash d'
                 | _ => False
                 end
  | _ => False
  end.

Eval compute in (sign nat (value 1) (private 1)).
Example ex1: (check nat (sign nat (value 1) (private 1)) (public 1)).
Proof.
  firstorder.
Qed.

(** Verify signature checking and signing *)

Theorem sig_check: forall T d1 k1 k2,
    k1 = kinverse k2 -> (check T (sign T (value d1) k1) k2).
Proof.
  intros T.
  intros d1 k3 k4.
  intros H.
  subst.
  firstorder.
Qed.

(** I would prefer using sets here, but will use lists to take advantage
  of structured mechanisms for traversal *)

(** [recoverable0] takes a data element [d] and appends a list of new data
  that is recoverable from [d] to [d]. *)
  
Fixpoint recoverable0(T:Type)(d:data T) : list (data T) :=
  cons d (match d with
  | value _ => nil
  | kval _ => nil
  | kapply _ d => recoverable0 T d
  | hash _ => nil
  | pair d1 d2 => app (recoverable0 T d1) (recoverable0 T d2)
          end).

Eval compute in recoverable0 nat (sign nat (value 1) (private 1)).

(** [recoverable] takes a list of data [dset] and walks the list with
  [recoverable0] to create a list of all data recoverable from the list
  of data.  This is effectively a fold of [recoverable0] over the input
  [dset] *)

Fixpoint recoverable(T:Type)(dset:list (data T)):list (data T) :=
  match dset with
  | nil => nil
  | cons h t => app (recoverable0 T h) (recoverable T t)
  end.

Eval compute in recoverable nat (cons (sign nat (value 1) (private 1)) nil).

(** This is dorky *)

Theorem recoverable_from_single: forall T d dset,
    In d (recoverable T dset) -> exists d0, In d (recoverable0 T d0).
Proof.
  intros. exists d. destruct d; simpl; tauto.
Qed.

Hint Resolve app_nil_r.

Theorem recoverable_single: forall T d,
    recoverable T (cons d nil) = recoverable0 T d.
Proof.
  intros.
  simpl.
  apply app_nil_r.
Qed.

(* Theorem recoverable_subterm: forall d dset, In d (recoverable dset) -> exists d0 *)


Theorem recoverable0_transitive: forall T d0 d1 d2,
    In d0 (recoverable0 T d1) -> In d1 (recoverable0 T d2) -> In d0 (recoverable0 T d2).
Proof.
  intros T.
  induction d0; induction d1.
  * intros d2.
    intros H1 H2.
    destruct d2.
    simpl.
    simpl in H1. simpl in H2.
    destruct H1. destruct H2. rewrite <- H. rewrite H0. left. reflexivity. right. assumption. right. assumption.
    simpl in *.
    destruct H1. destruct H2. rewrite <- H. rewrite H0. left. reflexivity. right. assumption. right. assumption.
    simpl in *.
    destruct H1. destruct H2. rewrite <- H. rewrite H0. left. reflexivity. rewrite <- H. right. assumption. contradiction.
    simpl in *.
    destruct H1. destruct H2. rewrite <- H. rewrite H0. left. reflexivity. contradiction. contradiction.
    simpl in *.
    destruct H1. destruct H2. rewrite <- H. rewrite H0. left. reflexivity. rewrite <- H. right. assumption. contradiction.
  * destruct d2.
    simpl.
    intros H1 H2.
    destruct H1; destruct H2.
    rewrite <- H. rewrite H0.
    left. reflexivity. contradiction. contradiction. contradiction.
    simpl.
    intros H1 H2.
    destruct H1; destruct H2.
    rewrite <- H. rewrite H0.
    left. reflexivity. contradiction. contradiction. contradiction.
    simpl.
    intros H1 H2.
    destruct H1; destruct H2.
    rewrite <- H. rewrite H0.
    left. reflexivity. rewrite <- H. right. assumption. contradiction. contradiction.
    simpl.
    intros H1 H2.
    destruct H1; destruct H2.
    rewrite <- H. rewrite H0.
    left. reflexivity. contradiction. contradiction. contradiction.
    simpl.
    intros H1 H2.
    destruct H1; destruct H2.
    rewrite <- H. rewrite H0.
    left. reflexivity. rewrite <- H. right. assumption. contradiction. contradiction. 
  * destruct d2.
    simpl;
    intros H1 H2;
    destruct H1; destruct H2.
    rewrite <- H. rewrite H0.
    left. reflexivity. contradiction.
    simpl.
    intros H1 H2.
    destruct H1; destruct H2.
    rewrite <- H. rewrite H0.
    left. reflexivity. contradiction. contradiction. contradiction.
    simpl.
    intros H1 H2.
    destruct H1; destruct H2.
    rewrite <- H. rewrite H0.
    left. reflexivity. rewrite <- H. right. assumption. contradiction. contradiction.
    simpl.
    intros H1 H2.
    destruct H1; destruct H2.
    rewrite <- H. rewrite H0.
    left. reflexivity. contradiction. contradiction. contradiction.
    simpl.
    intros H1 H2.
    destruct H1; destruct H2.
    rewrite <- H. rewrite H0.
    left. reflexivity. rewrite <- H. right. assumption. contradiction. contradiction. 
    
    
    
    
    
Admitted.

