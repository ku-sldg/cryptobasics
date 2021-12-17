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

Require Import Arith.
Require Import Relations.
Require Export List.
Require Export Lists.ListTactics.

Create HintDb crypto.

Inductive key: Set :=
| symmetric : nat -> key
| private : nat -> key
| public : nat -> key.

Theorem key_decidable (k0 k1: key):
  { k0 = k1 }+{ k0 <> k1 }.
Proof.
  destruct k0 as [n0 | n0 | n0], k1 as [n1 | n1 | n1];
    try (right; discriminate);
    case (Nat.eq_dec n0 n1);
    try (intros ->; left; reflexivity);
    intros Hneq; right; injection;
    contradiction.
Qed.

Definition eqb_key (k0 k1: key): bool :=
  match k0, k1 with
  | symmetric n0, symmetric n1 => Nat.eqb n0 n1
  | private n0, private n1 => Nat.eqb n0 n1
  | public n0, public n1 => Nat.eqb n0 n1
  | _, _ => false
  end.

Theorem key_eq_eqb (k0 k1: key):
  k0 = k1 <-> eqb_key k0 k1 = true.
Proof.
  split; [intros <- | intros Hb].
  { destruct k0 as [n0 | n0 | n0]; simpl;
      rewrite Nat.eqb_eq;
      reflexivity. }
  { destruct k0 as [n0 | n0 | n0],
      k1 as [n1 | n1 | n1];
      simpl in Hb; try (discriminate Hb);
      rewrite Nat.eqb_eq in Hb;
      subst; reflexivity. }
Qed.

Definition kinverse (k: key): key :=
  match k with
    | symmetric _ => k
    | private k' => (public k')
    | public k' => (private k')
  end.

  Lemma kinverse_inverse (k: key):
  kinverse (kinverse k) = k.
Proof.
  destruct k as [n | n | n];
    cbv;
    reflexivity.
Qed.

#[global]
Hint Resolve kinverse_inverse: crypto.

Lemma kinverse_injective (k1 k2: key):
  kinverse k1 = kinverse k2 ->
  k1 = k2.
Proof.
  intros Hinv.
  rewrite <- kinverse_inverse.
  rewrite <- Hinv.
  rewrite kinverse_inverse.
  reflexivity.
Qed.

#[global]
Hint Resolve kinverse_injective: crypto.

Lemma kinverse_surjective (k1: key):
  exists (k2: key), kinverse k2 = k1.
Proof.
  exists (kinverse k1).
  apply kinverse_inverse.
Qed.

#[global]
Hint Resolve kinverse_surjective: crypto.

Lemma kinverse_bijective :
  (forall (k1 k2: key),
    kinverse k1 = kinverse k2 ->
    k1 = k2)
  /\ (forall (k1: key),
    exists (k2: key), kinverse k2 = k1).
Proof.
  split;
    [ apply kinverse_injective
    | apply kinverse_surjective].
Qed.

Inductive data (T: Set): Set :=
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

Theorem data_decidable {T: Set}:
  (forall (t0 t1: T), { t0 = t1 }+{ t0 <> t1 }) ->
  forall (d0 d1: data T), { d0 = d1 }+{ d0 <> d1 }.
Proof.
  intros HTdec.
  induction d0 as [t0 | k0 | k0 d0 IHd0 | d0 IHd0 | d00 IHd00 d01 IHd01],
    d1 as [t1 | k1 | k1 d1 | d1 | d10 d11];
  try (right; discriminate).
  { case (HTdec t0 t1);
    [intros <-; left; reflexivity
    | intros; right; injection;
        contradiction]. }
  { case (key_decidable k0 k1);
    [intros <-; left; reflexivity
    | intros Hneq; right; injection;
        contradiction]. }
  { case (key_decidable k0 k1);
    [intros <-
    | intros; right; injection; contradiction].
    case (IHd0 d1);
    [intros <-; left; reflexivity
    | intros; right; injection; contradiction]. }
  { case (IHd0 d1);
    [intros <-; left; reflexivity
    | intros; right; injection; contradiction]. }
  { case (IHd00 d10);
    [intros <-
    | intros; right; injection; contradiction].
    case (IHd01 d11);
    [intros <-; left; reflexivity
    | intros; right; injection; contradiction]. }
Qed.

Definition sign {T: Set}(d: data T)(k: key): data T :=
  pair d (kapply k (hash d)).

Definition check {T: Set}(d: data T)(k: key): Prop :=
  match d with
  | pair d' s' =>
    match s' with
    | kapply k' s'' =>
      k = kinverse k' /\ s'' = hash d'
    | _ => False
    end
  | _ => False
  end.

Eval compute in (sign (value 1) (private 1)).
Example ex1:
  check (sign (value 1) (private 1)) (public 1).
Proof.
  firstorder.
Qed.

(** Verify signature checking and signing *)

Theorem sig_check {T: Set}(d: data T)(k1 k2: key):
  k1 = kinverse k2 ->
  check (sign (value d) k1) k2.
Proof.
  intros H.
  subst.
  firstorder.
  auto with crypto.
Qed.

Theorem sign_only {T: Set}(d0: data T)(k0: key):
  check d0 k0 ->
  exists (d1: data T)(k1: key),
    sign d1 k1 = d0 /\ k0 = kinverse k1.
Proof.
  destruct d0 as [t0 | k0' | k0' d0' | d0' | d0_0 d0_1];
    unfold check; try contradiction.
  destruct d0_1 as [t0 | k0' | k0' d0_1' | d0_1' | d0_1_0 d0_1_1];
    unfold check; try contradiction.
  intros [-> ->].
  exists d0_0; exists k0'.
  split; trivial.
Qed.

(** I would prefer using sets here, but will use lists to take advantage
  of structured mechanisms for traversal *)

(** [recoverable0] takes a data element [d] and appends a list of new data
  that is recoverable from [d] to [d]. *)
  
Fixpoint recoverable0 {T: Set}(d: data T): list (data T) :=
  cons d (match d with
    | kapply _ d => recoverable0 d
    | pair d1 d2 => app (recoverable0 d1) (recoverable0 d2)
    | _ => nil
    end).

Eval compute in recoverable0 (sign (value 1) (private 1)).

(** [recoverable] takes a list of data [dset] and walks the list with
  [recoverable0] to create a list of all data recoverable from the list
  of data.  This is effectively a fold of [recoverable0] over the input
  [dset] *)

Fixpoint recoverable {T: Set}(dset: list (data T)): list (data T) :=
  match dset with
  | nil => nil
  | cons h t => app (recoverable0 h) (recoverable t)
  end.

Eval compute in recoverable (cons (sign (value 1) (private 1)) nil).

(** This is dorky *)

Theorem recoverable_from_single {T: Set}(d: data T)(dset: list (data T)):
  In d (recoverable dset) ->
  exists (d0: data T), In d (recoverable0 d0).
Proof.
  intros.
  exists d.
  destruct d;
    simpl;
    tauto.
Qed.

(* Hint Resolve app_nil_r. *)

Theorem recoverable_single {T: Set}(d: data T):
  recoverable (cons d nil) = recoverable0 d.
Proof.
  intros.
  simpl.
  apply app_nil_r.
Qed.

(* Theorem recoverable_subterm: forall d dset, In d (recoverable dset) -> exists d0 *)
Lemma recoverable0_self {T: Set}(d: data T):
  In d (recoverable0 d).
Proof.
  destruct d; simpl;
  left; reflexivity.
Qed.

Lemma recoverable0_kapply {T: Set}(k: key)(d0 d1: data T):
  In (kapply k d0) (recoverable0 d1) ->
  In d0 (recoverable0 d1).
Proof.
  generalize dependent d0.
  induction d1; simpl;
    intros d0 [H | H];
    try contradiction;
    try (inversion H; fail).
  { inversion H; subst; clear H.
    right.
    apply recoverable0_self. }
  { right. apply IHd1; apply H. }
  { right. apply in_app_or in H.
    inversion_clear H as [H1 | H2];
    apply in_or_app.
    { apply IHd1_1 in H1.
      left; trivial. }
    { apply IHd1_2 in H2.
      right; trivial. } }
Qed.

Lemma recoverable0_pair {T: Set}(d0 d1 d2: data T):
  In (pair d0 d1) (recoverable0 d2) ->
  In d0 (recoverable0 d2) /\ In d1 (recoverable0 d2).
Proof.
  induction d2; simpl;
    intros [H | H0];
    try contradiction;
    try (inversion H; fail).
  { split; right;
      apply IHd2 in H0;
      inversion_clear H0;
      trivial. }
  { inversion H; subst; clear H.
    split; right; apply in_or_app.
    { left; apply recoverable0_self. }
    { right; apply recoverable0_self. } }
  { apply in_app_or in H0.
    inversion_clear H0.
    { apply IHd2_1 in H.
      inversion_clear H.
      split; right; apply in_or_app;
        left; trivial. }
    { apply IHd2_2 in H.
      inversion_clear H.
      split; right; apply in_or_app;
        right; trivial. } }
Qed.

Theorem in_recoverable0_transitive {T: Set}(d0 d1 d2: data T):
  In d0 (recoverable0 d1) ->
  In d1 (recoverable0 d2) ->
  In d0 (recoverable0 d2).
Proof.
  generalize dependent d2;
  generalize dependent d0;
  generalize dependent d1.
  induction d1;
  simpl;
  try (intros d0 d2 [<- | H] H0; trivial; contradiction).
  { intros d0 d2 [<- | H0] H1; trivial.
    (* In (kapply k d1) (recoverable0 d2) *)
    apply recoverable0_kapply in H1.
    apply IHd1; trivial. }
  { intros d0 d2 [<- | H0] H1; trivial.
    apply recoverable0_pair in H1.
    inversion_clear H1.
    apply in_app_or in H0.
    inversion_clear H0.
    { apply IHd1_1; trivial. }
    { apply IHd1_2; trivial. } }
Qed.

Theorem in_recoverable0_in_recoverable {T: Set}(d0 d1: data T)(ds: list (data T)):
  In d0 (recoverable0 d1) ->
  In d1 ds ->
  In d0 (recoverable ds).
Proof.
  induction ds; simpl;
    try contradiction.
  intros Hd0d1 [-> | Hd1];
    apply in_or_app;
    [left | right; apply IHds];
    trivial.
Qed.

Theorem recoverable_increasing {T: Set}(ds: list (data T)):
  forall (d: data T),
    In d ds ->
    In d (recoverable ds).
Proof.
  induction ds; simpl;
    intros d H;
    try contradiction.
  inversion_clear H.
  { subst.
    destruct d; simpl;
      left; reflexivity. }
  { apply IHds in H0.
    apply in_or_app.
    right; trivial. }
Qed.

Theorem in_recoverable_singleton {T: Set}(d: data T)(ds: list (data T)):
  In d (recoverable ds) ->
  exists (d': data T), In d' ds /\ In d (recoverable (d'::nil)).
Proof.
  induction ds; simpl;
    try contradiction.
  simpl in IHds; intros H.
  apply in_app_or in H.
  inversion_clear H.
  { exists a.
    split; [left; reflexivity |].
    rewrite app_nil_r.
    trivial. }
  { apply IHds in H0.
    inversion_clear H0.
    inversion_clear H.
    exists x.
    split; [right |];
      trivial. }
Qed.

Theorem in_recoverable_union {T: Set}(ds0 ds1: list (data T)):
  forall (d: data T),
    In d (recoverable (ds0 ++ ds1)) <->
    In d (recoverable ds0) \/ In d (recoverable ds1).
Proof.
  intros d; split.
  { intros Happ.
    apply in_recoverable_singleton in Happ.
    inversion_clear Happ;
      simpl in H; rewrite app_nil_r in H.
    inversion_clear H as (H0 & H1).
    apply in_app_or in H0.
    inversion_clear H0 as [H | H];
      [left | right];
      apply in_recoverable0_in_recoverable with x;
      trivial. }
  { generalize dependent ds1;
      generalize dependent d;
      induction ds0;
      simpl.
    { intros d ds1 [Hcontra | Hdds1];
        try contradiction;
        trivial. }
    { intros d ds1 [Hdads0 | Hdds1];
      apply in_or_app.
      { apply in_app_or in Hdads0.
        inversion_clear Hdads0;
          try (left; trivial; fail).
        right; apply IHds0.
        left; trivial. }
      { right; apply IHds0.
        right; trivial. } } }
Qed.

Lemma recoverable0_recoverable {T: Set}(d: data T):
  recoverable (d::nil) = recoverable0 d.
Proof.
  simpl.
  apply app_nil_r.
Qed.

Lemma in_recoverable_recoverable0 {T: Set}(d: data T):
  forall (d0: data T),
    In d0 (recoverable (recoverable0 d)) ->
    In d0 (recoverable0 d).
Proof.
  induction d; simpl; intros;
  try (inversion_clear H; try contradiction;
      left; trivial; fail).
  { inversion_clear H as [<- | Hin];
      [left; reflexivity | right].
    apply in_app_or in Hin.
    inversion_clear Hin as [H | H]; trivial.
    apply IHd; trivial. }
  { inversion_clear H as [<- | Hin];
      [left; reflexivity | right].
    apply in_app_or in Hin.
    inversion_clear Hin as [H | H]; trivial.
    rewrite in_recoverable_union in H.
    apply in_or_app;
    inversion_clear H as [H0 | H0];
      [ left; apply IHd1 | right; apply IHd2 ];
      trivial. }
Qed.

Theorem in_recoverable_idempotent {T: Set}(ds: list (data T)):
  forall (d: data T),
    In d (recoverable (recoverable ds)) <->
    In d (recoverable ds).
Proof.
  induction ds; simpl.
  { intros; split; contradiction. }
  { intros d; split; intros H.
    { apply in_or_app.
      rewrite in_recoverable_union in H.
      inversion_clear H as [H0 | H0].
      { apply in_recoverable_recoverable0 in H0.
          left; trivial. }
      { right; rewrite <- IHds; trivial. } }
    { apply in_app_or in H.
      rewrite in_recoverable_union.
      inversion_clear H as [H0 | H0].
      { left.
        apply recoverable_increasing; trivial. }
      { right; rewrite IHds; trivial. } } }
Qed.

Inductive analyzable {T: Set}: list (data T) -> list (data T) -> Prop :=
| analyzable_inj:
  forall (d: data T)(ds an: list (data T)),
    In d ds -> In d an ->
    analyzable ds an
| analyzable_fst:
  forall (d0 d1: data T)(an: list (data T)),
    In (pair d0 d1) an -> In d0 an ->
    forall (ds: list (data T)), analyzable ds an
| analyzable_snd:
  forall (d0 d1: data T)(an: list (data T)),
    In (pair d0 d1) an -> In d1 an ->
    forall (ds: list (data T)), analyzable ds an
| analyzable_decrypt:
  forall (k: key)(d: data T)(an: list (data T)),
    In (kapply k d) an /\ In (kval (kinverse k)) an ->
    In d an ->
    forall (ds: list (data T)), analyzable ds an.
