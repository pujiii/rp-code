Require Export UniMath.Foundations.All.
Require Export UniMath.MoreFoundations.All.

Definition apD {X:Type} {Y : X -> Type} (s : ∏ x, Y x) {x x':X} (p : x = x') :
  transportf Y p (s x) = s x'.
Proof.
  now induction p.
Defined.

Module Export S1.

Private Inductive S1 : Type :=
| base : S1.

Axiom loop : base = base.

Definition S1_ind (P : S1 -> Type) (b : P base) (l : transportf P loop b = b)
  : forall x : S1, P x :=
  fun x =>
    match x with
    | base => b
    end.

Axiom S1_ind_loop : forall (P : S1 -> Type) (b : P base) (l : transportf P loop b = b),
  apD (S1_ind P b l) loop = l.

Definition S1_recur (A : Type) (a : A) (l : a = a) : S1 -> A :=
  fun x =>
    match x with
    | base => a
    end.

Axiom S1_recur_loop : forall (A : Type) (a : A) (l : a = a) ,
  maponpaths (S1_recur A a l) loop = l.

End S1.


Lemma circle_eq_sym : forall (x y : S1), x = y -> y = x.
Proof.
  intros x y eqxy.
  rewrite eqxy.
  reflexivity.
Qed.

Lemma base_refl : base = base.
Proof.
  reflexivity.
Qed.

Lemma circle_connected : forall (z: S1), ∥ z = base ∥.
Proof.
  intro z.
  use (S1_ind (fun z => ∥ z = base ∥) _ _ z).
  - exact (hinhpr (idpath base)). 
  - apply propproperty.
Qed.

Definition ev (A : Type) : 
  (S1 → A) → ∑ (a : A), a = a :=
  fun g => tpair (fun a => a = a) (g base) (maponpaths g loop).

(* Definition ev' (A : Type) (a : A) :
  (S1 -> A × a = a) -> (a = a) :=
  fun t => (pr2 t) @ (maponpaths (pr1 t) loop). *)

Definition ve (A : Type) :
  (∑ (a : A), a = a) → (S1 → A) :=
  fun p => S1_recur A (pr1 p) (pr2 p).

Theorem evisweq (A : UU) : isweq (ev A).
Proof.
  use isweq_iso.
  - exact (ve A).
  - intro f.
    unfold ve.
    unfold ev.
    simpl.
    apply funextfun. (* provided by Copilot *)
    use S1_ind.
    + reflexivity.
    + Check transportf_paths_FlFr.
      simpl.
      rewrite transportf_paths_FlFr.
      rewrite S1_recur_loop.
      simpl.
      use pathsinv0l.
  - intro p.
    unfold ev.
    unfold ve.
    simpl.
    rewrite S1_recur_loop.
    reflexivity.
Qed.

Definition SetBundle (B : UU) : UU := ∑ (A : UU) (f : A -> B), ∏ (b : B), isaset (hfiber f b).

Definition is_groupoid (A : UU) := ∏ (x: A) (y : A), isaset (x = y).

Lemma map_rl {A : UU} : (∑ (B : UU) (f : B -> A) , ∏ (a : A), isaset (hfiber f a)) -> (A -> hSet).
Proof.
  intro Bf.
  intro a.
  exact (make_hSet _ ((pr2 (pr2 Bf)) a)).
Defined.

Lemma map_lr {A : UU} : (A -> hSet) -> (∑ (B : UU) (f : B -> A) , ∏ (a : A), isaset (hfiber f a)).
Proof.
  intro f.
  use tpair.
  - exact (∑ (a : A), f a).
  - simpl.
    use tpair.
    + exact pr1.
    + simpl.
      intro a.
      use (isofhlevelweqf 2).
      * exact (f a).
      * use weq_iso.
        -- intro x.
           use make_hfiber. 
           ++ use tpair.
              ** exact a.
              ** exact x.
           ++ reflexivity.
        -- intro x.
           refine (transportf f _ (pr21 x)).
           exact (pr2 x).
        -- simpl.
           intro x.
           reflexivity.
        -- intro x.
           induction x as [y z].
           induction z.
           reflexivity.
      * set (test := f a).
        apply (pr2 test). (* Given by copilot. *)
Defined.

Lemma map_inv_eq_lrrl {A : Type} (Bf : (∑ (B : UU) (f : B -> A) , ∏ (a : A), isaset (hfiber f a))) : (map_lr (map_rl Bf)) = Bf.
Proof.
unfold map_lr.
unfold map_rl.  
Admitted.

Lemma map_inv_eq_rllr {A : UU} (f : A -> hSet) : (map_rl (map_lr f)) = f.
Proof.
unfold map_rl.
unfold map_lr.
Admitted.

Lemma set_families (A : UU) : (∑ (B : UU) (f : B -> A) , ∏ (a : A), isaset (hfiber f a)) ≃ (A -> hSet).
Proof.
  exists map_rl. 
  apply (isweq_iso map_rl map_lr).
  - exact map_inv_eq_lrrl.
  - exact map_inv_eq_rllr.
Qed.

Lemma setbundle_isgroupoid (B : UU) : is_groupoid (SetBundle B).
Proof.
unfold is_groupoid.
unfold SetBundle.
intros x y.
Admitted.

Theorem ev_set_equiv (B : UU) : isweq (ev (hSet)).
Proof.
use evisweq.
Qed.

Theorem setbundle_s1_set : SetBundle S1 ≃ (S1 -> hSet).
Proof.
simpl.  
unfold SetBundle.
simpl.
use (set_families S1).
Qed.

Theorem setbundle_s1_sigmaequals : SetBundle S1 ≃ ∑ (X : hSet), X = X.
Proof.
  use weq_iso.
  - intro s.
    unfold SetBundle in s.
    use tpair.
    + induction s as [A s'].
      induction s' as [f g].
      exact (hfiber f base).

Theorem setbundle_s1_sigmasimeq : SetBundle S1 ≃ ∑ (X : hSet), X ≃ X.

Theorem setbundle_s1_isSet_times_isEquiv : SetBundle S1 ≃ ∑ (X : UU) (f : X -> X), isaset X × isweq X.