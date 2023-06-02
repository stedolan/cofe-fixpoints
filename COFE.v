(*
 * Definition of OFEs and COFEs
 *)

Structure OFE := mkOFE {
  Carrier :> Type;
  Equiv : nat -> Carrier -> Carrier -> Prop;

  Equiv_zero : forall a b, Equiv 0 a b;
  Equiv_decr : forall n a b, Equiv (S n) a b -> Equiv n a b;
  Equiv_refl : forall n a, Equiv n a a;
  Equiv_sym : forall n a b, Equiv n a b -> Equiv n b a;
  Equiv_trans : forall n a b c, Equiv n a b -> Equiv n b c -> Equiv n a c
}.

Notation "x ≡[ n ] y" := (Equiv _ n x y) (at level 70).

(* Instead of quotienting (which is awkward in Coq), let's deal with equality
   setoid-style, by *defining* equality as the intersection of ≡[n] *)
Notation "x ≡ y" := (forall n, x ≡[n] y) (at level 70).

Definition Seq (A : OFE) := nat -> A.
Definition Coherent {A} (x : Seq A) :=
  forall n, x n ≡[n] x (S n).
Definition Converges {A} (x : Seq A) (Cx : Coherent x) (l : A) :=
  forall n, l ≡[n] x n.

Structure COFE := mkCOFE {
  Ofe :> OFE;
  Limit : forall x, Coherent x -> Ofe;
  Limit_Converges : forall x (Cx : Coherent x), Converges x Cx (Limit x Cx);
}.

Lemma Equiv_le {A : OFE} {x y : A} :
  forall n m, n <= m -> x ≡[m] y -> x ≡[n] y.
Proof. induction 1; [easy | auto using Equiv_decr]. Qed.

Lemma Coherent_le {A : OFE} (x : Seq A) (Cx : Coherent x) :
  forall n m, n <= m -> x n ≡[n] x m.
Proof.
  induction 1.
  - auto using Equiv_refl.
  - eapply Equiv_trans. apply IHle. apply (Equiv_le _ _ H). apply Cx.
Qed.


(*
 * We will prove that iterating a contractive function yields the unique fixed point
 * but we first need to define "unique" and "iterate"
 *)

Inductive Exists_unique (A : OFE) (P : A -> Prop) :=
| exists_unique (x : A) (Px : P x) (Unique : forall y, P y -> x ≡ y).

Fixpoint iterate {A : OFE} (f : A -> A) (x : A) n :=
  match n with
  | 0 => x
  | S n => f (iterate f x n)
  end.

(*
 * Theorem 1:
 * If a function is contractive then it has a unique fixed point,
 * found by iterating from an arbitrary starting point.
 *)
Section Contractive.
  Variable (A : COFE).
  
  Definition Contractive (f : A -> A) :=
    forall n x y, x ≡[n] y -> f x ≡[S n] f y.

  Variable (f : A -> A) (f_Contractive : Contractive f).

  Lemma Contractive_at_most_one_fixed_point {x y} : f x ≡ x -> f y ≡ y -> x ≡ y.
  Proof.
    intros Fix_x Fix_y n. induction n; cbn.
    - apply Equiv_zero.
    - eapply Equiv_trans. eapply Equiv_sym. apply Fix_x.
      eapply Equiv_trans. apply f_Contractive. apply IHn.
      apply Fix_y.
  Qed.

  Lemma Contractive_convergence x : Coherent (iterate f x).
  Proof.
    intro n. induction n; cbn.
    - apply Equiv_zero.
    - apply f_Contractive. apply IHn.
  Qed.

  Definition Contractive_limit x := Limit A (iterate f x) (Contractive_convergence x).

  Lemma Contractive_fixed_point x : f (Contractive_limit x) ≡ Contractive_limit x.
  Proof.
    intros [|n]; [apply Equiv_zero | ].
    eapply Equiv_trans.
    - apply f_Contractive. apply Limit_Converges.
    - apply Equiv_sym. apply Limit_Converges.
  Qed.

  Theorem Contractive_functions_have_unique_fixed_points (inhab : A) : Exists_unique A (fun x => f x ≡ x).
  Proof.
    apply (exists_unique A _ (Contractive_limit inhab) (Contractive_fixed_point inhab)).
    intros; eapply Contractive_at_most_one_fixed_point; auto using Contractive_fixed_point.
  Qed.
End Contractive.

(*
 * Theorem 2:
 * If a function is contractive on fixed points then it has a unique fixed point,
 * found by iterating from an arbitrary starting point.
 *)
Section Contractive_on_fixed_points.
  Variable (A : COFE).

  Definition ContractiveFP (f : A -> A) :=
    forall n x y, x ≡[n] y -> f x ≡[n] x -> f y ≡[n] y -> f x ≡[S n] f y.

  Variable (f : A -> A) (f_ContractiveFP : ContractiveFP f).

  Lemma ContractiveFP_at_most_one_fixed_point {x y} : f x ≡ x -> f y ≡ y -> x ≡ y.
  Proof.
    intros Fix_x Fix_y n. induction n; cbn.
    - apply Equiv_zero.
    - eapply Equiv_trans. apply Equiv_sym. apply Fix_x.
      eapply Equiv_trans. apply f_ContractiveFP. apply IHn. apply Fix_x. apply Fix_y.
      apply Fix_y.
  Qed.
  
  Lemma ContractiveFP_lemma {z n} : z ≡[n] f z -> f z ≡[S n] f (f z).
  Proof.
    induction n; intros Hz.
    - apply f_ContractiveFP; apply Equiv_zero.
    - apply f_ContractiveFP. easy. apply Equiv_sym. easy. apply Equiv_sym. apply IHn. apply Equiv_decr. easy.
  Qed.

  Lemma ContractiveFP_convergence x : Coherent (iterate f x).
  Proof.
    intro n. induction n; cbn.
    - apply Equiv_zero.
    - apply ContractiveFP_lemma. easy.
  Qed.

  Definition ContractiveFP_limit x := Limit A (iterate f x) (ContractiveFP_convergence x).

  Lemma ContractiveFP_fixed_point x : f (ContractiveFP_limit x) ≡ ContractiveFP_limit x.
  Proof.
    intro n; induction n; cbn; [ apply Equiv_zero | ].
    eapply Equiv_trans.
    - apply f_ContractiveFP.
      * apply Limit_Converges. 
      * apply IHn.
      * apply Equiv_sym. apply ContractiveFP_convergence.
    - apply Equiv_sym. apply Limit_Converges.
  Qed.

  Theorem ContractiveFP_functions_have_unique_fixed_points (inhab : A) : Exists_unique A (fun x => f x ≡ x).
  Proof.
    apply (exists_unique A _ (ContractiveFP_limit inhab) (ContractiveFP_fixed_point inhab)).
    intros; eapply ContractiveFP_at_most_one_fixed_point; auto using ContractiveFP_fixed_point.
  Qed.
End Contractive_on_fixed_points.


(*
 * Example: showing that f(x) = if x = 0 then 0 else f(f(x-1)) uniquely defines f
 *)

Require Import PeanoNat.
Require Import Lt.
Section Example.
  Definition NN_OFE : OFE.
    apply (mkOFE (nat -> nat) (fun n f g => forall k, k < n -> f k = g k)).
    - inversion 1.
    - auto.
    - auto.
    - auto using eq_sym.
    - eauto using eq_trans.
  Defined.

  Lemma equality_is_extensional {f g : NN_OFE} : f ≡ g -> forall x, f x = g x.
  Proof. intros Hfg x. apply (Hfg (S x)). auto. Qed.

  Definition Limit_NN (x : Seq NN_OFE) (Cx : Coherent x) : NN_OFE :=
    fun n => x (S n) n.

  Definition NN_COFE : COFE.
    apply (mkCOFE NN_OFE Limit_NN).
    intros x Cx n k Hk.
    apply (Coherent_le x Cx _ _ Hk).
    auto.
  Defined.

  Definition zero_fn (f : NN_COFE) : NN_COFE :=
    fun x =>
      match x with
      | 0 => 0
      | S n => f (f n)
      end.

  Lemma partial_fix_zero_fn {n} {f : NN_COFE} : zero_fn f ≡[n] f -> forall k, k < n -> f k = 0.
  Proof.
    intros Hfix.
    induction n; cbn; intros k Hk.
    - inversion Hk.
    - destruct k as [|k]; cbn.
      * rewrite <- Hfix by auto. easy.
      * rewrite <- Hfix by auto.
        cbn.
        specialize (IHn (Equiv_decr _ _ _ _ Hfix)).
        rewrite (IHn k) by (auto using Lt.lt_S_n).
        rewrite <- Hfix by (auto using PeanoNat.Nat.lt_0_succ).
        easy.
  Qed.

  Lemma is_contractiveFP : ContractiveFP NN_COFE zero_fn.
  Proof.
    intros [|n] f g Hfg Hf Hg [|k] Hk; cbn; try easy;
      apply Lt.lt_S_n in Hk; try solve [inversion Hk].
    rewrite (partial_fix_zero_fn Hf k) by auto.
    rewrite (partial_fix_zero_fn Hg k) by auto.
    apply Hfg.
    apply PeanoNat.Nat.lt_0_succ.
  Qed.

  Lemma unique_fixed :
    Exists_unique _ (fun f => zero_fn f ≡ f).
  Proof. apply ContractiveFP_functions_have_unique_fixed_points. apply is_contractiveFP. easy. Qed.

  (* zero_fn is not contractive, so Theorem 1 would not have been enough *)
  Lemma noncontractive : ~(Contractive NN_COFE zero_fn).
  Proof.
    intros H.
    specialize (H 1 (fun x => 1) (fun x => match x with 0 => 1 | S _ => 2 end)).
    cbn in H.
    specialize (H ltac:(inversion 1; easy) 1 ltac:(auto)).
    cbn in H.
    congruence.
  Qed.
End Example.
