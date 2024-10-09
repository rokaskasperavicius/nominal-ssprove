From Coq Require Import Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".

From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool ssrnum eqtype
  choice reals distr seq all_algebra fintype realsum.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap ffun fperm.
From Mon Require Import SPropBase.
From Crypt Require Import Prelude Axioms ChoiceAsOrd SubDistr Couplings
  RulesStateProb UniformStateProb UniformDistrLemmas StateTransfThetaDens
  StateTransformingLaxMorph choice_type pkg_core_definition pkg_notation
  pkg_tactics pkg_composition pkg_heap pkg_semantics pkg_lookup pkg_advantage
  pkg_invariants pkg_distr pkg_rhl pkg_composition Package Prelude.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

(* Must come after importing Equations.Equations, who knows why. *)
From Crypt Require Import FreeProbProg.

From HB Require Import structures.

From NominalSSP Require Import Nominal Fresh.



Import Num.Theory.

Set Equations With UIP.
Set Equations Transparent.

Import SPropNotations.
Import PackageNotation.
Import RSemanticNotation.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

#[local] Open Scope rsemantic_scope.

#[local] Open Scope fset.
#[local] Open Scope fset_scope.
#[local] Open Scope type_scope.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
#[local] Open Scope real_scope.


(* Code as nominal *)

#[non_forgetful_inheritance]
HB.instance Definition _ : DeclareDiscrete R := DeclareDiscrete.Build R.
HB.instance Definition _ : DeclareDiscrete Interface := DeclareDiscrete.Build Interface.

Program Definition Location_IsNominal
  := IsNominal.Build Location (λ π l, (l.π1; natize (π (atomize l.π2)))) _ _.
Obligation 1. by elim: x => [T n]. Qed.
Obligation 2. rewrite fpermM natizeK //. Qed.

HB.instance Definition _ : IsNominal (sigT (λ _, nat)) := Location_IsNominal.
(*
HB.instance Definition _ : Choice Location := _.
HB.instance Definition _ : hasOrd Location := _.
HB.instance Definition _ : IsNominal Location := Location_IsNominal.
 *)


Fixpoint rename_code_def {A} π (c : raw_code A) := 
  match c with
  | ret x => ret x
  | opr o x k => opr o x (fun y => rename_code_def π (k y))
  | getr l k => getr (rename π l) (fun y => rename_code_def π (k y))
  | putr l v k => putr (rename π l) v (rename_code_def π k)
  | pkg_core_definition.sampler op k =>
      pkg_core_definition.sampler op (fun y => rename_code_def π (k y))
  end.

Program Definition code_IsNominal {A}
  := IsNominal.Build (raw_code A) rename_code_def _ _.
Obligation 1.
  elim: x; intros; try destruct l; simpl; try setoid_rewrite H; reflexivity.
Qed.
Obligation 2.
  elim: x; intros; try destruct l; simpl; try setoid_rewrite H; try reflexivity.
  1,2: unfold rename; simpl; rewrite fpermM natizeK //.
Qed.

HB.instance Definition _ {A} : IsNominal (raw_code A) := code_IsNominal.

Lemma mcode_bind {A B} : ∀ f (c : raw_code A) (k : A → raw_code B),
  rename f (a ← c ;; k a) = (a ← rename f c ;; rename f (k a)).
Proof.
  intros f c k.
  unfold rename.
  induction c;
    simpl; try setoid_rewrite H;
    try setoid_rewrite IHc; done.
Qed.


(* Bug: swapping the following two lines changes behaviour *)
(*
HB.instance Definition _ : Choice Location := _.
HB.instance Definition _ : hasOrd Location := _.
 *)

#[export]
Instance mcode_valid {L : {fset Location}} {I A f} {c : raw_code A}
  : ValidCode L I c → ValidCode (f ∙ L) I (f ∙ c).
Proof.
  intros H.
  induction H.
  + apply valid_ret.
  + apply valid_opr; easy.
  + apply valid_getr.
    - by apply mem_imfset.
    - apply H1.
  + apply valid_putr.
    - by apply mem_imfset.
    - apply IHvalid_code.
  + apply valid_sampler.
    apply H0.
Qed.

(* Package as nominal *)

Definition mtyped f : typed_raw_function → typed_raw_function
  := fun t => match t with
              | (T; P; k) => (T; P; fun s => rename f (k s))
              end.

Program Definition typed_IsNominal : IsNominal typed_raw_function
  := IsNominal.Build _ mtyped _ _.
Obligation 1.
  destruct x as [S [T k]].
  simpl.
  do 3 f_equal.
  by setoid_rewrite rename_id.
Qed.
Obligation 2.
  destruct x as [S [T k]].
  simpl.
  do 3 f_equal.
  by setoid_rewrite rename_comp.
Qed.

HB.instance Definition _ : IsNominal typed_raw_function
  := typed_IsNominal.

Program Definition raw_package_IsNominal : IsNominal raw_package
  := IsNominal.Build _ (λ π, mapm (rename π)) _ _.
Obligation 1.
  apply eq_fmap => i.
  rewrite mapmE.
  destruct (x i); [| reflexivity ].
  rewrite //= rename_id //.
Qed.
Obligation 2.
  rewrite -mapm_comp.
  apply eq_mapm => t.
  rewrite //= rename_comp //.
Qed.

HB.instance Definition _ : IsNominal raw_package
  := raw_package_IsNominal.

#[export]
Instance rename_valid {L I E p} f :
  ValidPackage L I E p → ValidPackage (rename f L) I E (rename f p).
Proof.
  intros [V].
  apply prove_valid_package.
  intros [n [A B]] H.
  specialize (V (n, (A, B)) H).
  destruct V as [k [V1 V2]].
  exists (fun a => rename f (k a)).
  split.
  - rewrite /rename mapmE V1 //.
  - intros a.
    apply mcode_valid.
    apply V2.
Qed.


(* Pr proof *)

Definition my_inv' π := fun '(s0, s1) =>
  ∀ l, get_heap s0 l = get_heap s1 (π ∙ l).

Fixpoint importless {A} (c : raw_code A) := 
  match c with
  | ret x => ret x
  | opr o _ k => importless (k (chCanonical (chtgt o)))
  | getr l k => getr l (fun x => importless (k x))
  | putr l v k => putr l v (importless k)
  | pkg_core_definition.sampler op k =>
      pkg_core_definition.sampler op (fun x => importless (k x))
  end.

Lemma renameK {X : nomType} π : cancel (@rename X π) (rename π^-1%fperm).
Proof.
  intros x.
  rewrite renameK //.
Qed.

Lemma r_rename {A} π (c : raw_code A) :
    ⊢ ⦃ λ '(h₀, h₁), my_inv' π (h₀, h₁) ⦄
        importless c ≈ importless (π ∙ c)
      ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ my_inv' π (s0, s1) ⦄.
Proof.
  induction c.
  + by apply r_ret.
  + unfold rename; simpl.
    apply H.
  + apply r_get_remember_lhs => x.
    destruct l as [T n]; simpl.
    eapply r_get_remind_rhs.
    2: apply r_forget_lhs, H.
    intros s0 s1 [h1 h2].
    unfold rem_lhs, rem_rhs in h2 |- *.
    subst; symmetry.
    apply (h1 (T; n)).
  + apply r_put_vs_put.
    ssprove_restore_pre; [| apply IHc ].
    intros s0 s1 H1.
    intros l'.
    elim: (eq_dec l l') => [H4|H4].
      * subst; rewrite !get_set_heap_eq //.
      * rewrite !get_set_heap_neq.
        ** by apply H1.
        ** apply /negP.
           move => /eqP E.
           apply (f_equal (rename π^-1%fperm)) in E.
           rewrite renameK in E.
           unfold rename in E; simpl in E.
           rewrite natizeK fpermK atomizeK in E.
           apply H4.
           rewrite E.
           by destruct l.
        ** apply /negP.
           move => /eqP E; subst.
           by apply H4.
  + eapply (rsame_head_cmd_alt (cmd_sample op)) ; [
        eapply cmd_sample_preserve_pre
      | idtac
      ].
    apply H.
Qed.

Lemma support_lookup {P : raw_package} {L} {n} {a}
  : support_set P L → support_set (get_op_default P n a) L.
Proof.
  unfold support_set.
  intros supp π inaction.
  specialize (supp π inaction).
  unfold rename in supp.
  apply eq_fmap in supp.
  unfold get_op_default, lookup_op.
  destruct n as [n [S T]].
  specialize (supp n).
  simpl in supp.
  rewrite mapmE in supp.
  destruct (P n).
  2: done.
  destruct t as [S' [T' n']].
  destruct (choice_type_eqP S' S).
  2: done.
  destruct (choice_type_eqP T' T).
  2: done.
  subst.
  rewrite cast_fun_K.
  simpl in supp.
  injection supp => {supp} supp0.
  do 2 apply inj_right_pair in supp0.
  rewrite -{2}supp0 //.
Qed.

Lemma repr_importless {A} (c : raw_code A) : repr (importless c) = repr c.
Proof.
  induction c.
  + done.
  + simpl.
    rewrite H //.
  + simpl.
    f_equal.
    apply functional_extensionality => x.
    rewrite H //.
  + simpl.
    f_equal.
    apply functional_extensionality => x.
    rewrite IHc //.
  + simpl.
    f_equal.
    apply functional_extensionality => x.
    rewrite H //.
Qed.


(* Proof heavily inspired by eq_upto_inv_perf_ind in SSProve *)
Lemma Pr_rename {π} {P : raw_package} {t} :
  Pr P t = Pr (π ∙ P) t.
Proof.
  unfold Pr, Pr_op.
  unfold rename; simpl.
  unfold get_op_default in *.
  rewrite lookup_op_map.
  destruct (lookup_op P RUN) eqn:req; [simpl | done].
  unfold Pr_code.
  unfold Pr_code, SDistr_bind, SDistr_unit.
  rewrite 2!dletE.
  simpl.

  assert (
    ∀ y,
      (λ x : prod (tgt RUN) heap_choiceType, (y x) * (let '(b, _) := x in dunit (R:=R) (T:=tgt RUN) b) t) =
      (λ x : prod (tgt RUN) heap_choiceType, (eq_op x.1 t)%:R * (y x))
  ) as Hrew.
  { intros y. extensionality x.
    destruct x as [x1 x2].
    rewrite dunit1E.
    simpl. rewrite GRing.mulrC. reflexivity.
  }
  rewrite 2!Hrew.

  unfold TransformingLaxMorph.rlmm_from_lmla_obligation_1. simpl.
  unfold SubDistr.SDistr_obligation_2. simpl.
  unfold OrderEnrichedRelativeAdjunctionsExamples.ToTheS_obligation_1.
  rewrite !SDistr_rightneutral. simpl.

  assert (
    ∀ x y : tgt RUN * heap_choiceType,
      (let '(b₀, s₀) := x in λ '(b₁, s₁), b₀ = b₁ ∧ my_inv' π (s₀, s₁)) y →
      (eq_op (fst x) t) ↔ (eq_op (fst y) t)
  ) as Ha.
  { intros [b₀ s₀] [b₁ s₁]. simpl.
    intros [e ?]. rewrite e. intuition auto.
  }

  pose (H := r_rename π (r tt)).
  apply to_sem_jdg in H.
  epose proof (Heq := Pr_eq_empty (my_inv' π)
    (λ '(b0, s0) '(b1, s1), b0 = b1 /\ my_inv' π (s0, s1))
    _ _ H _ Ha).
  rewrite -(repr_importless (r tt)).
  rewrite -(repr_importless (π ∙ r tt)).
  apply Heq.
  Unshelve.
  done.
Qed.

Add Parametric Morphism : Pr with
  signature alpha ==> eq as Pr_mor.
Proof.
  intros x y [π' H0].
  apply distr_ext.
  intros b.
  rewrite -H0.
  apply Pr_rename.
Qed.

