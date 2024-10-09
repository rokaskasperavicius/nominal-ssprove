Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap ffun fperm.

From HB Require Import structures.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.


(* Should not have dependency on SSProve *)

Inductive atom : Type :=
  | atomize : nat → atom.

Definition natize : atom → nat := λ '(atomize n), n.

Lemma natizeK : cancel natize atomize.
Proof. intros []. done. Qed.

Lemma atomizeK : cancel atomize natize.
Proof. done. Qed.

HB.instance Definition _ : Equality atom := _.
HB.instance Definition _ : hasChoice atom := _.
HB.instance Definition _ : hasOrd atom := _.
(*
HB.instance Definition _ : Equality atom := Equality.copy atom (can_type natizeK).
HB.instance Definition _ : hasChoice atom := CanHasChoice natizeK.
HB.instance Definition _ : hasOrd atom := CanHasOrd natizeK.
 *)


HB.mixin Record IsNominal X := {
  rename : {fperm atom} → X → X;
  rename_id : ∀ x, rename 1%fperm x = x;
  rename_comp : ∀ f g x, rename (f * g)%fperm x = rename f (rename g x);
}.

#[short(type="nomType")]
HB.structure Definition Nominal := { X of IsNominal X }.

Arguments rename {_} _%fperm & _.
Implicit Types X Y Z W : nomType.
Implicit Types π τ : {fperm atom}.

(* NomOrd is defined here, so that all `nomType`s will
   also become `NomOrd.type`s. Could also be solved with
   HB.saturate *)
#[short(type="nomOrdType")]
HB.structure Definition NomOrd
  := { X of hasOrd X & Choice X & IsNominal X }.


Declare Scope nominal_scope.
Delimit Scope nominal_scope with nom.
Open Scope nominal_scope.

Notation "π ∙ x" :=
  (rename π%fperm x)
  (at level 35, right associativity)
  : nominal_scope.


Lemma renameK {X} : ∀ π, cancel (@rename X π) (rename π^-1).
Proof. move => π x. rewrite -rename_comp fperm_mulVs rename_id //. Qed.

Lemma renameKV {X} : ∀ π, cancel (rename π^-1) (@rename X π).
Proof. move => π x. rewrite -rename_comp fperm_mulsV rename_id //. Qed.


(* Instances of nomType *)

Program Definition to_Nominal := IsNominal.Build atom appf _ _.
Obligation 2. rewrite fpermM //. Qed.
HB.instance Definition _ : IsNominal atom := to_Nominal.


Program Definition fset_IsNominal {X : nomOrdType} : IsNominal {fset X}
  := IsNominal.Build {fset X} (λ π xs, imfset (rename π) xs) _ _.
Obligation 1.
  rewrite -{2}(imfset_id x).
  apply eq_imfset => l.
  rewrite rename_id //.
Qed.
Obligation 2.
  rewrite -imfset_comp.
  apply eq_imfset => l.
  rewrite rename_comp //.
Qed.

HB.instance Definition _ {X : nomOrdType} : IsNominal {fset X}
  := fset_IsNominal.


Program Definition option_IsNominal {X}
  : IsNominal (option X)
  := IsNominal.Build _ (λ π, omap (rename π))  _ _.
Obligation 1.
  destruct x; rewrite //= rename_id //.
Qed.
Obligation 2.
  destruct x; rewrite //= rename_comp //.
Qed.

HB.instance Definition _ {X} : IsNominal (option X)
  := option_IsNominal.

Program Definition prod_IsNominal {X Y}
  : IsNominal (prod X Y)
  := IsNominal.Build _ (λ π '(x, y), (π ∙ x, π ∙ y)) _ _.
Obligation 1. rewrite 2!rename_id //. Qed.
Obligation 2. rewrite 2!rename_comp //. Qed.

HB.instance Definition _ {X Y} : IsNominal (prod X Y)
  := prod_IsNominal.

#[local]
Lemma fperm_1_inv {T : ordType} : @fperm_inv T 1%fperm = 1%fperm.
Proof.
  rewrite -(fperm_mul1s 1^-1%fperm) fperm_mulsV //.
Qed.

#[local]
Lemma fperm_mul_inv {T : ordType} (π π' : {fperm T})
  : (π * π')^-1%fperm = (π'^-1 * π^-1)%fperm.
Proof.
  eapply fperm_mulsI.
  erewrite fperm_mulsV.
  rewrite fperm_mulA -(fperm_mulA _ π').
  rewrite fperm_mulsV fperm_muls1 fperm_mulsV //.
Qed.

Program Definition fun_IsNominal {X Y}
  : IsNominal (X → Y)
  := IsNominal.Build _ (λ π f x, π ∙ f (π^-1%fperm ∙ x)) _ _.
Obligation 1.
  move: x => f.
  apply functional_extensionality => x.
  rewrite fperm_1_inv 2!rename_id //.
Qed.
Obligation 2.
  move: f g x => π π' f.
  apply functional_extensionality => x.
  rewrite fperm_mul_inv 2!rename_comp //.
Qed.

HB.instance Definition _ {X Y} : IsNominal (X → Y)
  := fun_IsNominal.


(* support set *)

Definition support_set {X} (x : X) (L : {fset atom})
  := ∀ (π : {fperm atom}), (∀ a, a \in L → π a = a) → π ∙ x = x.

Arguments support_set {_} _ _%fset.

(* Does not work with X - probably because of implicit type *)
HB.mixin Record HasFiniteSupport A of IsNominal A := {
  supp : A → {fset atom};
  is_support : ∀ x, support_set x (supp x);
  support_sub : ∀ x F, support_set x F → fsubset (supp x) F;
}.

#[short(type="suppType")]
HB.structure Definition FiniteSupport
  := { X of HasFiniteSupport X & IsNominal X }.

#[short(type="suppOrdType")]
HB.structure Definition SuppOrd
  := { X of hasOrd X & Choice X & IsNominal X & HasFiniteSupport X }.


(* discrete nominal types *)

HB.mixin Record IsDiscrete (X : Type) of IsNominal X :=
  { absorb : ∀ π (x : X), π ∙ x = x }.

#[short(type="discType")]
HB.structure Definition Discrete
  := { D of IsDiscrete D & HasFiniteSupport D & IsNominal D }.

HB.factory Record DeclareDiscrete (X : Type) := {}.

HB.builders Context (X : Type) (_ : DeclareDiscrete X).

  Program Definition to_Nominal := IsNominal.Build X
    (λ _, id) _ _.
  HB.instance Definition _ : IsNominal X := to_Nominal.

  Program Definition to_Support := HasFiniteSupport.Build X (λ _, fset0) _ _.
  Obligation 2. apply fsub0set. Qed.
  HB.instance Definition _ : HasFiniteSupport X := to_Support.

  Program Definition to_Discrete := IsDiscrete.Build X _.
  HB.instance Definition _ : IsDiscrete X := to_Discrete.
HB.end.

HB.instance Definition _ : DeclareDiscrete bool := DeclareDiscrete.Build bool.
HB.instance Definition _ : DeclareDiscrete Prop := DeclareDiscrete.Build Prop.

(*
Lemma supp_disc {D : discType} : ∀ d : D, supp d = fset0.
*)


(* equivariance *)

Definition equivariant {X Y} (f : X → Y)
  := ∀ π x, π ∙ (f x) = f (π ∙ x).

Lemma idE {X} : equivariant (@id X).
Proof. done. Qed.

Lemma compE {X Y Z} (f : Y → Z) (g : X → Y)
  : equivariant f → equivariant g → equivariant (f \o g).
Proof. intros Ef Eg π x. rewrite Ef Eg //. Qed.

Lemma SomeE {X}
  : equivariant (@Some X).
Proof. done. Qed.

Lemma equi2_prove {X Y Z} (f : X → Y → Z)
  : (∀ π x y, π ∙ (f x y) = f (π ∙ x) (π ∙ y)) → equivariant f.
Proof.
  intros P π x.
  apply functional_extensionality => y.
  specialize (P π x (π^-1 ∙ y)).
  rewrite renameKV in P.
  rewrite -P //.
Qed.

Lemma equi2_use {X Y Z} (f : X → Y → Z)
  : equivariant f → (∀ π x y, π ∙ (f x y) = f (π ∙ x) (π ∙ y)).
Proof.
  intros equi π x y.
  rewrite -equi.
  rewrite -{1}(renameK π y).
  done.
Qed.


Lemma adjoin_disc_l {X Y : nomType} {D : discType} {f : X → Y → D} :
  equivariant f → 
  ∀ π x y, f (π ∙ x) y = f x (π^-1 ∙ y).
Proof.
  intros equi π x y.
  rewrite -{1}(renameKV π y).
  rewrite -equi2_use // absorb //.
Qed.

Lemma adjoin_disc_r {X Y : nomType} {D : discType} {f : X → Y → D} :
  equivariant f → 
  ∀ π x y, f x (π ∙ y) = f (π^-1 ∙ x) y.
Proof.
  intros equi π x y.
  rewrite -{1}(renameKV π x).
  rewrite -equi2_use // absorb //.
Qed.

Lemma equi_fun {X Y Z : nomType} {f : X → Y → Z} : equivariant (uncurry f) → equivariant f.
Proof.
  intros H.
  apply equi2_prove.
  intros π x y.
  specialize (H π (x, y)).
  simpl in H.
  apply H.
Qed.

Lemma equi_Prop {X : nomType} (f : X → Prop) : (∀ π x, f x → f (π ∙ x)) → equivariant f.
Proof.
  intros H π x.
  rewrite absorb.
  apply boolp.propext.
  split. { apply H. }
  intros H'.
  rewrite -(renameK π x).
  apply H, H'.
Qed.

Lemma eqE {X : nomType} : equivariant (@eq X).
Proof.
  apply equi_fun, equi_Prop.
  intros π [x x'].
  simpl => [->] //.
Qed.

Lemma support_setE {X : nomType} : equivariant (@support_set X).
Proof.
  apply equi_fun, equi_Prop.
  simpl => π [x F] //= H.
  intros τ H'.
  rewrite adjoin_disc_r.
  2: apply eqE.
  rewrite -2!rename_comp.
  rewrite H //.
  intros a H''.
  rewrite fpermM /comp fpermM /comp.
  rewrite H'.
  1: rewrite fpermK //.
  unfold rename; simpl.
  apply mem_imfset, H''.
Qed.

Lemma equi_bool {X : nomType} {f : X → bool} : (∀ π x, f x → f (π ∙ x)) → equivariant f.
Proof.
  intros H.
  intros π x.
  rewrite absorb.
  destruct (f x) eqn:E.
  + specialize (H π _ E).
    rewrite H //.
  + destruct (f (π ∙ x)) eqn:E'; [| done ].
    specialize (H π^-1%fperm _ E').
    rewrite renameK in H.
    by rewrite H in E.
Qed.

Lemma fsubsetE {X : nomOrdType} : @equivariant _ _ (@fsubset X).
Proof.
  apply equi_fun.
  apply equi_bool.
  simpl => π [F G] //= H.
  apply imfsetS, H.
Qed.

Lemma equi_fset {X} {Y : nomOrdType} {f : X → {fset Y}}
  : (∀ π x, π ∙ f x :<=: f (π ∙ x))%fset → equivariant f.
Proof.
  intros H π x.
  rewrite -boolp.eq_opE eqEfsubset.
  rewrite H //=.
  specialize (H π^-1%fperm (π ∙ x)).
  rewrite renameK in H.
  rewrite -adjoin_disc_r // in H.
  apply fsubsetE.
Qed.

Lemma fsetUE {X : nomOrdType} : equivariant (@fsetU X).
Proof.
  apply equi_fun => π //= [F G] //=.
  apply imfsetU.
Qed.

Lemma fsetIE {X : nomOrdType} : equivariant (@fsetI X).
Proof.
  apply equi_fun => π //= [F G] //=.
  apply imfsetI.
  intros x y _ _ H.
  rewrite -(renameK π x) -(renameK π y) H //.
Qed.

Lemma in_memE {X : nomOrdType} : equivariant (λ (x : X) (xs : {fset X}), x \in xs).
Proof.
  apply equi_fun.
  apply equi_bool => π //= [x xs] //= H.
  eapply (mem_imfset) in H.
  apply H.
Qed.

Lemma eq_opE {X : nomOrdType} : equivariant (@eq_op X).
Proof.
  apply equi_fun.
  apply equi_bool => //= π [F G] //= H.
  rewrite boolp.eq_opE in H.
  rewrite H.
  apply eq_refl.
Qed.

Lemma fdisjointE {X : nomOrdType} : equivariant (@fdisjoint X).
Proof.
  apply equi_fun.
  apply equi_bool => //= π [F G] //= H.
  unfold fdisjoint.
  rewrite -equi2_use; [| apply fsetIE ].
  rewrite adjoin_disc_l; [| apply: eq_opE ].
  replace (_ ∙ fset0) with (@fset0 X); [| rewrite /rename //= imfset0 // ].
  apply H.
Qed.

Lemma suppE {X : suppType} : equivariant (@supp X).
Proof.
  apply equi_fset.
  intros π x.
  rewrite adjoin_disc_l; [| apply fsubsetE ].
  apply support_sub.
  rewrite -adjoin_disc_l; [| apply support_setE ].
  apply is_support.
Qed.

Lemma equi_disc {X Y : discType} : ∀ f : X → Y, equivariant f.
Proof.
  intros f π x.
  rewrite 2!absorb //.
Qed.

Program Definition prod_HasFiniteSupport {X Y : suppType}
  : HasFiniteSupport (prod X Y)
  := HasFiniteSupport.Build _ (λ '(x, y), fsetU (supp x) (supp y)) _ _.
Obligation 1.
  unfold rename; simpl.
  rewrite is_support ?is_support // => a H'.
  1,2: apply H.
  1,2: rewrite in_fsetU H' //=.
  rewrite orbT //.
Qed.
Obligation 2.
  rewrite fsubUset.
  apply /andP; split; apply support_sub => π H'.
  all: specialize (H π H').
  all: unfold rename in H; simpl in H.
  all: injection H => ? ?; by subst.
Qed.

HB.instance Definition _ {X Y : suppType} : HasFiniteSupport (prod X Y)
  := prod_HasFiniteSupport.



Lemma fset1E' {X : nomOrdType} : equivariant (@fset1 X).
Proof.
  intros π x.
  apply eq_fset => x'.
  rewrite in_fset1.
  rewrite (adjoin_disc_r in_memE).
  rewrite in_fset1.
  rewrite adjoin_disc_r //.
  apply eq_opE.
Qed.

Lemma support_set_equi {X Y} {x : X} {F} {f : X → Y}
  : equivariant f → support_set x F → support_set (f x) F.
Proof.
  intros E S π a.
  rewrite E.
  f_equal.
  by apply S.
Qed.


Program Definition seq_IsNominal {X : nomType} : IsNominal (seq X)
  := IsNominal.Build _ (λ π xs, map (rename π) xs) _ _.
Obligation 1.
  rewrite -{2}(map_id x).
  induction x => //=.
  rewrite IHx rename_id //.
Qed.
Obligation 2.
  rewrite -map_comp.
  induction x => //=.
  rewrite IHx rename_comp //.
Qed.

HB.instance Definition _ {X : nomType} : IsNominal (seq X)
  := seq_IsNominal.

Program Definition seq_HasFiniteSupport {X : suppType}
  : HasFiniteSupport (seq X)
  := HasFiniteSupport.Build _ (foldr fsetU fset0 \o map supp) _ _.
Obligation 1.
  induction x => //=.
  change (π ∙ (a :: x)) with (π ∙ a :: π ∙ x).
  f_equal.
  + apply is_support => a' H'.
    apply H.
    rewrite in_fsetU H' //.
  + apply IHx => a' H'.
    apply H.
    rewrite in_fsetU H' orbT //.
Qed.
Obligation 2.
  induction x => //=; [ apply fsub0set |].
  rewrite fsubUset.
  apply /andP; split.
  + apply support_sub => π H'.
    specialize (H π H').
    inversion H.
    rewrite !H1 //.
  + apply IHx => π H'.
    specialize (H π H').
    inversion H.
    rewrite !H2 //.
Qed.

HB.instance Definition _ {X : suppType} : HasFiniteSupport (seq X)
  := seq_HasFiniteSupport.

Lemma fsetE {X : nomOrdType} : @equivariant (seq X) _ fset.
Proof.
  intros π xs.
  rewrite /rename //= imfset_fset //.
Qed.


Lemma eq_in_F {X} {π π' : {fperm atom}} {F} {x : X} :
  support_set x F →
  {in F, π =1 π'} →
  (* (∀ x, x \in F → π x = π' x) →  *)
  π ∙ x = π' ∙ x.
Proof.
  unfold support_set.
  intros ss H.
  eapply can_inj.
  1: intros y; apply renameK.
  erewrite renameK.
  rewrite -rename_comp.
  symmetry.
  apply ss.
  intros a amemF.
  specialize (H a amemF).
  rewrite fpermM //=.
  rewrite -H.
  rewrite fpermK //.
Qed.

Lemma eq_in_supp {X : suppType} {π π' : {fperm atom}} {x : X} :
  {in supp x, π =1 π'} →
  π ∙ x = π' ∙ x.
Proof.
  apply eq_in_F.
  apply is_support.
Qed.

Definition disj {X Y : suppType} (x : X) (y : Y) := fdisjoint (supp x) (supp y).

Lemma disjE {X Y : suppType} : equivariant (@disj X Y).
Proof.
  apply equi_fun => π //= [x y] //=.
  unfold disj.
  rewrite equi2_use; [| apply: fdisjointE ].
  rewrite 2!suppE //.
Qed.

Definition subs {X Y : suppType} (x : X) (y : Y) := fsubset (supp x) (supp y).

Lemma subsE {X Y : suppType} : equivariant (@subs X Y).
Proof.
  apply equi_fun => π //= [x y] //=.
  unfold subs.
  rewrite equi2_use; [| apply: fsubsetE ].
  rewrite 2!suppE //.
Qed.


(* alpha-equivalence *)

Require Export Coq.Classes.SetoidClass.

Definition alpha {X} (x₀ x₁ : X) :=
  ∃ π, π ∙ x₀ = x₁.

Notation " x ≡ y " :=
  (alpha x y)
  (at level 50, format "x  ≡  y")
  : nominal_scope.

#[local]
Lemma alpha_1 {X} : Reflexive (@alpha X).
Proof. intros x. exists 1%fperm. apply rename_id. Qed.

#[local]
Lemma alpha_2 {X} : Symmetric (@alpha X).
Proof.
  intros x y [π H0]. exists π^-1%fperm. subst. apply renameK.
Qed.

#[local]
Lemma alpha_3 {X} : Transitive (@alpha X).
Proof.
  intros x y z [π H0] [π' H1]. exists (π' * π)%fperm. subst. apply rename_comp.
Qed.

Add Parametric Relation {X : nomType} : X alpha
  reflexivity proved by alpha_1
  symmetry proved by alpha_2
  transitivity proved by alpha_3
  as alpha_rel.

Add Parametric Morphism {X} π : (rename π) with
  signature (@alpha X) ==> alpha as rename_mor.
Proof.
  intros x y [π' H0].
  rewrite -H0.
  exists (π * π' * π^-1)%fperm.
  rewrite 2!rename_comp renameK //.
Qed.

