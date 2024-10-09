Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Mon Require Import SPropBase.

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude
  SigmaProtocol.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From HB Require Import structures.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.


Local Open Scope ring_scope.
Import GroupScope GRing.Theory.


Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.
Require Import Btauto.

Import PackageNotation.

From extructures Require Import ffun fperm.

From NominalSSP Require Import Nominal Fresh Pr.

(* Support lemmas *)

Program Definition Location_HasFiniteSupport
  : HasFiniteSupport Location
  := HasFiniteSupport.Build _ (λ '(_; l), fset1 (atomize l)) _ _.
Obligation 1.
  intros π H.
  unfold rename; simpl.
  rewrite H //.
  rewrite in_fset1 //.
Qed.
Obligation 2.
  eapply fsubset_trans.
  2: eapply (support_sub (atomize X)).
  1: apply fsubsetxx.
  Unshelve.
  intros π H'.
  specialize (H π H').
  rewrite /rename //= in H |- *.
  injection H => E.
  rewrite -(natizeK (π _)) E //.
Qed.

HB.instance Definition _ : HasFiniteSupport (sigT (λ _, nat))
  := Location_HasFiniteSupport.
(*
HB.instance Definition _ : HasFiniteSupport Location 
  := Location_HasFiniteSupport.
 *)


(* *)
(* HB.instance Definition _ : IsNominal ident (sigT (λ _, nat)) := Location_IsNominal. *)

Lemma supp_Locations {l : Location} {L : {fset Location}} : l \in L → (supp l :<=: supp L)%fset.
Proof.
  intros H.
  destruct l.
  unfold supp; simpl.
  rewrite fsub1set.
  unfold fsetSupp.
  apply /bigcupP.
  eapply BigCupSpec => //.
  + apply H.
  + rewrite in_fset1 //.
Qed.

Lemma valid_support_code {T S : choice_type} {L I} (c : T → raw_code S) {x : T}
  : ValidCode L I (c x) → support_set (c x) (supp L).
Proof.
  intros V.
  induction V => π H'.
  + done.
  + unfold rename; simpl.
    f_equal.
    apply functional_extensionality.
    intros t.
    apply H1, H'.
  + unfold rename; simpl.
    destruct l.
    unfold rename; simpl in *.
    f_equal.
    * intros _ eq eq'.
      apply inj_right_pair in eq.
      rewrite eq eq'.
      f_equal.
    * rewrite H' //.
      apply supp_Locations in H.
      rewrite fsub1set in H.
      apply H.
    * apply functional_extensionality => t.
      apply H1, H'.
  + unfold rename; simpl.
    destruct l.
    unfold rename; simpl in *.
    f_equal.
    * intros _ eq _ eq'.
      apply inj_right_pair in eq.
      rewrite eq eq'.
      f_equal.
    * rewrite H' //.
      apply supp_Locations in H.
      rewrite fsub1set in H.
      apply H.
    * apply IHV, H'.
  + unfold rename; simpl.
    f_equal.
    apply functional_extensionality => t.
    apply H0, H'.
Qed.

Lemma equi_trim : equivariant (trim : Interface → raw_package → raw_package).
Proof.
  apply equi_fun.
  move => //= π [E p] //=.
  rewrite absorb.
  apply eq_fmap => k.
  rewrite mapmE /trim 2!filtermE mapmE.
  elim: (p k) => //= t.
  elim: t => [S [T f]] //=.
  elim: ((k, (S, T)) \in E); done.
Qed.

Lemma valid_support_package {L I E p} `{ValidPackage L I E p} : support_set (trim E p : raw_package) (supp L).
Proof.
  move: H => V.
  intros π H.
  unfold rename; simpl.
  apply eq_fmap => k.
  apply valid_trim in V.

  rewrite mapmE.
  destruct (trim E p k) eqn:eq; rewrite eq; [| done ].
  simpl; f_equal.
  destruct s as [T [S c]].
  unfold rename; simpl.
  simpl; do 2 f_equal.
  apply functional_extensionality.
  assert (Htrim : trimmed E (trim E p)). { rewrite /trimmed trim_idemp //. }
  specialize (trimmed_valid_Some_in _ _ _ _ k T S c V Htrim eq) => H'.
  induction V as [V].
  specialize (V _ H').
  simpl in V.
  destruct V as [f [eq' V]].
  rewrite eq' {eq'} in eq.
  injection eq => {eq} eq'.
  apply inj_right_pair in eq'.
  apply inj_right_pair in eq'.
  subst.
  intros x.
  specialize (V x).
  eapply valid_support_code. { apply V. }
  apply H.
Qed.

Lemma valid_support_trimmed {L I E p} `{ValidPackage L I E p}
  : trimmed E p → support_set p (supp L).
Proof.
  unfold trimmed => tr.
  rewrite -tr.
  apply valid_support_package.
Qed.

(* Nom Package *)

Record nom_package := mkNom
  { loc : {fset Location}
  ; val :> raw_package
  ; has_support : support_set val (supp loc)
  }.

Definition nom_from_valid {L I E} p `{H : ValidPackage L I E p} : nom_package :=
  {| loc := L
  ;  val := trim E p
  ;  has_support := @valid_support_package _ _ _ _ H
  |}.

Definition nom_from_trimmed {L I E} p `{H : ValidPackage L I E p} (tr : trimmed E p) : nom_package :=
  {| loc := L
  ;  val := p
  ;  has_support := @valid_support_trimmed _ _ _ _ H tr
  |}.

Lemma eq_nom_package {P P' : nom_package}
  : loc P = loc P'
  → val P = val P'
  → P = P'.
Proof.
  intros H1 H2.
  destruct P, P'.
  simpl in *.
  subst.
  rewrite (proof_irrelevance _ has_support0 has_support1) //.
Qed.


(* Linking lemmas *)

Lemma rename_link : ∀ f p q, rename f (p ∘ q) = rename f p ∘ rename f q.
Proof.
  intros f p q.
  rewrite /link /rename //=.
  rewrite -mapm_comp -mapm_comp.
  apply eq_mapm => t.
  destruct t as [T [P k]].
  unfold rename; simpl.
  do 2 f_equal.
  apply functional_extensionality => t.
  generalize (k t); elim.
  + done.
  + intros.
    rewrite {2}/rename //=.
    rewrite lookup_op_map.
    destruct (lookup_op q o).
    - simpl.
      setoid_rewrite <- H.
      by rewrite mcode_bind.
    - by simpl.
  + intros.
    destruct l.
    rewrite {1}/rename //=.
    by setoid_rewrite H.
  + intros.
    destruct l.
    rewrite {1}/rename //=.
    by setoid_rewrite H.
  + intros.
    rewrite {1}/rename //=.
    by setoid_rewrite H.
Qed.

Lemma supp_fsetU {X : suppOrdType} {A B : {fset X}} : supp (A :|: B) = supp A :|: supp B.
Proof. apply fsetSuppU. Qed.

(* holds for any equivariant binary function? *)
Lemma support_link {P P'} {S S' : {fset Location}}
  : support_set P (supp S) → support_set P' (supp S') → support_set (P ∘ P') (supp (S :|: S')).
Proof.
  intros s1 s2 π H.
  rewrite rename_link.
  f_equal.
  + apply s1.
    intros a M.
    apply H.
    rewrite supp_fsetU.
    apply /fsetUP; by left.
  + apply s2.
    intros a M.
    apply H.
    rewrite supp_fsetU.
    apply /fsetUP; by right.
Qed.

Definition nom_link (P P' : nom_package)
  := {| loc := loc P :|: loc P'
      ; val := link (val P) (val P')
      ; has_support := support_link (has_support P) (has_support P')
      |}.

Lemma nom_link_assoc p1 p2 p3
  : nom_link p1 (nom_link p2 p3) = nom_link (nom_link p1 p2) p3.
Proof.
  apply eq_nom_package; rewrite //=.
  + rewrite fsetUA //.
  + rewrite link_assoc //.
Qed.


(* ID lemmas *)

Lemma support_ID {I} : support_set (ID I) (supp (@fset0 Location)).
Proof.
  intros π H.
  unfold rename; simpl.
  apply eq_fmap => n.
  rewrite mapmE.
  unfold ID.
  rewrite mkfmapE.
  rewrite getm_def_map_dep.
  destruct (getm_def I n) eqn:eq; rewrite eq //=.
  destruct s.
  f_equal.
Qed.

Definition nom_ID I
  := {| loc := fset0
      ; val := ID I
      ; has_support := support_ID
      |}.

Lemma nom_link_id {L I E} {p : nom_package} `{ValidPackage L I E p}
  : flat I → trimmed E p → nom_link p (nom_ID I) = p.
Proof.
  intros F T.
  apply eq_nom_package; rewrite //=.
  + rewrite fsetU0 //.
  + rewrite link_id //.
Qed.

Lemma id_nom_link {L I E} {p : nom_package} `{ValidPackage L I E p}
  : trimmed E p → nom_link (nom_ID E) p = p.
Proof.
  intros T.
  apply eq_nom_package; rewrite //=.
  + rewrite fset0U //.
  + rewrite id_link //.
Qed.


(* Par theorems *)

Lemma rename_par : ∀ f p q, rename f (par p q : raw_package) = par (rename f p) (rename f q).
Proof.
  intros f p q.
  rewrite /par /rename //=.
  apply eq_fmap => n.
  rewrite unionmE 3!mapmE unionmE.
  destruct (p n), (q n); done.
Qed.

Lemma support_par {P P'} {S S' : {fset Location}}
  : support_set P (supp S) → support_set P' (supp S') → support_set (par P P' : raw_package) (supp (S :|: S')).
Proof.
  intros s1 s2 π H.
  rewrite rename_par.
  f_equal.
  + apply s1.
    intros a M.
    apply H.
    rewrite supp_fsetU.
    apply /fsetUP; by left.
  + apply s2.
    intros a M.
    apply H.
    rewrite supp_fsetU.
    apply /fsetUP; by right.
Qed.

Definition nom_par (P P' : nom_package)
  := {| loc := loc P :|: loc P'
      ; val := par (val P) (val P')
      ; has_support := support_par (has_support P) (has_support P')
      |}.

Lemma nom_par_commut (p1 p2 : nom_package) `{Parable p1 p2} : nom_par p1 p2 = nom_par p2 p1.
Proof.
  apply eq_nom_package; rewrite //=.
  + rewrite fsetUC //.
  + rewrite par_commut //.
Qed.

Lemma nom_par_assoc {P1 P2 P3 : nom_package}
  : nom_par P1 (nom_par P2 P3) = nom_par (nom_par P1 P2) P3.
Proof.
  apply eq_nom_package; rewrite //=.
  + rewrite fsetUA //.
  + rewrite par_assoc //.
Qed.

Lemma nom_interchange {A B C D E F} {L1 L2 L3 L4} (p1 p2 p3 p4 : nom_package)
  `{ValidPackage L1 B A p1} `{ValidPackage L2 E D p2}
  `{ValidPackage L3 C B p3} `{ValidPackage L4 F E p4} :
  trimmed A p1 → trimmed D p2 → Parable p3 p4 → 
  nom_par (nom_link p1 p3) (nom_link p2 p4) = nom_link (nom_par p1 p2) (nom_par p3 p4).
Proof.
  intros tr1 tr2 par34.
  apply eq_nom_package; rewrite //=.
  + rewrite fsetUA -(fsetUA (loc p1)) (fsetUC (loc p3)) 2!fsetUA //.
  + rewrite interchange //.
Qed.


(* Definition as Nominal *)

(* redundant
Lemma rename_support {π p L} : support_set p L → support_set (π ∙ p) (π ∙ L).
Proof.
  intros S π' H.
  eapply (bij_inj (@rename_bij _ _ _ π^-1)%fperm).
  rewrite nominal_cancel -2!rename_comp.
  apply S.
  intros a H'.
  rewrite fpermM //= fpermM //=.
  rewrite H. { apply fpermK. }
  rewrite -(imfset_equi proj_equi).
  unfold rename; simpl. eapply mem_imfset in H'.
  apply H'.
Qed.
 *)


Lemma rename_support_set {X : nomType}
  : ∀{x : X} {loc} {π}, support_set x loc → support_set (π ∙ x) (rename π loc).
Proof.
  intros x loc π ss.
  rewrite -(equi2_use _ support_setE).
  rewrite absorb //.
Qed.

Program Definition nom_package_IsNominal
  := IsNominal.Build nom_package
    (λ π P, mkNom (π ∙ loc P) (π ∙ val P) (rename_support_set (has_support P))) _ _.
Obligation 1.
  rewrite suppE //.
Qed.
Obligation 2.
  apply eq_nom_package; rewrite //= rename_id //.
Qed.
Obligation 3.
  apply eq_nom_package; rewrite //= rename_comp //.
Qed.

HB.instance Definition _ : IsNominal nom_package
  := nom_package_IsNominal.

Lemma supp_atoms (A : {fset atom}) : supp A = A.
Proof.
  unfold supp; simpl.
  rewrite -(fsvalK A).
  elim: (\val A).
  { rewrite -fset0E fsetSupp0 //. }
  intros a L H.
  rewrite fset_cons fsetSuppU fsetSupp1 H //.
Qed.

Program Definition nom_package_HasFiniteSupport
  : HasFiniteSupport nom_package
  := HasFiniteSupport.Build _ (λ p, supp (loc p)) _ _.
Obligation 1.
  intros π H.
  apply eq_nom_package; rewrite /rename //=.
  + rewrite is_support //= supp_atoms //.
  + apply has_support, H.
Qed.
Obligation 2.
  destruct x as [L p H'] => //=.
  eapply support_sub.
  intros π H''.
  specialize (H π H'') => {H''}.
  rewrite /rename //= in H.
  inversion H.
  rewrite 2!H1 //.
Qed.

HB.instance Definition _ : HasFiniteSupport nom_package
  := nom_package_HasFiniteSupport.

(*
Definition s : nom_package → {fset nat_ordType} := λ P, proj @: loc P.

Lemma s_equi : equivariant s.
Proof.
  apply (comp_equi _ _ (imfset_equi proj_equi) loc_equi).
Qed.

Lemma support_s {P : nom_package} : support_set P (s P).
Proof.
  intros π H.
  apply eq_nom_package; rewrite /rename //=.
  + apply support_proj, H.
  + apply has_support, H.
Qed.

Lemma rename_union {A X : ordType} `{Nominal A X} {π} {L L' : {fset X}}
  : π ∙ (L :|: L') = (π ∙ L) :|: (π ∙ L').
Proof.
  unfold rename. simpl. rewrite imfsetU //.
Qed.

 *)
Lemma loc_nom_link {P P' : nom_package} {π}
  : loc (π ∙ nom_link P P') = loc (π ∙ P) :|: loc (π ∙ P').
Proof.
  simpl.
  rewrite (equi2_use _ fsetUE) //.
Qed.

Lemma s_nom_link {P P' : nom_package}
  : supp (nom_link P P') = supp P :|: supp P'.
Proof. rewrite -supp_fsetU //. Qed.

Lemma val_nom_link {P P' : nom_package} {π}
  : val (π ∙ nom_link P P') = nom_link (π ∙ P) (π ∙ P').
Proof.  
  unfold rename; simpl.
  rewrite rename_link //.
Qed.

Lemma rename_nom_link {P P' : nom_package} {π} :
  π ∙ nom_link P P' = nom_link (π ∙ P) (π ∙ P').
Proof.
  apply eq_nom_package.
  + rewrite loc_nom_link //.
  + rewrite val_nom_link //=.
Qed.

Lemma val_nom_par {P P' : nom_package} {π}
  : val (π ∙ nom_par P P') = nom_par (π ∙ P) (π ∙ P').
Proof.
  unfold rename; simpl.
  rewrite rename_par.
  f_equal.
Qed.

Lemma s_nom_par {P P' : nom_package}
  : supp (nom_par P P') = supp P :|: supp P'.
Proof. rewrite -supp_fsetU //. Qed.

Lemma rename_nom_par {P P' : nom_package} {π} :
  π ∙ nom_par P P' = nom_par (π ∙ P) (π ∙ P').
Proof.
  apply eq_nom_package.
  + rewrite loc_nom_link //.
  + rewrite val_nom_par //=.
Qed.

Open Scope nominal_scope.

Lemma nom_link_congr {P P' Q Q' : nom_package} :
  disj P Q → 
  disj P' Q' → 
  P ≡ P' →
  Q ≡ Q' →
  nom_link P Q ≡ nom_link P' Q'.
Proof.
  intros D1 D2 [π E1] [π' E2].
  subst.
  exists (split_pi π π' (supp P) (supp Q)).
  rewrite rename_nom_link.
  rewrite split_pi_left.
  1: rewrite split_pi_right; [ done | | done |].
  1: apply (is_support Q).
  2: apply (is_support P).
  1,2: rewrite 2!suppE.
  1,2: apply D2.
Qed.

Lemma nom_par_congr {P P' Q Q' : nom_package} :
  disj P Q →
  disj P' Q' →
  P ≡ P' →
  Q ≡ Q' →
  nom_par P Q ≡ nom_par P' Q'.
Proof.
  intros D1 D2 [π E1] [π' E2].
  subst.
  exists (split_pi π π' (supp P) (supp Q)).
  rewrite rename_nom_par.
  rewrite split_pi_left.
  1: rewrite split_pi_right; [ done | | done |].
  1: apply (is_support Q).
  2: apply (is_support P).
  1,2: rewrite 2!suppE.
  1,2: apply D2.
Qed.


(* trimmed_package *)

Ltac trimmed_cons :=
  (try apply trimmed_empty_package) ||
  (apply trimmed_package_cons; trimmed_cons).

Record trimmed_package L I E :=
  (* we do not coerce through package as it makes for two coercion paths to raw_pacakge *)
  { tr_package : package L I E
  ; tr_trimmed : trimmed E (pack tr_package)
  }.

Arguments tr_package {L I E}.
Arguments tr_trimmed {L I E}.
Arguments Build_trimmed_package {_ _ _} & _ _.

Definition trimmed_nom {L I E} : trimmed_package L I E → nom_package
  := λ t, nom_from_trimmed (pack (tr_package t)) (tr_trimmed t).

Coercion trimmed_nom : trimmed_package >-> nom_package.

#[export]
Instance trimmed_valid {L I E} {P : trimmed_package L I E} : ValidPackage L I E P.
Proof. apply tr_package. Qed.

#[export]
Hint Rewrite @s_nom_par @s_nom_link @imfset_fset @map_cons : in_fset_eq.


Notation is_trimmed P := (Build_trimmed_package P%pack (ltac:(trimmed_cons)))
  (only parsing).


Notation "[ 'trimmed_package' ]" :=
  (Build_trimmed_package
    (mkpackage (mkfmap [::]) _)
    ltac:(trimmed_cons)
  )
  ( at level 0
  , only parsing )
  : package_scope.

Notation "[ 'trimmed_package' x1 ]" :=
  (Build_trimmed_package
    (mkpackage (mkfmap (x1 :: [::])) _)
    ltac:(trimmed_cons)
  )
  ( at level 0
  , x1 custom package at level 2
  , only parsing )
  : package_scope.

Notation "[ 'trimmed_package' x1 ; x2 ; .. ; xn ]" :=
  (Build_trimmed_package
    (mkpackage (mkfmap (x1 :: x2 :: .. [:: xn] ..)) _)
    ltac:(trimmed_cons)
  )
  ( at level 0
  , x1 custom package at level 2
  , x2 custom package at level 2
  , xn custom package at level 2
  , only parsing )
  : package_scope.
