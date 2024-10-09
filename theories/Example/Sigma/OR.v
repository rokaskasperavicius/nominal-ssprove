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

Import PackageNotation.

Require Import Btauto.

From NominalSSP Require Import FsetSolve Group Fresh Pr Nominal NomPackage Disjoint Sigma SSProve.
Import FsetSolve.

Set Equations Transparent.

Module SigmaOR.

#[local] Open Scope package_scope.

(* Some kind of dual bijection between three sets. Does it have an established name?
   The operation is bijective either one of its arguments fixed.
   Some of these equations can probably be derived and do not have to be assumed.
*)
Record map_params {left} {right} :=
  { ch : finType
  ; chPos : Positive #|ch|
  ; toR : ∀ (c : ch) (cl : left.(Challenge)), right.(Challenge)
  ; toL : ∀ (c : ch) (cr : right.(Challenge)), left.(Challenge)
  ; toC : ∀ (cl : left.(Challenge)) (cr : right.(Challenge)), ch
  ; toR_toC : ∀ cl cr, toR (toC cl cr) cl = cr
  ; toL_toC : ∀ cl cr, toL (toC cl cr) cr = cl
  ; toC_toR : ∀ c cl, toC cl (toR c cl) = c
  ; toL_toR : ∀ c cl, toL c (toR c cl) = cl
  ; toC_toL : ∀ c cr, toC (toL c cr) cr = c
  ; toR_toL : ∀ c cr, toR c (toL c cr) = cr
  }.

#[export] Instance Positive_ch left right p : Positive #|@ch left right p|.
Proof. apply chPos. Qed.

Definition challenge_loc π : Location := (choiceChallenge π; 1%N).
Definition response_loc π : Location := (choiceResponse π; 2%N).

Definition Extra_locs_lr l r : {fset Location} :=
  fset [:: challenge_loc l ; response_loc l ; challenge_loc r ; response_loc r ].

Record or_params :=
  { left : raw_sigma
  ; right : raw_sigma
  ; mapping : @map_params left right
  ; d1 : disj left.(locs) right.(locs)
  ; d2 : disj (Extra_locs_lr left right) left.(locs)
  ; d3 : disj (Extra_locs_lr left right) right.(locs)
  }.

Implicit Type (π : or_params).

Definition Extra_locs π : {fset Location} :=
  Extra_locs_lr π.(left) π.(right).

Definition i_lwitness π := #| π.(left).(Witness) |.
Definition i_rwitness π := #| π.(right).(Witness) |.
Definition i_lchallenge π := #| π.(left).(Challenge) |.
Definition i_rchallenge π := #| π.(right).(Challenge) |.

#[export] Instance Positive_prod_finType {A B : finType} :
  Positive #|A| → Positive #|B| → Positive #|Casts.prod_finType A B|.
Proof. rewrite card_prod. apply Positive_prod. Qed.

#[export] Instance Positive_sum_finType_l {A B : finType} :
  Positive #|A| → Positive #|(Datatypes.sum A B : finType)|.
Proof. rewrite card_sum. apply ltn_addr. Qed.

#[global] Hint Unfold Extra_locs Extra_locs_lr : in_fset_eq.

Equations raw_or π : raw_sigma :=
  raw_or π :=
  {| Statement := prod π.(left).(Statement) π.(right).(Statement)
   ; Witness := Datatypes.sum π.(left).(Witness) π.(right).(Witness)
   ; Message := prod π.(left).(Message) π.(right).(Message)
   ; Challenge := π.(mapping).(ch)
   ; Response := prod (prod (prod π.(left).(Challenge) π.(left).(Response))
      π.(right).(Challenge)) π.(right).(Response)

   ; locs :=
      Extra_locs π
        :|: π.(left).(locs)
        :|: π.(right).(locs)
   ; R := λ h w,
      match w with
      | inl w1 => π.(left).(R) h.1 w1
      | inr w2 => π.(right).(R) h.2 w2
      end
   ; commit := λ h w,
      {code
        let (hl, hr) := h in
        match w with
        | inl wl =>
          R1 ← π.(left).(commit) hl wl ;;
          cr ← sample uniform (i_rchallenge π) ;;
          '(_, R2, _, s2) ← π.(right).(simulate) hr (otf cr) ;;
          #put challenge_loc π.(right)  := cr ;; (* Use c2 or cr? *)
          #put response_loc π.(right) := fto s2 ;;
          ret (R1, R2)
        | inr wr =>
          R2 ← π.(right).(commit) hr wr ;;
          cl ← sample uniform (i_lchallenge π) ;;
          '(_, R1, _, s1) ← π.(left).(simulate) hl (otf cl) ;;
          #put challenge_loc π.(left) := cl ;;
          #put response_loc π.(left) := fto s1 ;;
          ret (R1, R2)
        end
      }
   ; response := λ h w a c,
      {code
        let (hl, hr) := h in
        let (al, ar) := a in
        match w with
        | inl wl =>
          c2 ← get challenge_loc π.(right) ;;
          s2 ← get response_loc π.(right) ;;
          let c1 := π.(mapping).(toL) c (otf c2) in
          s1 ← π.(left).(response) hl wl al c1 ;;
          ret (c1, s1, otf c2, otf s2)
        | inr wr =>
          c1 ← get challenge_loc π.(left) ;;
          s1 ← get response_loc π.(left) ;;
          let c2 := π.(mapping).(toR) c (otf c1) in
          s2 ← π.(right).(response) hr wr ar c2 ;;
          ret (otf c1, otf s1, c2, s2)
        end
      }
   ; simulate := λ h c,
     {code
       let (hl, hr) := h in
       c1 ← sample (@uniform (i_lchallenge π) _) ;;
       let c2 := π.(mapping).(toR) c (otf c1) in
       '(_, R1, _, s1) ← π.(left).(simulate) hl (otf c1) ;;
       '(_, R2, _, s2) ← π.(right).(simulate) hr c2 ;;
       ret ((hl, hr), (R1, R2), c, (otf c1, s1, c2, s2))
     }
   ; verify := λ h R c z,
      let (hl, hr) := h in
      let (Rl, Rr) := R in
      let '(c1, s1, c2, s2) := z in
        π.(left).(verify) hl Rl c1 s1
        && π.(right).(verify) hr Rr c2 s2
        && (π.(mapping).(toR) c c1 == c2)
   ; extractor := λ h R e e' z z',
      let '(h1, h2) := h in
      let '(R1, R2) := R in
      let '(c1, s1, c2, s2) := z in
      let '(c1', s1', c2', s2') := z' in
      if c1 != c1' then
        omap inl
          (π.(left).(extractor) h1 R1 c1 c1' s1 s1')
      else
        omap inr 
          (π.(right).(extractor) h2 R2 c2 c2' s2 s2')
  |}.
  Obligation 1.
    ssprove_valid.
    1,2,5,6: eapply valid_injectLocations; [| apply prog_valid ].
    all: try fset_solve.
  Qed.
  Obligation 2.
    ssprove_valid.
    3,6: eapply valid_injectLocations; [| apply prog_valid ].
    all: try fset_solve.
  Qed.


#[local] Definition fto_toL_otf π (c : π.(mapping).(ch)) :
  Arit (uniform (i_rchallenge π)) →
  Arit (uniform (i_lchallenge π)) :=
  λ cr, fto (π.(mapping).(toL) c (otf cr)).

Lemma toL_bij π c : bijective (fto_toL_otf π c).
Proof.
  unfold fto_toL_otf.
  exists (λ cl, fto (π.(mapping).(toR) c (otf cl))).
  all: intro y; rewrite otf_fto ?toL_toR ?toR_toL; apply fto_otf.
Qed.


Definition Aux n m S T :=
  (@Build_trimmed_package
    fset0
    (fset ((m, (S, T)) :: [::]))
    (fset ((n, (S, T)) :: [::]))
    (mkpackage (mkfmap ( 
      (n, mkdef S T
        (λ x, opr (m, (S, T)) x (λ y, ret y))
      )
    :: [::])) _)
    (trimmed_package_cons _ _ _ _ _ _ trimmed_empty_package)
  ).

Definition LEFT := 0%N.
Definition RIGHT := 1%N.

Definition AuxL π :=
  (Aux LEFT TRANSCRIPT
    (choiceInput π.(left))
    (choiceTranscript π.(left) )
  ).

Definition AuxR π :=
  (Aux RIGHT TRANSCRIPT
    (choiceInput π.(right))
    (choiceTranscript π.(right))
  ).

Definition IF π : Interface :=
  [interface
     #val #[ LEFT ] : (chInput π.(left)) → chTranscript π.(left) ;
     #val #[ RIGHT ] : (chInput π.(right)) → chTranscript π.(right)
  ].
#[global] Hint Unfold IF : in_fset_eq.

Definition SHVZK_call_raw π (hwe : choiceInput (raw_or π)) :
  raw_code (choiceTranscript (raw_or π))
  :=
    #import {sig #[ LEFT ] :
      (chInput π.(left)) → chTranscript π.(left)} as LeftTranscript ;;
    #import {sig #[ RIGHT ] :
      (chInput π.(right)) → chTranscript π.(right)} as RightTranscript ;;

    let '(h, w, c) := hwe in
    let '(hl, hr) := otf h in
    c1 ← sample uniform (i_lchallenge π) ;;
    let c2 := π.(mapping).(toR) (otf c) (otf c1) in
    '(_, R1, _, s1) ←
      match otf w with
      | inl wl => LeftTranscript (fto hl, fto wl, c1)
      | inr wr => '(a, R1, b, s1) ← (π.(left).(simulate) hl (otf c1)) ;;
                  ret (fto a, fto R1, fto b, fto s1)
      end ;;
    '(_, R2, _, s2) ←
      match otf w with
      | inl wl => '(a, R2, b, s2) ← π.(right).(simulate) hr c2 ;;
                  ret (fto a, fto R2, fto b, fto s2)
      | inr wr => RightTranscript (fto hr, fto wr, fto c2)
      end ;;
    ret (fto (hl, hr), fto (otf R1, otf R2), c, fto (otf c1, otf s1, c2, otf s2)).

#[local] Instance SHVZK_call_proof π : ∀ hwe, ValidCode (fset [::]) (IF π) (SHVZK_call_raw π hwe).
Proof.
  intros hwe.
  unfold SHVZK_call_raw, IF.
  ssprove_valid.
  1,2: eapply valid_injectMap; [ apply fsub0set | rewrite fset0E ]; ssprove_valid.
  1,2: eapply valid_injectLocations; [| apply prog_valid ].
  1,2: simpl; fset_solve.
Qed.

Definition SHVZK_call π :
  trimmed_package (fset [::]) (IF π)
    [interface #val #[ TRANSCRIPT ] : (chInput (raw_or π)) → chTranscript (raw_or π)]
  := [trimmed_package
    #def #[ TRANSCRIPT ] (hwe : chInput (raw_or π)) : (chTranscript (raw_or π)) { SHVZK_call_raw π hwe }
  ].


Definition CALL π (L R : nom_package) :=
  nom_link (SHVZK_call π) (nom_par
    (nom_link (AuxL π) L)
    (nom_link (AuxR π) R)
  ).

Lemma domm_link {P Q} : domm (link P Q) = domm P.
Proof. apply domm_map. Qed.

Hint Rewrite domm_set domm0 @domm_link : in_fset_eq.

#[local] Instance call_valid π :
  ∀ (L R : nom_package),
    ValidPackage L.(loc) [interface] (Transcript π.(left)) L →
    ValidPackage R.(loc) [interface] (Transcript π.(right)) R →
    ValidPackage (CALL π L R).(loc) [interface] (Transcript (raw_or π))
      (CALL π L R).
Proof.
  move => L R VL VR.
  unfold CALL.
  dprove_valid.
Qed.

Lemma destruct_let_pair : ∀ A B C (xy : A * B) (f : A → B → C), (let (x, y) := xy in f x y) = f xy.1 xy.2.
Proof.
  intros A B C xy f.
  destruct xy.
  by simpl.
Qed.

Definition call_real_real π
  := CALL π (SHVZK_real π.(left)) (SHVZK_real π.(right)).
Definition call_ideal_real π
  := CALL π (SHVZK_ideal π.(left)) (SHVZK_real π.(right)).
Definition call_ideal_ideal π
  := CALL π (SHVZK_ideal π.(left)) (SHVZK_ideal π.(right)).

Lemma invariant_ignore_extra p :
  Invariant (SHVZK_real (raw_or p)).(loc)
    (call_real_real p).(loc)
    (heap_ignore (Extra_locs p)).
Proof.
  ssprove_invariant.
  simpl.
  fset_solve.
Qed.

Hint Rewrite in_fset : in_fset_eq.

Lemma commit_call π :
    SHVZK_real (raw_or π) ≈₀ call_real_real π.
Proof.
  eapply eq_rel_perf_ind.
  1: apply invariant_ignore_extra.
  simplify_eq_rel hwe.
  unfold SHVZK_call_raw.
  destruct hwe as [[h w] e].
  ssprove_code_simpl; simpl.
  rewrite !cast_fun_K.
  rewrite -(fto_otf h).
  move: (otf h) => [hl hr] {h}.
  rewrite 3!otf_fto.
  move: (otf w) => [wl|wr] {w}.
  + ssprove_swap_lhs 1%N.
    ssprove_swap_lhs 0%N.
    eapply r_uniform_bij with (1 := toL_bij π (otf e)) => cr.
    rewrite 2!bind_assoc.
    ssprove_code_simpl_more.
    rewrite //= otf_fto.
    ssprove_sync => H.
    ssprove_code_simpl; simpl.
    rewrite @code_link_scheme. 
    apply r_bind_eq.
    1: {
      eapply r_reflexivity_alt; [ apply prog_valid | |]; intros.
      1: apply get_pre_cond_heap_ignore.
      2: apply put_pre_cond_heap_ignore.
      apply /fdisjointP; [| eassumption ].
      rewrite fdisjointC.
      apply supp_fdisjoint, (d2 π).
    }
    move => a.
    eapply rel_jdg_replace_sem_r; simpl.
    2: eapply swap_code.
    3,4: apply prog_valid.
    2: fset_solve.
    rewrite /fto_toL_otf otf_fto toR_toL.
    apply r_bind_eq.
    1: {
      eapply r_reflexivity_alt; [ apply prog_valid | |];
        intros; exfalso; fset_solve.
    }
    intros [[[_ R1] _] s1].
    ssprove_swap_lhs 1%N.
    ssprove_contract_put_get_lhs.
    apply r_put_lhs.
    ssprove_contract_put_get_lhs.
    apply r_put_lhs.
    ssprove_restore_pre; [ ssprove_invariant |].
    apply r_bind_eq.
    1: {
      eapply r_reflexivity_alt; [ apply prog_valid | |]; intros.
      1: apply get_pre_cond_heap_ignore.
      2: apply put_pre_cond_heap_ignore.
      apply /fdisjointP; [| eassumption ].
      rewrite fdisjointC.
      apply supp_fdisjoint, (d2 π).
    }
    intros s2.
    rewrite !otf_fto.
    by apply r_ret.
  + ssprove_swap_lhs 1%N.
    ssprove_swap_lhs 0%N.
    ssprove_sync => cl.
    rewrite code_link_scheme.
    eapply rel_jdg_replace_sem_r; simpl.
    2: {
      eapply rsame_head => x.
      rewrite 3!destruct_let_pair 2!bind_assoc.
      eapply rreflexivity_rule.
    }
    eapply rel_jdg_replace_sem_r; simpl.
    2: eapply swap_code.
    3,4: ssprove_valid.
    3,4,5: apply prog_valid.
    2: fset_solve.
    ssprove_code_simpl_more.
    ssprove_code_simpl; simpl.
    rewrite otf_fto.
    ssprove_sync => H.
    apply r_bind_eq.
    1: {
      eapply r_reflexivity_alt; [ apply prog_valid | |]; intros.
      1: apply get_pre_cond_heap_ignore.
      2: apply put_pre_cond_heap_ignore.
      apply /fdisjointP; [| eassumption ].
      rewrite fdisjointC.
      apply supp_fdisjoint, (d3 π).
    }
    move => vr. 

    eapply rel_jdg_replace_sem_r; simpl.
    2: eapply swap_code.
    3,4: apply prog_valid.
    2: fset_solve.

    apply r_bind_eq.
    1: {
      eapply r_reflexivity_alt; [ apply prog_valid | |];
        intros; exfalso; fset_solve.
    }
    intros [[[h1 R1] z1] s1].
    ssprove_swap_lhs 1%N.
    ssprove_contract_put_get_lhs.
    apply r_put_lhs.
    ssprove_contract_put_get_lhs.
    apply r_put_lhs.
    ssprove_restore_pre; [ ssprove_invariant |].
    apply r_bind_eq.
    1: {
      rewrite otf_fto.
      eapply r_reflexivity_alt; [ apply prog_valid | |]; intros.
      1: apply get_pre_cond_heap_ignore.
      2: apply put_pre_cond_heap_ignore.
      apply /fdisjointP; [| eassumption ].
      rewrite fdisjointC.
      apply supp_fdisjoint, (d3 π).
    }
    intros s2.
    rewrite !otf_fto.
    by apply r_ret.
Qed.


Lemma simulate_call p :
  call_ideal_ideal p ≈₀ SHVZK_ideal (raw_or p).
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel hwe.
  unfold SHVZK_call_raw.
  move: hwe => [[h w] c].
  move: (otf h) (otf w) => [hl hr] {h} [wl|wr] {w}.
  1-2: simplify_linking; ssprove_code_simpl; simpl.
  1-2: ssprove_swap_rhs 0%N; ssprove_sync_eq => cl.
  1-2: rewrite !cast_fun_K bind_ret !otf_fto.
  + ssprove_code_simpl_more.
    ssprove_sync => P.
    rewrite code_link_scheme.
    ssprove_code_simpl.
    eapply rsame_head => t1.
    move: t1 => [[[l1 l2] l3] l4].
    eapply rsame_head => t2.
    move: t2 => [[[r1 r2] r3] r4].
    rewrite !fto_otf !otf_fto.
    by eapply r_ret.

  + rewrite code_link_scheme.
    move: (p.(right).(R) hr wr) => [].
    2: {
      eapply rel_jdg_replace_sem_l.
      2: eapply rel_jdg_replace_r.
      3: do 3 setoid_rewrite destruct_let_pair; reflexivity.
      2: eapply swap_code.
      3,4: ssprove_valid; apply prog_valid.
      2: fset_solve.
      ssprove_code_simpl_more; simpl.
      apply r_fail.
    }
    ssprove_code_simpl; simpl.
    eapply rsame_head => t1.
    move: t1 => [[[l1 l2] l3] l4].
    eapply rsame_head => t2.
    move: t2 => [[[r1 r2] r3] r4].
    rewrite !fto_otf !otf_fto.
    by eapply r_ret.
Qed.


Lemma rew_notin : forall (T : ordType) (x : T) (s : {fset T}), x \notin s = ~~ (x \in s).
Proof. reflexivity. Qed.

#[global] Hint Rewrite rew_notin : in_fset_eq.

Lemma supp_trimmed_package {L I E} (P : trimmed_package L I E)
  : supp (trimmed_nom P) = supp L.
Proof.
  done.
Qed.

(* #[local] Hint Unfold disj : in_fset_eq. *)
#[local] Hint Rewrite @supp_trimmed_package : in_fset_eq.
#[local] Hint Rewrite @supp0 : in_fset_eq.

Definition A_left p A : nom_package :=
  (((A ⊛ SHVZK_call p) ⊛ dpar (AuxL p) (AuxR p ⊛ SHVZK_real (right p)))).

Definition A_right p A : nom_package :=
  (((A ⊛ SHVZK_call p) ⊛ dpar (AuxL p ⊛ SHVZK_ideal (left p)) (AuxR p))).

Hint Rewrite @domm_ID : in_fset_eq.

Lemma trimmed_dlink {E} {P Q : nom_package} : trimmed E P → trimmed E (dlink P Q).
Proof.
  intros tr.
  rewrite /trimmed //= -link_trim_commut tr //.
Qed.

Lemma idents0 : idents fset0 = fset0.
Proof. rewrite /idents imfset0 //. Qed.

Hint Rewrite idents0 : in_fset_eq.

Theorem OR_SHVZK p :
  ∀ ε₁ ε₂ : nom_package → Axioms.R,
    Adv_SHVZK p.(left) ε₁ →
    Adv_SHVZK p.(right) ε₂ →
    Adv_SHVZK (raw_or p) (λ A, ε₁ (A_left p A) + ε₂ (A_right p A)).
Proof.
  intros ε₀ ε₁ AdvL AdvR A VA.
  unfold AdvantageP, SHVZK.
  erewrite (AdvantageD_perf_l (commit_call p)).
  erewrite <- (AdvantageD_perf_r (simulate_call p)).

  move: (d1 p) (d2 p) (d3 p) => H1 H2 H3.

  unfold call_real_real, call_ideal_ideal, CALL.
  repeat (rewrite nom_link_dlink || rewrite nom_par_dpar).
  2-9: move: H1; unfold disj; fset_solve.

  advantage_trans (call_ideal_real p).
  apply lerD.
  1,2: unfold call_ideal_real, CALL.
  1,2: repeat (rewrite nom_link_dlink || rewrite nom_par_dpar).
  2-5,7-10: move: H2 H3; unfold disj; try fset_solve.
  + rewrite AdvantageD_dlink.
    erewrite -> AdvantageD_dpar_l.
    6-8: apply: trimmed_dlink.
    2-8: try dprove_valid.
    2:{ rewrite /idents fset_cons -fset0E fsetU0 imfset1 in P. fset_solve. }

    rewrite AdvantageD_dlink.
    erewrite <- (@dpar_empty_r (AuxL p)).
    rewrite -dlink_assoc. 
    erewrite <- swash.
    7: apply: trimmed_dlink.
    2-7: dprove_valid.
    apply AdvL.
    unfold A_left.
    dprove_valid.
    1,2: apply fsubsetxx.
  + rewrite AdvantageD_dlink.
    erewrite -> AdvantageD_dpar_r.
    5-7: apply: trimmed_dlink.
    2-7: try dprove_valid.
    rewrite AdvantageD_dlink.
    erewrite <- (@dpar_empty_l (AuxR p)).
    rewrite -dlink_assoc.
    erewrite <- swish.
    6: apply: trimmed_dlink.
    2-7: try dprove_valid.
    apply AdvR.
    unfold A_right.
    dprove_valid.
    1,2: apply fsubsetxx.
Qed.

End SigmaOR.
