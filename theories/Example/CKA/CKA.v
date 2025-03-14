Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From NominalSSP Require Import Prelude Group.
Import Num.Def Num.Theory Order.POrderTheory.
Import PackageNotation.
#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.
Import GroupScope GRing.Theory.

From NominalSSP Require Import DDH Misc CKAScheme.

Module CKA (GP : GroupParam).

Module DDH' := DDH GP.
Import CKAscheme DDH'.

Module GT := GroupTheorems GP.
Import GP GT.

Definition cka : cka_scheme := {|
    Mes := 'fin #|el|
  ; Key := 'fin #|el|
  ; StateS := 'fin #|el|
  ; StateR := 'fin #|exp|
  
  ; sampleKey :=
    {code 
      x ← sample uniform #|exp| ;;
      ret (op_exp op_g x)
    }
  
  ; keygen := 
    {code 
      x ← sample uniform #|exp| ;;
      ret (op_exp op_g x, x)
    } 
  ; ckaS := λ γ,
    {code
      x ← sample uniform #|exp| ;;
      let h := γ in 
      ret (x, op_exp op_g x, op_exp h x)
    }
  ; ckaR := λ γ m,
    {code
      let x := γ in
      let h := m in
      ret (h, op_exp h x)
    }
  |}.


Theorem correct_cka_simple : CORR0_simple cka ≈₀ CORR1_simple cka.
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  intros x.
  unfold op_exp, op_g.
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  intros x'.
  rewrite !otf_fto expgAC.
  rewrite eq_refl.
  simpl.
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  intros x''.
  rewrite !otf_fto expgAC.
  rewrite eq_refl.
  simpl.
  apply r_ret => s0 s1.
  split.
    - reflexivity.
    - apply H.
Qed.

Theorem correct_cka : CORR0 cka ≈₀ CORR1 cka.
Proof.
  (*Fix heap_ignore, shouldnt be here*)
  apply (eq_rel_perf_ind _ _ (heap_ignore (fset [::]))).
  1: ssprove_invariant; fset_solve.
  simplify_eq_rel m.
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  induction m.
  - simpl.
    intros x.
    apply r_ret => s0 s1.
    split.
      + reflexivity.
      + apply H.
  - simpl.
    intros x.
    apply r_const_sample_L.
    1: apply LosslessOp_uniform.
    intros x'.
    unfold op_exp, op_g in *.
    rewrite !otf_fto expgAC in IHm |- *.
    rewrite eq_refl.
    simpl.
    apply IHm.
Qed.

  
Definition red_epoch_a : Location := ('nat; 10%N).
Definition red_epoch_b : Location := ('nat; 11%N).

Definition state_sa_loc (K: cka_scheme) : Location := ('stateS K; 13%N).
Definition state_sb_loc (K: cka_scheme) : Location := ('stateS K; 14%N).
Definition state_ra_loc (K: cka_scheme) : Location := ('stateR K; 15%N).
Definition state_rb_loc (K: cka_scheme) : Location := ('stateR K; 16%N).

Definition red_max_epoch : Location := ('nat; 17%N).

Definition RED_loc :=
  fset [::red_epoch_a ; red_epoch_b ; state_rb_loc cka; state_ra_loc cka; state_sb_loc cka ].

Definition RED t :
  module I_DDH (I_CKA_PCS cka) :=
  [module CKA_PCS_locs cka;
    #def #[ INIT ] (_ : 'unit) : 'unit {
      '(pk, x) ← cka.(keygen) ;;

      #put (state_sa_loc cka) := pk ;;
      #put (state_sb_loc cka) := pk ;;
      #put (state_ra_loc cka) := x ;;
      #put (state_rb_loc cka) := x ;;

      #put epoch_a := 0 ;;
      #put epoch_b := 0 ;;

      @ret 'unit Datatypes.tt
    } ;

    #def #[ SEND_A ] (_ : 'unit) : ('mes cka × 'key cka) {    
      #import {sig #[ GETA ] : 'unit → 'el } as GETA ;;
      #import {sig #[ GETBC ] : 'unit → 'el × 'el } as GETBC ;;

      epoch ← get epoch_a ;;
      let epoch_inc := epoch.+1 in
      #put epoch_a := epoch_inc ;;

      if epoch_inc == t.-1 then
        DDH_a ← GETA tt ;;
        stateRB ← get state_rb_loc cka ;;
        @ret ('el × 'el) (DDH_a, op_exp DDH_a stateRB)

      else if epoch_inc == t then 
        (*locations need fixing*)
        '(DDH_b, DDH_c) ← GETBC tt ;; 
        @ret ('el × 'el) (DDH_b, DDH_c)

      (* for the case of t+1, 
         we see that the behavior is captured by the default case *)
      else
        stateSA ← get state_sa_loc cka ;;
        '(stateRA, m, k) ← cka.(ckaS) stateSA ;;
        #put (state_ra_loc cka) := stateRA ;;
        @ret ('mes cka × 'key cka) (m, k)
    } ;

    #def #[ RCV_A ] (m : 'mes cka) : 'unit {
      epoch ← get epoch_a ;;
      #put epoch_a := epoch.+1 ;;
      (* if epoch_inc == t.-1 then
        #put (state_sa_loc cka) := m ;;
        @ret 'unit Datatypes.tt
        
      else if epoch_inc == t then (* should this not exist here *)
        #put (state_sa_loc cka) := m ;;
        @ret 'unit Datatypes.tt
        
      else if epoch_inc == t.+1 then
        #put (state_sa_loc cka) := m ;;
        @ret 'unit Datatypes.tt
        
      else *)
      stateRA ← get state_ra_loc cka ;;
      '(stateSA, k) ← cka.(ckaR) stateRA m ;;
      #put (state_sa_loc cka) := stateSA ;;
      @ret 'unit Datatypes.tt
    } ;

    #def #[ SEND_B ] (_ : 'unit) : ('mes cka × 'key cka) {
      #import {sig #[ GETA ] : 'unit → 'el } as GETA ;;
      #import {sig #[ GETBC ] : 'unit → 'el × 'el } as GETBC ;;

      epoch ← get epoch_b ;;
      let epoch_inc := epoch.+1 in
      #put epoch_b := epoch_inc ;;

      if epoch_inc == t.-1 then
        DDH_a ← GETA tt ;;
        stateRA ← get state_ra_loc cka ;;
        @ret ('el × 'el) (DDH_a, op_exp DDH_a stateRA)

      else if epoch_inc == t then 
        (* locations need fixing *)
        '(DDH_b, DDH_c) ← GETBC tt ;; 
        @ret ('el × 'el) (DDH_b, DDH_c)

      (* For the case of t+1, 
         we see that the behavior is captured by the default case *)
      else
        stateSB ← get state_sb_loc cka ;;
        '(stateRB, m, k) ← cka.(ckaS) stateSB ;;
        #put (state_rb_loc cka) := stateRB ;;
        @ret ('mes cka × 'key cka) (m, k)
      
    } ;

    #def #[ RCV_B ] (m : 'mes cka) : 'unit {
      epoch ← get epoch_b ;;
      #put epoch_b := epoch.+1 ;;
      (* if epoch_inc == t.-1 then
        #put (state_sa_loc cka) := m ;;
        @ret 'unit Datatypes.tt
        
      else if epoch_inc == t then (* should this not exist here *)
        #put (state_sa_loc cka) := m ;;
        @ret 'unit Datatypes.tt
        
      else if epoch_inc == t.+1 then
        #put (state_sa_loc cka) := m ;;
        @ret 'unit Datatypes.tt
        
      else *)
      stateRB ← get state_rb_loc cka ;;
      '(stateSB, k) ← cka.(ckaR) stateRB m ;;
      #put (state_sb_loc cka) := stateSB ;;
      @ret 'unit Datatypes.tt
    }
  ].




Notation init' := (
  mpk ← get PKScheme.init_loc elgamal ;;
  match mpk with
  | None => 
    #import {sig #[ GETA ] : 'unit → 'el } as GETA ;;
    pk ← GETA tt ;;
    #put PKScheme.init_loc elgamal := Some pk ;;
    ret pk 
  | Some pk =>
    ret pk
  end).

#[export] Instance valid_RED_DDH0
  : ValidPackage (RED_loc :|: DDH0_loc)
      Game_import (I_PK_OTSR elgamal) (nom_link RED DDH0).
Proof. dprove_valid. Qed.

#[export] Instance valid_RED_DDH1
  : ValidPackage (RED_loc :|: DDH1_loc)
      Game_import (I_PK_OTSR elgamal) (nom_link RED DDH1).
Proof. dprove_valid. Qed.

#[local] Hint Unfold DDH0_loc DDH1_loc PK_OTSR_loc RED_loc : in_fset_eq.

Definition Rel0
  (flag : flag_loc) (mpk : mpk_loc elgamal)
  (stop : stop_loc) (mga : mga_loc) : Prop
  := (isSome mpk == isSome stop)%B &&
      if flag then stop && ~~ mga else
        (if stop then (mpk == mga)%B else ~~ mpk).

Notation inv0 := (
  heap_ignore (PK_OTSR_loc elgamal :|: (RED_loc :|: DDH0_loc))
  ⋊ quad flag_loc (mpk_loc elgamal) stop_loc mga_loc Rel0
).

Lemma inv0_Invariant :
  Invariant (PK_OTSR_loc elgamal) (RED_loc :|: DDH0_loc) inv0.
Proof.
  ssprove_invariant; [ apply fsubsetxx | done ].
Qed.

Lemma pk_ots0_perf : PK_OTSR0 elgamal ≈₀ nom_link RED DDH0.
Proof.
  apply (eq_rel_perf_ind _ _ inv0).
  1: exact inv0_Invariant.
  simplify_eq_rel m.
  1,2: ssprove_code_simpl.
  + eapply r_get_remember_lhs => mpk.
    eapply r_get_remember_rhs => stop.
    eapply (rpre_learn). {
      intros s0 s1 [[[_ I1] I2] I3].
      rewrite /quad I2 I3 /Rel0 in I1.
      move: I1 => /andP [I1 _].
      apply I1.
    }
    move=> /eqP ?.
    destruct mpk, stop => //=.
    1: apply r_fail.
    ssprove_swap_rhs 0%N.
    ssprove_sync => sk.
    eapply r_put_lhs, r_put_rhs, r_put_rhs.
    ssprove_restore_mem.
    2: by eapply r_ret.

    ssprove_invariant. {
      apply preserve_update_r_ignored_heap_ignore.
      1: fset_solve.
      apply preserve_update_r_ignored_heap_ignore.
      1: fset_solve.
      apply preserve_update_l_ignored_heap_ignore.
      1: fset_solve.
      intros h0 h1 H.
      apply H.
    }
    intros s0 s1 [[I1 I2] I3].
    rewrite /quad /Rel0 //= in I1 |- *.
    get_heap_simpl.
    simpl.
    move: I1.
    elim: (get_heap s0 flag_loc) => //= _ H.
    rewrite /quad I2 I3 /Rel0 in H.
    done.

  + eapply r_get_remember_lhs => mpk.
    eapply r_get_remember_rhs => stop.
    eapply (rpre_learn). {
      intros s0 s1 [[[_ I1] I2] I3].
      rewrite /quad I2 I3 /Rel0 in I1.
      move: I1 => /andP [I1 _].
      apply I1.
    }
    move=> /eqP ?.
    destruct mpk, stop => //=.
    2: apply r_fail.
    ssprove_code_simpl_more.
    eapply r_get_remember_lhs => flag.
    eapply r_get_remember_rhs => mga.
    eapply (rpre_learn). {
      intros h0 h1 [[[[[_ I1] I2] I3] I4] I5].
      rewrite /quad I2 I3 I4 I5 /Rel0 in I1.
      apply I1.
    }
    destruct flag, mga.
    1,4: done.
    1: intros _; apply r_fail.
    move=> //= /eqP E.
    injection E => {}E.
    subst.
    eapply r_put_lhs, r_put_rhs.
    ssprove_sync => r.

    ssprove_restore_mem.
    2: by eapply r_ret.

    ssprove_invariant. {
      unfold PK_OTSR_loc, RED_loc, DDH0_loc.
      apply preserve_update_r_ignored_heap_ignore.
      1: fset_solve.
      apply preserve_update_l_ignored_heap_ignore.
      1: fset_solve.
      intros h0 h1 H.
      apply H.
    }
    intros h0 h1 [[[[I1 I2] I3] I4] I5].
    simpl.
    unfold quad, Rel0.
    get_heap_simpl.
    rewrite //= I2 I3 //.
Qed.

Definition Rel1
  (flag : flag_loc) (mpk : mpk_loc elgamal)
  (stop : stop_loc) (mga : init_loc) : Prop
  := (isSome mpk == isSome stop)%B &&
      if flag then stop && ~~ mga else
        (if stop then (isSome mpk == isSome mga)%B else ~~ mpk).

Notation inv1 := (
  heap_ignore (PK_OTSR_loc elgamal :|: (RED_loc :|: DDH1_loc))
  ⋊ quad flag_loc (mpk_loc elgamal) stop_loc init_loc Rel1
).

Lemma inv1_Invariant :
  Invariant (PK_OTSR_loc elgamal) (RED_loc :|: DDH1_loc) inv1.
Proof.
  ssprove_invariant; [ apply fsubsetxx | done ].
Qed.

Lemma pk_ots1_perf : PK_OTSR1 elgamal ≈₀ nom_link RED DDH1.
Proof.
  apply (eq_rel_perf_ind _ _ inv1).
  1: exact inv1_Invariant.
  simplify_eq_rel m.
  1,2: ssprove_code_simpl.
  + eapply r_get_remember_lhs => mpk.
    eapply r_get_remember_rhs => stop.
    eapply (rpre_learn). {
      intros s0 s1 [[[_ I1] I2] I3].
      rewrite /quad I2 I3 /Rel0 in I1.
      move: I1 => /andP [I1 _].
      apply I1.
    }
    move=> /eqP ?.
    destruct mpk, stop => //=.
    1: apply r_fail.
    ssprove_swap_rhs 0%N.
    ssprove_sync => sk.
    eapply r_put_lhs, r_put_rhs, r_put_rhs.
    ssprove_restore_mem.
    2: by eapply r_ret.

    ssprove_invariant. {
      apply preserve_update_r_ignored_heap_ignore.
      1: fset_solve.
      apply preserve_update_r_ignored_heap_ignore.
      1: fset_solve.
      apply preserve_update_l_ignored_heap_ignore.
      1: fset_solve.
      intros h0 h1 H.
      apply H.
    }
    intros s0 s1 [[I1 I2] I3].
    rewrite /quad /Rel1 //= in I1 |- *.
    get_heap_simpl.
    simpl.
    move: I1.
    elim: (get_heap s0 flag_loc) => //= _ H.
    rewrite /quad I2 I3 in H.
    done.

  + eapply r_get_remember_lhs => mpk.
    eapply r_get_remember_rhs => stop.
    eapply (rpre_learn). {
      intros s0 s1 [[[_ I1] I2] I3].
      rewrite /quad I2 I3 /Rel1 in I1.
      move: I1 => /andP [I1 _].
      apply I1.
    }
    move=> /eqP ?.
    destruct mpk, stop => //=.
    2: apply r_fail.
    ssprove_code_simpl_more.
    eapply r_get_remember_lhs => flag.
    eapply r_get_remember_rhs => mga.
    eapply (rpre_learn). {
      intros h0 h1 [[[[[_ I1] I2] I3] I4] I5].
      rewrite /quad I2 I3 I4 I5 /Rel1 in I1.
      apply I1.
    }
    destruct flag, mga.
    1,4: done.
    1: intros _; apply r_fail.
    move=> //= /eqP E.
    eapply r_put_lhs, r_put_rhs.

    ssprove_restore_mem.

    2: {
      eapply rsymmetry.
      eapply (r_uniform_bij _ _ _ _ _ _ _ bij_op_exp) => c1.
      eapply (r_uniform_bij _ _ _ _ _ _ _ (bij_op_mult_op_exp m)) => c2.
      by eapply r_ret.
    }

    ssprove_invariant. {
      unfold PK_OTSR_loc, RED_loc, DDH0_loc.
      apply preserve_update_r_ignored_heap_ignore.
      1: fset_solve.
      apply preserve_update_l_ignored_heap_ignore.
      1: fset_solve.
      intros h0 h1 H.
      apply H.
    }
    intros h0 h1 [[[[I1 I2] I3] I4] I5].
    simpl.
    unfold quad, Rel1.
    get_heap_simpl.
    rewrite //= I2 I3 //.
Qed.

Theorem elgamal_sound {LA : {fset Location}}
  : ∀ (A : trimmed_package LA (I_PK_OTSR elgamal) A_export),
  AdvantageP (PK_OTSR elgamal) A = AdvantageP DDH (dlink A RED).
Proof.
  intros A.
  unfold AdvantageP.
  rewrite (AdvantageD_perf_l pk_ots0_perf).
  rewrite (AdvantageD_perf_r pk_ots1_perf).
  rewrite -AdvantageD_dlink.
  dprove_convert.
Qed.

End ElGamal.
