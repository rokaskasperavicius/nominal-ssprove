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

From NominalSSP Require Import FsetSolve Group Nominal NomPackage Disjoint.


Module ElGamal (GP : GroupParam).

Module GT := GroupTheorems GP.
Import GP GT.

#[export] Instance Positive_el : Positive #|el|.
Proof. apply /card_gt0P. by exists g. Qed.

#[export] Instance Positive_exp : Positive #|exp|.
Proof. apply /card_gt0P. by exists 0. Qed.

Notation " 'el " := 'fin #|el|
  (in custom pack_type at level 2).

Notation " 'el " := 'fin #|el|
  (at level 3) : package_scope.

Notation " 'exp " := 'fin #|exp|
  (in custom pack_type at level 2).

Notation " 'exp " := 'fin #|exp|
  (at level 3) : package_scope.

Definition op_g : 'el := fto g.

Definition op_mul (x y : 'el) : 'el :=
   fto (otf x * otf y).

Definition op_exp (x : 'el) (a : 'exp) : 'el :=
  fto (otf x ^+ otf a).

Definition op_expn (x : 'el) (a : 'exp) : 'el :=
  fto (otf x ^- otf a).

Lemma bij_op_exp : bijective (op_exp op_g).
Proof.
  eexists (λ a, fto (log (otf a))).
  + intros x.
    rewrite /op_exp /op_g 2!otf_fto.
    rewrite -{2}(fto_otf x).
    f_equal.
    by apply expg_log.
  + intros x.
    rewrite /op_exp /op_g 2!otf_fto.
    rewrite -{2}(fto_otf x).
    f_equal.
    by apply log_expg.
Qed.

Lemma bij_op_mult_op_exp m : bijective (λ x, op_mul m (op_exp op_g x)).
Proof.
  eexists (λ a, fto (log ((otf m)^-1 * otf a))).
  + intros x.
    rewrite /op_exp /op_g 3!otf_fto.
    rewrite -{2}(fto_otf x).
    f_equal.
    rewrite mulKg.
    by apply expg_log.
  + intros x.
    rewrite /op_mul /op_exp /op_g 3!otf_fto.
    rewrite -{2}(fto_otf x).
    f_equal.
    rewrite -{2}(mulKVg (otf m) (otf x)).
    f_equal.
    by apply log_expg.
Qed.

(* Definition TRIPLE := 0%N. *)
Definition ONE := 0%N.
Definition TWO := 1%N.

Definition I_DDH :=
  [interface
    #val #[ ONE ] : 'unit → 'el ;
    #val #[ TWO ] : 'unit → 'el × 'el
  ].

Definition init_loc : Location := ('option 'unit; 5%N).
Definition mga_loc : Location := ('option 'el; 3%N).
Definition DDH0_loc := fset [:: mga_loc ].
Definition DDH1_loc := fset [:: init_loc ].


Definition DDH0 :
  trimmed_package DDH0_loc Game_import I_DDH :=
  [trimmed_package
    #def #[ ONE ] ('tt : 'unit) : 'el {
      a ← sample uniform #|exp| ;;
      #put mga_loc := Some (op_exp op_g a) ;;
      ret (op_exp op_g a)
    } ;
    #def #[ TWO ] ('tt : 'unit) : 'el × 'el {
      mga ← get mga_loc ;;
        #assert (isSome mga) as mgaSome ;;
        let ga := getSome mga mgaSome in
      #put mga_loc := None ;;
      b ← sample uniform #|exp| ;;
      @ret ('el × 'el) (op_exp op_g b, op_exp ga b)
    }
  ].

Definition DDH1 :
  trimmed_package DDH1_loc Game_import I_DDH :=
  [trimmed_package
    #def #[ ONE ] ('tt : 'unit) : 'el {
      a ← sample uniform #|exp| ;;
      #put init_loc := Some tt ;;
      ret (op_exp op_g a)
    } ;
    #def #[ TWO ] ('tt : 'unit) : 'el × 'el {
      init ← get init_loc ;;
        #assert init ;;
      #put init_loc := None ;;
      b ← sample uniform #|exp| ;;
      c ← sample uniform #|exp| ;;
      @ret ('el × 'el) (op_exp op_g b, op_exp op_g c)
    }
  ].

Definition DDH b :=
  if b then DDH0 : nom_package else DDH1.


Record pk_scheme :=
  { Sec : choice_type
  ; Pub : choice_type
  ; Mes : choice_type
  ; Cip : choice_type
  ; sample_Cip : code fset0 [interface] Cip

  ; keygen :
      code fset0 [interface] (Sec × Pub)

  ; enc : ∀ (pk : Pub) (m : Mes),
      code fset0 [interface] Cip

  ; dec : ∀ (sk : Sec) (c : Cip),
      code fset0 [interface] Mes
  }.


Notation " 'sec p " := (Sec p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'sec p " := (Sec p)
  (at level 3) : package_scope.

Notation " 'pub p " := (Pub p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'pub p " := (Pub p)
  (at level 3) : package_scope.

Notation " 'mes p " := (Mes p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'mes p " := (Mes p)
  (at level 3) : package_scope.

Notation " 'cip p " := (Cip p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'cip p " := (Cip p)
  (at level 3) : package_scope.

Definition flag_loc : Location := ('option 'unit; 0%N).
Definition mpk_loc (P : pk_scheme) : Location := ('option ('pub P); 1%N).
Definition GET := 0%N.
Definition QUERY := 1%N.

Definition I_PK_OTSR (P : pk_scheme) :=
  [interface
    #val #[ GET ] : 'unit → 'pub P ;
    #val #[ QUERY ] : 'mes P → 'cip P
  ].

From NominalSSP Require Import Prelude.

Definition PK_OTSR_loc (P : pk_scheme) :=
  fset [:: mpk_loc P ; flag_loc ].

Definition PK_OTSR0 (P : pk_scheme) :
  trimmed_package (PK_OTSR_loc P) Game_import (I_PK_OTSR P) :=
  [trimmed_package
    #def #[ GET ] (_ : 'unit) : ('pub P) {
      mpk ← get (mpk_loc P) ;;
        #assert (mpk == None) ;;
      '(_, pk) ← P.(keygen) ;;
      #put (mpk_loc P) := Some pk ;;
      ret pk
    } ;
    #def #[ QUERY ] (m : 'mes P) : ('cip P) {
      mpk ← get (mpk_loc P) ;;
       #assert (isSome mpk) as mpkSome ;;
       let pk := getSome mpk mpkSome in
      flag ← get flag_loc ;;
        #assert flag == None ;;
      #put flag_loc := Some tt ;;
      P.(enc) pk m
    }
  ].

Definition PK_OTSR1 (P : pk_scheme) :
  trimmed_package (PK_OTSR_loc P) Game_import (I_PK_OTSR P) :=
  [trimmed_package
    #def #[ GET ] (_ : 'unit) : ('pub P) {
      mpk ← get (mpk_loc P) ;;
        #assert (mpk == None) ;;
      '(_, pk) ← P.(keygen) ;;
      #put (mpk_loc P) := Some pk ;;
      ret pk
    } ;
    #def #[ QUERY ] (m : 'mes P) : ('cip P) {
      mpk ← get (mpk_loc P) ;;
        #assert (isSome mpk) as mpkSome ;;
        let pk := getSome mpk mpkSome in
      flag ← get flag_loc ;;
        #assert flag == None ;;
      #put flag_loc := Some tt ;;
      P.(sample_Cip)
    }
  ].
  
Definition PK_OTSR P b :=
  if b then PK_OTSR0 P : nom_package else PK_OTSR1 P.

Definition elgamal : pk_scheme := {|
    Sec := 'fin #|exp|
  ; Pub := 'fin #|el|
  ; Mes := 'fin #|el|
  ; Cip := 'fin #|el| × 'fin #|el|
  ; sample_Cip := {code
      c₁ ← sample uniform #|el| ;;
      c₂ ← sample uniform #|el| ;;
      ret (c₁, c₂)
    }
    
  ; keygen :=
    {code
      sk ← sample uniform #|exp| ;;
      ret (sk, op_exp op_g sk)
    }
  ; enc := λ pk m,
    {code
      r ← sample uniform #|exp| ;;
      ret (op_exp op_g r, op_mul m (op_exp pk r))
    }
  ; dec := λ sk c,
    {code
      ret (op_mul (snd c) (op_expn (fst c) sk))
    }
  |}.

Definition stop_loc : Location := ('option 'unit; 4%N).

Definition RED_loc :=
  fset [:: stop_loc ].

Definition RED :
  trimmed_package RED_loc I_DDH (I_PK_OTSR elgamal) :=
  [trimmed_package
    #def #[ GET ] (_ : 'unit) : 'el {
        #import {sig #[ ONE ] : 'unit → 'el } as ONE ;;
      stop ← get stop_loc ;;
        #assert (stop == None) ;;
      #put stop_loc := Some tt ;;
      pk ← ONE tt ;;
        @ret 'el pk
    } ;
    #def #[ QUERY ] (m : 'el) : 'el × 'el {
        #import {sig #[ TWO ] : 'unit → 'el × 'el } as TWO ;;
      stop ← get stop_loc ;;
        #assert (isSome stop) ;;
      '(r, sh) ← TWO tt ;;
        @ret ('el × 'el) (r, op_mul m sh)
    }
  ].

#[export] Instance valid_RED_DDH0
  : ValidPackage (RED_loc :|: DDH0_loc)
      Game_import (I_PK_OTSR elgamal) (nom_link RED DDH0).
Proof. dprove_valid. Qed.

#[export] Instance valid_RED_DDH1
  : ValidPackage (RED_loc :|: DDH1_loc)
      Game_import (I_PK_OTSR elgamal) (nom_link RED DDH1).
Proof. dprove_valid. Qed.

Definition quad (l₀ l₁ l₂ l₃ : Location) (R : l₀ → l₁ → l₂ → l₃ → Prop)
  : precond := λ '(h₀, h₁),
    R (get_heap h₀ l₀) (get_heap h₀ l₁) (get_heap h₁ l₂) (get_heap h₁ l₃).

Arguments quad : simpl never.

Lemma quad_SemiInvariant {l₀ l₁ l₂ l₃ : Location} {L₀ L₁ : {fset Location}} {R} :
  l₀ \in L₀ → l₁ \in L₀ → l₂ \in L₁ → l₃ \in L₁ → 
  quad l₀ l₁ l₂ l₃ R (empty_heap, empty_heap) →
  SemiInvariant L₀ L₁ (quad l₀ l₁ l₂ l₃ R).
Proof.
  intros H0 H1 H2 H3 H4.
  eapply Build_SemiInvariant; [| done ].
  intros s0 s1 l v.
  move=> /negP H5 /negP H6.
  intros Q.
  unfold quad.
  do 4 try rewrite get_set_heap_neq //.
  1-4: apply /eqP; move=> ?; by subst.
Qed.

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
  ssprove_invariant.
  + apply fsubsetxx.
  + apply quad_SemiInvariant.
    1-4: fset_solve.
    done.
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
  ssprove_invariant.
  + apply fsubsetxx.
  + apply quad_SemiInvariant.
    1-4: fset_solve.
    done.
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

Lemma elgamal_sound {LA}
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
