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

From NominalSSP Require Import Prelude Group Misc.
Import PackageNotation.
#[local] Open Scope package_scope.

Module CKAscheme.

Record cka_scheme :=
  { Mes : choice_type
  ; Key: choice_type
  ; StateS: choice_type
  ; StateR: choice_type
  
  ; keygen : ∀ (x : StateR),
    code fset0 [interface] (StateS)

  ; ckaS : ∀ (state: StateS),
      code fset0 [interface] (StateR × Mes × Key)

  ; ckaR : ∀ (state: StateR) (m : Mes),
      code fset0 [interface] (StateS × Key)
  }.

Notation " 'stateS p " := (StateS p)
  (at level 3) : package_scope.

Notation " 'stateS p " := (StateS p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'stateR p " := (StateR p)
  (at level 3) : package_scope.

Notation " 'stateR p " := (StateR p)
  (in custom pack_type at level 2, p constr at level 20).

Definition CKAKEY := 0%N.
Definition stater_loc (K: cka_scheme) : Location := ('option ('stateR K); 1%N).
Definition states_loc (K: cka_scheme) : Location := ('option ('stateS K); 2%N).

Definition CKA_loc (K : cka_scheme) :=
  fset [:: stater_loc K ; states_loc K ].

Definition I_CORR_simple (K : cka_scheme) :=
  [interface #val #[ CKAKEY ] : 'stateR K  → 'unit ].

Definition I_CORR (K : cka_scheme) :=
  [interface #val #[ CKAKEY] : ('stateR K × 'nat)  → 'unit ].

Definition CORR0_simple (K : cka_scheme) :
  game (I_CORR_simple K) :=
  [module no_locs ;
    #def #[ CKAKEY ] (x : 'stateR K) : 'unit {
      '(pk) ← K.(keygen) x ;;

      '(stateA, m, kA) ← K.(ckaS) pk ;;
      '(stateB, kB) ← K.(ckaR) x m ;;

      #assert (kA == kB) ;;

      '(stateB', m', kB') ← K.(ckaS) stateB ;;
      '(stateA', kA') ← K.(ckaR) stateA m' ;;

      #assert (kA' == kB') ;;

      @ret 'unit Datatypes.tt
    }
  ].

Definition CORR1_simple (K : cka_scheme) :
  game (I_CORR_simple K) :=
  [module no_locs ;
    #def #[ CKAKEY ] (s: 'stateR K) : 'unit {
      @ret 'unit Datatypes.tt
    }
  ].

Fixpoint repeat {A : choiceType} (n : nat) (x : A) (c : A → raw_code A) := 
  match n with
   | 0%N => ret x
   | n.+1 => 
      x' ← c x ;;
      repeat n x' c
  end.

Instance valid_repeat:
∀ {A : choiceType} (L : {fset Location}) (I : Interface) (c : A → raw_code A) (x : A) (N : nat),
    (∀ i : A, ValidCode L I (c i)) → ValidCode L I (repeat N x c).
Admitted.


Definition CORR0 (K : cka_scheme) : 
  game (I_CORR K) :=
  [module CKA_loc K ;
    #def #[ CKAKEY ] (state : ('stateR K × 'nat)) : 'unit {
      let '(x, n) := state in
      '(pk) ← K.(keygen) x ;;
      
      repeat (n) ((pk, x) : ('stateS K × 'stateR K))  (fun state =>       
        let '(stateS, stateR) := state in
        '(stateR', m, kS) ← K.(ckaS) stateS ;;
        '(stateS', kR) ← K.(ckaR) stateR m ;;

        #assert (kS == kR) ;;
        @ret ('stateS K × 'stateR K) (stateS', stateR')
      ) ;;
      @ret 'unit Datatypes.tt
    }
  ].
  
Definition CORR1 (K : cka_scheme) :
  game (I_CORR K) :=
  [module no_locs ;
    #def #[ CKAKEY ] (state: ('stateR K × 'nat)) : 'unit {
      @ret 'unit Datatypes.tt
    }
  ].

Definition CORR P b := if b then CORR0 P else CORR1 P.

End CKAscheme.
