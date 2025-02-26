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

Notation " 'mes p " := (Mes p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'stateS p " := (StateS p)
  (at level 3) : package_scope.

Notation " 'stateS p " := (StateS p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'stateR p " := (StateR p)
  (at level 3) : package_scope.

Notation " 'stateR p " := (StateR p)
  (in custom pack_type at level 2, p constr at level 20).

(* How does Mes p work? *)
Notation " 'mes p " := (Mes p)
  (at level 3) : package_scope.

Definition CKAKEY := 0%N.

Definition I_CORR (K : cka_scheme) :=
  [interface #val #[ CKAKEY ] : 'stateR K  → 'unit ].

Definition CORR0 (K : cka_scheme) :
  game (I_CORR K) :=
  [module no_locs ;
    (* takes a list of messages and runs epochs for length of list 
      "assert" on each loop that keys match
    *)
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

Definition CORR1 (K : cka_scheme) :
  game (I_CORR K) :=
  [module no_locs ;
    #def #[ CKAKEY ] (s: 'stateR K) : 'unit {
      @ret 'unit Datatypes.tt
    }
  ].

Definition CORR P b := if b then CORR0 P else CORR1 P.

End CKAscheme.
