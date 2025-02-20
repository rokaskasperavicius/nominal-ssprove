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
  { Sec : choice_type
  ; Pub : choice_type
  ; Mes : choice_type
  ; Key: choice_type

  ; keygen :
      code fset0 [interface] (Sec × Pub)

  (* How to pass the keygen? *)
  ; ckaInitA : ∀ (pk : Pub),
      code fset0 [interface] (Pub)

  ; ckaInitB : ∀ (sk : Sec),
      code fset0 [interface] (Sec)

  ; ckaS :
      code fset0 [interface] (Mes × Key)

  ; ckaR : ∀ (m : Mes),
      code fset0 [interface] (Key)
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

(* How does Mes p work? *)
Notation " 'mes p " := (Mes p)
  (at level 3) : package_scope.

Definition CKAKEY := 0%N.

Definition I_CORR (K : cka_scheme) :=
  [interface #val #[ CKAKEY ] : 'mes K × 'mes K  → 'unit ].

Definition CORR0 (K : cka_scheme) :
  game (I_CORR K) :=
  [module no_locs ;
    (* takes a list of messages and runs epochs for length of list 
      "assert" on each loop that keys match
    *)
    #def #[ CKAKEY ] (ms : ('mes K × 'mes K)) : 'unit {
      let '(m, m') := ms in

      '(skA, pkA) ← K.(keygen) ;;
      '(skB, pkB) ← K.(keygen) ;;
      stateA ← K.(ckaInitA) pkA ;;
      stateB ← K.(ckaInitB) skB ;;

      '(stateA, m, k) ← K.(ckaS) stateA ;;
      '(stateB, k') ← K.(ckaR) stateB m ;;
      
      ret tt
    }
  ].

Definition CORR1 (K : cka_scheme) :
  trimmed_package fset0 Game_import (I_CORR K) :=
  [trimmed_package
    #def #[ CKAKEY ] (m : 'mes K) : 'unit {
      ret tt
    }
  ].

Definition CORR P b := if b then CORR0 P : nom_package else CORR1 P.

Definition flag_loc : Location := ('option 'unit; 0%N).
Definition mpk_loc (P : cka_scheme) : Location := ('option ('pub P); 1%N).
Definition GET := 0%N.
Definition QUERY := 1%N.

End CKAscheme.
