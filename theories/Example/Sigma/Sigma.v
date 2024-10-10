
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Crypt Require Import Package Prelude.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Import PackageNotation.

From NominalSSP Require Import Nominal NomPackage Disjoint.

#[local] Open Scope ring_scope.

Record raw_sigma :=
  { Statement : choice_type
  ; Witness : choice_type
  ; Message : choice_type
  ; Challenge : choice_type
  ; Response : choice_type

  ; locs : {fset Location}

  ; R : Statement → Witness → bool

  ; commit :
    ∀ (h : Statement) (w : Witness),
      code locs [interface] Message

  ; response :
    ∀ (h : Statement) (w : Witness)
      (a : Message) (e : Challenge),
      code locs [interface] Response

  ; verify :
    ∀ (h : Statement) (a : Message) (e : Challenge)
      (z : Response),
      bool

  ; simulate :
    ∀ (h : Statement) (e : Challenge),
      code fset0 [interface] (Message × Response)

  ; extractor :
    ∀ (h : Statement) (a : Message)
      (e : Challenge) (e' : Challenge)
      (z : Response) (z' : Response),
      'option Witness
  }.

#[local] Open Scope package_scope.

Notation " 'statement p " :=
  (Statement p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'witness p " :=
  (Witness p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'message p " :=
  (Message p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'challenge p " :=
  (Challenge p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'response p " :=
  (Response p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'statement p " :=
  (Statement p)
  (at level 3) : package_scope.

Notation " 'witness p " :=
  (Witness p)
  (at level 3) : package_scope.

Notation " 'message p " :=
  (Message p)
  (at level 3) : package_scope.

Notation " 'challenge p " :=
  (Challenge p)
  (at level 3) : package_scope.

Notation " 'response p " :=
  (Response p)
  (at level 3) : package_scope.

(* Section: Correct *)

Definition RUN : nat := 1.

Definition Correct p :=
  [interface #val #[ RUN ] : ('statement p × 'witness p) × 'challenge p → 'bool ].

Definition Correct_real p :
  trimmed_package p.(locs) Game_import (Correct p) :=
  [trimmed_package
    #def #[ RUN ] ('(h, w, e) : ('statement p × 'witness p) × 'challenge p) : 'bool {
      #assert (p.(R) h w) ;;
      a ← p.(commit) h w ;;
      z ← p.(response) h w a e ;;
      @ret 'bool (p.(verify) h a e z)
    }
  ].

Definition Correct_ideal p :
  trimmed_package fset0 Game_import (Correct p) :=
  [trimmed_package
    #def #[ RUN ] ('(h, w, e) : ('statement p × 'witness p) × 'challenge p) : 'bool {
      #assert (p.(R) h w) ;;
      @ret 'bool true
    }
  ].

Definition Correct_pair p b :=
  if b then Correct_real p : nom_package else Correct_ideal p.

(* Main security statement for Special Honest-Verifier Zero-Knowledge. *)
Definition Adv_Correct p ε :=
  ∀ (A : nom_package),
  ValidPackage (loc A) (Correct p) A_export A →
  AdvantageP (Correct_pair p) A <= ε A.

(* Section: SHVZK *)

Definition TRANSCRIPT : nat := 0.

Definition chInput p := ('statement p × 'witness p) × 'challenge p.
Notation " 'input p " :=
  (chInput p)
  (in custom pack_type at level 2, p constr).

Definition chTranscript (p : raw_sigma) :=
  (('statement p × 'message p) × 'challenge p) × 'response p.
Notation " 'transcript p " :=
  (chTranscript p) (in custom pack_type at level 2, p constr).

Notation Transcript p := 
  [interface #val #[ TRANSCRIPT ] : ('input p) → 'transcript p ].

Definition SHVZK_real p :
  trimmed_package p.(locs) Game_import (Transcript p) :=
  [trimmed_package
    #def #[ TRANSCRIPT ] ('(h, w, e) : 'input p) : ('transcript p) {
      #assert (p.(R) h w) ;;
      a ← p.(commit) h w ;;
      z ← p.(response) h w a e ;;
      @ret (chTranscript p) (h, a, e, z)
    }
  ].

Definition SHVZK_ideal p :
  trimmed_package fset0 Game_import (Transcript p) :=
  [trimmed_package
    #def #[ TRANSCRIPT ] ('(h, w, e) : 'input p) : ('transcript p) {
      #assert (p.(R) h w) ;;
      '(a, z) ← p.(simulate) h e ;;
      @ret (chTranscript p) (h, a, e, z)
    }
  ].

Definition SHVZK p b :=
  if b then SHVZK_real p : nom_package else SHVZK_ideal p.

(* Main security statement for Special Honest-Verifier Zero-Knowledge. *)
Definition Adv_SHVZK p ε :=
  ∀ (A : nom_package),
  ValidPackage (loc A) (Transcript p) A_export A →
  AdvantageP (SHVZK p) A <= ε A.


(* Section: 2-special-soundness *)

Definition SOUNDNESS : nat := 4.

Definition chOpening p := 'challenge p × 'response p.
Notation " 'soundness p " :=
  (chProd (chProd ('statement p) ('message p)) (chProd (chOpening p) (chOpening p)))
  (in custom pack_type at level 2, p constr).

Notation Soundness p :=
  [interface #val #[ SOUNDNESS ] : ('soundness p) → 'bool ].

(*
Definition Special_Soundness_f p :
  trimmed_package fset0 Game_import (Soundness p) :=
  [trimmed_package
    #def #[ SOUNDNESS ] (arg : 'soundness p) : 'bool {
      let '((h, a), ((e, z), (e', z'))) := arg in
      let v1 := p.(verify) h a e z in
      let v2 := p.(verify) h a e' z' in
      if [&& (e != e') , v1 & v2 ] then
        match p.(extractor) (otf h) (otf a) (otf e) (otf e') (otf z) (otf z') with
        | Some w => ret (p.(R) (otf h) w)
        | None => ret false
        end
      else ret false
    }
  ].

Definition Special_Soundness_t p :
  trimmed_package fset0 Game_import (Soundness p) :=
  [trimmed_package
    #def #[ SOUNDNESS ] (t : chSoundness p) : 'bool {
      let '(h, (a, ((e, z), (e', z')))) := t in
      let v1 := p.(verify) (otf h) (otf a) (otf e) (otf z) in
      let v2 := p.(verify) (otf h) (otf a) (otf e') (otf z') in
      ret [&& (e != e') , v1 & v2 ]
    }
  ].

Definition Special_Soundness p b :=
  if b then Special_Soundness_t p : nom_package else Special_Soundness_f p.

(* Main security statement for 2-special soundness. *)
Definition TwoSpecialSoundness p ε :=
  ∀ (A : nom_package),
  ValidPackage (loc A) (Soundness p) A_export A →
  AdvantageP (Special_Soundness p) A <= ε A.
 *)
