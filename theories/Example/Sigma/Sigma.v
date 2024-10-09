
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl
  Package Prelude RandomOracle.

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
  { Statement : finType
  ; Witness : finType
  ; Message : finType
  ; Challenge : finType
  ; Response : finType

  (* Can be inferred most of the time *)
  ; StatementPos : Positive #|Statement|
  ; WitnessPos : Positive #|Witness|
  ; MessagePos : Positive #|Message|
  ; ChallengePos : Positive #|Challenge|
  ; ResponsePos : Positive #|Response|

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
      code fset0 [interface]
        (prod (prod (prod Statement Message) Challenge) Response)

  ; extractor :
    ∀ (h : Statement) (a : Message)
      (e : Challenge) (e' : Challenge)
      (z : Response) (z' : Response),
      option Witness
  }.

#[local] Open Scope package_scope.

Definition TRANSCRIPT : nat := 0.
Definition SOUNDNESS : nat := 4.

#[export] Instance Positive_Statement p : Positive #|Statement p|.
Proof. apply StatementPos. Qed.

#[export] Instance Positive_Witness p : Positive #|Witness p|.
Proof. apply WitnessPos. Qed.

#[export] Instance Positive_Message p : Positive #|Message p|.
Proof. apply MessagePos. Qed.

#[export] Instance Positive_Challenge p : Positive #|Challenge p|.
Proof. apply ChallengePos. Qed.

#[export] Instance Positive_Response p : Positive #|Response p|.
Proof. apply ResponsePos. Qed.

Definition choiceStatement p := 'fin #|Statement p|.
Definition choiceWitness p := 'fin #|Witness p|.
Definition choiceMessage p := 'fin #|Message p|.
Definition choiceChallenge p := 'fin #|Challenge p|.
Definition choiceResponse p := 'fin #|Response p|.

Definition COMMIT : nat := 1.
Definition RESPOND : nat := 2.

Notation " 'statement p " :=
  (choiceStatement p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'witness p " :=
  (choiceWitness p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'message p " :=
  (choiceMessage p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'challenge p " :=
  (choiceChallenge p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'response p " :=
  (choiceResponse p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'statement p " :=
  (choiceStatement p)
  (at level 3) : package_scope.

Notation " 'witness p " :=
  (choiceWitness p)
  (at level 3) : package_scope.

Notation " 'message p " :=
  (choiceMessage p)
  (at level 3) : package_scope.

Notation " 'challenge p " :=
  (choiceChallenge p)
  (at level 3) : package_scope.

Notation " 'response p " :=
  (choiceResponse p)
  (at level 3) : package_scope.


Definition Commit π : opsig := 
  (COMMIT, ('statement π × 'witness π, 'message π)).

Definition Respond π : opsig := 
  (RESPOND, ((('statement π × 'witness π) × 'message π) × 'challenge π, 'response π)).

Notation "'#commit' π" :=
  (Commit π) (in custom interface at level 0, π constr at level 20).

Notation "'#respond' π" :=
  (Respond π) (in custom interface at level 0, π constr at level 20).

Definition IProtocol π :=
  [interface #commit π ; #respond π ].

Definition Protocol π :
  trimmed_package π.(locs) [interface] (IProtocol π)
  :=
  [trimmed_package
    #def #[ COMMIT ] ('(h, x) : 'statement π × 'witness π) : ('message π) {
      a ← π.(commit) (otf h) (otf x) ;;
      ret (fto a)
    } ;
    #def #[ RESPOND ]
        ('(h, x, a, z) : (('statement π × 'witness π) × 'message π) × 'challenge π)
        : ('response π) {
      r ← π.(response) (otf h) (otf x) (otf a) (otf z) ;;
      ret (fto r)
    }
  ].


(* Section: SHVZK *)

Definition choiceInput p := (chProd (chProd (choiceStatement p) (choiceWitness p)) (choiceChallenge p)).
Notation " 'chInput' p " :=
  (choiceInput p)
  (in custom pack_type at level 2, p constr).

Definition choiceTranscript (p : raw_sigma) :=
  chProd (chProd (chProd (choiceStatement p) (choiceMessage p)) (choiceChallenge p)) (choiceResponse p).
Notation " 'chTranscript' p " :=
  (choiceTranscript p) (in custom pack_type at level 2, p constr).

Notation Transcript p := 
  [interface #val #[ TRANSCRIPT ] : (chInput p) → chTranscript p ].

Definition SHVZK_real p :
  trimmed_package p.(locs) Game_import (Transcript p) :=
  [trimmed_package
    #def #[ TRANSCRIPT ] (hwe : chInput p) : (chTranscript p) {
      let '(h, w, e) := hwe in
      #assert (p.(R) (otf h) (otf w)) ;;
      a ← p.(commit) (otf h) (otf w) ;;
      z ← p.(response) (otf h) (otf w) a (otf e) ;;
      @ret (choiceTranscript p) (h, fto a, e, fto z)
    }
  ].

Definition SHVZK_ideal p :
  trimmed_package fset0 Game_import (Transcript p) :=
  [trimmed_package
    #def #[ TRANSCRIPT ] (hwe : chInput p) : (chTranscript p) {
      let '(h, w, e) := hwe in
      #assert (p.(R) (otf h) (otf w)) ;;
      '(h, a, e, z) ← p.(simulate) (otf h) (otf e) ;;
      @ret (choiceTranscript p) (fto h, fto a, fto e, fto z)
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

Definition Opening p := chProd (choiceChallenge p) (choiceResponse p).
Notation " 'chSoundness' p " :=
  (chProd (choiceStatement p)
    (chProd (choiceMessage p) (chProd (Opening p) (Opening p)))
  )
  (in custom pack_type at level 2, p constr).

Notation Soundness p :=
  [interface #val #[ SOUNDNESS ] : (chSoundness p) → 'bool ].

Definition Special_Soundness_f p :
  trimmed_package fset0 Game_import (Soundness p) :=
  [trimmed_package
    #def #[ SOUNDNESS ] (t : chSoundness p) : 'bool {
      let '(h, (a, ((e, z), (e', z')))) := t in
      let v1 := p.(verify) (otf h) (otf a) (otf e) (otf z) in
      let v2 := p.(verify) (otf h) (otf a) (otf e') (otf z') in
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
