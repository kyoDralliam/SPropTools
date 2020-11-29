From Coq Require Import Logic.StrictProp.
From SPropTools Require Import Logic.


Definition decidable P := { P } + {~ P }.


Class squash_modal X := from_squash : Squash X -> X.

Definition squash_modal_decidable {P} : decidable P -> squash_modal P :=
  fun decP sqP =>
    match decP with
    | left p => p
    | right np => ltac:(scontradiction (destruct sqP as [[]%np]))
    end.

Instance squash_modal_False : squash_modal False.
Proof. intros sqF; scontradiction (destruct sqF as [[]]). Qed.

Instance  squash_modal_True : squash_modal True.
Proof. intros; constructor. Qed.

Instance squash_modal_unit : squash_modal unit.
Proof. intros; constructor. Qed.

Definition bind_squash {A B} (f : A -> Squash B) (sqA : Squash A) : Squash B :=
  match sqA with | squash a => f a end.

Definition map_squash {A B} (f : A -> B) (sqA : Squash A) : Squash B :=
  match sqA with | squash a => squash (f a) end.

Instance squash_modal_prod {X Y} `{squash_modal X} `{squash_modal Y} : squash_modal (X * Y) :=
  fun sqXY => (from_squash (map_squash fst sqXY), from_squash (map_squash snd sqXY)).
