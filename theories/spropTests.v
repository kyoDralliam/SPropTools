From SPropTools Require Import logic.


(** A few surprises (actually makes sense, but still...) *)

Section SPropExamplesAndCounterExamples.

  (* As indicated in the ceps/37 there is no cumulativity *)
  Goal SProp -> Type.
  Proof.
    intro x ; exact x. Fail Qed. (* Universe inconsistency *)
    Restart.
    intro x ; exact (Box x). (* But it works if wrapped (as it should) *)
  Qed.

  (* A dependent pair of a type and a proof it's a subsingleton *)
  Record hprop := { ty : Type ; is_hprop : forall (x y : ty), x = y}.

  (* SProps should be subsingleton (definitionally) *)
  Definition sprop_to_hprop (P : SProp) : hprop.
  Proof.
    (* But trying directly, it fails (P is accepted in Type though...) *)
    exists P. intros. Fail reflexivity.
    Restart.
    (* However it works if we wrap the SProp (but that's quite unconvenient) *)
    exists (Box P); intros [?] [?];  reflexivity.
  Qed.

  (* Here the problem is more visible, P is in SProp, not in Type so the equality is not well formed *)
  Fail Check forall (P : SProp) (x y : P), x = y.

  (* The goal does not typecheck, but Coq still allows me to try to prove it ??? *)
  Goal forall (P : SProp) (x y : P), x = y. Proof. admit. Fail Admitted.
  Abort All.

End SPropExamplesAndCounterExamples.
