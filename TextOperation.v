Module TextOperation.

Require Import
  Coq.Strings.Ascii
  Coq.Strings.String
  Coq.Lists.List.

Section TextOperation.

Variable A : Type.

Local Notation "[ ]" := nil : list_scope.
Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : list_scope.
(* Import ListNotations. *) (* in Coq 8.4 *)

Inductive ListOperation : Type :=
  | EmptyOp  : ListOperation
  | RetainOp : ListOperation -> ListOperation
  | InsertOp : A -> ListOperation -> ListOperation
  | DeleteOp : ListOperation -> ListOperation.

Inductive ListOperationLength : ListOperation -> nat -> nat -> Prop :=
  | LengthEmpty  : ListOperationLength EmptyOp 0 0
  | LengthRetain : forall o n m, ListOperationLength o n m -> ListOperationLength (RetainOp o) (S n) (S m)
  | LengthInsert : forall a o n m, ListOperationLength o n m -> ListOperationLength (InsertOp a o) n (S m)
  | LengthDelete : forall o n m, ListOperationLength o n m -> ListOperationLength (DeleteOp o) (S n) m.

Hint Constructors ListOperationLength.

Fixpoint start_length (o : ListOperation) : nat :=
  match o with
  | EmptyOp       => 0
  | RetainOp o'   => S (start_length o')
  | InsertOp _ o' => start_length o'
  | DeleteOp o'   => S (start_length o')
  end.

Fixpoint end_length (o : ListOperation) : nat :=
  match o with
  | EmptyOp       => 0
  | RetainOp o'   => S (end_length o')
  | InsertOp _ o' => S (end_length o')
  | DeleteOp o'   => end_length o'
  end.

Lemma operation_length : forall o, ListOperationLength o (start_length o) (end_length o).
Proof.
  intros o. induction o; constructor; assumption.
Qed.

Lemma operation_length_deterministic : forall o n m n' m',
  ListOperationLength o n m ->
  ListOperationLength o n' m' ->
  n = n' /\ m = m'.
Proof with auto.
  intros o. induction o; intros n m n' m' L1 L2; inversion L1; inversion L2; subst...
    destruct (IHo _ _ _ _ H0 H4)...
    destruct (IHo _ _ _ _ H3 H8)...
    destruct (IHo _ _ _ _ H0 H4)...
Qed.

Fixpoint apply (o : ListOperation) (l : list A) : option (list A) :=
  match o, l with
  | EmptyOp,       []      => Some []
  | RetainOp o',   x :: xs => option_map (fun xs' => x :: xs') (apply o' xs)
  | InsertOp x o', _       => option_map (fun l'  => x :: l')  (apply o' l)
  | DeleteOp o',   _ :: xs => apply o' xs
  | _,             _       => None
  end.

Theorem apply_length : forall (o : ListOperation) (l : list A) (m : nat),
  ListOperationLength o (length l) m ->
  exists l', apply o l = Some l' /\ length l' = m.
Proof with auto.
  intros o. induction o; intros.
    inversion H. destruct l.
      exists []...
      inversion H0.
    inversion H; subst. destruct l.
      inversion H1.
      inversion H1; subst. apply IHo in H2. destruct H2 as [l' [H2a H2b]]. exists (a :: l'). split.
        simpl. rewrite H2a...
        simpl. rewrite H2b...
    inversion H; subst. apply IHo in H4. destruct H4 as [l' [H4a H4b]]. exists (a :: l'). split.
      simpl. rewrite H4a...
      simpl. rewrite H4b...
    inversion H; subst. destruct l.
      inversion H1.
      inversion H1; subst. apply IHo in H2. destruct H2 as [l' [H2a H2b]]. exists l'. split.
        simpl. assumption.
        assumption.
Qed.

Fixpoint compose (a : ListOperation) : ListOperation -> option ListOperation :=
  fix compose' (b : ListOperation) : option (ListOperation) :=
    match a, b with
    | EmptyOp,       EmptyOp       => Some (EmptyOp)
    | DeleteOp a',   _             => option_map DeleteOp     (compose a' b)
    | _,             InsertOp c b' => option_map (InsertOp c) (compose' b')
    | RetainOp a',   RetainOp b'   => option_map RetainOp     (compose a' b')
    | RetainOp a',   DeleteOp b'   => option_map DeleteOp     (compose a' b')
    | InsertOp c a', RetainOp b'   => option_map (InsertOp c) (compose a' b')
    | InsertOp _ a', DeleteOp b'   => compose a' b'
    | _,             _             => None
    end.

Definition pair_map {A A' B B' : Type} (f : A -> A') (g : B -> B') (p : A * B) : A' * B' :=
  pair (f (fst p)) (g (snd p)).

Definition option_pair_map {A A' B B' : Type} (f : A -> A') (g : B -> B') (mp : option (A * B)) : option (A' * B') :=
  option_map (pair_map f g) mp.

Fixpoint transform (a : ListOperation) : ListOperation -> option (ListOperation * ListOperation) :=
  fix transform' (b : ListOperation) : option (ListOperation * ListOperation) :=
    match a, b with
    | EmptyOp,       EmptyOp       => Some (pair EmptyOp EmptyOp)
    | InsertOp c a', _             => option_pair_map (InsertOp c) RetainOp     (transform a' b)
    | _,             InsertOp c b' => option_pair_map RetainOp     (InsertOp c) (transform' b')
    | RetainOp a',   RetainOp b'   => option_pair_map RetainOp     RetainOp     (transform a' b')
    | DeleteOp a',   DeleteOp b'   => transform a' b'
    | RetainOp a',   DeleteOp b'   => option_pair_map DeleteOp     (fun x => x) (transform a' b')
    | DeleteOp a',   RetainOp b'   => option_pair_map (fun x => x) DeleteOp     (transform a' b')
    | _,             _             => None
    end.

End TextOperation.

End TextOperation.