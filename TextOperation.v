Module TextOperation.

Require Import
  Coq.Strings.Ascii
  Coq.Strings.String
  Coq.Lists.List.

Local Notation "[ ]" := nil : list_scope.
Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : list_scope.
(* Import ListNotations. *) (* in Coq 8.4 *)

Inductive ListOperation (A : Type) : Type :=
  | EmptyOp  : ListOperation A
  | RetainOp : ListOperation A -> ListOperation A
  | InsertOp : A -> ListOperation A -> ListOperation A
  | DeleteOp : ListOperation A -> ListOperation A.

Inductive ListOperationLength {A : Type} : ListOperation A -> nat -> nat -> Prop :=
  | LengthEmpty  : ListOperationLength (EmptyOp A) 0 0
  | LengthRetain : forall o n m, ListOperationLength o n m -> ListOperationLength (RetainOp A o) (S n) (S m)
  | LengthInsert : forall a o n m, ListOperationLength o n m -> ListOperationLength (InsertOp A a o) n (S m)
  | LengthDelete : forall o n m, ListOperationLength o n m -> ListOperationLength (DeleteOp A o) (S n) m.

Fixpoint apply {A : Type} (o : ListOperation A) (l : list A) : option (list A) :=
  match o, l with
  | EmptyOp,       []      => Some []
  | RetainOp o',   x :: xs => option_map (fun xs' => x :: xs') (apply o' xs)
  | InsertOp x o', _       => option_map (fun l'  => x :: l')  (apply o' l)
  | DeleteOp o',   _ :: xs => apply o' xs
  | _,             _       => None
  end.

Theorem apply_length : forall {A : Type} (o : ListOperation A) (l : list A) (m : nat),
  ListOperationLength o (length l) m ->
  exists l', apply o l = Some l' /\ length l' = m.
Proof with auto.
  intros A o. induction o; intros.
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

Fixpoint compose {A : Type} (a : ListOperation A) : ListOperation A -> option (ListOperation A) :=
  fix compose' (b : ListOperation A) : option (ListOperation A) :=
    match a, b with
    | EmptyOp,       EmptyOp       => Some (EmptyOp A)
    | DeleteOp a',   _             => option_map (DeleteOp A)   (compose a' b)
    | _,             InsertOp c b' => option_map (InsertOp A c) (compose' b')
    | RetainOp a',   RetainOp b'   => option_map (RetainOp A)   (compose a' b')
    | RetainOp a',   DeleteOp b'   => option_map (DeleteOp A)   (compose a' b')
    | InsertOp c a', RetainOp b'   => option_map (InsertOp A c) (compose a' b')
    | InsertOp _ a', DeleteOp b'   => compose a' b'
    | _,             _             => None
    end.

Definition pair_map {A A' B B' : Type} (f : A -> A') (g : B -> B') (p : A * B) : A' * B' :=
  pair (f (fst p)) (g (snd p)).

Definition option_pair_map {A A' B B' : Type} (f : A -> A') (g : B -> B') (mp : option (A * B)) : option (A' * B') :=
  option_map (pair_map f g) mp.

Fixpoint transform {A : Type} (a : ListOperation A) : ListOperation A -> option (ListOperation A * ListOperation A) :=
  fix transform' (b : ListOperation A) : option (ListOperation A * ListOperation A) :=
    match a, b with
    | EmptyOp,       EmptyOp       => Some (pair (EmptyOp A) (EmptyOp A))
    | InsertOp c a', _             => option_pair_map (InsertOp A c) (RetainOp A)   (transform a' b)
    | _,             InsertOp c b' => option_pair_map (RetainOp A)   (InsertOp A c) (transform' b')
    | RetainOp a',   RetainOp b'   => option_pair_map (RetainOp A)   (RetainOp A)   (transform a' b')
    | DeleteOp a',   DeleteOp b'   => transform a' b'
    | RetainOp a',   DeleteOp b'   => option_pair_map (DeleteOp A)   (fun x => x)   (transform a' b')
    | DeleteOp a',   RetainOp b'   => option_pair_map (fun x => x)   (DeleteOp A)   (transform a' b')
    | _,             _             => None
    end.

(*
Inductive ListOperation (A : Type) : nat -> nat -> Type :=
  | EmptyOp  : ListOperation A 0 0
  | RetainOp : forall n m, ListOperation A n m -> ListOperation A (S n) (S m)
  | InsertOp : forall n m, A -> ListOperation A n m -> ListOperation A n (S m)
  | DeleteOp : forall n m, ListOperation A n m -> ListOperation A (S n) m.

Definition TextOperation := ListOperation ascii.

Local Open Scope vector_scope.

Fixpoint apply {A : Type} {n m : nat} (o : ListOperation A n m) (v : t A n) : t A m :=
  match o with
  | EmptyOp => nil A (*[]%vector_scope nil []*)
  | RetainOp (S n) (S m) o' => match v with
    | cons x _ xs => cons x (apply o' xs)
    end
  | InsertOp n (S m) a o' => cons a _ (apply o' v)
  | DeleteOp (S n) m o' => match v with
    | cons _ _ xs => apply o' xs
    end
  end.

Fixpoint compose {A : Type} {n m k : nat} (a : ListOperation A n m) (b : ListOperation A m k) : ListOperation A n k := Admit.
*)

End TextOperation.