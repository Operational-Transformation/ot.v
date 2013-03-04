Module ListOperation.

Require Import
  Coq.Strings.Ascii
  Coq.Strings.String
  Coq.Arith.Peano_dec
  Coq.Lists.List.

Section ListOperation.

Variable A : Type.

Local Notation "[ ]" := nil : list_scope.
Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: nil) ..) : list_scope.
(* Import ListNotations. *) (* in Coq 8.4 *)

Inductive ListOperation : Type :=
  | EmptyOp  : ListOperation
  | RetainOp : ListOperation -> ListOperation
  | InsertOp : A -> ListOperation -> ListOperation
  | DeleteOp : ListOperation -> ListOperation.

Inductive ListOperationLength : ListOperation -> nat -> nat -> Prop :=
  | LengthEmpty  : ListOperationLength EmptyOp 0 0
  | LengthRetain : forall o m n, ListOperationLength o m n -> ListOperationLength (RetainOp o) (S m) (S n)
  | LengthInsert : forall a o m n, ListOperationLength o m n -> ListOperationLength (InsertOp a o) m (S n)
  | LengthDelete : forall o m n, ListOperationLength o m n -> ListOperationLength (DeleteOp o) (S m) n.

Hint Constructors ListOperationLength.

Fixpoint addDeleteOp (o : ListOperation) : ListOperation :=
  match o with
  | InsertOp i o' => InsertOp i (addDeleteOp o')
  | _             => DeleteOp o
  end.

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

Lemma operation_length_deterministic : forall o m n m' n',
  ListOperationLength o m n ->
  ListOperationLength o m' n' ->
  m = m' /\ n = n'.
Proof with auto.
  intros o. induction o; intros n m n' m' L1 L2; inversion L1; inversion L2; subst...
    destruct (IHo _ _ _ _ H0 H4)...
    destruct (IHo _ _ _ _ H3 H8)...
    destruct (IHo _ _ _ _ H0 H4)...
Qed.

Lemma operation_length_comb : forall o m n,
  ListOperationLength o m n ->
  m = start_length o /\ n = end_length o.
Proof.
  intros o m n H.
  assert (ListOperationLength o (start_length o) (end_length o)) as H' by apply operation_length.
  apply (operation_length_deterministic _ _ _ _ _ H H').
Qed.

Lemma start_length_addDeleteOp : forall o,
  start_length (addDeleteOp o) = S (start_length o).
Proof with auto.
  intros o. induction o...
Qed.

Lemma end_length_addDeleteOp : forall o,
  end_length (addDeleteOp o) = end_length o.
Proof with auto.
  intros o. induction o...
  (* InsertOp *) simpl. rewrite IHo...
Qed.

Lemma ListOperationLength_addDeleteOp : forall o m n,
  ListOperationLength (addDeleteOp o) m n <-> ListOperationLength (DeleteOp o) m n.
Proof.
  intros. split; intros L.
  (* -> *)
    destruct (operation_length_comb _ _ _ L) as [M N]; subst...
    rewrite start_length_addDeleteOp. rewrite end_length_addDeleteOp.
    constructor. apply operation_length.
  (* <- *)
    destruct (operation_length_comb _ _ _ L) as [M N]; subst. simpl.
    rewrite <- start_length_addDeleteOp. rewrite <- end_length_addDeleteOp.
    apply operation_length.
Qed.

Fixpoint apply (o : ListOperation) (l : list A) : option (list A) :=
  match o, l with
  | EmptyOp,       []      => Some []
  | RetainOp o',   x :: xs => option_map (fun xs' => x :: xs') (apply o' xs)
  | InsertOp x o', _       => option_map (fun l'  => x :: l')  (apply o' l)
  | DeleteOp o',   _ :: xs => apply o' xs
  | _,             _       => None
  end.

Lemma option_map_None : forall {S T : Type} (f : S -> T) (o : option S),
  option_map f o = None <-> o = None.
Proof.
  intros. split; intros H.
    destruct o. inversion H. reflexivity.
    rewrite H. reflexivity.
Qed.

Lemma apply_length : forall (o : ListOperation) (l : list A) (n : nat),
  ListOperationLength o (length l) n ->
  exists l', apply o l = Some l' /\ length l' = n.
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

Lemma apply_wrong_length : forall (o : ListOperation) (l : list A),
  start_length o <> length l ->
  apply o l = None.
Proof with auto.
  intros o. induction o; intros l H; destruct l as [| x xs]...
    contradiction H...
    simpl. rewrite option_map_None. apply IHo. intros Eq. apply H. simpl. rewrite Eq. reflexivity.
    simpl. rewrite option_map_None. apply IHo. assumption.
    simpl. rewrite option_map_None. apply IHo. assumption.
    simpl. apply IHo. intros Eq. apply H. simpl. rewrite Eq. reflexivity.
Qed.

Lemma apply_addDeleteOp : forall (o : ListOperation) (l : list A),
  apply (addDeleteOp o) l = apply (DeleteOp o) l.
Proof with auto.
  intros. induction o...
  (* InsertOp *)
    simpl. rewrite IHo. destruct l as [| x xs]...
Qed.

Fixpoint compose (a : ListOperation) : ListOperation -> option ListOperation :=
  fix compose' (b : ListOperation) : option (ListOperation) :=
    match a, b with
    | EmptyOp,       EmptyOp       => Some (EmptyOp)
    | DeleteOp a',   _             => option_map addDeleteOp  (compose a' b)
    | _,             InsertOp c b' => option_map (InsertOp c) (compose' b')
    | RetainOp a',   RetainOp b'   => option_map RetainOp     (compose a' b')
    | RetainOp a',   DeleteOp b'   => option_map addDeleteOp  (compose a' b')
    | InsertOp c a', RetainOp b'   => option_map (InsertOp c) (compose a' b')
    | InsertOp _ a', DeleteOp b'   => compose a' b'
    | _,             _             => None
    end.

Lemma compose_length : forall (a : ListOperation) (b : ListOperation) m n o,
  ListOperationLength a m n ->
  ListOperationLength b n o ->
  exists ab, compose a b = Some ab /\ ListOperationLength ab m o.
Proof with auto.
  intros a. induction a; intros.
  (* EmptyOp *)
    apply operation_length_comb in H; simpl in H; destruct H; subst.
    generalize dependent o. induction b; intros; try solve [inversion H0].
    (* EmptyOp *)
      exists EmptyOp...
    (* InsertOp *)
      inversion H0; subst. destruct (IHb _ H4) as [ab' [P Q]].
      exists (InsertOp a ab'). split... unfold compose. fold (compose EmptyOp). rewrite P...
  (* RetainOp *)
    apply operation_length_comb in H; simpl in H; destruct H; subst.
    generalize dependent o. induction b; intros; try solve [inversion H0].
    (* RetainOp *)
      inversion H0; subst. destruct (IHa _ _ _ _ (operation_length a) H2) as [ab' [P Q]].
      exists (RetainOp ab'). split... unfold compose. fold (compose a). rewrite P...
    (* InsertOp *)
      inversion H0; subst. destruct (IHb _ H4) as [ab' [P Q]].
      exists (InsertOp a0 ab'). split... unfold compose. fold (compose (RetainOp a)). rewrite P...
    (* DeleteOp *)
      inversion H0; subst. destruct (IHa _ _ _ _ (operation_length a) H2) as [ab' [P Q]].
      exists (addDeleteOp ab'). split.
        simpl. rewrite P...
        apply ListOperationLength_addDeleteOp...
  (* InsertOp *)
    rename a into c. rename a0 into a.
    apply operation_length_comb in H; simpl in H; destruct H; subst.
    generalize dependent o. induction b; intros; try solve [inversion H0].
    (* RetainOp *)
      inversion H0; subst. destruct (IHa _ _ _ _ (operation_length a) H2) as [ab' [P Q]].
      exists (InsertOp c ab'). split... unfold compose. fold (compose a). rewrite P...
    (* InsertOp *)
      inversion H0; subst. destruct (IHb _ H4) as [ab' [P Q]].
      exists (InsertOp a0 ab'). split... unfold compose. fold (compose (InsertOp c a)). rewrite P...
    (* DeleteOp *)
      inversion H0; subst. destruct (IHa _ _ _ _ (operation_length a) H2) as [ab' [P Q]].
      exists ab'...
  (* DeleteOp *)
    inversion H; subst. destruct (IHa _ _ _ _ H2 H0) as [ab' [P Q]].
    exists (addDeleteOp ab'). split.
      unfold compose. fold compose. destruct b; rewrite P...
      apply ListOperationLength_addDeleteOp...
Qed.

Lemma compose_wrong_length : forall a b,
  end_length a <> start_length b ->
  compose a b = None.
Proof with auto.
  intros a. induction a; intros.
  (* EmptyOp *)
    induction b...
    (* EmptyOp *)
      contradiction H...
    (* InsertOp *)
      unfold compose. fold (compose EmptyOp). rewrite option_map_None. apply IHb...
  (* RetainOp *)
    induction b...
    (* RetainOp *)
      unfold compose. fold compose. rewrite option_map_None. apply IHa.
      intros Eq. apply H. simpl. rewrite Eq...
    (* InsertOp *)
      unfold compose. fold (compose (RetainOp a)). rewrite option_map_None. apply IHb...
    (* DeleteOp *)
      unfold compose. fold compose. rewrite option_map_None. apply IHa.
      intros Eq. apply H. simpl. rewrite Eq...
  (* InsertOp *)
    induction b...
    (* RetainOp *)
      unfold compose. fold compose. rewrite option_map_None. apply IHa.
      intros Eq. apply H. simpl. rewrite Eq...
    (* InsertOp *)
      unfold compose. fold (compose (InsertOp a a0)). rewrite option_map_None. apply IHb...
    (* DeleteOp *)
      simpl. apply IHa.
      intros Eq. apply H. simpl. rewrite Eq...
  (* DeleteOp *)
    simpl. destruct b; simpl; rewrite option_map_None; apply IHa; assumption.
Qed.

Lemma compose_length' : forall a b ab,
  compose a b = Some ab ->
  end_length b = end_length ab.
Proof with auto.
  intros. set (La := operation_length a). set (Lb := operation_length b).
  destruct (eq_nat_dec (end_length a) (start_length b)) as [e | e].
  (* = *)
    rewrite e in La. destruct (compose_length _ _ _ _ _ La Lb) as [ab_ [P1 P2]].
    rewrite P1 in H. inversion H; subst. destruct (operation_length_comb _ _ _ P2) as [_ J]...
  (* <> *)
    apply compose_wrong_length in e. rewrite e in H. inversion H.
Qed.

Lemma compose_EmptyOp_left : forall b,
  start_length b = 0 ->
  compose EmptyOp b = Some b.
Proof with auto.
  intros b. induction b; intros H; inversion H...
  (* InsertOp *) unfold compose. fold (compose EmptyOp). rewrite IHb...
Qed.

Lemma compose_EmptyOp_right : forall a,
  end_length a = 0 ->
  compose a EmptyOp = Some a.
Proof with auto.
  intros a. induction a; intros H; inversion H...
  (* DeleteOp *)
    unfold compose. fold compose. rewrite IHa... simpl.
    destruct a; inversion H1...
Qed.

Definition option_join {T} (m : option (option T)) : option T :=
  match m with
  | None    => None
  | Some m' => m'
  end.

Lemma option_map_compose : forall S T U (f : S -> T) (g : T -> U) (m : option S),
  option_map g (option_map f m) = option_map (fun x => g (f x)) m.
Proof with auto.
  intros. destruct m...
Qed.

Lemma option_map_join : forall S T U (f : S -> option T) (g : T -> U) (m : option S),
  option_map g (option_join (option_map f m)) =
  option_join (option_map (fun x => option_map g (f x)) m).
Proof with auto.
  intros. destruct m...
Qed.

Definition compose_correct : forall a b l,
  option_join (option_map (apply b) (apply a l)) = option_join (option_map (fun ab => apply ab l) (compose a b)).
Proof with auto.
  intros a b l.
  destruct (eq_nat_dec (end_length a) (start_length b)) as [e | e].
  (* end_length a = start_length b *)
    destruct (eq_nat_dec (length l) (start_length a)) as [e0 | e0].
    (* length l = start_length a *)
      generalize dependent b. generalize dependent l. induction a; intros.
      (* EmptyOp *)
        rewrite compose_EmptyOp_left... destruct l as [| x xs]... inversion e0.
      (* RetainOp *)
        destruct l as [| x xs]. inversion e0.
        induction b; intros; inversion e; inversion e0...
        (* RetainOp *)
          unfold compose. fold compose.
          simpl. do 2 rewrite option_map_compose.
          simpl. do 2 rewrite <- option_map_join.
          rewrite IHa...
        (* InsertOp *)
          unfold compose. fold (compose (RetainOp a)).
          replace (apply (InsertOp a0 b)) with (fun x => option_map (fun y => a0 :: y) (apply b x)) by reflexivity.
          rewrite <- option_map_join. rewrite IHb...
          rewrite option_map_compose. simpl.
          rewrite <- option_map_join...
        (* DeleteOp *)
          unfold compose. fold compose.
          simpl. do 2 rewrite option_map_compose.
          rewrite IHa... destruct (compose a b)...
          simpl. rewrite apply_addDeleteOp...
      (* InsertOp *)
        rename a into c. rename a0 into a.
        induction b; intros; inversion e.
        (* RetainOp *)
          unfold compose. fold compose.
          simpl. do 2 rewrite option_map_compose.
          simpl. do 2 rewrite <- option_map_join.
          rewrite IHa...
        (* InsertOp *)
          unfold compose. fold (compose (InsertOp c a)).
          replace (apply (InsertOp a0 b)) with (fun x => option_map (fun y => a0 :: y) (apply b x)) by reflexivity.
          rewrite <- option_map_join. rewrite IHb...
          rewrite option_map_compose. simpl.
          rewrite <- option_map_join...
        (* DeleteOp *)
          unfold compose. fold compose.
          simpl. rewrite option_map_compose.
          rewrite IHa...
      (* DeleteOp *)
        destruct l as [| x xs]. inversion e0.
        simpl. rewrite IHa...
        replace ((fix compose' (b0 : ListOperation) : option ListOperation :=
            option_map addDeleteOp (compose a b0)) b) with (option_map addDeleteOp (compose a b)).
        rewrite option_map_compose. destruct (compose a b)...
        simpl. rewrite apply_addDeleteOp...
        (* replace *) destruct b...
  (* length l <> start_length a *)
    apply not_eq_sym in e0. rewrite (apply_wrong_length a l)...
    set (La := operation_length a). rewrite e in La.
    set (Lb := operation_length b).
    destruct (compose_length _ _ _ _ _ La Lb) as [ab [Eq_ab Lab]].
    rewrite Eq_ab. simpl. destruct (operation_length_comb _ _ _ Lab) as [H _].
    symmetry. apply (apply_wrong_length ab l). rewrite <- H...
    (* end_length a <> start_length b *)
      rewrite compose_wrong_length...
      destruct (eq_nat_dec (start_length a) (length l)).
      (* length l = start_length a *)
        set (La := operation_length a). rewrite e0 in La.
        destruct (apply_length _ _ _ La) as [l' [Eq_l' Len_l']]. rewrite Eq_l'.
        simpl. apply apply_wrong_length. rewrite Len_l'...
      (* length l <> start_length a *)
        rewrite apply_wrong_length...
Qed.

Lemma compose_InsertOp_right : forall a b c,
  compose a (InsertOp c b) = option_map (InsertOp c) (compose a b).
Proof with auto.
  intros. induction a...
  (* DeleteOp *)
    unfold compose. fold (compose a). rewrite IHa. rewrite option_map_compose. simpl.
    destruct b; rewrite option_map_compose...
Qed.

Lemma compose_addDeleteOp_right : forall a b,
  compose a (addDeleteOp b) = compose a (DeleteOp b).
Proof with auto.
  intros a. induction a; intros b...
    (* EmptyOp *)
      induction b...
      (* InsertOp *) simpl. fold (compose EmptyOp). rewrite IHb...
    (* RetainOp *)
      induction b...
      (* InsertOp *)
        unfold addDeleteOp. fold addDeleteOp.
        unfold compose. fold (compose (RetainOp a)). fold compose.
        rewrite compose_InsertOp_right.
        rewrite IHb. simpl. destruct (compose a b)...
    (* InsertOp *)
      induction b...
      (* InsertOp *)
        rename a into c. rename a0 into a.
        unfold addDeleteOp. fold addDeleteOp.
        unfold compose. fold (compose (InsertOp c a)). fold compose.
        rewrite compose_InsertOp_right.
        rewrite IHb. simpl. destruct (compose a b)...
    (* DeleteOp *)
      induction b...
      (* InsertOp *)
        unfold addDeleteOp. fold addDeleteOp.
        unfold compose. fold (compose (DeleteOp a)). fold compose.
        rewrite <- IHa...
Qed.

Lemma compose_RetainOp_addDeleteOp : forall a b c,
  compose a b = Some c ->
  compose (RetainOp a) (addDeleteOp b) = Some (addDeleteOp c).
Proof with auto.
  intros.
  rewrite compose_addDeleteOp_right.
  simpl. rewrite H...
Qed.

Definition pair_map {A A' B B' : Type} (f : A -> A') (g : B -> B') (p : A * B) : A' * B' :=
  pair (f (fst p)) (g (snd p)).

Definition option_pair_map {A A' B B' : Type} (f : A -> A') (g : B -> B') (mp : option (A * B)) : option (A' * B') :=
  option_map (pair_map f g) mp.

Lemma option_pair_map_None : forall A A' B B' (f : A -> A') (g : B -> B') mp,
  option_pair_map f g mp = None <-> mp = None.
Proof.
  intros. unfold option_pair_map. apply option_map_None.
Qed.

Fixpoint transform (a : ListOperation) : ListOperation -> option (ListOperation * ListOperation) :=
  fix transform' (b : ListOperation) : option (ListOperation * ListOperation) :=
    match a, b with
    | EmptyOp,       EmptyOp       => Some (pair EmptyOp EmptyOp)
    | InsertOp c a', _             => option_pair_map (InsertOp c) RetainOp     (transform a' b)
    | _,             InsertOp c b' => option_pair_map RetainOp     (InsertOp c) (transform' b')
    | RetainOp a',   RetainOp b'   => option_pair_map RetainOp     RetainOp     (transform a' b')
    | DeleteOp a',   DeleteOp b'   => transform a' b'
    | RetainOp a',   DeleteOp b'   => option_pair_map (fun x => x) addDeleteOp  (transform a' b')
    | DeleteOp a',   RetainOp b'   => option_pair_map addDeleteOp  (fun x => x) (transform a' b')
    | _,             _             => None
    end.

Lemma transform_correct : forall a b,
  start_length a = start_length b ->
  exists a' b' c, transform a b = Some (pair a' b') /\
                  compose a b' = Some c /\
                  compose b a' = Some c.
Proof with eauto.
  intros a. induction a; intros.
  (* EmptyOp *)
    induction b; inversion H.
    (* EmptyOp *)
      exists EmptyOp. exists EmptyOp. exists EmptyOp...
    (* InsertOp *)
      destruct (IHb H) as [a' [b' [c [T [C1 C2]]]]].
      exists (RetainOp a'). exists (InsertOp a b'). exists (InsertOp a c).
      simpl. fold (transform EmptyOp). fold (compose EmptyOp).
      rewrite T, C1, C2...
  (* RetainOp *)
    induction b; inversion H.
    (* RetainOp *)
      destruct (IHa _ H1) as [a' [b' [c [T [C1 C2]]]]].
      exists (RetainOp a'). exists (RetainOp b'). exists (RetainOp c).
      simpl. rewrite T, C1, C2...
    (* InsertOp *)
      rename a0 into ch.
      destruct (IHb H) as [a' [b' [c [T [C1 C2]]]]].
      exists (RetainOp a'). exists (InsertOp ch b'). exists (InsertOp ch c).
      unfold transform. fold (transform (RetainOp a)). unfold compose. fold (compose (RetainOp a)). fold compose.
      rewrite T, C1, C2...
    (* DeleteOp *)
      destruct (IHa _ H1) as [a' [b' [c [T [C1 C2]]]]].
      exists a'. exists (addDeleteOp b'). exists (addDeleteOp c).
      split. simpl. rewrite T...
      split.
        apply compose_RetainOp_addDeleteOp...
        simpl. destruct a'; rewrite C2...
  (* InsertOp *)
    rename a into ch. rename a0 into a.
    destruct (IHa _ H) as [a' [b' [c [T [C1 C2]]]]].
    exists (InsertOp ch a'). exists (RetainOp b'). exists (InsertOp ch c).
    rewrite compose_InsertOp_right.
    simpl. destruct b; rewrite T, C1, C2...
  (* DeleteOp *)
    induction b; inversion H.
    (* RetainOp *)
      destruct (IHa _ H1) as [a' [b' [c [T [C1 C2]]]]].
      exists (addDeleteOp a'). exists b'. exists (addDeleteOp c).
      split. simpl. rewrite T...
      split.
        simpl. destruct b'; rewrite C1...
        apply compose_RetainOp_addDeleteOp...
    (* InsertOp *)
      rename a0 into ch.
      destruct (IHb H) as [a' [b' [c [T [C1 C2]]]]].
      exists (RetainOp a'). exists (InsertOp ch b'). exists (InsertOp ch c).
      unfold transform. fold (transform (DeleteOp a)). unfold compose. fold compose.
      rewrite T, C2. split... split...
        rewrite compose_InsertOp_right.
        replace (Some (InsertOp ch c)) with (option_map (InsertOp ch) (Some c)) by reflexivity.
        rewrite <- C1. simpl. destruct b'; do 2 rewrite option_map_compose...
    (* DeleteOp *)
      destruct (IHa _ H1) as [a' [b' [c [T [C1 C2]]]]].
      exists a'. exists b'. exists (addDeleteOp c).
      simpl. split... split.
        destruct b'; rewrite C1...
        destruct a'; rewrite C2...
Qed.

Lemma transform_length : forall a b,
  start_length a = start_length b ->
  exists a' b', transform a b = Some (pair a' b') /\
                start_length a' = end_length b /\
                start_length b' = end_length a /\
                end_length a' = end_length b'.
Proof with auto.
  intros a b E. destruct (transform_correct a b E) as [a' [b' [c [T [C1 C2]]]]].
  exists a'. exists b'.
  assert (start_length a' = end_length b).
    destruct (eq_nat_dec (start_length a') (end_length b))...
    apply not_eq_sym in n. apply compose_wrong_length in n. rewrite n in C2. inversion C2.
  assert (start_length b' = end_length a).
    destruct (eq_nat_dec (start_length b') (end_length a))...
    apply not_eq_sym in n. apply compose_wrong_length in n. rewrite n in C1. inversion C1.
  split; [| split; [| split]]...
    apply compose_length' in C1. rewrite C1.
    apply compose_length' in C2. rewrite C2...
Qed.

Lemma transform_wrong_length : forall a b,
  start_length a <> start_length b ->
  transform a b = None.
Proof with auto.
  intros a. induction a; intros b E.
  (* EmptyOp *)
    induction b...
    (* EmptyOp *)
      contradiction E...
    (* InsertOp *)
      simpl. fold (transform EmptyOp). rewrite option_pair_map_None. apply IHb...
  (* RetainOp *)
    induction b...
    (* RetainOp *)
      simpl. rewrite option_pair_map_None. apply IHa.
      intros Eq. apply E. simpl. rewrite Eq...
    (* InsertOp *)
      unfold transform. fold (transform (RetainOp a)). rewrite option_pair_map_None. apply IHb...
    (* DeleteOp *)
      simpl. rewrite option_pair_map_None. apply IHa.
      intros Eq. apply E. simpl. rewrite Eq...
  (* InsertOp *)
    simpl. destruct b; rewrite IHa...
  (* DeleteOp *)
    induction b...
    (* RetainOp *)
      simpl. rewrite option_pair_map_None. apply IHa.
      intros Eq. apply E. simpl. rewrite Eq...
    (* InsertOp *)
      unfold transform. fold (transform (DeleteOp a)). rewrite option_pair_map_None. apply IHb...
    (* DeleteOp *)
      simpl. apply IHa.
      intros Eq. apply E. simpl. rewrite Eq...
Qed.

End ListOperation.

End ListOperation.