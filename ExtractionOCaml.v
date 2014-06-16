Require Import ListOperation.
Extraction Language Ocaml.

Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inlined Constant Datatypes.length => "List.length".
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inlined Constant option_map => "(fun f a -> match a with Some e -> Some (f e) | None -> None)".
Extract Inductive prod => "(*)" [ "(,)" ].
Extract Constant fst => "fst".
Extract Constant snd => "snd".
Extraction Inline fst snd.
Extract Inductive Datatypes.nat => "int" ["0" "succ"] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extraction "ListOps.ml"
  ListOperation.ListOperation
  ListOperation.apply
  ListOperation.compose
  ListOperation.transform.
