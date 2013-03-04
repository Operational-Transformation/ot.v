Require Import ListOperation.
Extraction Language Haskell.

Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inlined Constant Datatypes.length => "Prelude.length".
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].
Extract Inlined Constant option_map => "Prelude.fmap".
Extract Inductive prod => "(,)" [ "(,)" ].
Extract Constant fst => "Prelude.fst".
Extract Constant snd => "Prelude.snd".
Extraction Inline fst snd.
Extract Inductive Datatypes.nat => "Prelude.Int" ["0" "Prelude.succ"]
  "(\fO fS n -> if n==0 then fO () else fS (n-1))".

Extraction "ListOperation.hs"
  ListOperation.ListOperation
  ListOperation.apply
  ListOperation.compose
  ListOperation.transform.