/-- Heterogeneous list -/
inductive hlist {A: Type} (f: A → Type) : List A → Type where
  | HL_nil : hlist f []
  | HL_cons : ∀ x xs, f x → hlist f xs → hlist f (x::xs)

/-- Example -/
inductive T where
  | A : T
  | B : T

def T_to_Type : T → Type
  | T.A => Int
  | T.B => Bool

def ex : hlist T_to_Type [T.A] := hlist.HL_cons T.A [] (42 : Int) hlist.HL_nil
