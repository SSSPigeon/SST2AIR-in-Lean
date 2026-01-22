import LeanVerus.Hlist
import LeanVerus.Typ

open VerusLean

def arg_list (domain: ClosedTyp → Type) := hlist domain
