import LeanVerus.Typ
import LeanVerus.Typing
import LeanVerus.Exp
import LeanVerus.Domain
import LeanVerus.Ast

open VerusLean typing airast

variable (tenv : typ_env)  (dom_aux : ClosedTyp → Type)

def trans (e : Exp):
