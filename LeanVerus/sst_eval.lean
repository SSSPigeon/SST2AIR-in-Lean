import LeanVerus.My_sst

open VerusLean Std

abbrev var_env := List Exp

abbrev typ_env := HashMap Typ Typ

abbrev func_env := HashMap Typ Exp
