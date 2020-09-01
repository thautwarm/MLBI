module AST
type symbol = string

type ty_expr =
| TForall of symbol list * ty_expr
| TApp of ty_expr * ty_expr
| TArrow of ty_expr * ty_expr
| TVar of symbol
| TSym of symbol
| TNew of symbol



and expr =
| ELet of ty_expr option * symbol * expr * expr
| EApp of expr * expr
| EVar of symbol
| ELam of symbol * expr
| EQuery of expr


