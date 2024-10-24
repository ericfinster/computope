(*
 *  expr.ml - raw expressions
 *) 


open Syntax
    
type name = string

type expr =

  | VarE of name
  | HomE of expr * expr * expr
  | ObjE 
  | CohE of expr tele * expr * expr * expr Suite.t 

type defn =
  | TermDef of name * expr tele * expr * expr
  | CohDef of name * expr tele * expr * expr
  | Normalize of expr tele * expr
  | Assert of expr tele * expr * expr

(*****************************************************************************)
(*                             Expr Pd Conversion                            *)
(*****************************************************************************)

let rec equal e f =
  match (e,f) with
  | (VarE nmE , VarE nmF) -> String.equal nmE nmF
  | (HomE (cE,sE,tE) , HomE (cF,sF,tF)) ->
    if (equal cE cF) then
      if (equal sE sF) then
        equal tE tF
      else false
    else false
  | (ObjE , ObjE) -> true
  | (CohE (tlE,sE,tE,_) , CohE (tlF,sF,tF,_)) ->
    if Suite.equal (fun (nmE,tyE) (nmF,tyF) ->
        String.equal nmE nmF && equal tyE tyF) tlE tlF then
      if equal sE sF then
        equal tE tF
      else false 
    else false 
  | _ -> false 

let rec pp ppf = function
  | VarE nm -> Fmt.pf ppf "%s" nm
  | HomE (c,s,t) ->
    Fmt.pf ppf "%a | %a -> %a"
      pp c pp s pp t 
  | ObjE -> Fmt.pf ppf "*"
  | CohE (tl,s,t,_) ->
    Fmt.pf ppf "coh %a : %a -> %a"
      (pp_tele pp) tl
      pp s pp t 

module ExprPdSyntax = struct

  type s = expr

  let obj = ObjE
  let hom c s t = HomE (c,s,t)

  let match_hom e =
    match e with
    | HomE (c,s,t) -> Some (c,s,t)
    | _ -> None

  let match_obj e =
    match e with
    | ObjE -> Some () 
    | _ -> None

  let lift _ t = t
  let var _ _ nm = VarE nm
  let strengthen _ _ _ e = e

  let equal = equal 
  let pp_dbg = pp

end

module ExprPdUtil =
  Syntax.PdUtil(ExprPdSyntax)

let string_pd_to_expr_tele (pd : string Pd.t) : expr tele =
  ExprPdUtil.string_pd_to_tele pd


