(*****************************************************************************)
(*                                                                           *)
(*                            Suites (snoc lists)                            *)
(*                                                                           *)
(*****************************************************************************)

open Base

type 'a t =
  | Emp
  | Ext of 'a t * 'a
  [@@deriving equal] 

let (|@>) s x = Ext (s,x) 
  
type 'a suite = 'a t

let is_empty s =
  match s with
  | Emp -> true
  | _ -> false

let hd_exn s =
  match s with
  | Ext(_,a) -> a
  | _ -> invalid_arg "hd on empty suite" 

let init_exn s =
  match s with
  | Ext(s',_) -> s'
  | _ -> invalid_arg "init on empty suite" 

let rec first s =
  match s with
  | Emp -> invalid_arg "first on empty" 
  | Ext (Emp,x) -> x
  | Ext (s',_) -> first s'

let last s =
  match s with
  | Emp -> invalid_arg "last on empty" 
  | Ext (_,x) -> x

(* let rec match_init_exn s = *)
(*   match s with *)
(*   | Emp -> failwith "match init on empty" *)
(*   | Ext (Emp,x) -> (x,Emp) *)
(*   | Ext (s',x) -> *)
(*     let (i,s'') = match_init s' in *)
(*     (i,Ext (s'',x)) *)

let rec length s =
  match s with
  | Emp -> 0
  | Ext (s',_) -> length s' + 1

let rec map s ~f =
  match s with
  | Emp -> Emp
  | Ext (s',x) -> Ext (map s' ~f , f x)

let map_with_lvl s ~f =
  let rec go s =
    match s with
    | Emp -> (Emp , 0)
    | Ext (s',x) ->
      let (r,l) = go s' in
      (Ext (r,f l x),l+1)
  in fst (go s)

let rec build_from_lvl ~f k =
  if k > 0 then Ext (build_from_lvl ~f (k - 1), f (k-1)) else Emp

let rec filter s ~f =
  match s with
  | Emp -> Emp
  | Ext (s',x) ->
    let s'' = filter s' ~f in
    if (f x) then
      Ext (s'',x)
    else s''

let rec fold_left ~init ~f s =
  match s with
  | Emp -> init 
  | Ext (s',x) -> f (fold_left ~init ~f s') x

let rec fold_right ~init ~f s =
  match s with
  | Emp -> init 
  | Ext (s',x) -> fold_right s' ~init:(f x init) ~f

(* let rec fold_accum_cont : 'a suite -> 'c -> ('a -> 'c -> 'b * 'c) -> ('b suite -> 'c -> 'd) -> 'd = *)
(*   fun s c f cont -> *)
(*   match s with *)
(*   | Emp -> cont Emp c *)
(*   | Ext (s',a) -> *)
(*     fold_accum_cont s' c f (fun s'' c' -> *)
(*         let (b,c'') = f a c' in *)
(*         cont (Ext (s'',b)) c'') *)

(* let rec fold2 s t init f = *)
(*   match (s,t) with *)
(*   | (Emp,Emp) -> init *)
(*   | (Ext (s',x), Ext (t',y)) -> *)
(*     f (fold2 s' t' init f) x y *)
(*   | _ -> failwith "unequal length suites" *)

let rec append s t =
  match t with
  | Emp -> s
  | Ext (t',x) -> Ext (append s t',x)

let rec concat_map s ~f =
  match s with
  | Emp -> Emp
  | Ext (s',x) -> append (concat_map s' ~f) (f x)

let rec zip s t =
  match (s,t) with
  | (Emp,_) -> Emp
  | (_,Emp) -> Emp
  | (Ext (s',a), Ext (t',b)) ->
    Ext (zip s' t', (a, b))

let rec unzip s =
  match s with
  | Emp -> (Emp,Emp)
  | Ext (s',(a,b)) ->
    let (l,r) = unzip s' in
    (Ext (l,a), Ext (r,b))

let rec unzip3 s =
  match s with
  | Emp -> (Emp,Emp,Emp)
  | Ext (s',(a,b,c)) ->
    let (l,m,r) = unzip3 s' in
    (Ext (l,a), Ext (m,b), Ext (r,c))

let zip_with_idx s =
  let rec zip_with_idx_pr s =
    match s with
    | Emp -> (Emp,0)
    | Ext (s',x) ->
      let (s'', i) = zip_with_idx_pr s' in
      (Ext (s'',(i,x)), i+1)
  in fst (zip_with_idx_pr s)

let rec range i j =
  if (i > j) then Emp
  else Ext (range i (j-1), j)

let rec repeat n x =
  if (n = 0) then
    Emp
  else Ext (repeat (n-1) x , x)

let rec assoc ~eq ~key s = 
  match s with
  | Emp -> invalid_arg "empty in assoc"
  | Ext (s',(k',v)) ->
    if (eq key k') then v
    else assoc s' ~eq ~key 

(* let assoc_with_idx k s = *)
(*   let rec go i k s = *)
(*     match s with *)
(*     | Emp -> raise Lookup_error *)
(*     | Ext (s',(k',v)) -> *)
(*       if (Poly.(=) k k') then (i,v) *)
(*       else go (i+1) k s' *)
(*   in go 0 k s *)

let singleton a = Ext (Emp, a)

let rec append_list s l =
  match l with
  | [] -> s
  | x::xs -> append_list (Ext (s,x)) xs

let of_list l = append_list Emp l

let to_list s =
  let rec go s l =
    match s with
    | Emp -> l
    | Ext (s',x) -> go s' (x::l)
  in go s []

(* Extract de Brujin index from a suite *)
let rec db_get i s =
  match s with
  | Emp -> invalid_arg "db_get on empty"
  | Ext (s',x) ->
    if (i <= 0) then x
    else db_get (i-1) s'

let rec grab k s =
  if (k<=0) then (s,[]) else
  let (s',r) = grab (k-1) s in
  match s' with
  | Emp -> invalid_arg "grab on empty" 
  | Ext (s'',x) -> (s'',x::r)

let split_at k s =
  let d = length s in
  grab (d-k) s

(* let nth n s = *)
(*   let l = length s in *)
(*   db_get (l-n-1) s *)

let rev s =
  let rec go s acc =
    match s with
    | Emp -> acc
    | Ext (s',x) -> go s' (Ext (acc,x))
  in go s Emp

let drop s =
  match s with
  | Emp -> Error "Nothing to drop"
  | Ext (xs, x) -> Ok (x, xs)

let split_suite n s =
  let rec go n s =
    match s with
    | Emp -> (Emp,Emp,n)
    | Ext(xs,x) ->
       let (a, b, m) = go n xs in
       if m = 0 then (a, Ext(b,x),m) else (Ext(a,x),b,m - 1) in
  let (a, b, _) = go n s in (a, b)

(*****************************************************************************)
(*                                   Zipper                                  *)
(*****************************************************************************)

type 'a suite_zip = ('a suite * 'a * 'a list)

let close (l,a,r) =
  append_list (Ext(l,a)) r

let open_rightmost s =
  match s with
  | Emp -> Error "Empty suite on open"
  | Ext (s',a) -> Ok (s',a,[])

let move_left (l,a,r) =
  match l with
  | Emp -> Error "No left element"
  | Ext (l',a') -> Ok (l',a',a::r)

let move_right (l,a,r) =
  match r with
  | [] ->  Error "No right element"
  | a'::r' -> Ok (Ext (l,a),a',r')

let rec move_left_n n z =
  let open Base.Result.Monad_infix in
  if (n<=0) then Ok z else
    move_left z >>= move_left_n (n-1)

let open_leftmost s =
  let open Base.Result.Monad_infix in
  let n = length s in
  open_rightmost s >>= move_left_n (n-1)

let open_at k s =
  let open Base.Result.Monad_infix in
  let l = length s in
  if (k+1>l) then
    Error "Out of range"
  else open_rightmost s >>= move_left_n (l-k-1)

(*****************************************************************************)
(*                               Instances                                   *)
(*****************************************************************************)

module Cartesian_product = struct

  let bind = concat_map
  let map = map
  let map2 a b ~f = concat_map a ~f:(fun x -> map b ~f:(fun y -> f x y))
  let return = singleton
  let ( >>| ) l f = map l ~f
  let ( >>= ) t f = bind t ~f

  open struct
    module Applicative = Applicative.Make_using_map2 (struct
      type 'a t = 'a suite

      let return = return
      let map = `Custom map
      let map2 = map2
    end)

    module Monad = Monad.Make (struct
      type 'a t = 'a suite

      let return = return
      let map = `Custom map
      let bind = bind
    end)
  end

  let all = Monad.all
  let all_unit = Monad.all_unit
  let ignore_m = Monad.ignore_m
  let join = Monad.join

  module Monad_infix = struct
    let ( >>| ) = ( >>| )
    let ( >>= ) = ( >>= )
  end

  let apply = Applicative.apply
  let both = Applicative.both
  let map3 = Applicative.map3
  let ( <*> ) = Applicative.( <*> )
  let ( *> ) = Applicative.( *> )
  let ( <* ) = Applicative.( <* )

  module Applicative_infix = struct
    let ( >>| ) = ( >>| )
    let ( <*> ) = Applicative.( <*> )
    let ( *> ) = Applicative.( *> )
    let ( <* ) = Applicative.( <* )
  end

  module Let_syntax = struct
    let return = return
    let ( >>| ) = ( >>| )
    let ( >>= ) = ( >>= )

    module Let_syntax = struct
      let return = return
      let bind = bind
      let map = map
      let both = both

      module Open_on_rhs = struct end
    end
  end
end

include (Cartesian_product : Monad.S_local with type 'a t := 'a t)

(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)
    
let rec pp ?emp:(pp_emp=Fmt.nop) ?sep:(pp_sep=Fmt.sp) pp_el ppf s =
  match s with
  | Emp -> pp_emp ppf ()
  | Ext (Emp,el) ->
    Fmt.pf ppf "%a" pp_el el
  | Ext (s',el) ->
    Fmt.pf ppf "%a%a%a" (pp ~emp:pp_emp ~sep:pp_sep pp_el) s'
      pp_sep () pp_el el

