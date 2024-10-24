(*****************************************************************************)
(*                                                                           *)
(*                        Generic Syntax Constructions                       *)
(*                                                                           *)
(*****************************************************************************)

open Base

(*****************************************************************************)
(*                             Basic Syntax Types                            *)
(*****************************************************************************)

type lvl = int
type idx = int
type mvar = int
type name = string

let lvl_to_idx k l = k - l - 1
let idx_to_lvl k i = k - i - 1

let idx_pd pd =
  Pd.map_with_lvls pd 0
    ~f:(fun k l _ _ -> lvl_to_idx k l)

type 'a decl = (name * 'a)
type 'a tele = ('a decl) Suite.t

(*****************************************************************************)
(*                             Logging functions                             *)
(*****************************************************************************)

let log_msg ?idt:(i=0) (s : string) =
  let indt = String.make i ' ' in
  Fmt.pr "@[<v>%s@,@]" (indt ^ s)

let log_val ?idt:(i=0) (s : string) (a : 'a) (pp : 'a Fmt.t) =
  let indt = String.make i ' ' in
  Fmt.pr "@[<v>%s: @[%a@]@,@]@," (indt ^ s) pp a

(*****************************************************************************)
(*                                 Telescopes                                *)
(*****************************************************************************)

let tele_fold_with_idx g l f =
  Suite.fold_accum_cont g l
    (fun (nm,ict,tm) l' ->
       ((nm,ict,f tm l') , l'+1))

let pp_decl pp_el ppf (nm,t) =
  Fmt.pf ppf "(%s : %a)" nm pp_el t    

let pp_tele pp_el ppf tl =
  Suite.pp (pp_decl pp_el) ppf tl

(*****************************************************************************)
(*                         Pasting Diagram Conversion                        *)
(*****************************************************************************)

module type PdSyntax = sig

  type s

  val obj : s
  val hom : s -> s -> s -> s

  val match_hom : s -> (s * s * s) Option.t
  val match_obj : s -> unit Option.t

  val lift : int -> s -> s
  val var : lvl -> lvl -> name -> s

  val pp_dbg : s Fmt.t

  val equal : s -> s -> bool 

end

module PdUtil(P : PdSyntax) = struct
  include P

  let rec dim_ty c =
    match match_hom c with
    | None -> 0
    | Some (c,_,_) -> dim_ty c + 1

  let rec match_sph (c : s) : s Pd.sph Option.t =
    match match_hom c with
    | None -> None 
    | Some (c',s,t) ->
      Option.bind (match_sph c')
        ~f:(fun sph -> Some (Suite.Ext (sph,(s,t)))) 

  let rec sph_to_typ (sph : s Pd.sph) : s =
    match sph with
    | Emp -> obj 
    | Ext (sph',(s,t)) ->
      hom (sph_to_typ sph') s t

  let pd_to_tele (pd : 'a Pd.t)
      (lf : lvl -> 'a -> name)
      (nd : lvl -> 'a -> name) : s tele =

    let rec do_br sph br tl lvl =
      match br with
      | Pd.Br (x,brs) ->
        let nm = if (Suite.is_empty brs)
          then lf lvl x
          else nd lvl x in
        let sty = sph_to_typ sph in
        let tl' =  Suite.Ext (tl,(nm,sty)) in
        let src = var (lvl+1) lvl nm in
        do_brs (Pd.map_sph sph ~f:(lift 1)) src brs tl' (lvl+1)

    and do_brs sph src brs tl lvl =
      match brs with
      | Emp -> (tl, lvl, src)
      | Ext (brs',(x,br)) ->
        let (tl',lvl',src') = do_brs sph src brs' tl lvl in
        let sph' = Pd.map_sph sph ~f:(lift (lvl' - lvl)) in
        let tty = sph_to_typ sph' in
        let nm = nd lvl x in
        let tgt = var (lvl+1) lvl nm in (* check lvl here! *)
        let (tl'',lvl'',_) =
          do_br (Ext (Pd.map_sph sph' ~f:(lift 1),(lift 1 src',tgt)))
            br (Ext (tl',(nm,tty))) (lvl'+1) in
        (tl'',lvl'',lift (lvl''-lvl'-1) tgt)

    in let (tl,_,_) = do_br Emp pd Emp 0 in tl

  let string_pd_to_tele (pd : name Pd.t) : s tele =
    pd_to_tele pd (fun _ nm -> nm)
      (fun _ nm -> nm)

  let fresh_pd_tele (pd : 'a Pd.t) : s tele =
    let vn l = Fmt.str "x%d" l in
    pd_to_tele pd
      (fun l _ -> vn l)
      (fun l _ -> vn l)

  let tele_to_pd_fold (tl : s tele)
      (f : name -> lvl -> lvl -> s Pd.sph -> 'a)
    : ('a Pd.t , string) Result.t =

    let (let*) m f = Base.Result.bind m ~f in

    let rec go (d : int) (tl : s tele) =
      match tl with
      | Emp -> Error "Empty context is not a pasting diagram"

      | Ext(Emp,(onm,oty)) ->

        let depth = d + 1 in
        let svar = var 1 0 onm in

        if (equal oty obj) then
          Error "Initial type is not an object" 
        else

          let olbl = f onm depth 0 Emp in

          Ok (Pd.Br (olbl,Emp) , Suite.Emp, svar, depth, 1, 0)

      | Ext(Ext(tl',(tnm,tty)),(fnm,fty)) ->

        let* (pd,ssph,stm,dpth,lvl,dim) = go (d + 2) tl' in

        let* (tsph) = Result.of_option (match_sph tty)
            ~error:"Target cell does not have a spherical type." in

        let tdim = Suite.length tsph in
        let codim = dim - tdim in
        let (ssph',stm') = Pd.nth_target (ssph,stm) codim in

        if (Poly.(<>) ssph' tsph) then
          Error "Invalid target type"
        else

          let* (fsph) = Result.of_option (match_sph fty)
              ~error:"Filling cell does not have spherical type." in

          let tlbl = f tnm dpth lvl ssph' in
          let (lsph,ltm) = Pd.map_disc (ssph',stm') ~f:(lift 1) in
          let ttm = var (lvl+1) lvl tnm in

          let fsph' = Suite.Ext (lsph,(ltm,ttm)) in

          if (Poly.(<>) (fsph') (fsph)) then

            Error "Invalid filling type"

          else

            let ftm = var (lvl+2) (lvl+1) fnm in
            let lfsph = Pd.map_sph fsph' ~f:(lift 1) in
            let flbl = f fnm dpth (lvl+1) fsph' in
            let* pd' = Pd.insert_right pd tdim tlbl (Pd.Br (flbl,Emp)) in
            Ok (pd', lfsph, ftm, dpth, lvl+2, tdim+1)

    in let* (pd,_,_,_,_,_) = go 0 tl in Ok pd

  (* let fld_dbg (nm : name) (ict : icit) (k : lvl) (l : lvl) (sph : s sph) : unit = *)
  (*   let pp_ict i = match i with *)
  (*     | Impl -> "Impl" *)
  (*     | Expl -> "Expl" *)
  (*   in Fmt.pr "@[<v>----@,nm : %s@,ict: %s@,k: %d@,l: %d@,sph: @[%a@]@,@]" *)
  (*     nm (pp_ict ict) k l (pp_sph pp_dbg) sph *)

  let tele_to_pd (tl : s tele) : (name Pd.t , string) Result.t =
    let f nm _ _ _ = nm in
    tele_to_pd_fold tl f

  let tele_to_idx_pd (tl : s tele) : (idx Pd.t, string) Result.t =
    let f _ k l _ = lvl_to_idx k l in
    tele_to_pd_fold tl f

  let fresh_pd pd =
    let nm_lvl l = Fmt.str "x%d" l in
    Pd.map_pd_lf_nd_lvl pd
      ~lf:(fun lvl _ -> nm_lvl lvl)
      ~nd:(fun lvl _ -> nm_lvl lvl)

  let args_pd pd =
    let nm_lvl l = Fmt.str "x%d" l in
    Pd.map_with_lvls pd 0
      ~f:(fun k l _ _ -> var k l (nm_lvl l))

  let nm_ict_args_pd pd =
    Pd.map_with_lvls pd 0
      ~f:(fun k l _ (nm,ict) -> (nm, ict, var k l nm))

end

(*****************************************************************************)
(*                                 Coherences                                *)
(*****************************************************************************)

(* module type CohSyntax = sig *)
(*   include PdSyntax *)
(*   val app : s -> s -> icit -> s *)
(*   val coh : nm_ict pd -> s -> s -> s -> s *)
(*   val disc_coh : nm_ict pd -> s *)
(* end *)

(* module CohUtil(C : CohSyntax) = struct *)
(*   include C *)
(*   include PdUtil(C) *)

(*   let app_args t args = *)
(*     fold_left args t *)
(*       (fun t' (arg,ict) -> app t' arg ict) *)

(*   (\* Unbiased composition coherence *\) *)
(*   let rec ucomp_coh' (pd : nm_ict pd) (d : int) : s = *)
(*     if (is_disc pd) && d = dim_pd pd then *)
(*       disc_coh pd *)
(*     else *)
(*       match (match_hom (ucomp_ty' pd d)) with *)
(*       | None -> failwith "empty sphere in ucomp" *)
(*       | Some (ty,src,tgt) -> *)
(*          coh pd ty src tgt *)

(*   (\* Unbiased Type *\) *)
(*   and ucomp_ty' (pd : nm_ict pd) (d : int) : s = *)
(*     let bdry = boundary' (args_pd pd) d in *)
(*     let sph = map_with_lvl bdry ~f:(fun n (s,t) -> (ucomp_app' s n, ucomp_app' t n)) in *)
(*     sph_to_cat sph *)

(*   (\* Applied unbiased composite *\) *)
(*   and ucomp_app' : s pd -> int -> s = fun pd d -> *)
(*     if (is_disc pd) && d = dim_pd pd then *)
(*       head (labels pd) *)
(*     else *)
(*       let uc_coh = ucomp_coh' (fresh_pd pd) d in *)
(*       app_args uc_coh (pd_args pd) *)

(*   let ucomp_coh pd = ucomp_coh' pd (dim_pd pd) *)
(*   let ucomp_ty pd = ucomp_ty' pd (dim_pd pd) *)
(*   let ucomp_app pd = ucomp_app' pd (dim_pd pd) *)

(*   let ucomp_with_type' : s pd -> int -> s disc = fun pd d -> *)
(*     let bdry = boundary' pd d in *)
(*     let suite_sph = map_with_lvl bdry *)
(*         ~f:(fun n (s,t) -> (ucomp_app' s n, ucomp_app' t n)) in *)
(*     (suite_sph , ucomp_app' pd d) *)

(*   let ucomp_with_type pd = ucomp_with_type' pd (dim_pd pd) *)

(*   let whisker : s disc -> int -> s disc -> s disc = *)
(*     fun left i right -> *)
(*     let wpd = Base.Result.ok_or_failwith *)
(*         (whisk_right (disc_pd left) i right) in *)
(*     ucomp_with_type wpd *)

(*   let str_ucomp (pd : string pd) : s = *)
(*     ucomp_coh (pd_with_impl pd) *)

(*   let gen_ucomp (pd : 'a pd) : s = *)
(*     ucomp_coh (fresh_pd pd) *)

(* end *)

(*****************************************************************************)
(*                               Generic Syntax                              *)
(*****************************************************************************)

(* module type Syntax = sig *)
(*   include PdSyntax *)
(*   include CohSyntax *)
(*   val arr : s -> s *)
(*   val lam : name -> icit -> s -> s *)
(*   val pi : name -> icit -> s -> s -> s *)
(*   val pp_s : s Fmt.t *)
(* end *)

(* module SyntaxUtil(Syn : Syntax) = struct *)
(*   include Syn *)
(*   include PdUtil(Syn) *)

(*   (\* Utility Routines *\) *)
(*   (\* let app_args t args = *)
(*    *   fold_left args t *)
(*    *     (fun t' (arg,ict) -> app t' arg ict)  *\) *)

(*   let id_sub t = *)
(*     let k = length t in *)
(*     map_with_lvl t ~f:(fun l (nm,ict,_) -> *)
(*         (ict, var k l nm)) *)

(*   let abstract_tele tele tm = *)
(*     fold_right tele tm (fun (nm,ict,_) tm'  -> *)
(*         lam nm ict tm') *)

(*   let abstract_tele_with_type tl ty tm = *)
(*     fold_right tl (ty,tm) *)
(*       (fun (nm,ict,ty) (ty',tm') -> *)
(*         (pi nm ict ty ty', lam nm ict tm')) *)

(* end *)
