use std::rc::Rc;

use crate::compiler::runtypes::RunFailure;
use crate::compiler::sexp::SExp;

/*
open Sexp
open Binascii
open Arith
open Runtypes
 */

/*
fn choose_path(l: Srcloc, orig: 
let rec choose_path l orig p all context =
  if p == 1 then
    RunOk context
  else
    match context with
    | Cons (l,a,b) ->
      let next = if p mod 2 == 0 then a else b in
      choose_path l orig (p/2) all next

    | _ ->
      RunError
        (l, "bad path " ^ string_of_int orig ^ " in " ^ to_string all)
 */

/*
let cvt_to_string l : 'a sexp -> string runResult = function
  | Nil _ -> RunOk ""
  | Integer (_,v) -> RunOk (unhexlify @@ encode_int_to_bigint v)
  | Atom (_,v) -> RunOk v
  | QuotedString (_,_,v) -> RunOk v
  | any -> RunError (l, "bad argument to >s " ^ to_string any)

let cvt_to_int l = function
  | Nil _ -> RunOk 0
  | Integer (_,v) -> RunOk (intval v)
  | Atom (_,v) -> RunOk (intval @@ "0x" ^ encode_string_to_bigint v)
  | QuotedString (_,_,v) -> RunOk (intval @@ "0x" ^ encode_string_to_bigint v)
  | any -> RunError (l, "bad argument for int conversion " ^ to_string any)
     */

pub fn run(sexp: Rc<SExp>, context: Rc<SExp>) -> Result<SExp, RunFailure> {
    Err(RunFailure::RunErr(sexp.loc(), "unimplemented".to_string()))
}
/*
let rec run sexp context =
  let translate_head sexp =
    match sexp with
    | Nil l -> RunError (l, "cannot apply nil")
    | Atom (l,v) ->
      begin
        let matching_ops =
          List.filter
            (fun (pn,_pv) -> pn == v)
            Prims.prims
        in
        match matching_ops with
        | (_,hd) :: _ -> RunOk hd
        | _ -> RunError (l, "Can't find operator '" ^ v ^ "'")
      end
    | Integer (_,_) -> RunOk sexp
    | Cons (l,a,Nil l1) -> run (Cons (l,a,Nil l1)) context
    | any -> RunError (location_of any, "Unexpected head form in clvm " ^ to_string sexp)
  in
  let rec eval_args args =
    match args with
    | Nil l -> RunOk (Nil l)
    | Cons (l,a,b) ->
      run a context
      |> runBind
        (fun aval ->
           eval_args b
           |> runMap (fun atail -> Cons (l,aval,atail))
        )
    | any -> RunError (location_of any, "bad argument list")
  in
  let do_sgtr l (a : string) (b : string) : Srcloc.t sexp =
    if a > b then
      Integer (l,"1")
    else
      Nil l
  in
  let rec apply_op l head args =
    match (head,args) with
    | (Integer (_,"1"), any) ->
      RunOk any
    | (Integer (_,"2"), Cons (_,torun,Cons (_,nc,Nil _))) ->
      run torun nc
    | ( Integer (_,"3")
      , Cons
          ( _
          , cond
          , Cons
              ( _
              , iftrue
              , Cons
                  ( _
                  , iffalse
                  , Nil _
                  )
              )
          )
      ) ->
      if not @@ nilp cond then
        RunOk iftrue
      else
        RunOk iffalse
    | ( Integer (_,"4")
      , Cons
          ( _
          , first
          , Cons
              ( _
              , rest
              , Nil _
              )
          )
      ) -> RunOk (Cons (l,first,rest))
    | (Integer (_,"5"), Cons (_, lst, Nil _)) ->
      begin
        match lst with
        | Cons (_,x,_) -> RunOk x
        | _ -> RunError (l, "first applied to " ^ to_string lst)
      end
    | (Integer (_,"6"), Cons (_, lst, Nil _)) ->
      begin
        match lst with
        | Cons (_,_,y) -> RunOk y
        | _ -> RunError (l, "rest applied to " ^ to_string lst)
      end
    | (Integer (_,"7"), Cons (_, lstp, Nil _)) ->
      begin
        match lstp with
        | Cons (_,_,_) -> RunOk (Integer (l,"1"))
        | _ -> RunOk (Nil l)
      end
    | (Integer (_,"8"), any) -> RunExn (l,any)
    | ( Integer (_,"9")
      , Cons
          ( _
          , a
          , Cons
              ( _
              , b
              , Nil _
              )
          )
      ) ->
      if Sexp.equal a b then
        RunOk (Integer (l, "1"))
      else
        RunOk (Nil l)
    | ( Integer (_,"10")
      , Cons
          ( _
          , a
          , Cons
              ( _
              , b
              , Nil _
              )
          )
      ) ->
      cvt_to_string l a
      |> runBind
        (fun aval ->
           cvt_to_string l b
           |> runMap (do_sgtr l aval)
        )

    | (Integer (_,"11"), Cons (_, arg, Nil _)) ->
      cvt_to_string l arg
      |> runMap
        (fun s ->
           let hasher = Hash.create () in
           let _ = Hash.update hasher s in
           Integer (l, normalize_int (Hash.hex hasher) 16)
        )
    | ( Integer (_,"12")
      , Cons
          ( _
          , str
          , Cons
              ( _
              , from
              , Cons
                  ( _
                  , until
                  , Nil _
                  )
              )
          )
      ) ->
      cvt_to_string l str
      |> runBind
        (fun sval ->
           cvt_to_int l from
           |> runBind
             (fun fromval ->
                cvt_to_int l until
                |> runMap (fun uval -> (sval,fromval,uval))
             )
        )
      |> runBind
        (fun (str,fromval,uval) ->
           let slen = String.length str in
           if fromval < 0 || fromval >= slen || uval < 0 || uval > slen || uval < fromval then
             RunError (l, "bad range for strlen (s='" ^ str ^ "' f=" ^ to_string from ^ " u=" ^ to_string until ^ ")")
           else if fromval == uval then
             RunOk (Nil l)
           else
             RunOk (Atom (l,String.sub str fromval (uval - fromval)))
        )

    | (Integer (_,"13"), Cons (_, arg, Nil _)) ->
      cvt_to_string l arg
      |> runBind
        (fun a -> RunOk (Integer (l, string_of_int @@ String.length a)))

    | (Integer (_,"14"), Nil _) -> RunOk (Nil l)
    | (Integer (_,"14"), Cons (_, first, rest)) ->
      apply_op l head rest
      |> runBind (cvt_to_string l)
      |> runBind
        (fun cs ->
           cvt_to_string l first
           |> runMap (fun fs -> Atom (l, fs ^ cs))
        )

    | ( Integer (_,"16")
      , Cons
          ( _
          , a
          , Cons
              ( _
              , b
              , Nil _
              )
          )
      ) -> do_arith l add a b

    | ( Integer (_,"17")
      , Cons
          ( _
          , a
          , Cons
              ( _
              , b
              , Nil _
              )
          )
      ) -> do_arith l subtract a b

    | ( Integer (_,"18")
      , Cons
          ( _
          , a
          , Cons
              ( _
              , b
              , Nil _
              )
          )
      ) -> do_arith l multiply a b

    | ( Integer (_,"19")
      , Cons
          ( _
          , a
          , Cons
              ( _
              , b
              , Nil _
              )
          )
      ) -> do_arith l divide a b

    | ( Integer (_,"20")
      , Cons
          ( _
          , a
          , Cons
              ( _
              , b
              , Nil _
              )
          )
      ) -> do_divmod l a b

    | ( Integer (_,"21")
      , Cons
          ( _
          , a
          , Cons
              ( _
              , b
              , Nil _
              )
          )
      ) -> do_arith l do_greater a b

    | ( Integer (_,"22")
      , Cons
          ( _
          , a
          , Cons
              ( _
              , b
              , Nil _
              )
          )
      ) -> do_arith l ash a b

    | ( Integer (_,"23")
      , Cons
          ( _
          , a
          , Cons
              ( _
              , b
              , Nil _
              )
          )
      ) -> do_arith l lsh a b

    | ( Integer (_,"24")
      , Cons
          ( _
          , a
          , Cons
              ( _
              , b
              , Nil _
              )
          )
      ) -> do_arith l logand a b

    | ( Integer (_,"25")
      , Cons
          ( _
          , a
          , Cons
              ( _
              , b
              , Nil _
              )
          )
      ) -> do_arith l logior a b

    | ( Integer (_,"26")
      , Cons
          ( _
          , a
          , Cons
              ( _
              , b
              , Nil _
              )
          )
      ) -> do_arith l logxor a b

    | (Integer (_, "27"), Cons (_, v, Nil _)) ->
      if nilp v then
        RunOk (Integer (l, "1"))
      else
        RunOk (Nil l)

    (* | (Integer (_, "29"), ... point_add *)

    (* | (Integer (_, "30"), ... pubkey_for_exp *)

    | (Integer (_,"32"), Cons (_, v, Nil _)) ->
      if nilp v then
        RunOk (Integer (l, "1"))
      else
        RunOk (Nil l)

    | (Integer (_, "33"), Nil _) -> RunOk (Integer (l,"1"))
    | (Integer (_, "33"), Cons (_, first, rest)) ->
      apply_op l head rest
      |> runBind
        (fun rres ->
           if nilp rres && nilp first then
             RunOk (Nil l)
           else
             RunOk (Integer (l,"1"))
        )

    | (Integer (_, "34"), Nil _) -> RunOk (Nil l)
    | (Integer (_, "34"), Cons (_, first, rest)) ->
      apply_op l head rest
      |> runBind
        (fun rres ->
           if nilp rres || nilp first then
             RunOk (Nil l)
           else
             RunOk (Integer (l,"1"))
        )

    (* Softfork = 36 *)

    | (Integer (_,op), _) ->
      RunError (l, "bad arguments to op " ^ op)
    | (any, args) -> RunError (l, "bad op " ^ to_string any ^ " with args " ^ to_string args)
  in
  let result =
    match sexp with
    | Integer (l,v) ->
      (* An integer picks a value from the context *)
      choose_path l (intval v) (intval v) context context
    | QuotedString (_,_,_) ->
      RunOk sexp
    | Atom (l,v) ->
      run (Integer (l,encode_string_to_bigint v)) context
    | Nil l -> RunOk (Nil l)
    | Cons (l,a,b) ->
      translate_head a
      |> runBind
        (fun head ->
           match head with
           | Integer (_,"1") -> RunOk b
           | _ ->
             eval_args b
             |> runBind (apply_op l head)
        )
  in
  result

let parse_and_run file content args =
  let parse_result =
    parse_sexp
      Srcloc.combineSrcLocation
      (Srcloc.start file)
      Srcloc.advance
      content
  in
  let parse_args =
    parse_sexp
      Srcloc.combineSrcLocation
      (Srcloc.start file)
      Srcloc.advance
      args
  in
  match (parse_result, parse_args) with
  | (Sexp.Success code, Sexp.Success args) ->
    begin
      match (code, args) with
      | (real_code :: _, real_args :: _) ->
        run real_code real_args
      | ([], _) ->
        RunError (Srcloc.start file, "no code")
      | (_, []) ->
        RunError (Srcloc.start file, "no args")
    end
  | (_, Sexp.Failure (l,m)) ->
    RunError (l,m)
  | (Sexp.Failure (l,m), _) ->
    RunError (l,m)
*/
