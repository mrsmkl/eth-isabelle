chapter {* Generated by Lem from julia.lem. *}

theory "Julia" 

imports 
 	 Main
	 "Lem_pervasives" 
	 "Lem_list" 
	 "Lem_map" 
	 "Lem_string" 
	 "Lem_word" 
	 "/mnt/c/Users/mrsmk/Desktop/eth-isabelle/lem/Word256" 
	 "/mnt/c/Users/mrsmk/Desktop/eth-isabelle/lem/Word160" 
	 "/mnt/c/Users/mrsmk/Desktop/eth-isabelle/lem/Word8" 

begin 


(* Specification of Solidity intermediate language *)

(*open import Pervasives*)
(*open import List*)
(*open import Map*)
(*open import String*)
(*open import Word*)
(*open import Word256*)
(*open import Word160*)
(*open import Word8*)

(** Syntax *)

type_synonym id0 =" int "

datatype type_name =
   CustomType " id0 "
 | Boolean
 | S256
 | S128
 | S64
 | S32
 | S8
 | U256
 | U128
 | U64
 | U32
 | U8

datatype literal_kind =
   TrueLiteral
 | FalseLiteral
 | StringLiteral " int " (* list word8 *)
 | NumberLiteral " int "

datatype expression =
   FunctionCall " id0 " " expression list "
 | Identifier " id0 "
 | Literal " literal_kind " " type_name "

datatype statement =
   Block " statement list "
 | FunctionDefinition " id0 " " (id0 * type_name) list " " (id0 * type_name) list " " statement "
 | VariableDeclaration " (id0 * type_name) list " " expression "
 | EmptyVariableDeclaration " (id0 * type_name) list "
 | Assignment " id0 list " " expression "
 | Switch " expression " " (literal_kind * type_name * statement) list " "  statement option "
 | Break
 | Continue
 | ForLoopInit " statement list " " expression " " statement " " statement "
 | ForLoop " expression " " statement " " statement "
 | Expression " expression "

(** Interpreter *)

datatype seq_mode =
   RegularMode
 | BreakMode
 | ContinueMode

datatype builtin =
   Convert " type_name " " type_name "
 | AddU256
 | SplitU256U64

datatype gbuiltin =
   MLoad
 | MStore
 | MStore8
 | MSize
 | SLoad
 | SStore
 | Log " int "
 | Gasleft
 | Balance
 | This
 | Create
 | Call
 | Return
 | Revert
 | Selfdestruct

(* It might be necessary to assume that there is a function for compiling / decompiling code to
   implement stuff like code size etc. *)

(*val two8 : integer*)
(*val two32 : integer*)
(*val two64 : integer*)
(*val two128 : integer*)
(*val two256 : integer*)
definition two8  :: " int "  where 
     " two8 = (( 256 :: int))"

definition two32  :: " int "  where 
     " two32 = (( 2 :: int)^( 32 :: nat))"

definition two64  :: " int "  where 
     " two64 = (( 2 :: int)^( 64 :: nat))"

definition two128  :: " int "  where 
     " two128 = (( 2 :: int)^( 128 :: nat))"

definition two256  :: " int "  where 
     " two256 = (( 2 :: int)^( 256 :: nat))"


fun typesize  :: " type_name \<Rightarrow> int "  where 
     " typesize U8 = ( two8 )"
|" typesize S8 = ( two8 )"
|" typesize U32 = ( two32 )"
|" typesize S32 = ( two32 )"
|" typesize U64 = ( two64 )"
|" typesize S64 = ( two64 )"
|" typesize U128 = ( two128 )"
|" typesize S128 = ( two128 )"
|" typesize U256 = ( two256 )"
|" typesize S256 = ( two256 )"
|" typesize _ = (( 2 :: int))" 
declare typesize.simps [simp del]


datatype value0 =
   IntV " int "
 | StringV " int "
 | ListV " value0 list "
 | FalseV
 | TrueV
 | FunctionV " id0 " " (id0 * type_name) list " " (id0 * type_name) list " " statement "
 | BuiltinV " builtin "
 | GBuiltinV " gbuiltin "

record account = 

  memory ::" int \<Rightarrow> value0 " 

  storage ::" int \<Rightarrow> value0 " 

  balance ::" int " 



definition empty_account  :: " account "  where 
     " empty_account = ( (|
  memory = (\<lambda> _ .  IntV(( 0 :: int))),
  storage = (\<lambda> _ .  IntV(( 0 :: int))),
  balance =(( 0 :: int)) 
|) )"


record state = 

   address ::" int " 

   accounts ::" int \<Rightarrow> account " 

   compile ::" statement \<Rightarrow> value0 list " 

   decompile ::" value0  list \<Rightarrow> statement " 



definition simple_compile  :: " statement \<Rightarrow>(value0)list "  where 
     " simple_compile st = ( [FunctionV(( 0 :: int)) [] [] st])"

fun simple_decompile  :: "(value0)list \<Rightarrow> statement "  where 
     " simple_decompile ([FunctionV _ _ _ st]) = ( st )"
|" simple_decompile _ = ( Block [])" 
declare simple_decompile.simps [simp del]


definition init_global  :: " int \<Rightarrow> state "  where 
     " init_global addr = ( (|
   address = addr,
   accounts = (\<lambda> _ .  empty_account),
   compile = simple_compile,
   decompile = simple_decompile 
|) )"


(*val eval_builtin : builtin -> list value -> list value*)
definition eval_builtin  :: " builtin \<Rightarrow>(value0)list \<Rightarrow>(value0)list "  where 
     " eval_builtin b lst = ( (case  (b, lst) of
   (AddU256, [IntV a, IntV b]) => [IntV ((a+b) mod two256)]
 | (Convert _ Boolean, [IntV x]) => if x =( 0 :: int) then [FalseV] else [TrueV]
 | (Convert Boolean _, [FalseV]) => [IntV(( 0 :: int))]
 | (Convert Boolean _, [TrueV]) => [IntV(( 1 :: int))]
 | (Convert _ t, [IntV a]) => [IntV (a mod typesize t)]
 | (SplitU256U64, [IntV a]) =>
    (let a2 = (a div two64) in
    (let a3 = (a2 div two64) in
    (let a4 = (a3 div two64) in
    [IntV (a mod two64), IntV (a2 mod two64), IntV (a3 mod two64), IntV (a4 mod two64)])))
 | _ => []
))"


(*val initial : map id value*)
definition initial  :: "((int),(value0))Map.map "  where 
     " initial = ( Map.empty )"


(*val eval_literal : literal_kind -> value*)
fun eval_literal  :: " literal_kind \<Rightarrow> value0 "  where 
     " eval_literal TrueLiteral = ( TrueV )"
|" eval_literal FalseLiteral = ( FalseV )"
|" eval_literal (StringLiteral lst) = ( StringV lst )"
|" eval_literal (NumberLiteral i) = ( IntV i )" 
declare eval_literal.simps [simp del]


(*
val eval_statement : global -> map id value -> statement -> global * map id value * seq_mode
val eval_expression : global -> map id value -> expression -> global * map id value * value
val step_statement : statement -> global * map id value * seq_mode -> global * map id value * seq_mode

let rec eval_statement g (l:map id value) st = match st with
 | Block lst ->
    let (g', l', _) = List.foldr step_statement (g,l,RegularMode) lst in
    (g', Map.mapi (fun k _ -> Map.findWithDefault k ErrorV l') l, RegularMode)
 | VariableDeclaration lst expr ->
    eval_statement g l (Assignment (List.map fst lst) expr)
 | EmptyVariableDeclaration lst ->
    let (lnew : map id value) = Map.fromList (List.map (fun x -> (fst x, IntV 0)) lst) in
    (g, (l union lnew), RegularMode)
 | FunctionDefinition id params rets st ->
    (g, Map.insert id (FunctionV id params rets st) l, RegularMode)
 | Assignment lst expr ->
    let (g, l, v) = eval_expression g l expr in
    let v = match v with ListV x -> x | a -> [a] end in
    let lst2 = List.mapi (fun i x -> (x, match List.index v i with Nothing -> ErrorV | Just x -> x end)) lst in
    let (lnew : map id value) = Map.fromList (lst2) in
    (g, (l union lnew), RegularMode)
 | Break -> (g, l, BreakMode)
 | Continue -> (g, l, ContinueMode)
 | ForLoopInit init cond post body ->
    eval_statement g l (Block (init ++ [ForLoop cond post body]))
 | ForLoop cond post body ->
    let (g, l, v) = eval_expression g l cond in
    if v = FalseV then (g, l, RegularMode) else
    let (g, l, mode) = eval_statement g l body in
    if mode = BreakMode then (g, l, RegularMode) else
    let (g, l, _) = eval_statement g l post in
    eval_statement g l (ForLoop cond post body)
end

and step_statement st (g, l, mode) = if mode = RegularMode then eval_statement g l st else (g, l, mode)

and eval_expression g (l:map id value) expr = match expr with
 | Literal lit _ -> (g, l, eval_literal lit)
 | Identifier x -> (g, l, Map.findWithDefault x ErrorV l)
 | FunctionCall id lst ->
    let (g, l, lst) = List.foldr (fun expr (g, l, lst) -> let (g,l,v) = eval_expression g l expr in (g,l,v::lst)) (g,l,[]) lst in
    match Map.lookup id l with
    | Just (FunctionV id params rets st) ->
       if List.length params <> List.length lst then (g,l,ErrorV) else
       let param_init = List.zip (List.map fst params) lst in
       let rets_init = List.map (fun x -> (fst x, IntV 0)) rets in
       let fctx : map id value = Map.fromList ((id, FunctionV id params rets st) :: param_init ++ rets_init) in
       let (g, l', _) = eval_statement g (l union fctx) (Block st) in
       (g, l, ListV (List.map (fun (k,_) -> Map.findWithDefault k ErrorV l') rets))
    | _ -> (g,l,ErrorV)
    end
end
*)

(*val eval_statement : state -> map id value -> statement -> nat -> maybe (state * map id value * seq_mode)*)
(*val eval_expression : state -> map id value -> expression -> nat -> maybe (state * map id value * value)*)
(*val step_statement : statement -> maybe (state * map id value * seq_mode) -> nat -> maybe (state * map id value * seq_mode)*)

function (sequential,domintros)  step_statement  :: " statement \<Rightarrow>(state*((int),(value0))Map.map*seq_mode)option \<Rightarrow> nat \<Rightarrow>(state*((int),(value0))Map.map*seq_mode)option "  
                   and eval_expression  :: " state \<Rightarrow>((id0),(value0))Map.map \<Rightarrow> expression \<Rightarrow> nat \<Rightarrow>(state*((int),(value0))Map.map*value0)option "  
                   and eval_statement  :: " state \<Rightarrow>((id0),(value0))Map.map \<Rightarrow> statement \<Rightarrow> nat \<Rightarrow>(state*((int),(value0))Map.map*seq_mode)option "  where 
     " eval_statement g (l:: (id0, value0)Map.map) st 0 = ( None )"
|" eval_statement g (l:: (id0, value0)Map.map) st ((Suc n)) = (
 (case  st of
   Block lst =>
    (case  List.foldr (\<lambda> st a .  step_statement st a n) lst (Some (g,l,RegularMode)) of
       Some (g', l', _) =>
       (* Should we check for error here too? should be impossible *)
       Some (g', map_domain_image (\<lambda> k _ .  case_option (IntV(( 0 :: int))) id ( l' k)) l, RegularMode)
     | None => None
    )
 | VariableDeclaration lst expr =>
    eval_statement g l (Assignment (List.map fst lst) expr) n
 | Expression expr =>
    (case  eval_expression g l expr n of
      Some (g, l, _) => Some (g, l, RegularMode)
    | None => None
    )
 | EmptyVariableDeclaration lst =>
    (let (lnew :: (id0, value0) Map.map) = (Map.map_of (List.rev (List.map (\<lambda> x .  (fst x, IntV(( 0 :: int)))) lst))) in
    Some (g, (l ++ lnew), RegularMode))
 | FunctionDefinition id1 params rets st =>
    Some (g, map_update id1 (FunctionV id1 params rets st) l, RegularMode)
 | Assignment lst expr =>
    (case  eval_expression g l expr n of
      Some (g, l, v) =>
      (let v = ((case  v of ListV x => x | a => [a] )) in
      if \<not> ((List.length v) = (List.length lst)) then None else
      (let lnew = (Map.map_of (List.rev (List.zip lst v))) in
      Some (g, (l ++ lnew), RegularMode)))
    | None =>None
    )
 | Break => Some (g, l, BreakMode)
 | Continue => Some (g, l, ContinueMode)
 | ForLoopInit init cond post1 body =>
    eval_statement g l (Block (init @ [ForLoop cond post1 body])) n
 | ForLoop cond post1 body =>
    (case  eval_expression g l cond n of
      Some (g, l, v) =>
       if v = FalseV then Some (g, l, RegularMode) else
       (case  eval_statement g l body n of
         Some (g, l, mode) =>
          if mode = BreakMode then Some (g, l, RegularMode) else
          (case  eval_statement g l post1 n of
            Some (g, l, _) => eval_statement g l (ForLoop cond post1 body) n
          | None => None
          )
       | None => None
       )
    | None => None
    )
 | Switch expr cases def1 =>
    (case  eval_expression g l expr n of
      Some (g, l, v) => 
  (let handle_case = (\<lambda>p a .  (case  (p ,a ) of
                                          ( (lit, _, st) , a ) => (case  a of
                                                                      Some (g, l, None) =>
                                                                  (let 
                                                                  v2 = 
                                                                  (eval_literal
                                                                    lit) in
                                                                  if 
                                                                  v2 \<noteq>
                                                                    v then
                                                                    Some
                                                                    (g, l, None)
                                                                  else
                                                                    (case  
                                                                    eval_statement
                                                                    g 
                                                                    l 
                                                                    st 
                                                                    n of
                                                                      None => 
                                                                    None
                                                                    | Some (g, l, mode) => 
                                                                    Some
                                                                    (g, l, 
                                                                    Some 
                                                                    mode)
                                                                    ))
                                                                    | a => 
                                                                  a
                                                                  )
                                      )) in
  (case  List.foldr handle_case cases (Some (g, l, None)) of
        Some (g, l, Some mode) => Some (g, l, mode)
    | Some (g, l, None) =>
  (case  def1 of
        None => Some (g, l, RegularMode)
    | Some st => eval_statement g l st n
  )
    | None => None
  ))
    | None => None
    )
   
))" |" eval_expression g (l:: (id0, value0)Map.map) expr 0 = ( None )"
|" eval_expression g (l:: (id0, value0)Map.map) expr ((Suc n)) = (
 (case  expr of
   Literal lit _ => Some (g, l, eval_literal lit)
 | Identifier x =>
    (case   l x of
      Some v => Some (g, l, v)
    | None => None
    )
 | FunctionCall id1 lst => 
  (let loop = (\<lambda> expr a .  (case  a of
                                         Some (g, l, lst) =>
                                   (case  eval_expression g l expr n of
                                         Some (g,l,v) => Some (g,l,(v # lst))
                                     | None => None
                                   )
                                     | None => None
                                   )) in
  (case  List.foldr loop lst (Some (g,l,[])) of
        Some (g, l, lst) =>
  (case   l id1 of
        Some (BuiltinV name) => Some (g, l, ListV (eval_builtin name lst))
    | Some (FunctionV id1 params rets st) =>
  if \<not> ((List.length params) = (List.length lst)) then None else
    (let param_init = (List.zip (List.map fst params) lst) in
    (let rets_init = (List.map (\<lambda> x .  (fst x, IntV (( 0 :: int))))
                        rets) in
    (let fctx :: ( id0, value0) Map.map = (Map.map_of
                                             (List.rev
                                                ((id1, FunctionV id1 
                                                       params rets st) #
                                                   (param_init @ rets_init)))) in
    (case  eval_statement g (l ++ fctx) st n of
          Some (g, l', _) => Some
                               (g, l, ListV
                                        (List.map
                                           (\<lambda> (k,_) .  case_option
                                                                 (IntV
                                                                    (
                                                                    (
                                                                     0 :: int)))
                                                                 id ( l' k))
                                           rets))
      | None => None
    ))))
    | _ => None
  )
    | None => None
  ))
))" |" step_statement st (Some (g, l, mode)) n = ( if mode = RegularMode then eval_statement g l st n else Some (g, l, mode))"
|" step_statement st None n = ( None )" 
by pat_completeness auto


end
