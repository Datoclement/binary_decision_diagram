module type Ordered =
    sig
        type t
        val compare : t -> t -> int
    end
module type Serialized =
    sig
        type t
        val is_valid : char -> bool
        val from_string : string -> t
        val to_string : t -> string
    end
module type Variable =
    sig
        include Ordered
        include Serialized with type t := t
    end
module Int : Variable with type t = int =
    struct
        type t = int
        let compare a b = a-b
        let is_valid ch =
            match ch with
            | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' -> true
            | _ -> false
        let from_string = int_of_string
        let to_string = string_of_int
    end

module type Proposition =
    functor ( I : Variable ) ->
    sig
        type t
        val create : string -> t
        val to_string : t -> string
    end
module Prop =
    ( functor ( I : Variable ) ->
    struct
        type t =
            | Const of bool
            | Var of I.t
            | Not of t
            | And of t * t
            | Or of t * t
            | Imply of t * t
            | Equiv of t * t
        (* string to proposition *)
        let arty_ch ch =
            match ch with
            | '~' -> 1
            | _ -> 2
        let prty_ch ch =
            match ch with
            | '(' -> 0
            | '<' -> 1
            | '-' -> 2
            | '|' -> 3
            | '&' -> 4
            | _ -> 5
        let asso_ch ch =
            match ch with
            | '&' | '|' -> (-1)
            | '~' | '-' -> 1
            | _ -> 0
        let lnth_ch ch =
            match ch with
            | '~' -> 1
            | '&' | '|' | '-' -> 2
            | _ -> 3
        let create str =
                let l = String.length str in
                let ops = Stack.create () in
                let oprs = Stack.create () in
                let execute ch =
                    print_string ("execute: "^(String.make 1 ch)^"\n");
                    let ar = arty_ch ch in
                    if ar = 1 then
                        let f = Stack.pop oprs in
                        Stack.push (Not f) oprs
                    else
                        let s = Stack.pop oprs in
                        let f = Stack.pop oprs in
                        match ch with
                        | '&' -> Stack.push (And (f,s)) oprs
                        | '|' -> Stack.push (Or (f,s)) oprs
                        | '-' -> Stack.push (Imply (f,s)) oprs
                        | _ -> Stack.push (Equiv (f,s)) oprs
                in
                let rec execute_clo () =
                    let top = Stack.pop ops in
                    if top = '(' then ()
                    else (execute top; execute_clo ())
                in
                let rec execute_pri op =
                    let top = Stack.pop ops in
                    let prio_op = prty_ch op in
                    let prio_top = prty_ch top in
                    let asso = asso_ch op in
                    if prio_op > prio_top || ((asso > 0) && (prio_op = prio_top)) then
                        Stack.push top ops
                    else (execute top; execute_pri op)
                in
                Stack.push '(' ops;
                let rec aux = function p ->
                    if p = l then ctr p
                    else let ch = String.get str p in
                    if I.is_valid ch then num p
                    else
                    match ch with
                    | 't' | 'f' -> cst p
                    | '(' | ')' -> ctr p
                    | '~' | '&' | '|' | '-' | '<' -> opp p
                    | _ -> aux (p+1)
                and num = function p ->
                    let rec count q =
                        if p+q = l then q else
                        let ch = String.get str (p+q) in
                        if I.is_valid ch then count (q+1) else q
                    in
                    let cnt = count 0 in
                    Stack.push (Var (I.from_string (String.sub str p cnt))) oprs;
                    aux (p+cnt)
                and cst = function p ->
                    let ch = String.get str p in
                    if ch = 't' then (Stack.push (Const true) oprs; aux (p+4))
                    else (Stack.push (Const false) oprs; aux (p+5))
                and ctr = function p ->
                    if p = l then execute_clo ()
                    else if String.get str p = ')' then (execute_clo (); aux (p+1))
                    else (Stack.push '(' ops; aux (p+1))
                and opp = function p ->
                    let op = String.get str p in execute_pri op;
                    Stack.push op ops; aux (p+(lnth_ch op))
                in
                aux 0; Stack.top oprs
        (* proposition to string *)
        let priority p =
            match p with
            | Equiv (a,b)   -> 0
            | Imply (a,b)   -> 1
            | Or    (a,b)   -> 2
            | And   (a,b)   -> 3
            | Not   p       -> 4
            | Const b       -> 5
            | Var   v       -> 5
        let associativity p =
            match p with
            | Imply (a,b)   -> 1
            | Or    (a,b)   -> -1
            | And   (a,b)   -> -1
            | Not   p       -> -1
            | _ -> 0
        let rec to_string p =
                let prio_p = priority p in
                let asso_p = associativity p in
                let aux_binary str p1 p2 =
                    let str1 = to_string p1 in
                    let str2 = to_string p2 in
                    let prio_1 = priority p1 in
                    let prio_2 = priority p2 in
                    let b1 = prio_1 < prio_p || (prio_1 = prio_p && asso_p > 0) in
                    let b2 = prio_2 < prio_p || (prio_2 = prio_p && asso_p < 0) in
                    let left = if b1 then "("^str1^")" else str1 in
                    let right = if b2 then "("^str2^")" else str2 in
                    left^str^right
                in
                match p with
                | Const b -> string_of_bool b
                | Var   i -> I.to_string  i
                | Not   q ->
                    let str = to_string q in
                    let prio_q = priority q in
                    if prio_p >= prio_q then "~(" ^ str ^ ")" else "~"^str
                    | And (p1,p2) -> aux_binary "&&" p1 p2
                    | Or (p1,p2) -> aux_binary "||" p1 p2
                    | Imply (p1,p2) -> aux_binary "->" p1 p2
                    | Equiv (p1,p2) -> aux_binary "<->" p1 p2
    end : Proposition )
module PropInt = Prop(Int)

module type BinaryDecisionDiagram =
    functor ( I : Variable ) ->
    sig
        type t
        val create : Prop(I).t -> t
        val eval : t -> ( I.t -> bool ) -> bool
        val is_valid : t -> bool
        val is_satisfiable : t -> bool
        val save : string -> unit
    end

module BDD =
    ( functor ( I : Variable ) ->
    struct
        type t = | Leaf of bool | Node of t * I.t * t
        

    end : BinaryDecisionDiagram )


let () =
    let f = open_in "test.txt" in
    let l = input_line f in
    print_string (PropInt.to_string (PropInt.create l))
