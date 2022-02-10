type token = LPAREN | RPAREN | IMPLICATION | BIIMPLICATION | NOT | AND | OR | LETTER of string | END;;

type ast = Paren of ast | Not of ast | And of ast * ast | Or of ast * ast | Letter of string 
           | Implication of ast * ast | BiImplication of ast * ast;;

let single_string s x = String.sub s x 1;;
let string_to_list s = List.init (String.length s) (single_string s);;
let is_upper c = let i = int_of_char c in 65 <= i && i <= 90;;

exception LexingError of string;; 

let rec lexer_list xs =
    match xs with 
    |"(" :: xs -> LPAREN :: lexer_list xs
    |")" :: xs -> RPAREN :: lexer_list xs
    |"&" :: xs -> AND :: lexer_list xs
    |"|" :: xs -> OR :: lexer_list xs
    |"*" :: xs -> AND :: lexer_list xs
    |"+" :: xs -> OR :: lexer_list xs
    |"~" :: xs -> NOT :: lexer_list xs
    |"-" :: ">" :: xs -> IMPLICATION :: lexer_list xs 
    |"<" :: "-" :: ">" :: xs -> BIIMPLICATION :: lexer_list xs
    |" " :: xs -> lexer_list xs 
    |[] -> [END]
    |_ -> (
        let x = List.hd xs in 
        if is_upper (String.get x 0) then LETTER(x) :: lexer_list (List.tl xs)
        else raise (LexingError(x))
    );;
    
let lexer input = lexer_list (string_to_list input);;

exception ParsingError;;

let lookahead xs = 
    match xs with
    |x::xs -> (x, xs)
    |[] -> raise ParsingError;;
    
let parse_left parse_X xs  = 
    let y, xs' = parse_X xs in
    let x, xs'' = lookahead xs' in (y, x, xs'');;    

let parse_right parse_X xs = 
    let y, xs' = parse_X xs in (y, xs')

(*
    y = left AST 
    x = current token
    xs = remaining tokens
    
    y' = right AST 
    xs' = remaining tokens after right AST has been parsed
*)

let rec parser xs = parse_S xs

and parse_S xs = 
    let y, xs = parse_I xs in 
    if xs = [END] then y 
    else raise ParsingError 

and parse_I xs = 
    let y, x, xs = parse_left parse_O xs in 
    match x with
    |IMPLICATION -> let y', xs' = parse_right parse_I xs in (Implication(y, y'), xs')
    |BIIMPLICATION -> let y', xs' = parse_right parse_I xs in (BiImplication(y, y'), xs')
    |_ -> (y, x :: xs)

and parse_O xs = 
    let y, x, xs = parse_left parse_A xs in
    match x with
    |OR -> let y', xs' = parse_right parse_O xs in (Or(y, y'), xs')
    |_ -> (y, x :: xs)
    
and parse_A xs = 
    let y, x, xs = parse_left parse_N xs in
    match x with
    |AND -> let y', xs' = parse_right parse_A xs in (And(y, y'), xs')
    |_ -> (y, x :: xs)
    
and parse_N xs = 
    let x, xs = lookahead xs in
    match x with
    |NOT -> let y', xs' = parse_right parse_F xs in (Not(y'), xs')
    |_ -> let y', xs' = parse_right parse_F (x :: xs) in (y', xs')
    
and parse_F xs = 
    let x, xs = lookahead xs in 
    match x with
    |LPAREN -> (
       let y', xs' = parse_right parse_I xs in
       match xs' with
       |RPAREN::xs' -> (y', xs')
       |_ -> raise ParsingError
    )
    |LETTER(l) -> (Letter(l), xs)
    |_ -> raise ParsingError;;

exception PrintError

let rec pprint_string t p =
    let string, p' = 
        match t with    
        |Or(t1, t2) -> (
            match t1, t2 with
            |Or(_, _), Or(_, _) -> ((pprint_string t1 false) ^ " ∨ " ^ (pprint_string t2 false), p)
            |Or(_, _), _ -> ((pprint_string t1 false) ^ " ∨ " ^ (pprint_string t2 true), p)
            |_, Or(_, _) -> ((pprint_string t1 true) ^ " ∨ " ^ (pprint_string t2 false), p)
            |_ -> ((pprint_string t1 true) ^ " ∨ " ^ (pprint_string t2 true), p)
        )
        |And(t1, t2) -> (
            match t1, t2 with
            |And(_, _), And(_, _) -> ((pprint_string t1 false) ^ " ∧ " ^ (pprint_string t2 false), p)
            |And(_, _), _ -> ((pprint_string t1 false) ^ " ∧ " ^ (pprint_string t2 true), p)
            |_, And(_, _) -> ((pprint_string t1 true) ^ " ∧ " ^ (pprint_string t2 false), p)
            |_ -> ((pprint_string t1 true) ^ " ∧ " ^ (pprint_string t2 true), p)
        )
        |Not(Letter(l)) -> ("¬" ^ l, false)
        |Not(t) -> ("¬" ^ (pprint_string t true), p)
        |Letter(l) -> (l, false)
        |Implication(t1, t2) -> ((pprint_string t1 true) ^ "->" ^ (pprint_string t2 true), p)
        |BiImplication(t1, t2) -> ((pprint_string t1 true) ^ "<->" ^ (pprint_string t2 true), p)
        |_ -> raise PrintError
    in if p' then "(" ^ string ^ ")" else string;;
        
let pprint t = print_endline (pprint_string t false);; 

exception ConvertError

let convert_implications t =
    match t with
    |Not(Implication(t1, t2)) -> And(convert_implications t1, Not(convert_implications t2))
    |Implication(t1, t2) -> Or(Not(convert_implications t1), convert_implications t2)
    |Not(BiImplication(t1, t2)) -> Or(And(Not(convert_implications t1), convert_implications t2),
                                   And(Not(convert_implications t2), convert_implications t1))
    |BiImplication(t1, t2) -> And(Or(Not(convert_implications t1), t2), Or(Not(convert_implications t2), t1))
    |Letter(l) -> Letter(l)
    |And(t1, t2) -> And(convert_implications t1, convert_implications t2)
    |Or(t1, t2) -> Or(convert_implications t1, convert_implications t2)
    |Not(t1) -> Not(convert_implications t1)
    |_ -> raise ConvertError;;

exception PushInNotsError

let rec push_in_nots t = 
    match t with
    |Not(Or(t1, t2)) -> And(push_in_nots (Not(t1)), push_in_nots (Not(t2)))
    |Not(And(t1, t2)) -> Or(push_in_nots (Not(t1)), push_in_nots (Not(t2)))
    |Not(Not(t1)) -> push_in_nots t1
    |Not(Letter(l)) -> Not(Letter(l))
    |Or(t1, t2) -> Or(push_in_nots t1, push_in_nots t2)
    |And(t1, t2) -> And(push_in_nots t1, push_in_nots t2)
    |Letter(l) -> Letter(l)
    |_ -> raise PushInNotsError;;

let rec power a = function
  |0 -> 1
  |1 -> a
  |n -> (
    let b = pow a (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else a)
  )

let rec get_and_expressions t = 
    match t with
    |And(t1, t2) -> get_and_expressions(t1) @ get_and_expressions(t2)
    |_ -> [t];;

let rec find_all_combinations xs ys =
    let rec find_all_combinations' xs y = 
        match xs with
        |x::xs -> [(x, y)] @ find_all_combinations' xs y
        |[] -> []
    in match ys with
    |y::ys -> find_all_combinations' xs y @ find_all_combinations xs ys
    |[] -> [];;

exception GenerateError

let generate_and_tree' xs = 
    let len = List.length xs in 
    let layers = Misc.log2 len in
    let excess = len - (power 2 layers) in
    let create_or pair = 
        let x, y = pair in Or(x, y) 
    in 
    let rec generate_and layer_level excess_count ys =
        if layer_level = 0 then (
            if excess_count > 0 then (
                match ys with
                |y :: y' :: ys -> (And(create_or y, create_or y'), excess_count - 1, ys)
                |_ -> raise GenerateError
            ) else (
                match ys with
                |y :: ys -> (create_or y, excess_count, ys)
                |_ -> raise GenerateError
            )
        )
        else (
            let left_tree, excess_count', ys' = generate_and (layer_level - 1) excess_count ys in
            let right_tree, excess_count'', ys'' = generate_and (layer_level - 1) excess_count' ys' in
            (And(left_tree, right_tree), excess_count'', ys'')
        )
    in generate_and layers excess xs;;
    
let generate_and_tree xs = let t, _, _ = generate_and_tree' xs in t;;

let and_or_swap t1 t2 = generate_and_tree (find_all_combinations (get_and_expressions t1) (get_and_expressions t2))

exception TakeOutAndActionError

let take_out_and_action t = 
    match t with
    |Or(t1, t2) -> (
        match t1, t2 with
        |Or(s1, s2), Or(r1, r2) -> Or(t1, t2)
        |_, And(r1, r2) -> and_or_swap t1 t2
        |And(s1, s2), _ -> and_or_swap t1 t2
        |_ -> t 
    )
    |And(t1, t2) -> And(t1, t2)
    |Not(Letter(l)) -> Not(Letter(l))
    |Letter(l) -> Letter(l)
    |_ -> raise TakeOutAndActionError;;

exception TakeOutAndError

let rec take_out_and_step t = 
    match t with
    |Or(t1, t2) -> let s1 = take_out_and_action (take_out_and_step t1) in 
                   let s2 = take_out_and_action (take_out_and_step t2) in 
                   Or(s1, s2)
    |And(t1, t2) -> let s1 = take_out_and_action (take_out_and_step t1) in 
                    let s2 = take_out_and_action (take_out_and_step t2) in 
                    And(s1, s2)
    |Not(Letter(l)) -> Not(Letter(l))
    |Letter(l) -> Letter(l)
    |_ -> raise TakeOutAndError;;

let take_out_ands t = take_out_and_action (take_out_and_step t);;

let input_to_ast input = parser ( lexer input )

let ast_to_cnf t = take_out_ands (push_in_nots (convert_implications t))

let input_to_cnf input = ast_to_cnf ( input_to_ast input );;

(* Examples *)

pprint (input_to_cnf "~(P | Q | R) | ((P & Q) | R)");;

(* (¬P ∨ P ∨ R) ∧ (¬Q ∨ P ∨ R) ∧ (¬R ∨ P ∨ R) ∧ (¬P ∨ Q ∨ R) ∧ (¬Q ∨ Q ∨ R) ∧ (¬R ∨ Q ∨ R) *) 

pprint (input_to_cnf "(P <-> Q) -> R")

(* (P ∨ Q ∨ R) ∧ (¬Q ∨ Q ∨ R) ∧ (P ∨ ¬P ∨ R) ∧ (¬Q ∨ ¬P ∨ R) *)
