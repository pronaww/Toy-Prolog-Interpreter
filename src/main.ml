open List;;

type exp = Int of int | Float of float | Symbolic_const of string | String of string | Bool of bool;;
type term = Var of string | Const of exp | Func of string * (term list);;
type atomic_formula = Symbol of string * term list | FAIL | CUT;;
type goal = Sequence of atomic_formula list;;
type head = atomic_formula;;
type body = Subgoals of atomic_formula list;;
type clause = Fact of head | Rule of head * body;;
type program = clause list;;

type return = false | true | Unification of (term * term) list | NEXT | Unifier of return list;;




let varshash = Hashtbl.create 123456;;

let filter x = if (Hashtbl.mem varshash x)=true then (true,()) else (false,(Hashtbl.add varshash x x));; 

(* vars' gets all the variables in the term if uses filter to filter out the variables alrady appeared in the term and not make duplicates*)
let rec vars' l t = match t with
	| Var(str) -> if (filter (Var(str)))=(false,()) then Var(str)::l else l
	| Const(a) -> l
	| Func(_, termList) -> (fold_left List.append [] (map (vars' []) termList))@l;;

(* vars gives the set of variables appearing in the well-formed term *)
let vars t = Hashtbl.clear varshash; vars' [] t;;

(*-------------------------------------------------------------------------------------------*)

(* find is function which takes list l of tuple ('a,'b) and element a and if element is present returns the corresponding 'b else return a itself *)
let rec find l a = match l with
		[] -> a
	| (x,y)::xs -> if x=a then y else find xs a;;

(* subst takes a term t and a substitution s as input, applies the (Unique Homomorphic Extension of) substitution s to t and returns the substituted term*)
let rec subst s t = match t with
		Var(a) -> find s (Var(a))
	| Const(a) -> Const(a)
	| Func(str,[]) -> Func(str,[])
	| Func((str),l) -> Func(str,(map (subst s) l));;

(* checkPresent' returns false if element is not present in list else it returns the corresponding 'b from list l *)
let rec checkPresent' a l = match l with
	[] -> false
| (x,_)::xs -> if(x=a) then true else checkPresent' a xs;;


exception NOT_UNIFIABLE;;

(* if t = f(t_1,...,t_k) and u = f(u_1,...,u_k) then fy applies the subst to get the composition of subst which is mgu here*)
let rec fy f l1 l2 (s, boo) = match (l1,l2) with
	  (x1::xs1, x2::xs2) -> fy f xs1 xs2 (f (subst s x1) (subst s x2) (s,true))
	| ([],[]) -> (s,true);;

let rec reverse l1 l =match l with
[] -> l1
| x::xs -> reverse (x::l1) xs;;


(* mgu' takes terms t and u and list l = [] and gives the most general unifier l *)
let rec mgu' t u (l, boo) = let boolXinL = checkPresent' t l and boolYinL = checkPresent' u l in
	match (t,u) with
	(Var(x),Var(y)) -> if x = y then (l,true) else if boolXinL=false && boolYinL=false then (((Var(x),Var(y))::l), boo)
								   else if boolXinL=false && boolYinL=true then (((Var(x),Var(y))::l), boo)
								   else if boolXinL=true && boolYinL=false then (((Var(y),Var(x))::l), boo)
								   else (l, false)
| ((Var(x),Func(str,[]))|(Func(str,[]),Var(x))) -> if boolYinL=false then (((Var(x),Func(str,[]))::l), boo)
									else if (List.mem (Var(x),Func(str,[])) l) then (l,boo)
									else (l, false)
| ((Var(x),Const(a))|(Const(a),Var(x))) -> if boolXinL=false then (((Var(x),Const(a))::l), boo)
									else if (List.mem (Var(x),Const(a)) l) then (l,boo)
									else (l, false)
| (Var(x),Func(str,termList)) -> if (List.mem t (vars u))=false && (checkPresent' (Var(x)) l)=false then (((Var(x),Func(str,termList))::l), boo)
							  else if (List.mem t (vars u))=false && (List.mem (Var(x),Func(str,termList)) l)=true then (l, boo)
							  else (l, false)

| (Func(str,termList),Var(x)) -> if (List.mem u (vars t))=false && (checkPresent' (Var(x)) l)=false then (((Var(x),Func(str,termList))::l), boo)
							  else if (List.mem u (vars t))=false && (List.mem (Var(x),Func(str,termList)) l)=true then (l, boo)
							  else (l, false)
| (Func((c1),[]),Func((c2),[])) -> if c1 = c2 then (l, boo) else (l, false)
| (Const(a), Const(b)) -> if a = b then (l,true) else (l, false)
| (Func(str, termList), Const(a))|(Const(a), Func(str, termList)) -> (l, false)
| (Func(str,termList1),Func(g,termList2)) -> if str=g && (length termList1)=(length termList2) then (fy mgu' termList1 termList2 (l,true)) else (l, false);;

(* mgu gives most general unifier *)
let mgu (l, boo) (t,u) = match (mgu' t u (l,boo)) with
	(l', true) -> (reverse [] l', true)
  | (l', false) -> (l, false);;




let rec tupform' l1 l2 l = match l1 with
	[] -> l
| x1::xs1 -> (match l2 with
				x2::xs2 -> tupform' xs1 xs2 (l@[(x1,x2)]));;
let tupform l1 l2 = tupform' l1 l2 [];;

let rec subtheadlist' t l l' = match l with
		[] -> l'
	| (Symbol(s,l2))::xs -> subtheadlist' t xs (l'@[Symbol(s, map (subst t) l2)])
	| (CUT::xs) -> subtheadlist' t xs (l'@[CUT])
	| (FAIL::xs) -> subtheadlist' t xs (l'@[FAIL]);;
let subtheadlist t l = (subtheadlist' t l []);;

let rec remove x l l' = match l with
		[] -> l'
	| (x1,x2)::xs -> if x1 = x then (l'@xs) else (remove x xs (l'@[(x1,x2)]));;

let rec foo786 l1 l2 = match l1 with
		[] -> l2
	| x::xs -> foo786 xs (remove x l2 []);;

let rec remVar l = match l with
	[] -> []
|	(Var(x), Var(y))::tl -> remVar tl
| c::tl ->  c::(remVar tl);;
(*
q is of type atomic_formula list.
*)

let table = Hashtbl.create 123456;;

let rec filterRealVar l = match l with
	[] -> []
| (Var(s), c)::xs -> if (Hashtbl.mem table (Var s)) = true then (Var(s), c)::(filterRealVar xs) else filterRealVar xs;;


let rec tToVar l = match l with
	[] -> ()
| x::xs -> (match x with
				Var(s) -> Hashtbl.add table (Var(s)) (Var(s));(tToVar xs)
			| _ -> tToVar xs);;

let rec extrVar l = match l with
	[] 	-> ()
| Symbol(str, l)::xs -> (tToVar l); extrVar xs
| CUT::xs -> extrVar xs
| FAIL::xs -> extrVar xs;;

let rec str l sfin = match l with
					[] -> sfin
				| x::xs -> (match x with
							Var a -> str xs (sfin^" "^a)
						| Const (String b) -> str xs (sfin^" "^b) );;

let stringTo s  sfin = match s with
	Symbol(s, l) -> (str l sfin	);;

(* let rec tPrint t = match t with
	[] -> ()
| (Var a, Const (String b))::xs -> Printf.printf "%s %s\n" a b; tPrint xs
| (Var a, Var b)::xs -> Printf.printf "%s %s\n" a b; tPrint xs;;
 *)
let rec nextPresent p' qHead = match p' with
	[] -> false
| Fact(Symbol(s, l))::xs -> nextPresent (tl p') qHead
| Rule(Symbol(s, l), b)::xs -> (match qHead with
									Symbol(s',l') -> if (s' = s && (length l) = (length l')) then true else nextPresent (tl p') qHead);;

let rec last l = match l with
		[x] -> x
	| x::xs -> last xs;;

let rec eval' (prgm, p,t,q,d, u) = match p with
	[] -> (match d with
					[] -> eval'(prgm, prgm, t, tl q, d, u)
				| (p',t'',q')::d' -> eval'(prgm, p', t'', q', d', u) )
| Fact(Symbol(s, l))::xs -> if (length q > 0) then (match (hd q) with
								Symbol(s', l') -> (if ((s = s') && (length l) = (length l')) then
																							(match (fold_left mgu (t,true) (tupform l' l)) with
																								(t', true) -> eval'(prgm, prgm, filterRealVar t' (* t' *), (subtheadlist t' (tl q)), (((tl p), t, q)::d), u )
																							  | (t', false) -> (length d);eval'(prgm, xs, t, q, d, u) )
													else eval'(prgm, xs, t, q, d, u)	)
								| FAIL -> (match d with
													[] -> u
												| [(p',t'',q')] -> if (nextPresent p' (hd q'))=true then eval'(prgm, p', t'', q', [], u) else eval'(prgm, p', t'', q', [], u@[false])
												| (p',t'',q')::d' -> eval'(prgm, p', t'', q', d', u) 	)					
								| CUT -> eval'(prgm, prgm, t, (tl q), [], u) )
							(* else if (length t) = 0 then [true] *)
							else (match d with
											[] -> if (length u) = 0 then [false] else u
										| (p',t'',q')::d' -> (match (last d) with
																	(p'',t''',q'') -> if (length q'') > 1 then 
																						if ((hd (tl q'')) = CUT) then
																							if (length (filterRealVar (remVar t)))=0 then
																								eval'(prgm, prgm, t, tl (tl q''), [], u@[true]@[NEXT])
																							else
																								eval'(prgm, prgm, t, tl (tl q''), [], u@[Unification (filterRealVar(remVar t))]@[NEXT])
																						else
																							if (length (filterRealVar (remVar t)))=0 then
																								eval'(prgm, p', t'', q', d', u@[true]@[NEXT])
																							else
																								eval'(prgm, p', t'', q', d', u@[Unification (filterRealVar(remVar t))]@[NEXT])
																					   else 
																					   		if (length (filterRealVar (remVar t)))=0 then
																								eval'(prgm, p', t'', q', d', u@[true]@[NEXT])
																							else
																								eval'(prgm, p', t'', q', d', u@[Unification (filterRealVar(remVar t))]@[NEXT])	) 	)

| Rule(Symbol(s, l),b)::xs -> if (length q > 0) then (match (hd q) with
								Symbol(s', l') -> (if s = s' && (length l) = (length l') then
																							(match (fold_left mgu (t,true) (tupform l l')) with
																								(t', true) -> (match b with
																								Subgoals af_list -> eval' (prgm, prgm, filterRealVar t' (* (foo786 l t') *), (subtheadlist t' af_list), (((tl p),t,q)::d), u) )
																							  | (t', false) -> eval'(prgm, xs, t, q, d, u) )
													else eval'(prgm, xs, t, q, d, u)	)
								| FAIL -> (match d with
													[] -> u
												| [(p',t'',q')] -> if (nextPresent p' (hd q'))=true then eval'(prgm, p', t'', q', [], u) else eval'(prgm, p', t'', q', [], u@[false])
												| (p',t'',q')::d' -> eval'(prgm, p', t'', q', d', u)  )
								| CUT -> eval'(prgm, prgm, t, (tl q), [], u)	)
							  (* else if (length t) = 0 then [true] *)
							else (match d with
											[] -> if (length u) = 0 then [false] else u
										| (p',t'',q')::d' -> (match (last d) with
																	(p'',t''',q'') -> if (length q'') > 1 then 
																						if ((hd (tl q'')) = CUT) then
																							if (length (filterRealVar (remVar t)))=0 then
																								eval'(prgm, prgm, t, tl (tl q''), [], u@[true]@[NEXT])
																							else
																								eval'(prgm, prgm, t, tl (tl q''), [], u@[Unification (filterRealVar(remVar t))]@[NEXT])
																						else
																							if (length (filterRealVar (remVar t)))=0 then
																								eval'(prgm, p', t'', q', d', u@[true]@[NEXT])
																							else
																								eval'(prgm, p', t'', q', d', u@[Unification (filterRealVar(remVar t))]@[NEXT])
																					   else 
																					   		if (length (filterRealVar (remVar t)))=0 then
																								eval'(prgm, p', t'', q', d', u@[true]@[NEXT])
																							else
																								eval'(prgm, p', t'', q', d', u@[Unification (filterRealVar(remVar t))]@[NEXT])	) 	);;		

let eval (prgm, p, t, q, d, u) = Hashtbl.clear table; extrVar (q); eval' (prgm, p, t, q, d, u);;
