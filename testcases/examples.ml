Test case 1
Variables: X, Y
Constants: john, mary, andrew doe
Note: andrew doe is one constant i.e. It should be a 2-ary term having a function symbol and two child constant terms

Program:
    male(john).
    parent(john).
    father(X) :- male(X), parent(X).
    male(andrew doe).
    female(mary).

ProgramA6:-
let prgm = [Fact(Symbol("male",[Const(String("john"))]));
Fact(Symbol("parent",[Const(String("john"))]));
Rule(Symbol("father", [Var "X"]),Subgoals([(Symbol("male",[Var "X"]));(Symbol("parent", [Var "X"]))]));
Fact(Symbol("male",[Func("",[Const(String("andrew"));Const(String("joe"))])]));
Fact(Symbol("female",[Const(String("mary"))]))];;


 
Goal:
goal11 = [] (* no goal *)
let q1 = [];;
eval (prgm, prgm, [], q1, [], []);;

goal12 = male(john)
let q2 = [(Symbol("male",[Const(String "john")]))];;
eval (prgm, prgm, [], q2, [], []);;

goal13 = male(andrew)
let q3 = [(Symbol("male",[Const(String "andrew")]))];;
eval (prgm, prgm, [], q3, [], []);;

goal14 = male(X)
let q4 = [(Symbol("male",[Var "X"]))];;
eval (prgm, prgm, [], q4, [], []);;

goal15 = father(john) female(A)
let q5 = [(Symbol("father",[Const(String "john2")])); (Symbol("female", [Var "A"]))];;
eval (prgm, prgm, [], q5, [], []);;

goal16 = father(A) father(B)
let q6 = [(Symbol("father",[Var "A"])); (Symbol("father",[Var "B"]))];;
eval (prgm, prgm, [], q6, [], []);;


Test case 2
Variables: X, Y
Constants: a,b,c,d

Program:
    edge(a,b).
    edge(b,c).
    edge(c,d).
    edge(a,d).
    path(X,Y):- edge(X,Y).
    path(X,Y):- edge(X,Z),path(Z,Y).

Test case:
goal21 = path(a,c)
goal22 = edge(a,A)
goal23 = path(a,A)
goal24 = edge(A,B)
goal25 = path(A,B)
goal26 = path(A,B), cut
