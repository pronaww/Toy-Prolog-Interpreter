let p2 = [Rule ((Symbol ("compare_cut",[Var("X")])), Subgoals([(Symbol ("data", [Var("X")] ) ) ]));
			Fact (Symbol ("compare_cut",[Const(String("last chip"))]));
		    Fact (Symbol ("data",[Const(String("pentium"))]));
			Fact (Symbol ("data",[Const(String("athlon"))]))];;

let q2 = (Symbol ("compare_cut",[Var "X"]));;

let p2 = [Rule ((Symbol ("compare_cut",[Var("X")])), Subgoals([(Symbol ("data", [Var("X")] ) ); CUT ]));
			Fact (Symbol ("compare_cut",[Const(String("last chip"))]));
		    Fact (Symbol ("data",[Const(String("pentium"))]));
			Fact (Symbol ("data",[Const(String("athlon"))]))];;

let p2 = [Rule ((Symbol ("compare_cut",[Var("X"); Var("Y")])), Subgoals([(Symbol ("data", [Var("X")] ) ); CUT; (Symbol ("data", [Var("Y")] ) ) ]));
			Fact (Symbol ("compare_cut",[Const(String("last chip"))]));
		    Fact (Symbol ("data",[Const(String("pentium"))]));
			Fact (Symbol ("data",[Const(String("athlon"))]))];;

let q2 = (Symbol ("compare_cut",[Var "X"; (Var "Y")]));;
