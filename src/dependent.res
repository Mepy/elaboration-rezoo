module Named = {

type name = string

type 
rec ty  = tm
and raw = tm
and tm  = 
    | Var(name)             // x
    | Lam(name, tm)         // λ x . t
    | App(tm, tm)           // t u
    | U                     // U
    | Pi(name, ty, ty)      // (x : A) -> B
    | Let(name, ty, tm, tm) // let x : A = t; u

let rec pp = (tm:tm)=>switch tm {
    | U => "U"
    | Var(x) => x
    | Lam(x, t) => "λ "++x++" . "++t->pp
    | App(t, u) => {
        switch t {
        | Var(_) | App(_, _) => t->pp
        | _ => "("++t->pp++")"
        }
        ++" "++
        switch u {
        | Var(_) => u->pp
        | _ => "("++u->pp++")"
        }
    }
    | Pi(x, a, b) => {
        let ppa = switch a {
        | Pi(_, _, _) => "("++a->pp++")"
        | _ => a->pp
        }
        let ppb = switch b {
        | Var(_) | Pi(_, _, _) => b->pp
        | _ => "("++b->pp++")"
        }
        if(x=="_"){ ppa++" -> "++ppb }
        else{ "( "++x++" : "++ppa++" ) -> "++ppb }
    }
    | Let(x, a, t, u) => "let "++x++" : "++a->pp++" = "++t->pp++";\n"++u->pp
}

@inline let arr = (a, b)=>Pi("_", a, b)

let ex0 = 
(   Let("id", Pi("A", U, arr(Var("A"), Var("A"))), Lam("A", Lam("x", Var("x")))
,   Let("foo", U, U
,   Let("bar", U, App(Var("id"), Var("id"))
,   Var("id")
))))

let ex1 = 
(   Let("id", Pi("A", U, arr(Var("A"), Var("A"))), 
        Lam("A", Lam("x", Var("x")))
,   Let("const", Pi("A", U, Pi("B", U, arr(Var("A"), arr(Var("B"), Var("A"))))),
        Lam("A", Lam("B", Lam("x", Lam("y", Var("x")))))
,   App(App(Var("id"), Pi("A", U, Pi("B", U, arr(Var("A"), arr(Var("B"), Var("A")))))), 
        Var("const"))
)))

let ex2 = 
(   Let("Nat", U, Pi("N", U, arr(arr(Var("N"), Var("N")), arr(Var("N"), Var("N"))))
,   Let("five", Var("Nat"), Lam("N", Lam("s", Lam("z", App(Var("s"), App(Var("s"), App(Var("s"), App(Var("s"), App(Var("s"), Var("z")))))))))
,   Let("add", arr(Var("Nat"), arr(Var("Nat"), Var("Nat"))), Lam("a", Lam("b", Lam("N", Lam("s", Lam("z", App(App(App(Var("a"), Var("N")), Var("s")), App(App(App(Var("b"), Var("N")), Var("s")), Var("z"))))))))
,   Let("mul", arr(Var("Nat"), arr(Var("Nat"), Var("Nat"))), Lam("a", Lam("b", Lam("N", Lam("s", Lam("z", App(App(App(Var("a"), Var("N")), App(App(Var("b"), Var("N")), Var("s"))), Var("z")))))))
,   Let("ten", Var("Nat"), App(App(Var("add"), Var("five")), Var("five")) 
,   Let("hundred", Var("Nat"), App(App(Var("mul"), Var("ten")), Var("ten"))
,   Let("thousand", Var("Nat"), App(App(Var("mul"), Var("ten")), Var("hundred"))
,   Var("thousand")
))))))))

}

module DeBruijn = {

}