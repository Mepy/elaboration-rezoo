module Named = {
    
type name = string
type rec tm = 
    | Var(name)         // x
    | Lam(name, tm)     // λ x . t
    | App(tm, tm)       // t u
    | Let(name, tm, tm) // let x = t in u

let rec pp = (tm:tm)=>switch tm {
    | Var(x) => x
    | Lam(x, t) => "λ "++x++" . "++t->pp
    | App(t, u) => {
        switch t {
        | Var(_) => t->pp
        | App(_, _) => t->pp
        | _ => "("++t->pp++")"
        }
        ++" "++
        switch u {
        | Var(_) => u->pp
        | _ => "("++u->pp++")"
        }
    }
    | Let(x, t, u) => "let "++x++" = "++t->pp++";\n"++u->pp
}

let ex1 = Lam("x", Var("x"))
let ex2 = App(Lam("x", Var("x")), Lam("x", Var("x")))
let ex3 = 
(   Let("five", Lam("s", Lam("z", App(Var("s"), App(Var("s"), App(Var("s"), App(Var("s"), App(Var("s"), Var("z"))))))))
,   Let("add", Lam("a", Lam("b", Lam("s", Lam("z", App(App(Var("a"), Var("s")), App(App(Var("b"), Var("s")), Var("z")))))))
,   Let("mul", Lam("a", Lam("b", Lam("s", Lam("z", App(App(Var("a"), App(Var("b"), Var("s"))), Var("z"))))))
,   Let("ten", App(App(Var("add"), Var("five")), Var("five")) 
,   Let("hundred", App(App(Var("mul"), Var("ten")), Var("ten"))
,   Let("thousand", App(App(Var("mul"), Var("ten")), Var("hundred"))
,   Var("thousand")
)))))))

}

module DeBruijn = {
    
@unboxed type ix = Ix(int)   // De Bruijn index
@unboxed type lvl = Lvl(int) // De Bruijn level

type rec tm = 
    | Var(ix)
    | Lam(tm)     // lam (x.t)
    | App(tm, tm)
    | Let(tm, tm) // let t (x.u)

let rec pp = (tm:tm)=>switch tm {
    | Var(Ix(x)) => x->Belt.Int.toString
    | Lam(t) => "λ "++t->pp
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
    | Let(t, u) => "let "++t->pp++";\n"++u->pp
}

let ex = 
(   Let(Lam(Lam(App(Var(Ix(1)), App(Var(Ix(1)), App(Var(Ix(1)), App(Var(Ix(1)), App(Var(Ix(1)), Var(Ix(0)))))))))
,   Let(Lam(Lam(Lam(Lam(App(App(Var(Ix(3)), Var(Ix(1))), App(App(Var(Ix(2)), Var(Ix(1))), Var(Ix(0))))))))
,   Let(Lam(Lam(Lam(Lam(App(App(Var(Ix(3)), App(Var(Ix(2)), Var(Ix(1)))), Var(Ix(0)))))))
,   Let(App(App(Var(Ix(1)), Var(Ix(2))), Var(Ix(2)))
,   Let(App(App(Var(Ix(1)), Var(Ix(0))), Var(Ix(0)))
,   Let(App(App(Var(Ix(2)), Var(Ix(1))), Var(Ix(0)))
,   Var(Ix(0))
)))))))

}