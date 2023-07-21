module Calculus = Untyped.Named
open Calculus

module Map = Belt.Map.String // immutable string map

@unboxed
type rec closure =  Cl((name, env, tm))
and val = 
    | VVar(name)
    | VApp(val, val)
    | VLam(closure)
and env = Map.t<val>

let rec fresh = (env:env, x:name)=>switch x {
    | "_" => "_"
    | _ => switch env->Map.has(x) {
        | true => env->fresh(x++"'")
        | false => x
    }
}

@inline
let freshCl = (env:env) => (Cl(x, _, _) as cl:closure)=>{
    (env->fresh(x), cl)
}


let rec appCl = (Cl(x, env, t):closure)=>(u:val)=>
    env->Map.set(x, u)->eval(t)

and eval = (env:env, tm:tm)=> switch tm {
    | Var(x) => env->Map.getExn(x)
    | App(t, u) => switch (env->eval(t), env->eval(u)) {
        | (VLam(cl), u) => cl->appCl(u)
        | ( _ as t , u) => VApp(t, u)
    }
    | Lam(x, t) => VLam(Cl(x, env, t))
    | Let(x, t, u) => env->Map.set(x, env->eval(t))->eval(u)
}

let rec quote = (env:env, val:val)=> switch val {
    | VVar(x) => Var(x)
    | VApp(t, u) => App(env->quote(t), env->quote(u))
    | VLam(cl) => {
        let (x, cl) = env->freshCl(cl)
        Lam(x, env->Map.set(x, VVar("x"))->quote(cl->appCl(VVar(x))))
    }
}

let nf = (env:env, tm:tm)=>{
    let val = env->eval(tm)
    let tm = env->quote(val)
    tm
}

let test = (tm:tm)=>{
    let nf = Map.empty->nf(tm)
    Js.log3(tm->pp, "\n~>\n", nf->pp)
}

ex3->test