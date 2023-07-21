module Calculus = Untyped.Named
open Calculus

type rec val = 
    | VVar(name)
    | VApp(val, val)
    | VLam(name, val=>val)

module Map = Belt.Map.String // immutable string map
type env = Map.t<val>

let rec fresh = (env:env, x:name)=>switch x {
    | "_" => "_"
    | _ => switch env->Map.has(x) {
        | true => env->fresh(x++"'")
        | false => x
    }
}

let app = (t:val, u:val) => switch t {
    | VLam(_, t) => t(u)
    | _ => VApp(t, u)
}

let rec eval = (env:env, tm:tm)=>switch tm {
    | Var(x) => env->Map.getExn(x)
    | App(t, u) => env->eval(t)->app(env->eval(u))
    | Lam(x, t) => VLam(x, u=>env->Map.set(x, u)->eval(t))
    | Let(x, t, u) => env->Map.set(x, env->eval(t))->eval(u)
}

let rec quote = (env:env, val:val) => switch val {
    | VVar(x) => Var(x)
    | VApp(t, u) => App(env->quote(t), env->quote(u))
    | VLam(x, t) => {
        let x = env->fresh(x) // if env already has x as var, fresh it
        Lam(x, env->Map.set(x, VVar(x))->quote(t(VVar(x))))
    }
}

let nf = (env:env, tm:tm) => {
    let val = env->eval(tm)
    env->quote(val)
}

let test = (tm:tm)=>{
    let nf = Map.empty->nf(tm)
    Js.log3(tm->pp, "\n~>\n", nf->pp)
}




ex3->test