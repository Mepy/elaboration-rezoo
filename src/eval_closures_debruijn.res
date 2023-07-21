module Calculus = Untyped.DeBruijn
open Calculus
module Map = Belt.Map.String // immutable string map

@unboxed 
type rec closure = Closure((env, tm))
and env =
    | Nil
    | Define(env, val)
and val = 
    | VVar(lvl)
    | VApp(val, val)
    | VLam(closure)

let length = (env:env)=>{
    let rec go = (Lvl(acc):lvl, env:env)=>switch env {
        | Nil => Lvl(acc)
        | Define(env, _) => go(Lvl(acc+1), env)
    }
    go(Lvl(0), env)
}

@inline
let set = (env:env, u:val)=>Define(env, u)

let rec lookup = (env:env, Ix(x):ix)=>switch (env, x) {
    | (Define( _ , v), 0) => v
    | (Define(env, _), x) => env->lookup(Ix(x-1))
    | _ => Js.Exn.raiseRangeError("index out of range")
}

let rec cApp = (Closure(env, t):closure, u:val)=>
    env->set(u)->eval(t)

and eval = (env:env, tm:tm)=>switch tm {
    | Var(x) => env->lookup(x)
    | App(t, u) => switch (env->eval(t), env->eval(u)) {
        | (VLam(t), u) => cApp(t, u)
        | ( _ as t, u) => VApp(t, u)
    }
    | Lam(t) => VLam(Closure(env, t))
    | Let(t, u) => env->set(env->eval(t))->eval(u)
}

@inline
let lvl2Ix = (Lvl(l):lvl, Lvl(x):lvl)=>Ix(l-x-1)

let rec quote = (Lvl(l):lvl, val:val)=>switch val {
    | VVar(x) => Var(lvl2Ix(Lvl(l), x))
    | VApp(t, u) => App(Lvl(l)->quote(t), Lvl(l)->quote(u))
    | VLam(t) => Lam(Lvl(l+1)->quote(cApp(t, VVar(Lvl(l)))))
}

let nf = (env:env, tm:tm)=>{
    let val = env->eval(tm)
    let tm = env->length->quote(val)
    tm
}

let test = (tm:tm)=>{
    let nf = Nil->nf(tm)
    Js.log3(tm->pp, "\n~>\n", nf->pp)
}

ex->test