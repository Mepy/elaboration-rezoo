@@warning("-27")

module Calculus = Dependent.Named
open Calculus

type rec val =
    | VVar(name)
    | VApp(val, val)
    | VLam(name, (val=>val))
    | VPi(name, val, (val=>val))
    | VU

module Map = Belt.Map.String // immutable string map
type env = Map.t<val>


let rec fresh = (env:env, x:name)=>switch x {
    | "_" => "_"
    | _ => switch env->Map.has(x) {
        | true => env->fresh(x++"'")
        | false => x
    }
}

let rec eval = (env:env, tm:tm)=>switch tm {
    | Var(x) => env->Map.getExn(x)
    | App(t, u) => switch (env->eval(t), env->eval(u)) {
        | (VLam(_, t), u) => t(u)
        | (t         , u) => VApp(t, u)
    }
    | Lam(x, t) => VLam(x, u=>env->Map.set(x, u)->eval(t))
    | Pi(x, a, b) => VPi(x, env->eval(a), u=>env->Map.set(x, u)->eval(b))
    | Let(x, _, t, u) => env->Map.set(x, env->eval(t))->eval(u)
    | U => VU
}

let rec quote = (env:env, val:val)=>switch val {
    | VVar(x) => Var(x)
    | VApp(t, u) => App(env->quote(t), env->quote(u))
    | VLam(x, t) => {
        let x = env->fresh(x)
        Lam(x, env->Map.set(x, VVar(x))->quote(t(VVar(x))))
    }
    | VPi(x, a, b) => {
        let x = env->fresh(x)
        Pi(x, env->quote(a), env->Map.set(x, VVar(x))->quote(b(VVar(x))))
    }
    | VU => U
}

let nf = (env:env, tm:tm)=>{
    let val = env->eval(tm)
    let tm = env->quote(val)
    tm
}

// beta-eta conversion checking
let rec conv = (env:env, t:val, u:val)=>switch (t, u) {
    | (VU, VU) => true
    | (VPi(x, a, b), VPi(x', a', b')) => {
        let x = env->fresh(x) // if env already has x as var, fresh it
        env->conv(a, a') &&
        env->Map.set(x, VVar(x))->conv(b(VVar(x)), b'(VVar(x)))
    }
    | (VLam(x, t), VLam(x', t')) => {
        let x = env->fresh(x) 
        env->Map.set(x, VVar(x))->conv(t(VVar(x)), t'(VVar(x)))
    } 
    // checking eta conversion for Lam
    | (VLam(x, t), u) => {
        let x = env->fresh(x) 
        env->Map.set(x, VVar(x))->conv(t(VVar(x)), VApp(u, VVar(x)))
    }
    | (u, VLam(x, t)) => {
        let x = env->fresh(x) 
        env->Map.set(x, VVar(x))->conv(VApp(u, VVar(x)), (t(VVar(x))))
    }
    | (VVar(x), VVar(x')) => x == x'
    | (VApp(t, u), VApp(t', u')) =>
        env->conv(t, t') &&
        env->conv(u, u') 
    | _ => false
}
type vty = val
type cxt = Map.t<vty> // typing context

let rec check = (env:env, cxt:cxt, t:raw, a:vty)=>switch (t, a) {
    | (Lam(x, t), VPi(x', a, b)) => {
        let x' = env->fresh(x')
        check(
            env->Map.set(x, VVar(x')),
            cxt->Map.set(x, a), t, b(VVar(x'))
        )
    }
    | (Let(x, a', t', u), _) => {
        check(env, cxt, a', VU)
        let a' = env->eval(a')
        check(env, cxt, t', a')
        check(
            env->Map.set(x, env->eval(t')),
            cxt->Map.set(x, a'), u, a
        )
    }
    | _ => { 
        let tty = infer(env, cxt, t)
        if(env->conv(tty, a)==false)
        {
            Js.Exn.raiseTypeError("type mismatch")
        }
    }
        
}
and infer = (env:env, cxt:cxt, t:raw) => switch t {
    | Var(x) => switch cxt->Map.get(x) {
        | Some(a) => a
        | None => Js.Exn.raiseReferenceError("Name not in scope: "++x)
    }
    | U => VU
    | App(t, u) => {
        let tty = infer(env, cxt, t)
        switch tty {
        | VPi(_, a, b) => {
            check(env, cxt, u, a)
            (b(env->eval(u)))
        }
        | _ => Js.Exn.raiseTypeError("Expected a function type, instead inferred:")
        }
    }
    | Lam(_, _) => Js.Exn.raiseTypeError("Can't infer type for lambda expresion "++t->pp)
    | Pi(x, a, b) => {
        check(env, cxt, a, VU)
        check(
            env->Map.set(x, VVar(x)),
            cxt->Map.set(x, env->eval(a)), b, VU
        )
        VU
    }
    | Let(x, a, t, u) => {
        check(env, cxt, a, VU)
        let a = env->eval(a)
        check(env, cxt, t, a)
        infer(
            env->Map.set(x, env->eval(t)),
            cxt->Map.set(x, a), u
        )
    }
}

let test = (tm:tm)=>{
    try {
        let ty = infer(Map.empty, Map.empty, tm)
        let ty = Map.empty->quote(ty)
        let nf = Map.empty->nf(tm)
        Js.log(tm->pp++"\n ~> \n"++nf->pp++"\n : \n"++ty->pp)
    } catch
    {
    | Js.Exn.Error(error) => Js.log(error)
    }

}

ex0->test

ex1->test

ex2->test