@@warning("-27")
module DeBruijn = Dependent.DeBruijn
module Named = Dependent.Named
open DeBruijn
module List = Belt.List
module Map = Belt.Map.String


// normalize by evaluation
type 
rec closure = Closure(env, tm) 
and env = List.t<val>
and vty = val
and val = 
    | VVar(lvl)
    | VApp(val, val)
    | VLam(name, closure)
    | VPi(name, vty, closure)
    | VU

@inline
let 
rec cApp = (Closure(env, t):closure, u:val)=>
    env->List.add(u)->eval(t)

and eval = (env:env, tm:tm)=>switch tm {
    | Var(Ix(x)) => env->List.getExn(x)
    | App(t, u) => switch (env->eval(t), env->eval(u)) {
        | (VLam(_, t), u) => cApp(t, u)
        | (t         , u) => VApp(t, u)
    }
    | Lam(x, t) => VLam(x, Closure(env, t))
    | Pi(x, a, b) => VPi(x, env->eval(a), Closure(env, b))
    | Let(x, _, t, u) => env->List.add(env->eval(t))->eval(u)
    | U => VU
}

@inline 
let lvl2Ix = (Lvl(l):lvl, Lvl(x):lvl)=>Ix(l-x-1)

let rec quote = (Lvl(l):lvl, val:val)=>switch val {
    | VVar(x) => Var(lvl2Ix(Lvl(l), x))
    | VApp(t, u) => App(Lvl(l)->quote(t), Lvl(l)->quote(u))
    | VLam(x, t) => Lam(x, Lvl(l+1)->quote(cApp(t, VVar(Lvl(l)))))
    | VPi(x, a, b) => Pi(x, Lvl(l)->quote(a), Lvl(l+1)->quote(cApp(b, VVar(Lvl(l)))) )
    | VU => U
}

let nf = (env:env, t:tm)=>{
    let val = env->eval(t)
    let tm = Lvl(env->List.length)->quote(val)
    tm
}

// Beta-eta conversion checking. Precondition: both values have the same type.
let rec conv = (Lvl(l):lvl, t:val, u:val)=>switch (t, u) {
    | (VU, VU) => true
    | (VPi(_, a, b), VPi(_, a', b')) => {
        Lvl(l)->conv(a, a') &&
        Lvl(l+1)->conv(
            b ->cApp(VVar(Lvl(l)))
        ,   b'->cApp(VVar(Lvl(l))))
    }
    | (VLam(_, t), VLam(_, t')) => 
        Lvl(l+1)->conv(
            t ->cApp(VVar(Lvl(l)))
        ,   t'->cApp(VVar(Lvl(l))))
    // eta rule for Lam
    | (VLam(_, t), u) =>
        Lvl(l+1)->conv(
            cApp(t, VVar(Lvl(l)))
        ,   VApp(u, VVar(Lvl(l))))
    | (u, VLam(_, t)) =>
        Lvl(l+1)->conv(
            VApp(u, VVar(Lvl(l)))
        ,   cApp(t, VVar(Lvl(l))))
    | (VVar(Lvl(x)), VVar(Lvl(x'))) => x==x' 
    | (VApp(t, u), VApp(t', u')) => 
        Lvl(l)->conv(t, t') &&
        Lvl(l)->conv(u, u')
    | _ => false
}

// elaboration
type types = List.t<(name, vty)>
type cxt = {env:env, types:types, lvl:lvl} // unzip due to performance and convenience
let empty : cxt = {env:List.make(0, VU), types:List.make(0, ("_", VU)), lvl:Lvl(0)}

@inline 
let bind = ({env, types, lvl:Lvl(l)}:cxt, x:name, a:vty)=>
    {env:env->List.add(VVar(Lvl(l))), types:types->List.add((x, a)), lvl:Lvl(l+1)}
@inline 
let define = ({env, types, lvl:Lvl(l)}:cxt, x:name, t:val, a:vty)=>
    {env:env->List.add(t), types:types->List.add((x, a)), lvl:Lvl(l+1)}

// check : cxt-> Named.tm -> vty -> DeBruijn.tm
let rec check = (cxt:cxt, t:Named.tm, a:vty)=>switch (t, a) {
    | (Named.Lam(x, t), VPi(x', a, b)) => 
        Lam(x, cxt->bind(x, a)->check(t, b->cApp(VVar(cxt.lvl))))
    | (Named.Let(x, a, t, u), a') => {
        let a = cxt->check(a, VU) 
        let va = cxt.env->eval(a)
        let t = cxt->check(t, va)
        let vt = cxt.env->eval(t)
        let u = cxt->define(x, vt, va)->check(u, a')
        Let(x, a, t, u)
    }
    | _ => {
        let (t, tty) = cxt->infer(t)
        if(cxt.lvl->conv(tty, a)==false)
        {
            Js.Exn.raiseTypeError("type mismatch")
        }
        else { t }
    }
}
// infer : cxt-> Named.tm -> (DeBruijn.tm, vty)
and infer = (cxt:cxt, t:Named.tm)=>switch t {
    | Named.Var(x) => 
        let rec find = (types, Ix(i))=>switch (types->List.head, types->List.tail) {
            | (Some((x', a)), Some(types)) => 
                if x==x' { (Var(Ix(i)), a) }
                else { types->find(Ix(i+1)) }
            | (_, None) | (None, _) => Js.Exn.raiseReferenceError("variable out of scope: " ++ x)
        }
        cxt.types->find(Ix(0))
    | Named.U => (U, VU)
    | Named.App(t, u) =>
        let (t, tty) = cxt->infer(t)
        switch tty {
        | VPi(_, a, b) => {
            let u = cxt->check(u, a)
            let vu = cxt.env->eval(u)
            (App(t, u), b->cApp(vu))
        }
        | _ => Js.Exn.raiseTypeError("Expected a function type")
        }
    | Named.Lam(_, _) => Js.Exn.raiseTypeError("Can't infer type for lambda expresion "++t->Named.pp)
    | Named.Pi(x, a, b) => {
        let a = cxt->check(a, VU)
        let va = cxt.env->eval(a)
        let b = cxt->bind(x, va)->check(b, VU)
        (Pi(x, a, b), VU)
    }
    | Named.Let(x, a, t, u) => {
        let a = cxt->check(a, VU)
        let va = cxt.env->eval(a)
        let t = cxt->check(t, va)
        let vt = cxt.env->eval(t)
        let (u, uty) = cxt->define(x, vt, va)->infer(u)
        (Let(x, a, t, u), uty)
    }
}

let rec fresh = (types:types, x:name)=>
    if(types->List.some(((x', _))=>x==x'))
    { types->fresh(x++"'") } else { x }

let rec give = (cxt:cxt, tm:tm)=>switch tm {
    | Var(Ix(x)) => {
        let (name, _) = cxt.types->List.getExn(x)
        Named.Var(name)
    }
    | Lam(x, tm) => Named.Lam(x, 
        cxt->bind(x, VU)->give(tm))
        // VU will never be accessed
        
    | App(t, u) => Named.App(
        cxt->give(t), 
        cxt->give(u))
    | U => Named.U
    | Pi(x, a, b) => Named.Pi(x, 
        cxt->give(a), 
        cxt->bind(x, VU)->give(b))
    | Let(x, a, t, u) => Named.Let(x, 
        cxt->give(a), 
        cxt->give(t),
        cxt->bind(x, VU)->give(u))
}


let test = (t:Named.tm)=>{
    try {
        let (tm, ty) = empty->infer(t)
        let ty = empty.lvl->quote(ty)
        
        let nf = empty.env->nf(tm)
        
        let named_ty = empty->give(ty)
        let named_nf = empty->give(nf)
        Js.log(t->Named.pp++"\n ~> \n"++named_nf->Named.pp++"\n : \n"++named_ty->Named.pp)
    } catch
    {
    | Js.Exn.Error(error) => Js.log(error)
    }
}

{ open Named

ex0->test
ex1->test
ex2->test

}
