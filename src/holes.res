@@warning("-27")
@unbox type metaVar = | MetaVar(int)


type name = string
type rec raw = // raw syntax
    | RVar(name)                // x
    | RLam(name, raw)           // \ x . t
    | RApp(raw, raw)            // t u
    | RU                        // U
    | RPi(name, raw, raw)       // (x : A) -> B
    | RLet(name, raw, raw, raw) // let x : A = t; u
    | RHole

@unbox type ix = | Ix(int)
@unbox type lvl = | Lvl(int)
type bd = | Bound | Defined
type 
rec ty = tm
and tm = 
    | Var(ix)
    | Lam(name, tm)
    | App(tm, tm)
    | U 
    | Pi(name, ty, ty)
    | Let(name, ty, tm, tm)
    | Meta(metaVar)
    | InsertedMeta(metaVar, List.t<bd>)

type 
rec env = List.t<Lazy.t<val>>
and spine = List.t<Lazy.t<val>>
and closure = | Closure(env, tm)
and vty = val
and val =
    | VFlex(metaVar, spine) // app meta ...
    | VRigid(lvl, spine)    // app var  ...
    | VLam(name, closure)
    | VPi(name, Lazy.t<vty>, closure)
    | VU
and metaEntry = | Solved(val) | Unsolved

let (nextMeta, lookupMeta) = {
    open Js.Array2
    let metas : array<metaEntry> = []
    (()=>{
        let meta = metas->length
        let _ = metas->push(Unsolved)
        meta
    }, 
    (MetaVar(m):metaVar)=>{
        metas->unsafe_get(m)
    })
}

let 
rec cApp = (Closure(env, t):closure, u:Lazy.t<val>)=>
    env->List.add(u)->eval(t)
and vApp = (t:val, u:Lazy.t<val>)=>switch t {
    | VLam(_, t) => t->cApp(u)
    | VFlex(m, sp) => VFlex(m, sp->List.add(u))
    | VRigid(x, sp) => VRigid(x, sp->List.add(u))
    | _ => Js.Exn.raiseError("impossible")
}
and vAppSp = (t:val, sp:spine)=>switch sp {
    | Nil => t
    | Cons(u, sp) => t->vAppSp(sp)->vApp(u)
}
and vMeta = (m:metaVar)=>switch lookupMeta(m) {
    | Solved(v) => v
    | Unsolved => VFlex(m, List.Nil)
}
and vAppBDs = (env:env, v:Lazy.t<val>, bds:List.t<bd>)=>switch (env, bds) {
    | (Nil, Nil) => v
    | (Cons(t, env), Cons(Bound, bds))=> {
        let lazy(f) = env->vAppBDs(v, bds)
        lazy(f->vApp(t))
    }
    | (Cons(t, env), Cons(Defined, bds))=> env->vAppBDs(v, bds)
    | _ => Js.Exn.raiseError("impossible")
}
and eval = (env:env, tm:tm)=>switch tm {
    | Var(Ix(x)) => {
        let lazy(val) = env->List.unsafe_get(x)
        val
    }
    | App(t, u) => env->eval(t)->vApp(lazy(env->eval(u)))
    | Lam(x, t) => VLam(x, Closure(env, t))
    | Pi(x, a, b) => VPi(x, lazy(env->eval(a)), Closure(env, b))
    | Let(_, _, t, u) => Cons(lazy(env->eval(t)), env)->eval(u)
    | U => VU
    | Meta(m) => vMeta(m)
    | InsertedMeta(m, bds) => {
        let lazy(val) = env->vAppBDs(lazy(vMeta(m)), bds)
        val
    }
}


@inline 
let lvl2Ix = (Lvl(l):lvl, Lvl(x):lvl)=>Ix(l-x-1)

let 
rec quoteSp = (l:lvl, t:tm, sp:spine)=>switch sp {
    | Nil => t
    | Cons(u, sp) => App(l->quoteSp(t, sp), l->quote(u))
}
and quote = (Lvl(l):lvl, t:Lazy.t<val>)=>switch t {
    | lazy(VFlex(m, sp)) => Lvl(l)->quoteSp(Meta(m), sp)
    | lazy(VRigid(x, sp)) => Lvl(l)->quoteSp(Var(lvl2Ix(Lvl(l), x)), sp)
    | lazy(VLam(x, t)) => Lam(x, Lvl(l+1)->quote(lazy(t->cApp(lazy(VRigid(Lvl(l), List.Nil))))))
    | lazy(VPi(x, a, b)) => Pi(x, Lvl(l)->quote(a), Lvl(l+1)->quote(lazy(b->cApp(lazy(VRigid(Lvl(l), List.Nil))))))
    | lazy(VU) => U
}

let nf = (env:env, t:tm) => 
    Lvl(env->List.length)->quote(lazy(env->eval(t)))


