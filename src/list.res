type rec t<'a> = 
    | Nil
    | Cons('a, t<'a>)

let empty = Nil
let add = (ls, elm) => Cons(elm, ls) 
let rec unsafe_get = (ls, i) =>switch ls {
    | Nil => Js.Exn.raiseRangeError("list index out of range")
    | Cons(hd, tl) => {
        if(i==0){ hd }
        else { tl->unsafe_get(i-1) }
    } 
}
let length = (ls:t<'a>)=>{
    let rec auto = (ls, i)=>switch ls {
    | Nil => i
    | Cons(_, tl) => auto(tl, i+1)
    }
    auto(ls, 0)
}