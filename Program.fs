open FSharpPlus

type Var = V of string

type Term =
    | Var of Var
    | Letrec of List<Binding> * Term
    | Abs of Var * Term
    | App of Term * Term
    | Constr of Constr * List<Term>
    | Match of Term * List<Clause>

and Binding = Bind of Var * Term

and Constr = string

and Clause = Clause of Pattern * Term

and Pattern = Pattern of Constr * List<Var>

let getBoundVariables bs =
    List.map (function Bind(v, _) -> v) bs


type Mode =
    | Ignore
    | Delay
    | Guard
    | Return
    | Dereference
    static member Max (x : Mode) y =
        if x < y
        then y
        else x
    member this.Compose(m2) =
        match (this, m2) with
            | (Ignore, _)      -> Ignore
            | (_, Ignore)      -> Ignore
            | (Delay, _)       -> Delay
            | (Dereference, _) -> Dereference
            | (_, Dereference) -> Dereference
            | (_, Delay)       -> Delay
            | (Guard, _)       -> Guard
            | (Return, Guard)  -> Guard
            | (Return, Return) -> Return

type Env = Env of Map<Var, Mode>
with
    static member empty = Env Map.empty
    member this.Insert x y =
        match this with
            | Env m -> Map.add x y m |> Env
    member this.Delete v =
        match this with
            | Env m -> Map.remove v m |> Env
    member this.Overlap env =
        match this, env with
            | Env m1, Env m2 -> Map.unionWith Mode.Max m1 m2 |> Env
    member this.Separate vs =
        match this with
            | Env m ->
                let (m1, m2) = Map.partition (fun v _ -> not (List.contains v vs)) m in
                (Env m1, Env m2)
    member this.Compose (m1 : Mode) =
        match this with
            | Env m -> Map.mapValues m1.Compose m |> Env
    member this.Lookup v =
        match this with
            | Env m -> Map.find v m
    member this.GuardedIfAny v =
        match this with
            | Env m ->
                match Map.tryFind v m with
                    | Some mode -> mode <= Guard
                    | None      -> true
    member this.Equal env2 =
        match this, env2 with
            | (Env m1, Env m2) ->
                let f v m =
                    match Map.tryFind v m2 with
                        | Some m' -> m = m'
                        | None    -> m = Ignore
                let g v m = Map.containsKey v m1 || m = Ignore
                Map.forall f m1 && Map.forall g m2

exception UnguardedUseException of Var * Var * Mode

let rec fixMap (m : Map<Var, Env * Env>) : Map<Var, Env * Env> =
    let f (env, Env recEnv) =
        let g (acc : Env) (v : Var) (mode : Mode) =
            acc.Overlap ((Map.find v m |> fst).Compose(mode))
        ( Map.fold g env recEnv
        , Env recEnv
        )
    let m' = Map.mapValues f m
    if Map.zip m m' |> Map.forall (fun _ ((x, _), (y, _)) -> x.Equal y)
    then m
    else fixMap m'

let rec typecheck (t : Term) (m : Mode) : Env =
    match t with
        | Var v     -> Env.empty.Insert v m
        | Abs(v, x) -> m.Compose Delay |> typecheck x |> fun env -> env.Delete v
        | App(x, y) ->
            let m' = m.Compose Dereference
            (typecheck x m').Overlap(typecheck y m')
        | Constr(c, xs) ->
            let f (acc : Env) x = acc.Overlap(typecheck x (m.Compose Guard))
            List.fold f Env.empty xs
        | Match(t, cs) ->
            let env1 = typecheck t (m.Compose Dereference)
            List.fold (fun (acc : Env) c -> acc.Overlap (typecheckClause c m)) env1 cs
        | Letrec(bs, x) ->
            let vm = typecheckBindings bs
            let vs = getBoundVariables bs

            let env = typecheck x m
            let (env1, env2) = env.Separate vs

            let f (acc : Env) (v : Var) (env : Env) =
                env.Compose(Mode.Max Guard (env2.Lookup v))
                |> acc.Overlap
            Map.fold f env1 vm

and typecheckClause (Clause(Pattern(_, vs), t)) m =
    List.fold (fun (acc : Env) v -> acc.Delete v) (typecheck t m) vs

and typecheckBindings bs =
    let vs = getBoundVariables bs
    let envs : List<Env> = List.map (function Bind(_, t) -> typecheck t Return) bs
    let f (v0, env : Env) =
        let check v = if env.GuardedIfAny v then () else raise (UnguardedUseException(v0, v, env.Lookup v))
        List.iter check vs
    let () = List.zip vs envs |> List.iter f
    let m0 : Map<Var, Env * Env> =
        List.map (fun (env : Env) -> env.Separate vs) envs
        |> List.zip vs
        |> Map.ofList
    Map.mapValues fst (fixMap m0)

let check t =
    try
        typecheck t Return
        |> printfn "%A"
    with
        | e -> printfn "%A" e

let var s = Var (V s)

open System

[<EntryPoint>]
let main argv =
    printfn "Hello World from F#!"
    check (Var (V "A"))
    check (Letrec([Bind(V "A", var "B")], var "A"))
    check (Letrec([Bind(V "A", var "A")], var "B"))
    0 // return an integer exit code
