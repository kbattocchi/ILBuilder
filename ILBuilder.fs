module ILBuilder

open System
open System.Reflection
open System.Reflection.Emit
open System.Collections.Generic
open Samples.FSharp.ProvidedTypes

// Marker phantom types
type Ok = class end
type Nok = class end
/// <summary>Represents a value of type <typeparamref name="'a"/></summary>
type V<'a> = class end
/// <summary>Represents a managed referece to a location of type <typeparamref name="'a"/></summary>
type B<'a> = class end

/// <summary>Represents a method that can be called with stack state <typeparamref name="'pre"/>, resulting in stack state <typeparamref name="'post"/></summary>
type M<'pre,'post> = M of System.Reflection.MethodInfo

let internal unM (M m) = m

type internal InstrState = { ilg : ILGenerator; labelMap : Dictionary<int,Label>; localMap : Dictionary<int,LocalBuilder>; meth : System.Reflection.MethodInfo }
type Instrs<'s,'r,'dne> = 
    internal Instrs of (InstrState -> unit)

let internal ensureLabel s i =
    let d = s.labelMap
    if not (d.ContainsKey i) then 
        d.[i] <- s.ilg.DefineLabel()
    d.[i]

let internal ensureLocal<'t> s i =
    let d = s.localMap
    if not (d.ContainsKey i) then 
        d.[i] <- s.ilg.DeclareLocal(typeof<'t>)
    d.[i]


type Label<'s> = internal Label of int
type Local<'t> = internal Local of int

let internal unlabel (Label i) = i
let internal unlocal (Local i) = i

let internal cntr = ref 0

let makeLabel() = 
    incr cntr
    Label !cntr
            
let declareLocal() =
    incr cntr
    Local !cntr

let internal (+>) f g x = 
    f x;
    g x

type MethodGeneralization =
    static member Generalize(M m : M<unit,unit>) : M<'b, 'b> = M m
    // Note that this is not quite right...
    // We want M<unit,#'a*unit> -> M<'b,'a*'b> instead iff 'a is a reference type (but the F# type system doesn't allow that)
    static member Generalize(M m : M<unit,'a*unit>) : M<'b,'a*'b> = M m
    // Likewise, we want M<'a*unit,unit> -> M<#'a*'b,'b> instead iff 'a is a reference type
    static member Generalize(M m : M<'a*unit,unit>) : M<'a * 'b, 'b> = M m
    static member Generalize(M m : M<'a*unit,'b*unit>) : M<'a * 'c, 'b * 'c> = M m
    static member Generalize(M m : M<'a*('b*unit),unit>) : M<'a * ('b * 'c), 'c> = M m
    static member Generalize(M m : M<'a*('b*unit),'c*unit>) : M<'a * ('b * 'd), 'c * 'd> = M m
    static member Generalize(M m : M<'a*('b*('c*unit)),unit>) : M<'a * ('b * ('c * 'd)), 'd> = M m
    static member Generalize(M m : M<'a*('b*('c*unit)),'d*unit>) : M<'a * ('b * ('c * 'e)), 'd * 'e> = M m

let inline internal generalizeHelper m = ((^a or ^b or ^c) : (static member Generalize : ^b -> ^c)(m))
let inline adjustToStack m = generalizeHelper< ^b,MethodGeneralization,^c> m

[<CompilerServices.TypeProvider>]
type MethodProvider() =
    inherit TypeProviderForNamespaces()

    let prettyPrintSig (m:MethodInfo) verbose = 
        let prettyPrintTy = function
        | ty when ty = typeof<int> -> "int"
        | ty when ty = typeof<string> -> "string"
        | ty when ty = typeof<bool> -> "bool"
        | ty when ty = typeof<obj> -> "obj"
        | ty when ty = typeof<System.Void> -> "unit"
        | ty -> ty.FullName
        
        let ps = m.GetParameters() 
        let prettyPrintParm (p:ParameterInfo) =
            if verbose then
                sprintf " %s:%s " p.Name (prettyPrintTy p.ParameterType)
            else
                prettyPrintTy p.ParameterType
        sprintf "%s : %s->%s" m.Name (if ps.Length > 0 then System.String.Join("*", ps |> Array.map prettyPrintParm) else "unit") (prettyPrintTy m.ReturnType)

    let root = ProvidedTypeDefinition(typeof<MethodProvider>.Assembly, "MethodProvider", "Methods", None)
    do
        let canHandle (t:System.Type) =
            if List.exists ((=) t.FullName) ["System.ArgIterator"; "System.RuntimeArgumentHandle"; "System.TypedReference"] then
                false
            elif t.IsPointer || (t.IsByRef && t.GetElementType().IsPointer) then
                false
            else
                true
        let wrap (t:System.Type) =
            if t.IsByRef then 
                typedefof<B<_>>.MakeGenericType(t.GetElementType())
            else
                typedefof<V<_>>.MakeGenericType(t)
        let uniquify (m:System.Reflection.MethodInfo seq) =
            m |> Seq.groupBy (fun mi -> mi.Name)
            |> Seq.collect (fun (n, ms) -> ms |> Seq.map (fun m -> (if (Seq.length ms <= 1) then n else prettyPrintSig m false), prettyPrintSig m true, m))
        let parts = 
            seq {
             for ty in typeof<int>.Assembly.ExportedTypes do
             if ty <> typeof<System.Void> && not ty.IsGenericType && canHandle ty then
                 for nm,sg,m in uniquify (ty.GetMethods()) do
                 // TODO: what about generic methods?
                 if not m.IsGenericMethod && (m.GetParameters() |> Array.forall (fun p -> canHandle p.ParameterType)) && canHandle m.ReturnType then
                     let nsFrags = ty.Namespace.Split('.') |> List.ofArray
                     yield nsFrags @ [ty.Name], fun () -> 
                        let inputs = 
                            [for p in m.GetParameters() -> 
                                wrap p.ParameterType]
                        let inputTy = 
                            if m.IsStatic then
                                inputs
                            else
                                (if ty.IsValueType && ty.FullName <> "System.ArgIterator" then typedefof<B<_>> else typedefof<V<_>>).MakeGenericType(ty) :: inputs
                            |> List.fold (fun t t1 -> typedefof<_*_>.MakeGenericType(t1, t)) typeof<unit>
                        let returnTy =
                            if m.ReturnType = typeof<System.Void> then typeof<unit>
                            else typedefof<_*_>.MakeGenericType(wrap m.ReturnType, typeof<unit>)
                        let retTy = typedefof<M<_,_>>.MakeGenericType(inputTy,returnTy)
                        let [|uc|] = Reflection.FSharpType.GetUnionCases(retTy)
                        let tok = m.MetadataToken
                        let p = ProvidedProperty(nm, retTy, IsStatic=true, GetterCode = fun [] -> Quotations.Expr.NewUnionCase(uc, [ <@ typeof<int>.Assembly.ManifestModule.ResolveMethod tok :?> System.Reflection.MethodInfo @>]))
                        p.AddXmlDoc(sg)
                        p}
        let rec createTypes (t:ProvidedTypeDefinition) l =
            t.AddMembersDelayed(fun () -> 
                [for mi in l |> Seq.choose (function ([],m) -> Some(m()) | _ -> None) do
                    yield mi :> System.Reflection.MemberInfo
                 let groups =
                     l 
                     |> Seq.choose (function (h::r,m) -> Some(h,(r,m)) | _ -> None)
                     |> Seq.groupBy fst
                     |> Seq.map (fun (i,g) -> i, Seq.map snd g)
                 for (nm, items) in groups do
                     let t' = ProvidedTypeDefinition(nm, None)
                     createTypes t' items
                     yield t' :> System.Reflection.MemberInfo])
                        
        createTypes root parts
        base.AddNamespace("MethodProvider", [root])

type IlBuilder() =
    [<CustomOperation("ldc_i4", MaintainsVariableSpace=true)>]
    member __.Ldc_I4((Instrs f : Instrs<'a,'r,_>, j), [<ProjectionParameter>]h:_->int) : Instrs<V<int> * 'a,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Ldc_I4, h j)), j
    [<CustomOperation("ldstr", MaintainsVariableSpace=true)>]
    member __.Ldstr((Instrs f : Instrs<'a,'r,_>, j), [<ProjectionParameter>]h:_->string) : Instrs<V<string> * 'a,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Ldstr, h j)), j
    [<CustomOperation("pop", MaintainsVariableSpace=true)>]
    member __.Pop((Instrs f : Instrs<_*'a,'r,_>, j)) : Instrs<'a,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Pop)), j
    [<CustomOperation("dup", MaintainsVariableSpace=true)>]
    member __.Dup((Instrs f : Instrs<'t*'a,'r,_>, j)) : Instrs<'t*('t*'a),'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Dup)), j
    [<CustomOperation("nop", MaintainsVariableSpace=true)>]
    member __.Nop((Instrs f : Instrs<'a,'r,_>, j)) : Instrs<'a,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Nop)), j
    [<CustomOperation("add", MaintainsVariableSpace=true)>]
    member __.Add((Instrs f : Instrs<V<int>*(V<int>*'a),'r,_>, j)) : Instrs<V<int>*'a,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Add)), j
    [<CustomOperation("sub", MaintainsVariableSpace=true)>]
    member __.Sub((Instrs f : Instrs<V<int>*(V<int>*'a),'r,_>, j)) : Instrs<V<int>*'a,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Sub)), j
    [<CustomOperation("mul", MaintainsVariableSpace=true)>]
    member __.Mul((Instrs f : Instrs<V<int>*(V<int>*'a),'r,_>, j)) : Instrs<V<int>*'a,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Mul)), j
    [<CustomOperation("div", MaintainsVariableSpace=true)>]
    member __.Div((Instrs f : Instrs<V<int>*(V<int>*'a),'r,_>, j)) : Instrs<V<int>*'a,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Div)), j
    [<CustomOperation("rem", MaintainsVariableSpace=true)>]
    member __.Rem((Instrs f : Instrs<V<int>*(V<int>*'a),'r,_>, j)) : Instrs<V<int>*'a,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Rem)), j
    [<CustomOperation("ret", MaintainsVariableSpace=true)>]
    member __.Ret((Instrs f : Instrs<'r,'r,_>, j)) : Instrs<'a,'r,_> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Ret)), j
    [<CustomOperation("br", MaintainsVariableSpace=true)>]
    member __.Br((Instrs f : Instrs<'s,'r,_>, j), [<ProjectionParameter>]h:_->Label<'s>) : Instrs<_,'r,Ok> * _ =
        Instrs(f +> fun s-> s.ilg.Emit(OpCodes.Br, h j |> unlabel |> ensureLabel s)), j
    [<CustomOperation("beq", MaintainsVariableSpace=true)>]
    member __.Beq((Instrs f : Instrs<V<int>*(V<int>*'s),'r,_>, j), [<ProjectionParameter>]h:_->Label<'s>) : Instrs<'s,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Beq, h j |> unlabel |> ensureLabel s)), j
    [<CustomOperation("bgt", MaintainsVariableSpace=true)>]
    member __.Bgt((Instrs f : Instrs<V<int>*(V<int>*'s),'r,_>, j), [<ProjectionParameter>]h:_->Label<'s>) : Instrs<'s,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Bgt, h j |> unlabel |> ensureLabel s)), j
    [<CustomOperation("bge", MaintainsVariableSpace=true)>]
    member __.Bge((Instrs f : Instrs<V<int>*(V<int>*'s),'r,_>, j), [<ProjectionParameter>]h:_->Label<'s>) : Instrs<'s,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Bge, h j |> unlabel |> ensureLabel s)), j
    [<CustomOperation("blt", MaintainsVariableSpace=true)>]
    member __.Blt((Instrs f : Instrs<V<int>*(V<int>*'s),'r,_>, j), [<ProjectionParameter>]h:_->Label<'s>) : Instrs<'s,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Blt, h j |> unlabel |> ensureLabel s)), j
    [<CustomOperation("ble", MaintainsVariableSpace=true)>]
    member __.Ble((Instrs f : Instrs<V<int>*(V<int>*'s),'r,_>, j), [<ProjectionParameter>]h:_->Label<'s>) : Instrs<'s,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Ble, h j |> unlabel |> ensureLabel s)), j
    /// Pseudo-opcode for marking a label
    [<CustomOperation("markLabel", MaintainsVariableSpace=true)>]
    member __.MarkLabel((Instrs f : Instrs<'s,'r,'d>, j), [<ProjectionParameter>]h:_->Label<'s>) : Instrs<'s,'r,'d> * _ =
        Instrs(f +> fun s -> s.ilg.MarkLabel(h j |> unlabel |> ensureLabel s)), j
    [<CustomOperation("ldloc", MaintainsVariableSpace=true)>]
    member __.Ldloc((Instrs f : Instrs<'s,'r,_>, j), [<ProjectionParameter>]h:_->Local<'a>) : Instrs<V<'a>*'s,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Ldloc, h j |> unlocal |> ensureLocal<'a> s)), j
    [<CustomOperation("ldloca", MaintainsVariableSpace=true)>]
    member __.Ldloca((Instrs f : Instrs<'s,'r,_>, j), [<ProjectionParameter>]h:_->Local<'a>) : Instrs<B<'a>*'s,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Ldloca, h j |> unlocal |> ensureLocal<'a> s)), j
    [<CustomOperation("stloc", MaintainsVariableSpace=true)>]
    member __.Stloc((Instrs f : Instrs<V<'a>*'s,'r,_>, j), [<ProjectionParameter>]h:_->Local<'a>) : Instrs<'s,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Stloc, h j |> unlocal |> ensureLocal<'a> s)), j
    [<CustomOperation("box", MaintainsVariableSpace=true)>]
    member __.Box((Instrs f : Instrs<V<'a>*'s,'r,_>, j)) : Instrs<V<obj>*'s,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Box, typeof<'a>)), j
    [<CustomOperation("call", MaintainsVariableSpace=true)>]
    member __.Call((Instrs f : Instrs<'pre,'r,_>, j), [<ProjectionParameter>]h:_->M<'pre,'post>) : Instrs<'post,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Call, h j |> unM)), j
    [<CustomOperation("callvirt", MaintainsVariableSpace=true)>]
    member __.CallVirt((Instrs f : Instrs<'pre,'r,_>, j), [<ProjectionParameter>]h:_->M<'pre,'post>) : Instrs<'post,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Call, h j |> unM)), j
    member __.Yield(x) : Instrs<unit,'r,Nok> * _ = Instrs ignore, x
    member __.Run((Instrs f : Instrs<V<'a>*unit,V<'a>*unit,Ok>, _)) = 
        let r = DynamicMethod("", typeof<'a>, [||])
        f { ilg = r.GetILGenerator(); localMap = Dictionary(); labelMap = Dictionary(); meth = r }
        r.CreateDelegate(typeof<System.Func<'a>>) :?> System.Func<'a>
    member __.Run((Instrs f : Instrs<unit,unit,Ok>, _)) = 
        let r = DynamicMethod("", typeof<System.Void>, [||])
        f { ilg = r.GetILGenerator(); localMap = Dictionary(); labelMap = Dictionary(); meth = r }
        r.CreateDelegate(typeof<System.Action>) :?> System.Action

type IlBuilder<'t1>() =
    inherit IlBuilder()
    [<CustomOperation("ldarg_0", MaintainsVariableSpace=true)>]
    member __.Ldarg_0((Instrs f : Instrs<'a,'r,_>, j)) : Instrs<V<'t1>*'a,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Ldarg_0)), j
    [<CustomOperation("starg_0", MaintainsVariableSpace=true)>]
    member __.Starg_0((Instrs f : Instrs<V<'t1>*'a,'r,_>, j)) : Instrs<'a,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Starg, 0s)), j
    [<CustomOperation("ldarga_0", MaintainsVariableSpace=true)>]
    member __.Ldarga_0((Instrs f : Instrs<'a,'r,_>, j)) : Instrs<B<'t1>*'a,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Ldarga, 0s)), j
    (* haven't determined how to overload these for other arities... *)
    /// Pseudo-opcode for recursive calls when building an Action<_>
    [<CustomOperation("callRecA", MaintainsVariableSpace=true)>]
    member __.CallRecA((Instrs f : Instrs<V<'t1>*'a,unit,_>, j)) : Instrs<'a,unit,_> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Call, s.meth)), j
    /// Pseudo-opcode for recursive calls when building a Func<_, _>
    [<CustomOperation("callRecF", MaintainsVariableSpace=true)>]
    member __.CallRecF((Instrs f : Instrs<V<'t1>*'a,'r*unit,_>, j)) : Instrs<'r*'a,'r*unit,_> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Call, s.meth)), j
    member __.Run((Instrs f : Instrs<V<'a>*unit,V<'a>*unit,Ok>, _)) = 
        let r = DynamicMethod("", typeof<'a>, [|typeof<'t1>|])
        f { ilg = r.GetILGenerator(); localMap = Dictionary(); labelMap = Dictionary(); meth = r }
        r.CreateDelegate(typeof<System.Func<'t1,'a>>) :?> System.Func<'t1,'a>
    member __.Run((Instrs f : Instrs<unit,unit,Ok>, _)) = 
        let r = DynamicMethod("", typeof<System.Void>, [|typeof<'t1>|])
        f { ilg = r.GetILGenerator(); localMap = Dictionary(); labelMap = Dictionary(); meth = r }
        r.CreateDelegate(typeof<System.Action<'t1>>) :?> System.Action<'t1>

type IlBuilder<'t1,'t2>() =
    inherit IlBuilder<'t1>()
    [<CustomOperation("ldarg_1", MaintainsVariableSpace=true)>]
    member __.Ldarg_1((Instrs f : Instrs<'a,'r,_>, j)) : Instrs<V<'t2>*'a,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Ldarg_1)), j
    [<CustomOperation("starg_1", MaintainsVariableSpace=true)>]
    member __.Starg_1((Instrs f : Instrs<V<'t2>*'a,'r,_>, j)) : Instrs<'a,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Starg, 1s)), j
    [<CustomOperation("ldarga_1", MaintainsVariableSpace=true)>]
    member __.Ldarga_1((Instrs f : Instrs<'a,'r,_>, j)) : Instrs<B<'t2>*'a,'r,Nok> * _ =
        Instrs(f +> fun s -> s.ilg.Emit(OpCodes.Ldarga, 1s)), j
    member __.Run((Instrs f : Instrs<V<'a>*unit,V<'a>*unit,Ok>, _)) = 
        let r = DynamicMethod("", typeof<'a>, [|typeof<'t1>;typeof<'t2>|])
        f { ilg = r.GetILGenerator(); localMap = Dictionary(); labelMap = Dictionary(); meth = r }
        r.CreateDelegate(typeof<System.Func<'t1,'t2,'a>>) :?> System.Func<'t1,'t2,'a>
    member __.Run((Instrs f : Instrs<unit,unit,Ok>, _)) = 
        let r = DynamicMethod("", typeof<System.Void>, [|typeof<'t1>;typeof<'t2>|])
        f { ilg = r.GetILGenerator(); localMap = Dictionary(); labelMap = Dictionary(); meth = r }
        r.CreateDelegate(typeof<System.Action<'t1,'t2>>) :?> System.Action<'t1,'t2>

/// Builder for delegates taking no arguments (i.e. Action or Func<_>)
let il = IlBuilder()
/// Builder for delegates taking one argument (i.e. Action<_> or Func<_, _>)
let il1<'t> = IlBuilder<'t>()
/// Builder for delegates taking two arguments (i.e. Action<_, _> or Func<_, _, _>)
let il2<'t1,'t2> = IlBuilder<'t1,'t2>()

type IlBuilder with
    member __.For((i,j),f) = 
        i,f j

[<CompilerServices.TypeProviderAssembly>]
do()


