
#r "bin/Debug/ILBuilder.dll"

open ILBuilder

// Print out the hailstone sequence for a given input (x -> x/2 if x even, 3x+1 if odd), stopping when the result is 1.
// Note that using the format string "{0,4}" in the call to WriteLine isn't particularly useful but tests out a few extra code paths
// The il1 builder indicates that there should be a single argument to the generated delegate; 
// the argument type and return type (if any) are inferred based on the stack states
let hailstone = il1 {
    let loop = makeLabel()
    let ret = makeLabel()
    let half = makeLabel()
    ldarg_0
    markLabel loop
    dup
    starg_0
    ldstr "{0,4}"
    ldarga_0
    call (adjustToStack MethodProvider.Methods.System.Int32.``ToString : unit->string``)
    box
    call (adjustToStack MethodProvider.Methods.System.Console.``WriteLine : string*obj->unit``)
    dup
    ldc_i4 1
    ble ret
    dup
    ldc_i4 2
    rem
    ldc_i4 0
    beq half
    ldc_i4 3
    mul
    ldc_i4 1
    add
    br loop
    markLabel half
    ldc_i4 2
    div
    br loop
    markLabel ret
    pop
    ret
}

// test the generated function
hailstone.Invoke 27

