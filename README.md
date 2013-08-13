ILBuilder
=========

This is a simple prototype for an F# MSIL DSL.  There are many limitations, some of which are due to fairly fundamental issues with what the type system can support.  Here are some of the limitations:

 - Many opcodes are unimplmented; pull requests fleshing out the supported set are welcome
 - Arithmetic opcodes are all monomorphic; they work on integers but not (say) floats, even though in IL they are supported on multiple numeric types
 - There's no way to call methods given a receiver of a derived type, even though this would be perfectly valid code
 - The method type provider doesn't provide values for generic methods, and only looks in mscorlib


