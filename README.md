# compilers-inline

Implementing inline functions:

What we could have done differently:
- CAExpr and cleanup is not the best way to implement function inlining and branch elimination. We could have do the unwrapping of AExpr right at the point that it was used. This makes for a cleaner implementation.
- Inlining is now explicit and enforced. If we had time we would implement some heuristics to decide which function could be inlined, and which function is best left as a function. This way, the code can be optimized for code size or compilation time depends on the programmer's preference.
- Inlining will break if it was given an argument with a wrong or ambigous type. We should be able to throw an error or discard the inline function to a normal lambda here. However, there seems to not be an easy way to implement this without a static type system.
- Badly written inlined functions and applications can lead to massive compiler memory usage and/or cause the compiler to hang. We would like to implement a mechanic that discover these errors and prevent them from happening.

Lesson learned:
- While our functional language at first seems like a good candidate for function inlining, the lack of a static type system in our language makes it a massive pain to implement inline correctly
- The performance improvement is small enough that it does not really justify the inclusion of function inlining, especially since functional languages are rarely used in performance-constrained environment like embedded systems.
- Overall a fun idea to think about and try, but the deeper we get into it the more impractical it becomes.
