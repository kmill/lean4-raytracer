# Simple raytracer in Lean 4

[Lean 4](https://github.com/leanprover/lean4) is a dependently typed programming language, and 
it can be used both as a proof assistant and for practical programs.

This repository implements the ray tracer described in 
[_Ray Tracing in One Weekend_](https://raytracing.github.io/books/RayTracingInOneWeekend.html).

The raytracer uses `Task`s to do supersampling in parallel.  The entire image is rendered multiple
times in parallel, and the results are averaged together.