# Simple raytracer in Lean 4

[Lean 4](https://github.com/leanprover/lean4) is a dependently typed programming language, and 
it can be used both as a proof assistant and for practical programs.

This repository implements the ray tracer described in 
[_Ray Tracing in One Weekend_](https://raytracing.github.io/books/RayTracingInOneWeekend.html).

The raytracer uses `Task`s to render in parallel.  Part of a raytracer is using supersampling
to better estimate the amount of light entering each pixel, so it is trivial to parallelize:
the entire image is rendered multiple times, and the results are averaged together.

![final test image](https://github.com/kmill/lean4-raytracer/blob/master/test13.png?raw=true)

(10 minutes with 8 threads on an Intel Xeon E5-2665. 500x333 pixels, 80 total samples per pixel, max depth 30.)

![final test image, higher resolution](https://github.com/kmill/lean4-raytracer/blob/master/test13.bigger.png?raw=true)

(2 hours with 16 threads on an Intel Xeon E5-2665. 800x533 pixels, 480 total samples per pixel, max depth 50.)