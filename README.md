# Simple raytracer in Lean 4

[Lean 4](https://github.com/leanprover/lean4) is a dependently typed programming language, and 
it can be used both as a proof assistant and for practical programs.

This repository implements the ray tracer described in 
[_Ray Tracing in One Weekend_](https://raytracing.github.io/books/RayTracingInOneWeekend.html).
Code for writing PPM files originally came from
[TOTBWF/lean4-raytrace](https://github.com/TOTBWF/lean4-raytrace).

The raytracer uses `Task`s to render in parallel.  Part of a raytracer is using supersampling
to better estimate the amount of light entering each pixel, so it is trivial to parallelize:
the entire image is rendered multiple times, and the results are averaged together.

![final test image](https://github.com/kmill/lean4-raytracer/blob/master/output/test13.png?raw=true)

(8 minutes 10 seconds with 10 threads on an Apple M2 Max. 500x333 pixels, 80 total samples per pixel, max depth 30.)

![final test image, higher resolution](https://github.com/kmill/lean4-raytracer/blob/master/output/test13.bigger.png?raw=true)

(2 hours with 16 threads on an Intel Xeon E5-2665. 800x533 pixels, 480 total samples per pixel, max depth 50.)

## Running the code

Assuming you already have Lean 4 setup, this builds an executable and runs it:
```
$ lake build && time lake exe render test.ppm
```
The rendering settings are hard-coded in `writeTestImage` in `render.lean`.

## C benchmark

The `c` folder contains an implementation of the raytracer in C, hand translated from Lean using C idioms.
This is not meant to be a fair comparison, and I spent more time thinking about optimizing the C version.
The only purpose here is to get some idea of the relative speed of my Lean code.

The first test image in C took 5.9 seconds with the same configuration,
and the second test image took 1 minute 19 seconds (but with Apple M2 Max).
