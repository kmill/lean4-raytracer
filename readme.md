# Simple raytracer in Lean 4

**Note.** This is a branch experimenting with a faster version of the ray tracer.  It currently runs in about 75% the time.

## Background

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

## Running the code

Assuming you already have Lean 4 setup, this builds an executable and runs it:
```
$ leanpkg build build/bin/render && time ./build/bin/render test.ppm
```
The rendering settings are hard-coded in `writeTestImage` in `render.lean`.

## C benchmark

The `c` folder contains an implementation of the raytracer in C, hand translated from Lean using C idioms.
This is not a fair comparison because I spent almost no time thinking about optimizing the Lean version, and the only purpose here is to get some idea of the relative speed of my Lean code to see if I made any horrible mistakes.

The first test image in C took 20 seconds with the same configuration, and the second test image took 3 minutes 30 seconds with the same configuration.  This means my Lean program takes about 32x as long to run as the C version.

Writing the Lean program more like the C program would likely make it run significantly faster.
