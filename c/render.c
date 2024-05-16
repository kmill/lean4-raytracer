#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <errno.h>
#include <signal.h>
#include <pthread.h>

// Halts the program, printing an error message.
#define error(...) do {                                              \
    if (errno) { perror("ERROR"); }                                  \
    fprintf(stderr, "ERROR %s:%d: ", __FILE__, __LINE__);            \
    fprintf(stderr, __VA_ARGS__);                                    \
    fprintf(stderr, "\n");                                           \
    raise(SIGABRT);                                                  \
    exit(22);                                                        \
  } while(0)

inline double fmin(double x, double y) { return x <= y ? x : y; }
inline double fmax(double x, double y) { return x <= y ? y : x; }

typedef struct Vec3 {
  double x, y, z;
} Vec3;

Vec3 Vec3_add(Vec3 v, Vec3 w) { return (Vec3){v.x + w.x, v.y + w.y, v.z + w.z}; }
Vec3 Vec3_sub(Vec3 v, Vec3 w) { return (Vec3){v.x - w.x, v.y - w.y, v.z - w.z}; }
Vec3 Vec3_mul(Vec3 v, Vec3 w) { return (Vec3){v.x * w.x, v.y * w.y, v.z * w.z}; }
Vec3 Vec3_div(Vec3 v, Vec3 w) { return (Vec3){v.x / w.x, v.y / w.y, v.z / w.z}; }
Vec3 Vec3_scale(double c, Vec3 w) { return (Vec3){c * w.x, c * w.y, c * w.z}; }

double Vec3_sum(Vec3 v) { return v.x + v.y + v.z; }
double Vec3_dot(Vec3 v, Vec3 w) { return Vec3_sum(Vec3_mul(v, w)); }
double Vec3_length_squared(Vec3 v) { return Vec3_dot(v, v); }
double Vec3_length(Vec3 v) { return sqrt(Vec3_length_squared(v)); }
Vec3 Vec3_normalized(Vec3 v) { return Vec3_scale(1 / Vec3_length(v), v); }

Vec3 Vec3_cross(Vec3 v, Vec3 w) {
  return (Vec3){v.y*w.z - v.z*w.y, v.z*w.x - v.x*w.z, v.x*w.y - v.y*w.x};
}

/* Reflect v over plane with normal (unit) vector n. */
Vec3 Vec3_reflect(Vec3 v, Vec3 n) {
  return Vec3_sub(v, Vec3_scale(2 * Vec3_dot(v, n), n));
}

bool Vec3_near_zero(Vec3 v) { return Vec3_length(v) < 1e-8; }

typedef Vec3 Color;

const Color Color_black = (Color){0, 0, 0};
const Color Color_white = (Color){1, 1, 1};

/* The random number generator in Lean 4, which appears to be
   from ranlib. Barry W. Brown, James Lovato, Kathy Russell <bwb@odin.mda.uth.tmc.edu>,
   based on L'Ecuyer and  Cote, ACM TOMS 17:98-111 (1991).

   Copying the Lean implementation. */

typedef struct Rand {
  int32_t s1, s2;
} Rand;

/* s and q are seeds to the random number generator. */
void Rand_init(Rand *r, int32_t s, int32_t q) {
  r->s1 = (s % 2147483562) + 1;
  r->s2 = (q % 2147483398) + 1;
}

/* Returns a random integer in [1, 2147483562] inclusive. */
int32_t Rand_next(Rand *r) {
  int32_t s1 = r->s1;
  int32_t s2 = r->s2;
  int32_t k = s1 / 53668;
  int32_t s1_ = 40014 * (s1 - k * 53668) - k * 12211;
  int32_t s1__ = s1_ < 0 ? s1_ + 2147483563 : s1_;
  int32_t k_ = s2 / 52774;
  int32_t s2_ = 40692 * (s2 - k_ * 52774) - k_ * 3791;
  int32_t s2__ = s2_ < 0 ? s2_ + 2147483399 : s2_;
  int32_t z = s1__ - s2__;
  int32_t z_ = z < 1 ? z + 2147483562 : z % 2147483562;
  r->s1 = s1__;
  r->s2 = s2__;
  return z_;
}

/* Split a random number generator, initializing r_new. */
void Rand_split(Rand *r, Rand *r_new) {
  int32_t newS1 = r->s1 == 2147483562 ? 1 : r->s1 + 1;
  int32_t newS2 = r->s2 == 1 ? 2147483398 : r->s2 - 1;
  Rand_next(r);
  r_new->s1 = r->s1;
  r_new->s2 = newS2;
  r->s1 = newS1;
}

/* Uniform at random double in range [0, 1). */
double Rand_unif(Rand *r) {
  int32_t i = Rand_next(r);
  return (double)(i - 1) / 2147483562;
}

/* Uniform at random double in range [lo, hi). */
double Rand_unif_range(Rand *r, double lo, double hi) {
  return (hi - lo) * Rand_unif(r) + lo;
}

Vec3 Rand_Vec3_range(Rand *r, double lo, double hi) {
  double x, y, z;
  x = Rand_unif_range(r, lo, hi);
  y = Rand_unif_range(r, lo, hi);
  z = Rand_unif_range(r, lo, hi);
  return (Vec3){x, y, z};
}

/* Gives a vector with length less than 1 uniformly at random. */
Vec3 Rand_Vec3_in_unit_sphere(Rand *r) {
  for (int i = 0; i < 100; i++) { // 7e-33 probability of failure
    Vec3 v = Rand_Vec3_range(r, -1, 1);
    if (Vec3_length_squared(v) < 1.0) {
      return v;
    }
  }
  return (Vec3){1, 0, 0};
}

/* Gives a vector in the XY unit disk with length less than 1 uniformly at random. */
Vec3 Rand_Vec3_in_unit_disk(Rand *r) {
  double x, y;
  for (int i = 0; i < 100; i++) { // 2e-67 probability of failure
    x = Rand_unif_range(r, -1, 1);
    y = Rand_unif_range(r, -1, 1);
    Vec3 v = (Vec3){x, y, 0};
    if (Vec3_length_squared(v) < 1.0) {
      return v;
    }
  }
  return (Vec3){0, 0, 0};
}

typedef struct Ray {
  Vec3 origin, dir;
} Ray;

Vec3 Ray_at(Ray const *r, double t) {
  return Vec3_add(r->origin, Vec3_scale(t, r->dir));
}

typedef struct Camera {
  Vec3 origin, lower_left_corner, horizontal, vertical;
  Vec3 u, v, w; /* right, up, back */
  double lens_radius;
} Camera;

void Camera_default(Camera *cam,
                    Vec3 look_from, Vec3 look_at, Vec3 vup,
                    double vfov,
                    double aspect_ratio,
                    double aperture,
                    double focus_dist) {
  double theta = vfov / 180 * M_PI;
  double h = tan(theta / 2);
  double viewport_height = 2.0 * h;
  double viewport_width = aspect_ratio * viewport_height;

  Vec3 w = Vec3_normalized(Vec3_sub(look_from, look_at));
  Vec3 u = Vec3_normalized(Vec3_cross(vup, w));
  Vec3 v = Vec3_cross(w, u);

  cam->origin = look_from;
  cam->horizontal = Vec3_scale(focus_dist * viewport_width, u);
  cam->vertical = Vec3_scale(focus_dist * viewport_height, v);
  cam->lower_left_corner = Vec3_sub(cam->origin, Vec3_add(Vec3_add(Vec3_scale(0.5, cam->horizontal),
                                                                   Vec3_scale(0.5, cam->vertical)),
                                                          Vec3_scale(focus_dist, w)));
  cam->u = u;
  cam->v = v;
  cam->w = w;
  cam->lens_radius = aperture / 2;
}

void Camera_get_ray(Camera const *cam, Rand *rand, double s, double t, Ray *ray) {
  Vec3 rd = Vec3_scale(cam->lens_radius, Rand_Vec3_in_unit_disk(rand));
  Vec3 offset = Vec3_add(Vec3_scale(rd.x, cam->u), Vec3_scale(rd.y, cam->v));
  ray->origin = Vec3_add(cam->origin, offset);
  ray->dir = Vec3_sub(Vec3_add(cam->lower_left_corner,
                               Vec3_add(Vec3_scale(s, cam->horizontal),
                                        Vec3_scale(t, cam->vertical))),
                      ray->origin);
}

typedef struct HitRecord {
  Vec3 p;
  double t;
  Vec3 normal;
  bool front_face;
} HitRecord;

/* Given a HitRecord with p and t set, set normal and front_face */
void HitRecord_set_normal(HitRecord *hit, Ray const *ray, Vec3 outward_normal) {
  hit->front_face = Vec3_dot(ray->dir, outward_normal) < 0.0;
  hit->normal = hit->front_face ? outward_normal : Vec3_scale(-1, outward_normal);
}

void HitRecord_init_from(HitRecord *dest, HitRecord const *src) {
  dest->p = src->p;
  dest->t = src->t;
  dest->normal = src->normal;
  dest->front_face = src->front_face;
}

enum MaterialResponse_type { ABSORB, SCATTER };

typedef struct MaterialResponse {
  enum MaterialResponse_type type;
  union {
    struct {} absorb;
    struct {
      Color albedo;
      Ray scattered;
    } scatter;
  };
} MaterialResponse;

typedef struct Material_lambertian {
  Color albedo;
} Material_lambertian;

typedef struct Material_metal {
  Color albedo;
  double fuzz;
} Material_metal;

typedef struct Material_dielectric {
  double index_of_refraction;
} Material_dielectric;

enum Material_type { LAMBERTIAN, METAL, DIELECTRIC };

typedef struct Material {
  enum Material_type type;
  union {
    Material_lambertian lambertian;
    Material_metal metal;
    Material_dielectric dielectric;
  };
} Material;

void Material_make_lambertian(Material *mat, Color albedo) {
  mat->type = LAMBERTIAN;
  mat->lambertian.albedo = albedo;
}
void Material_make_metal(Material *mat, Color albedo, double fuzz) {
  mat->type = METAL;
  mat->metal.albedo = albedo;
  mat->metal.fuzz = fuzz;
}
void Material_make_dielectric(Material *mat, double index_of_refraction) {
  mat->type = DIELECTRIC;
  mat->dielectric.index_of_refraction = index_of_refraction;
}

void Material_lambertian_scatter(Material_lambertian const *mat,
                                 Rand *rand, Ray const *ray, HitRecord const *hitrec,
                                 MaterialResponse *response) {
  (void)ray;
  Vec3 scatter_dir = Vec3_add(hitrec->normal, Vec3_normalized(Rand_Vec3_in_unit_sphere(rand)));
  if (Vec3_near_zero(scatter_dir)) {
    scatter_dir = hitrec->normal;
  }
  response->type = SCATTER;
  response->scatter.albedo = mat->albedo;
  response->scatter.scattered.origin = hitrec->p;
  response->scatter.scattered.dir = scatter_dir;
}

void Material_metal_scatter(Material_metal const *mat,
                            Rand *rand, Ray const *ray, HitRecord const *hitrec,
                            MaterialResponse *response) {
  Vec3 reflected = Vec3_reflect(Vec3_normalized(ray->dir), hitrec->normal);
  Vec3 scattered_dir = Vec3_add(reflected, Vec3_scale(mat->fuzz, Rand_Vec3_in_unit_sphere(rand)));
  if (Vec3_dot(scattered_dir, hitrec->normal) > 0.0) {
    response->type = SCATTER;
    response->scatter.albedo = mat->albedo;
    response->scatter.scattered.origin = hitrec->p;
    response->scatter.scattered.dir = scattered_dir;
  } else {
    response->type = ABSORB;
  }
}

Vec3 Vec3_refract(Vec3 uv, Vec3 n, double etai_over_etat) {
  double cos_theta = fmin(-Vec3_dot(uv, n), 1.0);
  Vec3 r_out_perp = Vec3_scale(etai_over_etat,
                               Vec3_add(uv, Vec3_scale(cos_theta, n)));
  Vec3 r_out_parallel = Vec3_scale(-sqrt(fabs(1.0 - Vec3_length_squared(r_out_perp))),
                                   n);
  return Vec3_add(r_out_perp, r_out_parallel);
}

void Material_dielectric_scatter(Material_dielectric const *mat,
                                 Rand *rand, Ray const *ray, HitRecord const *hitrec,
                                 MaterialResponse *response) {
  double refraction_ratio = hitrec->front_face ? 1.0 / mat->index_of_refraction : mat->index_of_refraction;
  Vec3 unit_dir = Vec3_normalized(ray->dir);
  double cos_theta = fmin(-Vec3_dot(unit_dir, hitrec->normal), 1.0);
  double sin_theta = sqrt(1.0 - cos_theta * cos_theta);
  bool cannot_refract = refraction_ratio * sin_theta > 1.0;

  /* Schlick's approximation */
  double r0_ = (1 - refraction_ratio) / (1 + refraction_ratio);
  double r0 = r0_ * r0_;
  double reflectance = r0 + (1 - r0) * pow(1 - cos_theta, 5);

  Vec3 direction;
  if (cannot_refract || reflectance > Rand_unif(rand)) {
    direction = Vec3_reflect(unit_dir, hitrec->normal);
  } else {
    direction = Vec3_refract(unit_dir, hitrec->normal, refraction_ratio);
  }
  response->type = SCATTER;
  response->scatter.albedo = Color_white;
  response->scatter.scattered.origin = hitrec->p;
  response->scatter.scattered.dir = direction;
}

void Material_scatter(Material const *mat,
                      Rand *rand, Ray const *ray, HitRecord const *hitrec,
                      MaterialResponse *response) {
  switch (mat->type) {
  case LAMBERTIAN:
    Material_lambertian_scatter(&mat->lambertian, rand, ray, hitrec, response);
    return;
  case METAL:
    Material_metal_scatter(&mat->metal, rand, ray, hitrec, response);
    return;
  case DIELECTRIC:
    Material_dielectric_scatter(&mat->dielectric, rand, ray, hitrec, response);
    return;
  default:
    error("Unknown material type");
  }
}

enum Hittable_type { SPHERE };

typedef struct Hittable_sphere {
  Vec3 center;
  double radius;
  Material const *mat;
} Hittable_sphere;

typedef struct Hittable {
  enum Hittable_type type;
  union {
    Hittable_sphere sphere;
  };
} Hittable;

bool Hittable_sphere_hit(Hittable_sphere const *sphere,
                         Ray const *ray, double tmin, double tmax,
                         HitRecord *hitrec, Material const **mat) {
  Vec3 oc = Vec3_sub(ray->origin, sphere->center);
  double a = Vec3_length_squared(ray->dir);
  double halfb = Vec3_dot(oc, ray->dir);
  double c = Vec3_length_squared(oc) - sphere->radius * sphere->radius;
  double discr = halfb * halfb - a * c;
  if (discr < 0.0) {
    return false;
  }
  double sqrtd = sqrt(discr);
  /* Find the nearest root that lies in the acceptable range */
  double root = (-halfb - sqrtd) / a;
  if (root < tmin || tmax < root) {
    root = (-halfb + sqrtd) / a;
    if (root < tmin || tmax < root) {
      return false;
    }
  }
  double t = root;
  Vec3 p = Ray_at(ray, t);
  Vec3 outward_normal = Vec3_scale(1/sphere->radius, Vec3_sub(p, sphere->center));
  *mat = sphere->mat;
  hitrec->p = p;
  hitrec->t = t;
  HitRecord_set_normal(hitrec, ray, outward_normal);
  return true;
}

void make_sphere(Hittable *obj, Vec3 center, double radius, Material const *mat) {
  obj->type = SPHERE;
  obj->sphere.center = center;
  obj->sphere.radius = radius;
  obj->sphere.mat = mat;
}

bool Hittable_hit(Hittable const *obj,
                  Ray const *ray, double tmin, double tmax,
                  HitRecord *hitrec, Material const **mat) {
  switch (obj->type) {
  case SPHERE:
    return Hittable_sphere_hit(&obj->sphere, ray, tmin, tmax, hitrec, mat);
  default:
    error("Unknown hittable type");
  }
}

bool hit_list(int nobj, Hittable const *obj_list,
              Ray const *ray, double tmin, double tmax,
              HitRecord *hitrec, Material const **mat) {
  hitrec->p = ray->origin;
  hitrec->t = tmax;
  HitRecord curr_hitrec;
  Material const *curr_mat = NULL;
  bool did_hit = false;
  for (int i = 0; i < nobj; i++) {
    if (Hittable_hit(&obj_list[i], ray, tmin, hitrec->t, &curr_hitrec, &curr_mat)) {
      did_hit = true;
      HitRecord_init_from(hitrec, &curr_hitrec);
      *mat = curr_mat;
    }
  }
  return did_hit;
}

Vec3 ray_color(int nobj, Hittable const *obj_list,
               Ray const *ray, Rand *rand,
               int depth) {
  if (depth <= 0) {
    return Color_black;
  }
  HitRecord hitrec;
  Material const *mat = NULL;
  if (hit_list(nobj, obj_list, ray, 0.001, INFINITY, &hitrec, &mat)) {
    MaterialResponse response;
    Material_scatter(mat, rand, ray, &hitrec, &response);
    switch (response.type) {
    case ABSORB:
      return Color_black;
    case SCATTER:
      return Vec3_mul(response.scatter.albedo,
                      ray_color(nobj, obj_list, &response.scatter.scattered, rand, depth - 1));
    default:
      error("Unknown material response type");
    }
  } else {
    Vec3 unit = Vec3_normalized(ray->dir);
    double t = 0.5 * (unit.y + 1.0);
    return Vec3_add(Vec3_scale(1.0 - t, Color_white),
                    Vec3_scale(t, (Color){0.5, 0.7, 1.0}));
  }
}

/* Takes a floating-point number with [0,1) mapped to [0,256).  Clamps result to 0-255. */
uint8_t clamp_to_uint8_t(double f) {
  int i = (int)(256*f);
  if (i < 0) {
    return 0;
  } else if (i > 255) {
    return 255;
  } else {
    return i;
  }
}

/* Write the color with x^(1/2) gamma encoding */
void write_color(FILE *f, Color c) {
  fprintf(f, "%d %d %d\n",
          clamp_to_uint8_t(sqrt(c.x)),
          clamp_to_uint8_t(sqrt(c.y)),
          clamp_to_uint8_t(sqrt(c.z)));
}

void random_scene(Rand *rand, int *nobj, Hittable **world) {
  Material *mats = malloc(1000 * sizeof(Material));
  int n_mat = 0;
  Hittable *objs = malloc(1000 * sizeof(Hittable));
  int n_obj = 0;

  Material *mat_glass = &mats[n_mat++];
  Material_make_dielectric(mat_glass, 1.5);

  // Ground
  Material *ground_mat = &mats[n_mat++];
  Material_make_lambertian(ground_mat, (Color){0.5, 0.5, 0.5});
  make_sphere(&objs[n_obj++], (Vec3){0, -1000, 0}, 1000, ground_mat);

  for (int a = -11; a < 11; a++) {
    for (int b = -11; b < 11; b++) {
      Vec3 center = (Vec3) {a + 0.9 * Rand_unif(rand), 0.2, b + 0.9 * Rand_unif(rand)};
      if (Vec3_length(Vec3_sub(center, (Vec3){4, 0.2, 0})) > 0.9) {
        double choose_mat = Rand_unif(rand);
        if (choose_mat < 0.9) {
          Color albedo = Vec3_mul(Rand_Vec3_range(rand, 0, 1), Rand_Vec3_range(rand, 0, 1));
          Material *mat = &mats[n_mat++];
          Material_make_lambertian(mat, albedo);
          make_sphere(&objs[n_obj++], center, 0.2, mat);
        } else if (choose_mat < 0.95) {
          Color albedo = Rand_Vec3_range(rand, 0.5, 1);
          double fuzz = Rand_unif_range(rand, 0, 0.5);
          Material *mat = &mats[n_mat++];
          Material_make_metal(mat, albedo, fuzz);
          make_sphere(&objs[n_obj++], center, 0.2, mat);
        } else {
          make_sphere(&objs[n_obj++], center, 0.2, mat_glass);
        }
      }
    }
  }
  
  // 3 big spheres
  make_sphere(&objs[n_obj++], (Vec3){0, 1, 0}, 1, mat_glass);

  Material *mat_lambert = &mats[n_mat++];
  Material_make_lambertian(mat_lambert, (Color){0.4, 0.2, 0.1});
  make_sphere(&objs[n_obj++], (Vec3){-4, 1, 0}, 1, mat_lambert);

  Material *mat_metal = &mats[n_mat++];
  Material_make_metal(mat_metal, (Color){0.7, 0.6, 0.5}, 0);
  make_sphere(&objs[n_obj++], (Vec3){4, 1, 0}, 1, mat_metal);

  printf("%d objects, %d materials\n", n_obj, n_mat);

  *nobj = n_obj;
  *world = objs;
}

struct RenderData {
  int width, height;
  int samples_per_pixel;
  int max_depth;
  Color *pixels;
  Camera *cam;
  Hittable *world;
  int nobj;
  Rand rand;
  bool show_progress;
};

void *render_task(void *arg) {
  struct RenderData const *rd = arg;
  Rand rand = rd->rand;

  for (int line = 0; line < rd->height; line++) {
    if (rd->show_progress) {
      printf("line %d of %d\n", line+1, rd->height);
    }
    int j = rd->height - line - 1;
    for (int i = 0; i < rd->width; i++) {
      Color pixel_color = Color_black;
      for (int s = 0; s < rd->samples_per_pixel; s++) {
        double u = (i + Rand_unif(&rand)) / rd->width;
        double v = (j + Rand_unif(&rand)) / rd->height;
        Ray ray;
        Camera_get_ray(rd->cam, &rand, u, v, &ray);
        Color rc = ray_color(rd->nobj, rd->world, &ray, &rand, rd->max_depth);
        //Color rc = (Color){(double)i/width, (double)j/height, 0.25};
        pixel_color = Vec3_add(pixel_color, rc);
      }
      rd->pixels[line * rd->width + i] = pixel_color;
    }
  }

  return arg;
}

void write_test_image(const char *filename) {
  double aspect_ratio = 3.0 / 2.0;
  int width = 500;
  int height = (int)(width / aspect_ratio);
  int samples_per_pixel = 8;
  int max_depth = 30;
  int num_threads = 10;

  printf("%d threads, %dx%d pixels, %d total samples per pixel, max depth %d.\n",
    num_threads, width, height, samples_per_pixel*num_threads, max_depth);

  Rand rand;
  Rand_init(&rand, 0, 0);

  Hittable *world;
  int nobj;
  random_scene(&rand, &nobj, &world);

  Vec3 look_from = (Vec3){13, 2, 3};
  Vec3 look_at = (Vec3){0, 0, 0};
  Vec3 vup = (Vec3){0, 1, 0};
  double dist_to_focus = 10;
  double aperture = 0.1;
  Camera cam;
  Camera_default(&cam,
                 look_from, look_at, vup,
                 20.0, aspect_ratio, aperture, dist_to_focus);

  printf("Starting %d threads.\n", num_threads);

  pthread_t threads[num_threads];

  for (int i = 0; i < num_threads; i++) {
    struct RenderData *rd = malloc(sizeof(struct RenderData));
    rd->width = width;
    rd->height = height;
    rd->samples_per_pixel = samples_per_pixel;
    rd->max_depth = max_depth;
    rd->pixels = malloc(height * width * sizeof(Color));
    rd->cam = &cam;
    rd->world = world;
    rd->nobj = nobj;
    Rand_split(&rand, &rd->rand);
    rd->show_progress = (i == 0);
    pthread_create(&threads[i], NULL, &render_task, (void*)rd);
  }

  Color *pixels = malloc(height * width * sizeof(Color));
  for (int i = 0; i < height * width; i++) {
    pixels[i] = Color_black;
  }

  for (int i = 0; i < num_threads; i++) {
    struct RenderData *rd = NULL;
    pthread_join(threads[i], (void **)&rd);
    Color *new_pixels = rd->pixels;
    for (int i = 0; i < height * width; i++) {
      pixels[i] = Vec3_add(pixels[i], new_pixels[i]);
    }
    free(new_pixels);
    free(rd);
  }
  
  printf("Writing to %s\n", filename);
  FILE *f = fopen(filename, "w");
  fprintf(f, "P3\n%d %d 255\n", width, height);
  for (int i = 0; i < width * height; i++) {
    write_color(f, Vec3_scale(1.0 / (samples_per_pixel * num_threads), pixels[i]));
  }
  fclose(f);
  free(pixels);
}

int main(int argc, char **argv) {
  char *filename = "out.ppm";
  if (argc > 1) {
    filename = argv[1];
  }
  write_test_image(filename);
  return 0;
}
