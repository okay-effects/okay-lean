/*
 * okay's in-process ABI for a Lean worker (okay's polyglot-one-wire, stage 3): a library exporting
 *
 *   uint8_t* okay_exchange(const uint8_t* req, size_t len, size_t* out_len);  // an empty request: the hello
 *   void     okay_free(uint8_t* resp, size_t len);
 *
 * is a worker okay loads into its own process through FFM (`ForeignWorker.inProcess(path)`): one request in, one
 * answer out, no second process. The Lean side is three functions of Okay.Wire.Worker (`okay_lean_hello`,
 * `okay_lean_state0`, `okay_lean_exchange`) and the library's worker (`okay_lean_worker`); the worker's state lives
 * here between calls. Lean's runtime and the worker's module are initialized on the first call (the module's
 * initializer named at compile time, OKAY_LEAN_INIT); a caller's thread is made Lean's on its first call; calls are
 * one at a time.
 */
#include <lean/lean.h>
#include <pthread.h>
#include <stdlib.h>
#include <string.h>

#ifndef OKAY_LEAN_INIT
#error "OKAY_LEAN_INIT: the worker module's initializer, initialize_<package>_<Module>"
#endif

/* the module's initializer (Lean 4.35: of `builtin` alone), which starts Lean's runtime and initializes all the
 * module imports; then what a Lean executable's main does after it */
extern lean_object* OKAY_LEAN_INIT(uint8_t builtin);
extern void lean_initialize_thread(void);
extern void lean_init_task_manager(void);
extern lean_object* okay_lean_worker(lean_object* unit);
extern lean_object* okay_lean_state0(lean_object* unit);
extern lean_object* okay_lean_hello(lean_object* unit);
extern lean_object* okay_lean_exchange(lean_object* worker, lean_object* state, lean_object* req);

static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;
static lean_object* worker = NULL;
static lean_object* state = NULL;
static _Thread_local int lean_thread = 0;

static void start(void) {
  lean_object* r = OKAY_LEAN_INIT(1);
  if (lean_io_result_is_error(r)) {
    lean_io_result_show_error(r);
    abort();
  }
  lean_dec_ref(r);
  lean_io_mark_end_initialization();
  lean_init_task_manager();
  worker = okay_lean_worker(lean_box(0));
  state = okay_lean_state0(lean_box(0));
}

uint8_t* okay_exchange(const uint8_t* req, size_t len, size_t* out_len) {
  pthread_mutex_lock(&lock);
  if (worker == NULL) {
    start();
    lean_thread = 1;
  } else if (!lean_thread) {
    lean_initialize_thread();
    lean_thread = 1;
  }
  lean_object* answer;
  if (len == 0) {
    answer = okay_lean_hello(lean_box(0));
  } else {
    lean_object* s = lean_mk_string_from_bytes((const char*)req, len);
    lean_inc(worker);
    lean_object* next = okay_lean_exchange(worker, state, s);  /* the state, the request: given; the worker: lent */
    state = lean_ctor_get(next, 0);
    answer = lean_ctor_get(next, 1);
    lean_inc(state);
    lean_inc(answer);
    lean_dec(next);
  }
  size_t n = lean_string_size(answer) - 1;
  uint8_t* out = malloc(n == 0 ? 1 : n);
  memcpy(out, lean_string_cstr(answer), n);
  lean_dec(answer);
  *out_len = n;
  pthread_mutex_unlock(&lock);
  return out;
}

void okay_free(uint8_t* resp, size_t len) {
  (void)len;
  free(resp);
}
