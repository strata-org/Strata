/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/

/*
  Debug statistics counters and timers, callable from Lean via FFI.

  Usage from Lean:
    increment_stat "myCounter";
    increment_stat "myCounter" 5;
    get_stat "myCounter" v;
    get_stat_keys keys;
    start_timer "myOp";
    finish_timer;

  Each function takes a leading `_inh` argument for the [Inhabited α]
  typeclass instance required by `opaque` declarations.
*/

#include <lean/lean.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#define STATS_MAX_ENTRIES 256
#define STATS_MAX_KEY_LEN 128

typedef struct {
    char key[STATS_MAX_KEY_LEN];
    uint64_t count;
} stats_entry_t;

static stats_entry_t g_stats[STATS_MAX_ENTRIES];
static int g_num_stats = 0;

static int stats_find(const char *id) {
    for (int i = 0; i < g_num_stats; i++) {
        if (strcmp(g_stats[i].key, id) == 0)
            return i;
    }
    return -1;
}

/* --- Statistics --- */

/* Lean: {α} → [Inhabited α] → String → Nat → (Unit → α) → α */
LEAN_EXPORT lean_obj_res strata_increment_statistics_pure(
        lean_obj_arg _inh, lean_obj_arg stat_id, lean_obj_arg amount, lean_obj_arg f) {
    lean_dec(_inh);
    const char *id = lean_string_cstr(stat_id);
    uint64_t n = lean_is_scalar(amount) ? lean_unbox(amount) : 1;

    int idx = stats_find(id);
    if (idx >= 0) {
        g_stats[idx].count += n;
    } else if (g_num_stats < STATS_MAX_ENTRIES) {
        strncpy(g_stats[g_num_stats].key, id, STATS_MAX_KEY_LEN - 1);
        g_stats[g_num_stats].key[STATS_MAX_KEY_LEN - 1] = '\0';
        g_stats[g_num_stats].count = n;
        g_num_stats++;
    } else {
        fprintf(stdout, "[statistics] WARNING: table full, ignoring '%s'\n", id);
    }

    lean_dec(stat_id);
    lean_dec(amount);
    return lean_apply_1(f, lean_box(0));
}

/* Lean: {α} → [Inhabited α] → String → (Nat → α) → α */
LEAN_EXPORT lean_obj_res strata_get_statistics_pure(
        lean_obj_arg _inh, lean_obj_arg stat_id, lean_obj_arg f) {
    lean_dec(_inh);
    const char *id = lean_string_cstr(stat_id);
    uint64_t val = 0;

    int idx = stats_find(id);
    if (idx >= 0)
        val = g_stats[idx].count;

    lean_dec(stat_id);
    return lean_apply_1(f, lean_box(val));
}

/* Lean: {α} → [Inhabited α] → (Array String → α) → α */
LEAN_EXPORT lean_obj_res strata_get_stat_keys_pure(
        lean_obj_arg _inh, lean_obj_arg f) {
    lean_dec(_inh);
    lean_object *arr = lean_mk_empty_array();
    for (int i = 0; i < g_num_stats; i++) {
        lean_object *s = lean_mk_string(g_stats[i].key);
        arr = lean_array_push(arr, s);
    }
    return lean_apply_1(f, arr);
}

/* --- Timers (stack-based) --- */

#define TIMER_MAX_DEPTH 64

typedef struct {
    char label[STATS_MAX_KEY_LEN];
    struct timespec start;
} timer_entry_t;

static timer_entry_t g_timers[TIMER_MAX_DEPTH];
static int g_num_timers = 0;

/* Lean: {α} → [Inhabited α] → String → (Unit → α) → α */
LEAN_EXPORT lean_obj_res strata_start_timer_pure(
        lean_obj_arg _inh, lean_obj_arg label, lean_obj_arg f) {
    lean_dec(_inh);
    if (g_num_timers < TIMER_MAX_DEPTH) {
        const char *s = lean_string_cstr(label);
        strncpy(g_timers[g_num_timers].label, s, STATS_MAX_KEY_LEN - 1);
        g_timers[g_num_timers].label[STATS_MAX_KEY_LEN - 1] = '\0';
        clock_gettime(CLOCK_MONOTONIC, &g_timers[g_num_timers].start);
        g_num_timers++;
    } else {
        fprintf(stdout, "[timer] WARNING: timer stack full\n");
    }
    lean_dec(label);
    return lean_apply_1(f, lean_box(0));
}

/* Lean: {α} → [Inhabited α] → (Unit → α) → α */
LEAN_EXPORT lean_obj_res strata_finish_timer_pure(
        lean_obj_arg _inh, lean_obj_arg f) {
    lean_dec(_inh);
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    if (g_num_timers <= 0) {
        fprintf(stdout, "[timer] WARNING: finish_timer with no active timer\n");
    } else {
        g_num_timers--;
        timer_entry_t *e = &g_timers[g_num_timers];
        long ms = (now.tv_sec - e->start.tv_sec) * 1000
                + (now.tv_nsec - e->start.tv_nsec) / 1000000;
        fprintf(stdout, "[timer] %-40s %ldms\n", e->label, ms);
    }
    return lean_apply_1(f, lean_box(0));
}
