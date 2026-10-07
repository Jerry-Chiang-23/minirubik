#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum {
    CUBIES = 7,
    PERMUTATIONS = 5040,
    ORIENTATIONS = 729,
    STATES = PERMUTATIONS * ORIENTATIONS,
    MOVES = 9
};

typedef struct {
    uint8_t p[CUBIES], o[CUBIES];
} state_t;

/*@ predicate valid_state(state_t *state) =
      (\forall integer i; 0 <= i < CUBIES ==>
         state->p[i] < CUBIES && state->o[i] < 3) &&
      (\forall integer i, j; 0 <= i < j < CUBIES ==>
         state->p[i] != state->p[j]) &&
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
 */

static const char *const move_names[MOVES] = {"R",  "R2", "R'", "B", "B2",
                                              "B'", "D",  "D2", "D'"};
static const uint8_t inverse_move[MOVES] = {2, 1, 0, 5, 4, 3, 8, 7, 6};
/* Each destination takes a cubie from source[face][destination]. */
static const uint8_t source[3][CUBIES] = {
    {1, 4, 2, 0, 3, 5, 6},
    {0, 1, 2, 4, 5, 6, 3},
    {0, 2, 5, 3, 1, 4, 6},
};
static const uint8_t twist[3][CUBIES] = {
    {1, 2, 0, 2, 1, 0, 0},
    {0, 0, 0, 1, 2, 1, 2},
    {0, 0, 0, 0, 0, 0, 0},
};

/* Search tables, filled once by build_search_tables(). */
static uint16_t trans_p[3][PERMUTATIONS];
static uint16_t trans_o[3][ORIENTATIONS];
static uint8_t pdb_p[PERMUTATIONS];
static uint8_t pdb_o[ORIENTATIONS];

/* One array per face, so that search() needs no face * row-length
 * multiplication. Filled from trans_p / trans_o by build_search_tables(). */
static uint16_t tp0[PERMUTATIONS], tp1[PERMUTATIONS], tp2[PERMUTATIONS];
static uint16_t to0[ORIENTATIONS], to1[ORIENTATIONS], to2[ORIENTATIONS];
static uint16_t *const tp[3] = {tp0, tp1, tp2};
static uint16_t *const to[3] = {to0, to1, to2};

/* The three quarter-turns preserve the fixed front-upper-left corner. */
/*@ requires face < 3;
    assigns \nothing;
    ensures \forall integer i; 0 <= i < CUBIES ==>
              \result.p[i] == state.p[source[face][i]];
    ensures \forall integer i; 0 <= i < CUBIES ==>
              \result.o[i] == (state.o[source[face][i]] + twist[face][i]) % 3;
 */
static state_t quarter_turn(state_t state, uint8_t face)
{
    state_t result;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant \forall integer j; 0 <= j < i ==>
          result.p[j] == state.p[source[face][j]];
        loop invariant \forall integer j; 0 <= j < i ==>
          result.o[j] == (state.o[source[face][j]] + twist[face][j]) % 3;
        loop assigns i, result.p[0..6], result.o[0..6];
        loop variant CUBIES - i;
    */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t from = source[face][i];
        result.p[i] = state.p[from];
        result.o[i] = (uint8_t) ((state.o[from] + twist[face][i]) % 3U);
    }
    return result;
}

static state_t apply_move(state_t state, uint8_t move)
{
    uint8_t turns = (uint8_t) (move % 3U + 1U);
    for (uint8_t i = 0; i < turns; ++i)
        state = quarter_turn(state, (uint8_t) (move / 3U));
    return state;
}


static uint16_t rank_p(const state_t *state)
{
    uint16_t p = 0;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t smaller = 0;
        for (uint8_t j = (uint8_t) (i + 1U); j < CUBIES; ++j)
            if (state->p[j] < state->p[i])
                ++smaller;
        switch (i) {
        case 0: break;
        case 1: p = (uint16_t) ((p << 2) + (p << 1)); break; /* ×6 */
        case 2: p = (uint16_t) ((p << 2) + p); break;
        case 3: p = (uint16_t) (p << 2); break;
        case 4: p = (uint16_t) ((p << 1) + p); break;
        case 5: p = (uint16_t) (p << 1); break;
        default: break;                                      /* ×1 */
        }
        p = (uint16_t) (p + smaller);
    }
    return p;
}

static uint16_t rank_o(const state_t *state){
    uint16_t o = 0;
    for (uint8_t i = 0; i < 6; ++i)
        o = (uint16_t) ((o << 1) + o + state->o[i]);
    return o;
}

/*@ requires \valid_read(state);
    requires \forall integer i; 0 <= i < CUBIES ==>
      0 <= state->p[i] < CUBIES;
    requires \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    requires \forall integer i; 0 <= i < CUBIES ==>
      0 <= state->o[i] < 3;
    assigns \nothing;
    ensures \result < STATES;
 */
static uint32_t rank_state(const state_t *state)
{
    uint32_t p = 0, o = 0;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant (i == 0 ==> p == 0) && (i == 1 ==> p <= 6) &&
          (i == 2 ==> p <= 41) && (i == 3 ==> p <= 209) &&
          (i == 4 ==> p <= 839) && (i == 5 ==> p <= 2519) &&
          (i >= 6 ==> p <= 5039);
        loop assigns i, p;
        loop variant CUBIES - i;
     */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t smaller = 0;
        /*@ loop invariant i + 1 <= j <= CUBIES;
            loop invariant smaller <= j - i - 1;
            loop assigns j, smaller;
            loop variant CUBIES - j;
         */
        for (uint8_t j = (uint8_t) (i + 1U); j < CUBIES; ++j)
            if (state->p[j] < state->p[i])
                ++smaller;
        p = p * (CUBIES - i) + smaller;
    }
    /*@ loop invariant 0 <= i <= 6;
        loop invariant (i == 0 ==> o == 0) && (i == 1 ==> o < 3) &&
          (i == 2 ==> o < 9) && (i == 3 ==> o < 27) &&
          (i == 4 ==> o < 81) && (i == 5 ==> o < 243) &&
          (i == 6 ==> o < 729);
        loop assigns i, o;
        loop variant 6 - i;
     */
    for (uint8_t i = 0; i < 6; ++i)
        o = o * 3U + state->o[i];
    return p * ORIENTATIONS + o;
}

/*@ requires \valid(state); requires rank < STATES; assigns *state; */
static void unrank_state(uint32_t rank, state_t *state)
{
    uint8_t available[CUBIES] = {0, 1, 2, 3, 4, 5, 6};
    uint32_t p = rank / ORIENTATIONS, o = rank % ORIENTATIONS, f = 720;
    uint8_t sum = 0;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t q = (uint8_t) (p / f);
        p %= f;
        state->p[i] = available[q];
        for (uint8_t j = q; j + 1U < CUBIES - i; ++j)
            available[j] = available[j + 1U];
        if (i < 5)
            f /= 6U - i;
    }
    for (uint8_t i = 6; i-- > 0;) {
        state->o[i] = (uint8_t) (o % 3U);
        sum = (uint8_t) (sum + state->o[i]);
        o /= 3U;
    }
    state->o[6] = (uint8_t) ((3U - sum % 3U) % 3U);
}

/*@ requires \valid_read(state);
    requires \initialized(&state->p[0..6]) && \initialized(&state->o[0..6]);
    assigns \nothing;
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] < CUBIES && state->o[i] < 3;
    ensures \result != 0 ==> \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    ensures \result != 0 ==>
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
    ensures complete: valid_state(state) ==> \result != 0;
 */
static int valid(const state_t *state)
{
    uint8_t sum = 0;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant sum <= 2 * i;
        loop invariant sum == (i > 0 ? state->o[0] : 0) +
          (i > 1 ? state->o[1] : 0) + (i > 2 ? state->o[2] : 0) +
          (i > 3 ? state->o[3] : 0) + (i > 4 ? state->o[4] : 0) +
          (i > 5 ? state->o[5] : 0) + (i > 6 ? state->o[6] : 0);
        loop invariant \forall integer j; 0 <= j < i ==>
          state->p[j] < CUBIES && state->o[j] < 3;
        loop invariant \forall integer j, k; 0 <= j < k < i ==>
          state->p[j] != state->p[k];
        loop assigns i, sum;
        loop variant CUBIES - i;
    */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        if (state->p[i] >= CUBIES || state->o[i] >= 3)
            return 0;
        /*@ loop invariant 0 <= j <= i;
            loop invariant \forall integer k; 0 <= k < j ==>
              state->p[k] != state->p[i];
            loop assigns j;
            loop variant i - j;
        */
        for (uint8_t j = 0; j < i; ++j)
            if (state->p[j] == state->p[i])
                return 0;
        sum = (uint8_t) (sum + state->o[i]);
    }
    return (0x1249u >> sum) & 1u;
}

static void build_transition(uint16_t permutation[3][PERMUTATIONS], uint16_t orientation[3][ORIENTATIONS]){
    state_t state;
    for (uint16_t rank = 0; rank < PERMUTATIONS; ++rank) {
        unrank_state((uint32_t) rank * ORIENTATIONS, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            permutation[face][rank] =
                (uint16_t) (rank_state(&next) / ORIENTATIONS);
        }
    }
    for (uint16_t rank = 0; rank < ORIENTATIONS; ++rank) {
        unrank_state(rank, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            orientation[face][rank] =
                (uint16_t) (rank_state(&next) % ORIENTATIONS);
        }
    }
}

static int build_pdb(const uint16_t *trans, uint16_t n, uint8_t *dist)
{
    uint16_t queue[PERMUTATIONS];   /* big enough for both tables */
    uint16_t head = 0, tail = 1;
    memset(dist, UINT8_MAX, n);
    queue[0] = 0;
    dist[0] = 0;
    while (head < tail) {
        uint16_t here = queue[head++];
        for (uint8_t face = 0; face < 3; ++face) {
            uint16_t next = here;
            for (uint8_t turn = 0; turn < 3; ++turn) {
                next = trans[face * n + next];
                if (dist[next] == UINT8_MAX) {
                    dist[next] = dist[here] + 1;
                    queue[tail++] = next;
                }
            }
        }
    }
    return tail == n;               /* 1 if every state was reached */
}

/* Build both transition tables and both pattern databases.
 * Returns 1 on success, 0 if a table is incomplete. */
static int build_search_tables(void)
{
    build_transition(trans_p, trans_o);
    memcpy(tp0, trans_p[0], sizeof tp0);
    memcpy(tp1, trans_p[1], sizeof tp1);
    memcpy(tp2, trans_p[2], sizeof tp2);
    memcpy(to0, trans_o[0], sizeof to0);
    memcpy(to1, trans_o[1], sizeof to1);
    memcpy(to2, trans_o[2], sizeof to2);
    return build_pdb(&trans_p[0][0], PERMUTATIONS, pdb_p) &&
           build_pdb(&trans_o[0][0], ORIENTATIONS, pdb_o);
}

/* Lower bound on the moves still needed from the state with permutation
 * rank p and orientation rank o: the larger of the two PDB values. */
static uint8_t h(uint16_t p, uint16_t o)
{
    uint8_t hp = pdb_p[p], ho = pdb_o[o];
    return hp > ho ? hp : ho;
}

static void emit_half(const char *label, const uint16_t *v, uint16_t n)
{
    printf("%s:\n", label);
    for (uint16_t i = 0; i < n; ++i) {
        if (i % 16 == 0)
            printf("    .half ");
        printf("%u%s", v[i], (i % 16 == 15 || i + 1 == n) ? "\n" : ", ");
    }
}

static void emit_byte(const char *label, const uint8_t *v, uint16_t n)
{
    printf("%s:\n", label);
    for (uint16_t i = 0; i < n; ++i) {
        if (i % 16 == 0)
            printf("    .byte ");
        printf("%u%s", v[i], (i % 16 == 15 || i + 1 == n) ? "\n" : ", ");
    }
}

static void emit_asm(void)
{
    puts("# generated by 'solver_v1 --emit-asm'; do not edit by hand");
    puts(".data");
    emit_half("tp0", tp0, PERMUTATIONS);
    emit_half("tp1", tp1, PERMUTATIONS);
    emit_half("tp2", tp2, PERMUTATIONS);
    emit_half("to0", to0, ORIENTATIONS);
    emit_half("to1", to1, ORIENTATIONS);
    emit_half("to2", to2, ORIENTATIONS);
    emit_byte("pdb_p", pdb_p, PERMUTATIONS);
    emit_byte("pdb_o", pdb_o, ORIENTATIONS);
}

static uint8_t path[12];        /* the current path: one move per depth */
static unsigned long nodes;     /* states visited in total */
static unsigned long calls;     /* Number of states expanded by search() */
static uint16_t sp[12], so[12];     /* state expanded at this depth */
static uint16_t cp[12], co[12];     /* state after the turns tried so far */
static uint8_t face_at[12], turn_at[12], last_at[12];
/* iterative replacement for expand(). It visits states in the
 * same order, so nodes and calls must match the recursive version. */
static int search(uint16_t p, uint16_t o, uint8_t bound)
{
    uint8_t g = 0;
    sp[0] = cp[0] = p;
    so[0] = co[0] = o;
    face_at[0] = 0;
    turn_at[0] = 0;
    last_at[0] = 255;                       /* no previous face at the root */
    ++calls;
    for (;;) {
        if (turn_at[g] == 3) {              /* all three turns of this face used */
            ++face_at[g];
            turn_at[g] = 0;
            cp[g] = sp[g];
            co[g] = so[g];
        }
        if (face_at[g] == last_at[g]) {     /* never turn the same face twice */
            ++face_at[g];
            turn_at[g] = 0;
            cp[g] = sp[g];
            co[g] = so[g];
        }
        if (face_at[g] == 3) {              /* no children left: backtrack */
            if (g == 0)
                return 0;
            --g;
            continue;
        }
        uint8_t face = face_at[g];
        uint8_t turn = turn_at[g]++;
        cp[g] = tp[face][cp[g]];
        co[g] = to[face][co[g]];
        ++nodes;
        uint8_t hh = h(cp[g], co[g]);
        if (g + 1 + hh > bound)
            continue;                       /* pruned: nothing is pushed */
        path[g] = (uint8_t) ((face << 1) + face + turn);
        if (hh == 0)
            return 1;
        sp[g + 1] = cp[g + 1] = cp[g];      /* push the child */
        so[g + 1] = co[g + 1] = co[g];
        face_at[g + 1] = 0;
        turn_at[g + 1] = 0;
        last_at[g + 1] = face;
        ++g;
        ++calls;
    }
}


/* Iterative deepening: try bound = h(start), h(start) + 1, ... until a
 * solution is found. Returns its length, and the moves are in path[]. */
static uint8_t solve(const state_t *state)
{
    nodes = 0;
    calls = 0; 
    uint16_t p = rank_p(state), o = rank_o(state);
    uint8_t h0 = h(p, o);
    for (uint8_t bound = h0; bound <= 11; ++bound) {
        ++nodes;
        if (h0 == 0 || search(p, o, bound))
            return bound;
    }
    return 255;                  /* should not happen for a valid state */
}

/* Exact distance of a state: follow the BFS table of build_table()
 * back to the solved state and count the moves. */
static uint8_t exact_distance(const uint8_t *table, uint32_t rank)
{
    state_t s;
    unrank_state(rank, &s);
    uint8_t d = 0;
    uint32_t r = rank;
    while (r) {
        s = apply_move(s, table[r]);
        ++d;
        r = rank_state(&s);
    }
    return d;
}

/* H2 for the transition tables: for each face, the row must be a
 * permutation of 0..n-1 (every entry reached exactly once), and four
 * quarter turns must return to the starting rank. */
static int check_transitions(void)
{
    for (uint8_t face = 0; face < 3; ++face) {
        static uint8_t seen_p[PERMUTATIONS], seen_o[ORIENTATIONS];
        memset(seen_p, 0, sizeof seen_p);
        memset(seen_o, 0, sizeof seen_o);
        for (uint16_t i = 0; i < PERMUTATIONS; ++i) {
            if (tp[face][i] != trans_p[face][i])
                return 0;
            uint16_t t = trans_p[face][i];
            if (t >= PERMUTATIONS || seen_p[t])
                return 0;
            seen_p[t] = 1;
            uint16_t x = i;
            for (uint8_t k = 0; k < 4; ++k)
                x = trans_p[face][x];
            if (x != i)
                return 0;
        }
        for (uint16_t i = 0; i < ORIENTATIONS; ++i) {
            if (to[face][i] != trans_o[face][i])
                return 0;
            uint16_t t = trans_o[face][i];
            if (t >= ORIENTATIONS || seen_o[t])
                return 0;
            seen_o[t] = 1;
            uint16_t x = i;
            for (uint8_t k = 0; k < 4; ++k)
                x = trans_o[face][x];
            if (x != i)
                return 0;
        }
    }
    return 1;
}

/* H2: both pattern databases fully populated, solved entry is 0, and
 * report the maximum value. H1: h(s) <= d(s) for every state. */
static int check_tables(const uint8_t *table)
{
    if (!check_transitions()) {
        puts("H2: transition tables are not permutations");
        return 0;
    }
    puts("H2: transition tables are permutations, four turns return");

    uint8_t max_p = 0, max_o = 0;
    for (uint16_t i = 0; i < PERMUTATIONS; ++i) {
        if (pdb_p[i] == UINT8_MAX)
            return 0;                       /* entry never reached by the BFS */
        if (pdb_p[i] > max_p)
            max_p = pdb_p[i];
    }
    for (uint16_t i = 0; i < ORIENTATIONS; ++i) {
        if (pdb_o[i] == UINT8_MAX)
            return 0;
        if (pdb_o[i] > max_o)
            max_o = pdb_o[i];
    }
    printf("H2: pdb_p[0]=%u max_p=%u, pdb_o[0]=%u max_o=%u\n",
           pdb_p[0], max_p, pdb_o[0], max_o);

    unsigned long bad = 0;
    for (uint32_t rank = 0; rank < STATES; ++rank) {
        state_t s;
        unrank_state(rank, &s);
        if (h(rank_p(&s), rank_o(&s)) > exact_distance(table, rank))
            ++bad;
    }
    printf("H1: %lu states with h > d\n", bad);
    return pdb_p[0] == 0 && pdb_o[0] == 0 && bad == 0;
}

/* H3, T5 and worst case: run the search on every state whose exact
 * distance is at least min_d. Check that the returned length equals the
 * exact distance, that applying the returned path solves the state, and
 * remember the most expensive distance-11 state. */
static int scan(const uint8_t *table, uint8_t min_d)
{
    unsigned long checked = 0, wrong = 0, count11 = 0;
    unsigned long bad_path = 0;
    unsigned long max_nodes = 0, max_calls = 0;
    state_t worst;
    memset(&worst, 0, sizeof worst);
    for (uint32_t rank = 0; rank < STATES; ++rank) {
        uint8_t d = exact_distance(table, rank);
        if (d < min_d)
            continue;
        state_t s;
        unrank_state(rank, &s);
        uint8_t len = solve(&s);
        ++checked;
        if (len != d)
            ++wrong;
        /* T5 on the host. Applying the returned path with the
         * original apply_move() and rank_state() must reach the solved
         * state. This also catches a wrong move index in path[]. */
        {
            state_t t = s;
            for (uint8_t i = 0; i < len; ++i)
                t = apply_move(t, path[i]);
            if (rank_state(&t) != 0)
                ++bad_path;
        }
        if (d == 11) {
            ++count11;
            if (nodes > max_nodes) {
                max_nodes = nodes;
                worst = s;
            }
            if (calls > max_calls)
                max_calls = calls;
        }
    }
    printf("checked=%lu wrong=%lu distance-11 states=%lu\n",
           checked, wrong, count11);
    printf("paths that do not solve the state: %lu\n", bad_path);
    printf("distance-11 maximum: nodes=%lu calls=%lu\n", max_nodes, max_calls);
    printf("most expensive distance-11 state: ");
    for (uint8_t i = 0; i < CUBIES; ++i)
        putchar('1' + worst.p[i]);
    for (uint8_t i = 0; i < CUBIES; ++i)
        putchar('1' + worst.o[i]);
    putchar('\n');
    return wrong == 0 && bad_path == 0;
}

static uint8_t *build_table(uint8_t *diameter)
{
    uint8_t *toward_solved = malloc(STATES);
    uint32_t *queue = malloc((size_t) STATES * sizeof *queue);
    uint16_t permutation[3][PERMUTATIONS], orientation[3][ORIENTATIONS];
    uint32_t head = 0, tail = 1, level_end = 1;
    // state_t state;
    if (!toward_solved || !queue) {
        free(toward_solved);
        free(queue);
        return NULL;
    }
    build_transition(permutation, orientation);
    memset(toward_solved, UINT8_MAX, STATES);
    queue[0] = 0;
    toward_solved[0] = 0;
    *diameter = 0;
    while (head < tail) {
        if (head == level_end) {
            level_end = tail;
            ++*diameter;
        }
        uint32_t here = queue[head++];
        uint16_t p = (uint16_t) (here / ORIENTATIONS);
        uint16_t o = (uint16_t) (here % ORIENTATIONS);
        for (uint8_t face = 0; face < 3; ++face) {
            uint16_t next_p = p, next_o = o;
            for (uint8_t turn = 0; turn < 3; ++turn) {
                next_p = permutation[face][next_p];
                next_o = orientation[face][next_o];
                uint32_t there = (uint32_t) next_p * ORIENTATIONS + next_o;
                if (toward_solved[there] == UINT8_MAX) {
                    uint8_t move = (uint8_t) (face * 3U + turn);
                    toward_solved[there] = inverse_move[move];
                    queue[tail++] = there;
                }
            }
        }
    }
    free(queue);
    if (tail != STATES) {
        free(toward_solved);
        return NULL;
    }
    return toward_solved;
}

/*@ requires valid_read_string(input);
    requires \valid(state);
    assigns state->p[0..6], state->o[0..6];
    ensures \result != 0 ==> input[14] == '\0';
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] < CUBIES && state->o[i] < 3;
    ensures \result != 0 ==> \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    ensures \result != 0 ==>
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] == input[i] - '1';
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->o[i] == input[i + CUBIES] - '1';
 */
static int parse_state(const char *input, state_t *state)
{
    /*@ loop invariant 0 <= i <= 14;
        loop invariant i <= strlen(input);
        loop invariant i <= 7 ==> \initialized(&state->p[0..i-1]);
        loop invariant i >= 7 ==> \initialized(&state->p[0..6]);
        loop invariant i >= 7 ==> \initialized(&state->o[0..i-8]);
        loop invariant \forall integer j; 0 <= j < i && j < CUBIES ==>
          state->p[j] == input[j] - '1';
        loop invariant \forall integer j; 0 <= j < i - CUBIES ==>
          state->o[j] == input[j + CUBIES] - '1';
        loop assigns i, state->p[0..6], state->o[0..6];
        loop variant 14 - i;
     */
    for (int i = 0; i < 7; ++i) {
        if (input[i] < '1' || input[i] > '7')
            return 0;
        state->p[i] = (uint8_t) (input[i] - '1');
    }
    for (int i = 0; i < 7; ++i) {
        if (input[7 + i] < '1' || input[7 + i] > '3')
            return 0;
        state->o[i] = (uint8_t) (input[7 + i] - '1');
    }
    return input[14] == '\0' && valid(state);
}

/* stdout is fully buffered off a terminal, so a write error surfaces at the
 * flush, not at the printf that queued the bytes. Every exit path that has
 * produced output goes through here.
 */
static int output_failed(void)
{
    return fflush(stdout) != 0 || ferror(stdout);
}

static int self_test(void)
{
    const state_t solved = {{0, 1, 2, 3, 4, 5, 6}, {0}};
    state_t state;
    for (uint8_t move = 0; move < MOVES; ++move) {
        state = solved;
        state = apply_move(state, move);
        state = apply_move(state, inverse_move[move]);
        if (memcmp(&solved, &state, sizeof solved))
            return 0;
    }
    for (uint32_t rank = 0; rank < STATES; ++rank) {
        unrank_state(rank, &state);
        if (!valid(&state) || rank_state(&state) != rank)
            return 0;
    }
    return 1;
}

int main(int argc, char **argv)
{
    state_t state;
    uint8_t diameter;
    if (argc == 2 && !strcmp(argv[1], "--pdb")) {
        uint16_t permutation[3][PERMUTATIONS], orientation[3][ORIENTATIONS];
        uint8_t pdb_perm[PERMUTATIONS], pdb_orient[ORIENTATIONS];
        build_transition(permutation, orientation);
        int ok_p = build_pdb(&permutation[0][0], PERMUTATIONS, pdb_perm);
        int ok_o = build_pdb(&orientation[0][0], ORIENTATIONS, pdb_orient);
        printf("ok_p=%d ok_o=%d\n", ok_p, ok_o);
        for (uint8_t d = 0; d <= 11; d++) {
            int cp = 0, co = 0;
            for (int i = 0; i < PERMUTATIONS; i++) cp += (pdb_perm[i] == d);
            for (int i = 0; i < ORIENTATIONS; i++) co += (pdb_orient[i] == d);
            printf("d=%2d perm=%4d orient=%3d\n", d, cp, co);
        }
        return output_failed();
    }
    if (argc == 3 && !strcmp(argv[1], "--rank") && parse_state(argv[2], &state)) {
        printf("p=%u o=%u full=%u check=%u\n",
            rank_p(&state), rank_o(&state), rank_state(&state),
            rank_p(&state) * ORIENTATIONS + rank_o(&state));
        return output_failed();
    }
    if (argc == 3 && !strcmp(argv[1], "--h") && parse_state(argv[2], &state)) {
        if (!build_search_tables()) {
            fputs("could not build search tables\n", stderr);
            return 1;
        }
        printf("h=%u\n", h(rank_p(&state), rank_o(&state)));
        return output_failed();
    }

    if (argc == 3 && !strcmp(argv[1], "--ida") && parse_state(argv[2], &state)) {
        if (!build_search_tables()) {
            fputs("could not build search tables\n", stderr);
            return 1;
        }
        uint8_t len = solve(&state);
        if (len == 255) {
            fputs("no solution found\n", stderr);
            return 1;
        }
        const char *separator = "";
        for (uint8_t i = 0; i < len; ++i) {
            printf("%s%s", separator, move_names[path[i]]);
            separator = " ";
        }
        putchar('\n');
        fprintf(stderr, "nodes=%lu calls=%lu\n", nodes, calls);
        return output_failed();
    }

    if (argc == 2 && !strcmp(argv[1], "--emit-asm")) {
        if (!build_search_tables()) {
            fputs("could not build search tables\n", stderr);
            return 1;
        }
        emit_asm();
        return output_failed();
    }

    if (argc == 2 && !strcmp(argv[1], "--check")) {
        uint8_t *table = build_table(&diameter);
        if (!table || !build_search_tables()) {
            fputs("could not build tables\n", stderr);
            return 1;
        }
        int ok = check_tables(table);
        free(table);
        puts(ok ? "H1 and H2 pass" : "H1 or H2 FAILED");
        return ok ? output_failed() : 1;
    }

    if (argc == 2 && (!strcmp(argv[1], "--worst") || !strcmp(argv[1], "--h3"))) {
        uint8_t *table = build_table(&diameter);
        if (!table || !build_search_tables()) {
            fputs("could not build tables\n", stderr);
            return 1;
        }
        int ok = scan(table, !strcmp(argv[1], "--worst") ? 11 : 0);
        free(table);
        puts(ok ? "all lengths match the exact distance" : "MISMATCH FOUND");
        return ok ? output_failed() : 1;
    }

    if (argc == 2 && !strcmp(argv[1], "--self-test")) {
        if (!self_test()) {
            fputs("self-test failed\n", stderr);
            return 1;
        }
        uint8_t *table = build_table(&diameter);
        if (!table) {
            fputs("could not build complete state table\n", stderr);
            return 1;
        }
        free(table);
        if (diameter != 11) {
            fputs("BFS check failed\n", stderr);
            return 1;
        }
        puts("3674160 states; diameter 11");
        return output_failed();
    }
    if (argc != 2 || !parse_state(argv[1], &state)) {
        /* C99 5.1.2.2.1 lets argv[0] be null when argc is 0. */
        fprintf(stderr, "usage: %s PPPPPPPOOOOOOO\n",
                argc > 0 && argv[0] ? argv[0] : "solver");
        return 2;
    }
    uint8_t *table = build_table(&diameter);
    if (!table) {
        fputs("could not build complete state table\n", stderr);
        return 1;
    }
    const char *separator = "";
    for (uint32_t rank = rank_state(&state); rank; rank = rank_state(&state)) {
        uint8_t move = table[rank];
        printf("%s%s", separator, move_names[move]);
        separator = " ";
        state = apply_move(state, move);
    }
    putchar('\n');
    free(table);
    return output_failed();
}
