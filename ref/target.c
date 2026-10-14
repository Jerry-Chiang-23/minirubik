/* target.c -- the target-side C of minirubik (the Stage 3 algorithm), made
 * freestanding so that riscv64-unknown-elf-gcc -O2 -march=rv32i can compile it.
 * Same work as the assembly: parse, validate, rank, IDA*, then print the moves
 * and re-apply them to the root ranks as a check.  No libc, no M extension.   */
#include <stdint.h>

enum { CUBIES = 7 };
typedef struct { uint8_t p[CUBIES], o[CUBIES]; } state_t;

extern const uint16_t tp0[], tp1[], tp2[], to0[], to1[], to2[];
extern const uint8_t pdb_p[], pdb_o[];
static const uint16_t *const tp[3] = {tp0, tp1, tp2};
static const uint16_t *const to[3] = {to0, to1, to2};

char input[15] = "21345671111111";
static uint8_t path[12];

static int valid(const state_t *state)
{
    uint8_t sum = 0;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        if (state->p[i] >= CUBIES || state->o[i] >= 3)
            return 0;
        for (uint8_t j = 0; j < i; ++j)
            if (state->p[j] == state->p[i])
                return 0;
        sum = (uint8_t) (sum + state->o[i]);
    }
    return (0x1249u >> sum) & 1u;
}

static int parse_state(const char *in, state_t *state)
{
    for (int i = 0; i < 7; ++i) {
        if (in[i] < '1' || in[i] > '7')
            return 0;
        state->p[i] = (uint8_t) (in[i] - '1');
    }
    for (int i = 0; i < 7; ++i) {
        if (in[7 + i] < '1' || in[7 + i] > '3')
            return 0;
        state->o[i] = (uint8_t) (in[7 + i] - '1');
    }
    return in[14] == '\0' && valid(state);
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
        case 1: p = (uint16_t) ((p << 2) + (p << 1)); break;
        case 2: p = (uint16_t) ((p << 2) + p); break;
        case 3: p = (uint16_t) (p << 2); break;
        case 4: p = (uint16_t) ((p << 1) + p); break;
        case 5: p = (uint16_t) (p << 1); break;
        default: break;
        }
        p = (uint16_t) (p + smaller);
    }
    return p;
}

static uint16_t rank_o(const state_t *state)
{
    uint16_t o = 0;
    for (uint8_t i = 0; i < 6; ++i)
        o = (uint16_t) ((o << 1) + o + state->o[i]);
    return o;
}

static uint8_t h(uint16_t p, uint16_t o)
{
    uint8_t hp = pdb_p[p], ho = pdb_o[o];
    return hp > ho ? hp : ho;
}

static uint16_t sp[12], so[12];
static uint16_t cp[12], co[12];
static uint8_t face_at[12], turn_at[12], last_at[12];

static int search(uint16_t p, uint16_t o, uint8_t bound)
{
    uint8_t g = 0;
    sp[0] = cp[0] = p;
    so[0] = co[0] = o;
    face_at[0] = 0;
    turn_at[0] = 0;
    last_at[0] = 255;
    for (;;) {
        if (turn_at[g] == 3) {
            ++face_at[g];
            turn_at[g] = 0;
            cp[g] = sp[g];
            co[g] = so[g];
        }
        if (face_at[g] == last_at[g]) {
            ++face_at[g];
            turn_at[g] = 0;
            cp[g] = sp[g];
            co[g] = so[g];
        }
        if (face_at[g] == 3) {
            if (g == 0)
                return 0;
            --g;
            continue;
        }
        uint8_t face = face_at[g];
        uint8_t turn = turn_at[g]++;
        cp[g] = tp[face][cp[g]];
        co[g] = to[face][co[g]];
        uint8_t hh = h(cp[g], co[g]);
        if (g + 1 + hh > bound)
            continue;
        path[g] = (uint8_t) ((face << 2) | turn);
        if (hh == 0)
            return 1;
        sp[g + 1] = cp[g + 1] = cp[g];
        so[g + 1] = co[g + 1] = co[g];
        face_at[g + 1] = 0;
        turn_at[g + 1] = 0;
        last_at[g + 1] = face;
        ++g;
    }
}

static uint8_t solve(uint16_t p, uint16_t o)
{
    uint8_t h0 = h(p, o);
    for (uint8_t bound = h0; bound <= 11; ++bound)
        if (h0 == 0 || search(p, o, bound))
            return bound;
    return 255;
}

static void put(char c)
{
    register int a0 __asm__("a0") = c;
    register int a7 __asm__("a7") = 11;
    __asm__ volatile("ecall" : "+r"(a0) : "r"(a7) : "memory");
}

static void put_int(unsigned v)          /* ecall 1: print integer, as the assembly does */
{
    register int a0 __asm__("a0") = (int) v;
    register int a7 __asm__("a7") = 1;
    __asm__ volatile("ecall" : "+r"(a0) : "r"(a7) : "memory");
}

int main(void)
{
    state_t state;
    if (!parse_state(input, &state))
        return 2;
    uint16_t p0 = rank_p(&state), o0 = rank_o(&state);
    uint8_t len = solve(p0, o0);
    uint16_t p = p0, o = o0;
    for (uint8_t i = 0; i < len; ++i) {
        uint8_t face = path[i] >> 2, turn = path[i] & 3;
        put(face == 0 ? 'R' : face == 1 ? 'B' : 'D');
        if (turn == 1) put('2');
        else if (turn == 2) put('\'');
        for (uint8_t k = 0; k <= turn; ++k) {
            p = tp[face][p];
            o = to[face][o];
        }
        put(' ');
    }
    put('\n');
    put_int(len);
    put('\n');
    return (p | o) != 0;
}
