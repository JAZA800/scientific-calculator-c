/*
 * Scientific Calculator in C
 * ===========================
 *
 * A menu-driven command-line scientific calculator featuring:
 *   - A recursive-descent expression parser (functions, constants, implicit
 *     multiplication, right-associative powers, unary minus, "ans")
 *   - Symbolic differentiation (product/quotient/chain/general power rule)
 *   - Symbolic integration (linearity, substitution for linear arguments,
 *     a table of elementary antiderivatives, integration by parts)
 *   - Adaptive numerical definite integration, graphing, bisection root solver
 *   - Calculation history, memory, precision controls, user-defined variables
 *   - A separate complex-number expression mode
 *   - Trigonometric, inverse trigonometric, logarithmic and exponential
 *     functions implemented from scratch (series expansions with argument
 *     range reduction) and validated against <math.h> by a built-in self-test
 *
 * Build : gcc -std=c11 -O2 -Wall -Wextra calculator.c -o calculator -lm
 * Run   : ./calculator            (interactive)
 *         ./calculator --test     (run the built-in self-test)
 */

#include <ctype.h>
#include <errno.h>
#include <math.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <complex.h>

#define VERSION "3.0"
#define MAX_INPUT 256
#define MAX_TERMS 64
#define MAX_DEPTH 6

#define PI 3.14159265358979323846
#define MY_E 2.71828182845904523536
#define LN2 0.693147180559945309417
#define LN2_HI 6.93147180369123816490e-01
#define LN2_LO 1.90821492927058770002e-10
#define LN10 2.302585092994045684018

/* ======================================================================== */
/*  Global state                                                            */
/* ======================================================================== */

static bool g_deg = true; /* angle mode: true = degrees, false = radians   */
static bool g_eof = false; /* set when standard input is exhausted          */
static double g_ans = 0.0; /* result of the last expression ("ans")         */
static bool g_has_ans = false;
static double g_memory = 0.0;
static int g_precision = 6;
#define HISTORY_CAP 100
typedef struct { char expr[MAX_INPUT]; double value; } HistoryItem;
static HistoryItem g_history[HISTORY_CAP];
static size_t g_history_count = 0;
#define VAR_CAP 26
typedef struct { bool set; double value; } UserVar;
static UserVar g_vars[VAR_CAP];

static void history_add(const char *expr, double value)
{
    if (g_history_count == HISTORY_CAP) {
        memmove(g_history, g_history + 1, (HISTORY_CAP - 1) * sizeof g_history[0]);
        g_history_count--;
    }
    snprintf(g_history[g_history_count].expr, sizeof g_history[0].expr, "%s", expr);
    g_history[g_history_count++].value = value;
}

static void action_history(void)
{
    if (!g_history_count) { puts("  No calculations in history yet."); return; }
    puts("  Calculation history:");
    for (size_t i = 0; i < g_history_count; ++i)
        printf("  %zu) %s = %.*f\n", i + 1, g_history[i].expr, g_precision, g_history[i].value);
    puts("  Enter :recall N at the expression prompt to reuse an expression.");
}


/* ======================================================================== */
/*  1. Robust input helpers                                                 */
/* ======================================================================== */

/* Read one line (without the newline). Oversized lines are discarded. */
static bool read_line(const char *prompt, char *buf, size_t size)
{
    if (prompt) {
        printf("%s", prompt);
        fflush(stdout);
    }
    if (!fgets(buf, (int)size, stdin)) {
        g_eof = true;
        return false;
    }
    size_t len = strlen(buf);
    if (len > 0 && buf[len - 1] == '\n') {
        buf[len - 1] = '\0';
    } else {
        int c;
        while ((c = getchar()) != '\n' && c != EOF) {
        }
    }
    return true;
}

static bool is_blank(const char *s)
{
    while (*s) {
        if (!isspace((unsigned char)*s))
            return false;
        s++;
    }
    return true;
}

/* Read an integer in [lo, hi], re-prompting until the input is valid. */
static bool read_int(const char *prompt, long lo, long hi, long *out)
{
    char buf[MAX_INPUT];
    for (;;) {
        if (!read_line(prompt, buf, sizeof buf))
            return false;
        char *end;
        errno = 0;
        long v = strtol(buf, &end, 10);
        while (isspace((unsigned char)*end))
            end++;
        if (end != buf && *end == '\0' && errno != ERANGE && v >= lo && v <= hi) {
            *out = v;
            return true;
        }
        printf("  Please enter a whole number between %ld and %ld.\n", lo, hi);
    }
}

/* ======================================================================== */
/*  2. Numerical functions implemented from scratch                         */
/* ======================================================================== */

/* Reduce an angle (radians) to [-pi, pi]. */
static double reduce_angle(double x)
{
    x = fmod(x, 2.0 * PI);
    if (x > PI)
        x -= 2.0 * PI;
    else if (x < -PI)
        x += 2.0 * PI;
    return x;
}

/* sin(x) = x - x^3/3! + x^5/5! - ...   (x in radians) */
static double my_sin(double x)
{
    if (!isfinite(x))
        return NAN;
    x = reduce_angle(x);
    double x2 = x * x, term = x, sum = x;
    for (int n = 1; n < 40 && fabs(term) > 1e-18; n++) {
        term *= -x2 / ((2.0 * n) * (2.0 * n + 1.0));
        sum += term;
    }
    return sum;
}

/* cos(x) = 1 - x^2/2! + x^4/4! - ...   (x in radians) */
static double my_cos(double x)
{
    if (!isfinite(x))
        return NAN;
    x = reduce_angle(x);
    double x2 = x * x, term = 1.0, sum = 1.0;
    for (int n = 1; n < 40 && fabs(term) > 1e-18; n++) {
        term *= -x2 / ((2.0 * n - 1.0) * (2.0 * n));
        sum += term;
    }
    return sum;
}

#define POLE_EPS 1e-12
static double my_tan(double x)
{
    double c = my_cos(x);
    return fabs(c) < POLE_EPS ? NAN : my_sin(x) / c;
}
static double my_cot(double x)
{
    double s = my_sin(x);
    return fabs(s) < POLE_EPS ? NAN : my_cos(x) / s;
}
static double my_sec(double x)
{
    double c = my_cos(x);
    return fabs(c) < POLE_EPS ? NAN : 1.0 / c;
}
static double my_csc(double x)
{
    double s = my_sin(x);
    return fabs(s) < POLE_EPS ? NAN : 1.0 / s;
}

/* exp(x): write x = k*ln2 + r with |r| <= ln2/2, sum the series for e^r and
 * scale by 2^k. */
static double my_exp(double x)
{
    if (isnan(x))
        return NAN;
    if (x > 709.78)
        return INFINITY;
    if (x < -745.0)
        return 0.0;
    double k = floor(x / LN2 + 0.5);
    double r = (x - k * LN2_HI) - k * LN2_LO;
    double term = 1.0, sum = 1.0;
    for (int n = 1; n < 40; n++) {
        term *= r / n;
        sum += term;
        if (fabs(term) < 1e-18)
            break;
    }
    return ldexp(sum, (int)k);
}

/* ln(x): write x = m * 2^e with m in [sqrt(1/2), sqrt(2)), then
 * ln(m) = 2 * (z + z^3/3 + z^5/5 + ...), z = (m-1)/(m+1). */
static double my_ln(double x)
{
    if (isnan(x) || x < 0.0)
        return NAN;
    if (x == 0.0)
        return -INFINITY;
    if (isinf(x))
        return INFINITY;
    int e;
    double m = frexp(x, &e); /* m in [0.5, 1) */
    m *= 2.0;
    e -= 1; /* m in [1, 2)   */
    if (m > 1.41421356237309504880) {
        m /= 2.0;
        e += 1;
    }
    double z = (m - 1.0) / (m + 1.0), z2 = z * z, term = z, sum = z;
    for (int n = 1; n < 60 && fabs(term) > 1e-18; n++) {
        term *= z2;
        sum += term / (2.0 * n + 1.0);
    }
    return 2.0 * sum + e * LN2;
}

static double my_log10(double x) { return my_ln(x) / LN10; }

/* arctan series, valid and fast for small |t|. */
static double atan_series(double t)
{
    double t2 = t * t, term = t, sum = t;
    for (int n = 1; n < 60 && fabs(term) > 1e-18; n++) {
        term *= -t2;
        sum += term / (2.0 * n + 1.0);
    }
    return sum;
}

/* atan(x): fold |x| into [0,1] using atan(x) = pi/2 - atan(1/x), then apply
 * the half-angle identity twice so the series argument is below 0.2. */
static double my_atan(double x)
{
    if (isnan(x))
        return NAN;
    if (isinf(x))
        return x > 0 ? PI / 2 : -PI / 2;
    double sign = x < 0 ? -1.0 : 1.0, ax = fabs(x);
    bool inv = ax > 1.0;
    if (inv)
        ax = 1.0 / ax;
    double t = ax / (1.0 + sqrt(1.0 + ax * ax));
    t = t / (1.0 + sqrt(1.0 + t * t));
    double r = 4.0 * atan_series(t);
    if (inv)
        r = PI / 2 - r;
    return sign * r;
}

static double my_asin(double x)
{
    if (isnan(x) || x < -1.0 || x > 1.0)
        return NAN;
    if (x == 1.0)
        return PI / 2;
    if (x == -1.0)
        return -PI / 2;
    return my_atan(x / sqrt(1.0 - x * x));
}

static double my_acos(double x)
{
    if (isnan(x) || x < -1.0 || x > 1.0)
        return NAN;
    if (x == -1.0)
        return PI;
    return 2.0 * my_atan(sqrt((1.0 - x) / (1.0 + x)));
}

static double my_acot(double x) { return PI / 2 - my_atan(x); } /* range (0, pi) */
static double my_asec(double x) { return fabs(x) < 1.0 ? NAN : my_acos(1.0 / x); }
static double my_acsc(double x) { return fabs(x) < 1.0 ? NAN : my_asin(1.0 / x); }

static double deg_to_rad(double d) { return d * (PI / 180.0); }
static double rad_to_deg(double r) { return r * (180.0 / PI); }

/* ======================================================================== */
/*  3. Expression tree                                                      */
/* ======================================================================== */

typedef enum {
    N_CONST, N_VAR,
    N_ADD, N_SUB, N_MUL, N_DIV, N_POW, N_NEG,
    /* ---- everything below is a one-argument function ---- */
    N_SIN, N_COS, N_TAN, N_SEC, N_CSC, N_COT,
    N_ASIN, N_ACOS, N_ATAN, N_ACOT, N_ASEC, N_ACSC,
    N_LN, N_LOG10, N_EXP, N_SQRT, N_ABS
} NodeType;

#define IS_FUNC(t) ((t) >= N_SIN)

typedef struct Node {
    NodeType type;
    double value; /* N_CONST only */
    struct Node *left;
    struct Node *right; /* NULL for unary nodes */
} Node;

typedef struct {
    const char *name;
    NodeType type;
} FuncInfo;

/* The first entry for a given type is the name used when printing. */
static const FuncInfo FUNCS[] = {
    {"sin", N_SIN},    {"cos", N_COS},     {"tan", N_TAN},     {"sec", N_SEC},
    {"csc", N_CSC},    {"cosec", N_CSC},   {"cot", N_COT},     {"asin", N_ASIN},
    {"acos", N_ACOS},  {"atan", N_ATAN},   {"acot", N_ACOT},   {"asec", N_ASEC},
    {"acsc", N_ACSC},  {"acosec", N_ACSC}, {"ln", N_LN},       {"log", N_LOG10},
    {"exp", N_EXP},    {"sqrt", N_SQRT},   {"abs", N_ABS},
};
#define NUM_FUNCS (sizeof FUNCS / sizeof FUNCS[0])

static const char *func_name(NodeType t)
{
    for (size_t i = 0; i < NUM_FUNCS; i++)
        if (FUNCS[i].type == t)
            return FUNCS[i].name;
    return "?";
}

static Node *node_new(NodeType type, double value, Node *l, Node *r)
{
    Node *n = malloc(sizeof *n);
    if (!n) {
        fprintf(stderr, "Fatal error: out of memory\n");
        exit(EXIT_FAILURE);
    }
    n->type = type;
    n->value = value;
    n->left = l;
    n->right = r;
    return n;
}

/* Short constructors. They take ownership of their child arguments. */
static Node *num(double v) { return node_new(N_CONST, v == 0.0 ? 0.0 : v, NULL, NULL); }
static Node *var(void) { return node_new(N_VAR, 0.0, NULL, NULL); }
static Node *un(NodeType t, Node *a) { return node_new(t, 0.0, a, NULL); }
static Node *bin(NodeType t, Node *a, Node *b) { return node_new(t, 0.0, a, b); }

static Node *cp(const Node *n)
{
    return n ? node_new(n->type, n->value, cp(n->left), cp(n->right)) : NULL;
}

static void free_node(Node *n)
{
    if (!n)
        return;
    free_node(n->left);
    free_node(n->right);
    free(n);
}

static bool has_var(const Node *n)
{
    return n && (n->type == N_VAR || has_var(n->left) || has_var(n->right));
}

static bool node_equal(const Node *a, const Node *b)
{
    if (!a || !b)
        return a == b;
    if (a->type != b->type)
        return false;
    if (a->type == N_CONST)
        return fabs(a->value - b->value) <= 1e-12 * fmax(1.0, fabs(a->value));
    return node_equal(a->left, b->left) && node_equal(a->right, b->right);
}

static bool is_c(const Node *n, double v) { return n->type == N_CONST && n->value == v; }

/* ======================================================================== */
/*  4. Evaluation                                                           */
/* ======================================================================== */

static double to_rad(double v, bool deg) { return deg ? deg_to_rad(v) : v; }
static double from_rad(double v, bool deg) { return deg ? rad_to_deg(v) : v; }

/* Evaluate the tree at x. 'deg' selects the unit for trig functions. */
static double eval(const Node *n, double x, bool deg)
{
    double a = n->left ? eval(n->left, x, deg) : 0.0;
    double b = n->right ? eval(n->right, x, deg) : 0.0;
    switch (n->type) {
    case N_CONST: return n->value;
    case N_VAR: return x;
    case N_ADD: return a + b;
    case N_SUB: return a - b;
    case N_MUL: return a * b;
    case N_DIV: return a / b;
    case N_POW: return pow(a, b);
    case N_NEG: return -a;
    case N_SIN: return my_sin(to_rad(a, deg));
    case N_COS: return my_cos(to_rad(a, deg));
    case N_TAN: return my_tan(to_rad(a, deg));
    case N_SEC: return my_sec(to_rad(a, deg));
    case N_CSC: return my_csc(to_rad(a, deg));
    case N_COT: return my_cot(to_rad(a, deg));
    case N_ASIN: return from_rad(my_asin(a), deg);
    case N_ACOS: return from_rad(my_acos(a), deg);
    case N_ATAN: return from_rad(my_atan(a), deg);
    case N_ACOT: return from_rad(my_acot(a), deg);
    case N_ASEC: return from_rad(my_asec(a), deg);
    case N_ACSC: return from_rad(my_acsc(a), deg);
    case N_LN: return my_ln(a);
    case N_LOG10: return my_log10(a);
    case N_EXP: return my_exp(a);
    case N_SQRT: return a < 0.0 ? NAN : sqrt(a);
    case N_ABS: return fabs(a);
    }
    return NAN;
}

static const char *math_error_message(const Node *n)
{
    if (!n) return NULL;
    const char *child = math_error_message(n->left);
    if (child) return child;
    child = math_error_message(n->right);
    if (child) return child;
    double a = n->left ? eval(n->left, 0.0, g_deg) : 0.0;
    double b = n->right ? eval(n->right, 0.0, g_deg) : 0.0;
    switch (n->type) {
    case N_DIV: if (b == 0.0) return "Division by zero: denominator evaluates to zero."; break;
    case N_LN: if (a <= 0.0) return "Domain error: ln(x) requires x > 0."; break;
    case N_LOG10: if (a <= 0.0) return "Domain error: log(x) requires x > 0."; break;
    case N_SQRT: if (a < 0.0) return "Domain error: sqrt(x) requires x >= 0 in real mode."; break;
    case N_ASIN: case N_ACOS: if (a < -1.0 || a > 1.0) return "Domain error: asin/acos require an argument in [-1, 1]."; break;
    case N_ASEC: case N_ACSC: if (fabs(a) < 1.0) return "Domain error: asec/acsc require |x| >= 1."; break;
    case N_POW: if (a < 0.0 && fabs(b - nearbyint(b)) > 1e-12) return "Domain error: a negative base cannot have a non-integer real exponent."; break;
    default: break;
    }
    return NULL;
}

/* ======================================================================== */
/*  5. Parser (recursive descent)                                           */
/* ======================================================================== */
/*
 *   expr    := term (('+' | '-') term)*
 *   term    := unary (('*' | '/') unary | implicit-multiplication)*
 *   unary   := ('-' | '+') unary | power
 *   power   := atom ('^' unary)?                 (right associative)
 *   atom    := number | '(' expr ')' | function '(' expr ')' | constant | x
 */

typedef struct {
    const char *s;
    size_t pos;
    bool allow_var;
    char err[96];
} Parser;

static void perr(Parser *p, const char *fmt, ...)
{
    if (p->err[0])
        return; /* keep the first error */
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(p->err, sizeof p->err, fmt, ap);
    va_end(ap);
}

static int peekc(Parser *p)
{
    while (isspace((unsigned char)p->s[p->pos]))
        p->pos++;
    return (unsigned char)p->s[p->pos];
}

static Node *parse_expr(Parser *p);

static Node *parse_number(Parser *p)
{
    const char *s = p->s + p->pos;
    size_t i = 0;
    while (isdigit((unsigned char)s[i]))
        i++;
    if (s[i] == '.') {
        i++;
        while (isdigit((unsigned char)s[i]))
            i++;
    }
    if (s[i] == 'e' || s[i] == 'E') { /* exponent only if digits follow */
        size_t j = i + 1;
        if (s[j] == '+' || s[j] == '-')
            j++;
        if (isdigit((unsigned char)s[j])) {
            while (isdigit((unsigned char)s[j]))
                j++;
            i = j;
        }
    }
    char buf[64];
    if (i == 0 || (i == 1 && s[0] == '.')) {
        perr(p, "invalid number");
        return NULL;
    }
    if (i >= sizeof buf) {
        perr(p, "number is too long");
        return NULL;
    }
    memcpy(buf, s, i);
    buf[i] = '\0';
    double v = strtod(buf, NULL);
    if (!isfinite(v)) {
        perr(p, "number out of range");
        return NULL;
    }
    p->pos += i;
    return num(v);
}

static Node *parse_atom(Parser *p)
{
    int c = peekc(p);

    if (isdigit(c) || c == '.')
        return parse_number(p);

    if (c == '(') {
        p->pos++;
        Node *e = parse_expr(p);
        if (!e)
            return NULL;
        if (peekc(p) != ')') {
            perr(p, "missing closing ')'");
            free_node(e);
            return NULL;
        }
        p->pos++;
        return e;
    }

    if (isalpha(c)) {
        char name[16];
        size_t len = 0;
        while (isalpha((unsigned char)p->s[p->pos])) {
            if (len < sizeof name - 1)
                name[len++] = (char)tolower((unsigned char)p->s[p->pos]);
            p->pos++;
        }
        name[len] = '\0';

        for (size_t i = 0; i < NUM_FUNCS; i++) {
            if (strcmp(name, FUNCS[i].name) != 0)
                continue;
            if (peekc(p) != '(') {
                perr(p, "function '%s' needs an argument in parentheses", name);
                return NULL;
            }
            p->pos++;
            Node *arg = parse_expr(p);
            if (!arg)
                return NULL;
            if (peekc(p) != ')') {
                perr(p, "missing closing ')' after %s(...", name);
                free_node(arg);
                return NULL;
            }
            p->pos++;
            return un(FUNCS[i].type, arg);
        }
        if (strcmp(name, "x") == 0) {
            if (!p->allow_var) {
                perr(p, "variable 'x' is not allowed here");
                return NULL;
            }
            return var();
        }
        if (strcmp(name, "pi") == 0)
            return num(PI);
        if (strcmp(name, "e") == 0)
            return num(MY_E);
        if (strcmp(name, "ans") == 0) {
            if (!g_has_ans) {
                perr(p, "no previous result stored in 'ans'");
                return NULL;
            }
            return num(g_ans);
        }
        if (len == 1 && name[0] >= 'a' && name[0] <= 'z' && g_vars[name[0] - 'a'].set)
            return num(g_vars[name[0] - 'a'].value);
        perr(p, "unknown name '%s' (define a variable with name=value)", name);
        return NULL;
    }

    if (c == '\0')
        perr(p, "expression ended unexpectedly");
    else
        perr(p, "unexpected character '%c'", c);
    return NULL;
}

static Node *parse_unary(Parser *p);

static Node *parse_power(Parser *p)
{
    Node *base = parse_atom(p);
    if (!base)
        return NULL;
    if (peekc(p) == '^') {
        p->pos++;
        Node *ex = parse_unary(p);
        if (!ex) {
            free_node(base);
            return NULL;
        }
        return bin(N_POW, base, ex);
    }
    return base;
}

static Node *parse_unary(Parser *p)
{
    int c = peekc(p);
    if (c == '-' || c == '+') {
        p->pos++;
        Node *operand = parse_unary(p);
        if (!operand)
            return NULL;
        return c == '-' ? un(N_NEG, operand) : operand;
    }
    return parse_power(p);
}

static Node *parse_term(Parser *p)
{
    Node *node = parse_unary(p);
    while (node) {
        int c = peekc(p);
        NodeType t = N_MUL;
        if (c == '*' || c == '/') {
            t = c == '*' ? N_MUL : N_DIV;
            p->pos++;
        } else if (!(isalpha(c) || c == '(')) {
            break; /* otherwise: implicit multiplication, e.g. 2x, 3(x+1) */
        }
        Node *rhs = parse_unary(p);
        if (!rhs) {
            free_node(node);
            return NULL;
        }
        node = bin(t, node, rhs);
    }
    return node;
}

static Node *parse_expr(Parser *p)
{
    Node *node = parse_term(p);
    while (node) {
        int c = peekc(p);
        if (c != '+' && c != '-')
            break;
        p->pos++;
        Node *rhs = parse_term(p);
        if (!rhs) {
            free_node(node);
            return NULL;
        }
        node = bin(c == '+' ? N_ADD : N_SUB, node, rhs);
    }
    return node;
}

/* Parse a whole string. On failure returns NULL and fills err. */
static Node *parse_string(const char *s, bool allow_var, char *err, size_t errsize)
{
    Parser p = {s, 0, allow_var, {0}};
    Node *tree = NULL;
    if (peekc(&p) == '\0') {
        perr(&p, "empty expression");
    } else {
        tree = parse_expr(&p);
        if (tree && peekc(&p) != '\0') {
            perr(&p, "unexpected character '%c'", p.s[p.pos]);
            free_node(tree);
            tree = NULL;
        }
    }
    if (!tree)
        snprintf(err, errsize, "%s", p.err);
    return tree;
}

/* Evaluate a constant expression such as "pi/4" or "2^10". */
static bool eval_constant_string(const char *s, double *out)
{
    char err[96];
    Node *t = parse_string(s, false, err, sizeof err);
    if (!t)
        return false;
    double v = eval(t, 0.0, g_deg);
    free_node(t);
    if (!isfinite(v))
        return false;
    *out = v;
    return true;
}

typedef enum { IN_OK, IN_BLANK, IN_EOF } InStatus;

/* Read a number; expressions such as "pi/2" or "sqrt(2)" are accepted. */
static InStatus read_number(const char *prompt, double *out, bool allow_blank)
{
    char buf[MAX_INPUT];
    for (;;) {
        if (!read_line(prompt, buf, sizeof buf))
            return IN_EOF;
        if (allow_blank && is_blank(buf))
            return IN_BLANK;
        if (eval_constant_string(buf, out))
            return IN_OK;
        printf("  Invalid number, please try again.\n");
    }
}

static bool read_double(const char *prompt, double *out)
{
    return read_number(prompt, out, false) == IN_OK;
}

/* ======================================================================== */
/*  6. Printing                                                             */
/* ======================================================================== */

static int node_prec(const Node *n)
{
    switch (n->type) {
    case N_ADD:
    case N_SUB: return 1;
    case N_MUL:
    case N_DIV: return 2;
    case N_NEG: return 3;
    case N_POW: return 4;
    case N_CONST: return n->value < 0.0 ? 3 : 5;
    default: return 5;
    }
}

/* ctx is the precedence of the surrounding context; parentheses are added
 * only where they are required. */
static void print_node(const Node *n, int ctx)
{
    bool paren = node_prec(n) < ctx;
    if (paren)
        putchar('(');
    switch (n->type) {
    case N_CONST: printf("%.10g", n->value); break;
    case N_VAR: putchar('x'); break;
    case N_ADD:
        print_node(n->left, 1);
        printf(" + ");
        print_node(n->right, 1);
        break;
    case N_SUB:
        print_node(n->left, 1);
        printf(" - ");
        print_node(n->right, 2);
        break;
    case N_MUL:
        print_node(n->left, 2);
        putchar('*');
        print_node(n->right, n->right->type == N_MUL ? 2 : 4);
        break;
    case N_DIV:
        print_node(n->left, 2);
        putchar('/');
        print_node(n->right, 4);
        break;
    case N_NEG:
        putchar('-');
        print_node(n->left, 2);
        break;
    case N_POW:
        print_node(n->left, 5);
        putchar('^');
        print_node(n->right, 4);
        break;
    default:
        printf("%s(", func_name(n->type));
        print_node(n->left, 0);
        putchar(')');
        break;
    }
    if (paren)
        putchar(')');
}

/* ======================================================================== */
/*  7. Algebraic simplifier                                                 */
/* ======================================================================== */

static Node *take_left(Node *n)
{
    Node *c = n->left;
    n->left = NULL;
    free_node(n);
    return c;
}
static Node *take_right(Node *n)
{
    Node *c = n->right;
    n->right = NULL;
    free_node(n);
    return c;
}
static void split(Node *n, Node **a, Node **b)
{
    *a = n->left;
    *b = n->right;
    n->left = n->right = NULL;
    free_node(n);
}

/* View n as base^exp with a constant exponent (exp = 1 for plain nodes). */
static void base_exp(const Node *n, const Node **base, double *ex)
{
    if (n->type == N_POW && n->right->type == N_CONST) {
        *base = n->left;
        *ex = n->right->value;
    } else {
        *base = n;
        *ex = 1.0;
    }
}

static bool is_integral_value(double v) { return fabs(v - round(v)) < 1e-12; }

/* ---- sums: flatten, merge like terms, rebuild ---- */

typedef struct {
    double coef;
    const Node *rest; /* NULL means the constant 1 */
} Term;

static void term_split(const Node *t, double *coef, const Node **rest)
{
    double c = 1.0;
    for (;;) {
        if (t->type == N_NEG) {
            c = -c;
            t = t->left;
        } else if (t->type == N_MUL && t->left->type == N_CONST) {
            c *= t->left->value;
            t = t->right;
        } else if (t->type == N_DIV && t->right->type == N_CONST && t->right->value != 0.0) {
            c /= t->right->value;
            t = t->left;
        } else {
            break;
        }
    }
    if (t->type == N_CONST) {
        c *= t->value;
        t = NULL;
    }
    *coef = c;
    *rest = t;
}

static bool collect_terms(const Node *n, double sign, Term *terms, int *cnt)
{
    if (n->type == N_ADD)
        return collect_terms(n->left, sign, terms, cnt) && collect_terms(n->right, sign, terms, cnt);
    if (n->type == N_SUB)
        return collect_terms(n->left, sign, terms, cnt) && collect_terms(n->right, -sign, terms, cnt);

    double c;
    const Node *rest;
    term_split(n, &c, &rest);
    for (int i = 0; i < *cnt; i++) {
        bool same = (!terms[i].rest && !rest) ||
                    (terms[i].rest && rest && node_equal(terms[i].rest, rest));
        if (same) {
            terms[i].coef += sign * c;
            return true;
        }
    }
    if (*cnt >= MAX_TERMS)
        return false;
    terms[*cnt].coef = sign * c;
    terms[*cnt].rest = rest;
    (*cnt)++;
    return true;
}

static bool as_fraction(double v, int *p, int *q)
{
    for (int d = 1; d <= 12; d++) {
        double scaled = v * d;
        if (fabs(scaled - round(scaled)) < 1e-9 * fmax(1.0, fabs(scaled))) {
            *p = (int)round(scaled);
            *q = d;
            return true;
        }
    }
    return false;
}

static Node *term_node(double ac, const Node *rest)
{
    if (!rest)
        return num(ac);
    int p, q;
    if (as_fraction(ac, &p, &q)) {
        Node *base = p == 1 ? cp(rest) : bin(N_MUL, num(p), cp(rest));
        return q == 1 ? base : bin(N_DIV, base, num(q));
    }
    return bin(N_MUL, num(ac), cp(rest));
}

static Node *rebuild_terms(const Term *t, int cnt)
{
    int order[MAX_TERMS], n = 0, start = 0;
    for (int i = 0; i < cnt; i++) {
        if (t[i].coef > 1e-15) {
            start = i;
            break;
        }
    }
    order[n++] = start;
    for (int i = 0; i < cnt; i++)
        if (i != start)
            order[n++] = i;

    Node *acc = NULL;
    for (int k = 0; k < n; k++) {
        const Term *tm = &t[order[k]];
        if (fabs(tm->coef) < 1e-15)
            continue;
        bool neg = tm->coef < 0.0;
        double ac = fabs(tm->coef);
        if (!acc) {
            if (!tm->rest)
                acc = num(tm->coef);
            else
                acc = neg ? un(N_NEG, term_node(ac, tm->rest)) : term_node(ac, tm->rest);
        } else {
            acc = bin(neg ? N_SUB : N_ADD, acc, term_node(ac, tm->rest));
        }
    }
    return acc ? acc : num(0);
}

static Node *rule_sum(NodeType t, Node *l, Node *r)
{
    Term terms[MAX_TERMS];
    int cnt = 0;
    bool ok = collect_terms(l, 1.0, terms, &cnt) &&
              collect_terms(r, t == N_ADD ? 1.0 : -1.0, terms, &cnt);
    Node *res = ok ? rebuild_terms(terms, cnt) : bin(t, cp(l), cp(r));
    free_node(l);
    free_node(r);
    return res;
}

/* ---- products ---- */

static Node *rule_mul(Node *l, Node *r)
{
    if (l->type == N_CONST && r->type == N_CONST) {
        double v = l->value * r->value;
        free_node(l);
        free_node(r);
        return num(v);
    }
    if (is_c(l, 0) || is_c(r, 0)) {
        free_node(l);
        free_node(r);
        return num(0);
    }
    if (is_c(l, 1)) {
        free_node(l);
        return r;
    }
    if (is_c(r, 1)) {
        free_node(r);
        return l;
    }
    if (is_c(l, -1)) {
        free_node(l);
        return un(N_NEG, r);
    }
    if (is_c(r, -1)) {
        free_node(r);
        return un(N_NEG, l);
    }
    if (l->type == N_NEG)
        return un(N_NEG, bin(N_MUL, take_left(l), r));
    if (r->type == N_NEG)
        return un(N_NEG, bin(N_MUL, l, take_left(r)));
    if (l->type == N_DIV) {
        Node *a, *c;
        split(l, &a, &c);
        return bin(N_DIV, bin(N_MUL, a, r), c);
    }
    if (r->type == N_DIV) {
        Node *a, *c;
        split(r, &a, &c);
        return bin(N_DIV, bin(N_MUL, l, a), c);
    }
    if (r->type == N_CONST) /* constants go to the left */
        return bin(N_MUL, r, l);
    if (l->type == N_CONST && r->type == N_MUL && r->left->type == N_CONST) {
        double v = l->value * r->left->value;
        free_node(l);
        return bin(N_MUL, num(v), take_right(r));
    }
    if (l->type == N_MUL && l->left->type == N_CONST) {
        Node *c = l->left;
        l->left = NULL;
        Node *y = take_right(l);
        return bin(N_MUL, c, bin(N_MUL, y, r));
    }
    if (l->type != N_CONST && r->type == N_MUL && r->left->type == N_CONST) {
        Node *c = r->left;
        r->left = NULL;
        Node *y = take_right(r);
        return bin(N_MUL, c, bin(N_MUL, l, y));
    }
    const Node *bl, *br;
    double el, er;
    base_exp(l, &bl, &el);
    base_exp(r, &br, &er);
    if (bl->type != N_CONST && node_equal(bl, br)) {
        Node *b = cp(bl);
        free_node(l);
        free_node(r);
        return bin(N_POW, b, num(el + er));
    }
    return bin(N_MUL, l, r);
}

/* ---- quotients ---- */

static long gcd_long(long a, long b)
{
    while (b) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static Node *rule_div(Node *l, Node *r)
{
    if (r->type == N_CONST && r->value == 0.0)
        return bin(N_DIV, l, r);
    if (l->type == N_CONST && r->type == N_CONST) {
        double v = l->value / r->value;
        int p, q;
        free_node(l);
        free_node(r);
        if (is_integral_value(v))
            return num(round(v));
        if (as_fraction(v, &p, &q))
            return bin(N_DIV, num(p), num(q));
        return num(v);
    }
    if (r->type == N_CONST && r->value < 0.0) {
        double v = -r->value;
        free_node(r);
        return un(N_NEG, bin(N_DIV, l, num(v)));
    }
    if (is_c(r, 1)) {
        free_node(r);
        return l;
    }
    if (is_c(l, 0)) {
        free_node(l);
        free_node(r);
        return num(0);
    }
    if (l->type == N_NEG)
        return un(N_NEG, bin(N_DIV, take_left(l), r));
    if (r->type == N_NEG)
        return un(N_NEG, bin(N_DIV, l, take_left(r)));
    if (node_equal(l, r)) {
        free_node(l);
        free_node(r);
        return num(1);
    }

    /* Cancel common factors when numerator and/or denominator is c*y. */
    double cl = 1.0, cr = 1.0;
    const Node *yl = l, *yr = r;
    if (l->type == N_MUL && l->left->type == N_CONST) {
        cl = l->left->value;
        yl = l->right;
    }
    if (r->type == N_MUL && r->left->type == N_CONST) {
        cr = r->left->value;
        yr = r->right;
    }
    if (yl != l || yr != r) {
        const Node *bl, *br;
        double el, er;
        base_exp(yl, &bl, &el);
        base_exp(yr, &br, &er);
        if (bl->type != N_CONST && node_equal(bl, br)) {
            double e = el - er;
            Node *q = e == 0.0 ? num(1)
                      : e > 0.0 ? bin(N_POW, cp(bl), num(e))
                                : bin(N_DIV, num(1), bin(N_POW, cp(bl), num(-e)));
            free_node(l);
            free_node(r);
            return bin(N_DIV, bin(N_MUL, num(cl), q), num(cr));
        }
        if (yl != l && yr != r && is_integral_value(cl) && is_integral_value(cr)) {
            long g = gcd_long(llround(fabs(cl)), llround(fabs(cr)));
            if (g > 1) {
                Node *y = cp(yl), *z = cp(yr);
                free_node(l);
                free_node(r);
                return bin(N_DIV, bin(N_MUL, num(cl / (double)g), y),
                           bin(N_MUL, num(cr / (double)g), z));
            }
        }
    }

    if (l->type == N_DIV) {
        Node *a, *b;
        split(l, &a, &b);
        return bin(N_DIV, a, bin(N_MUL, b, r));
    }
    if (r->type == N_DIV) {
        Node *a, *b;
        split(r, &a, &b);
        return bin(N_DIV, bin(N_MUL, l, b), a);
    }
    if (r->type == N_CONST && l->type == N_MUL && l->left->type == N_CONST) {
        double q = l->left->value / r->value;
        if (is_integral_value(q)) {
            free_node(r);
            return bin(N_MUL, num(round(q)), take_right(l));
        }
    }
    return bin(N_DIV, l, r);
}

/* ---- powers ---- */

static Node *rule_pow(Node *l, Node *r)
{
    if (is_c(r, 0)) {
        free_node(l);
        free_node(r);
        return num(1);
    }
    if (is_c(r, 1)) {
        free_node(r);
        return l;
    }
    if (is_c(l, 1)) {
        free_node(l);
        free_node(r);
        return num(1);
    }
    if (l->type == N_CONST && r->type == N_CONST) {
        double v = pow(l->value, r->value);
        if (isfinite(v) && is_integral_value(v)) {
            free_node(l);
            free_node(r);
            return num(round(v));
        }
        return bin(N_POW, l, r);
    }
    if (l->type == N_CONST && fabs(l->value - MY_E) < 1e-12) {
        free_node(l);
        return un(N_EXP, r);
    }
    if (is_c(l, 0) && r->type == N_CONST && r->value > 0.0) {
        free_node(l);
        free_node(r);
        return num(0);
    }
    if (l->type == N_POW && l->right->type == N_CONST && r->type == N_CONST &&
        is_integral_value(r->value)) {
        double b = l->right->value, c = r->value;
        free_node(r);
        return bin(N_POW, take_left(l), num(b * c));
    }
    return bin(N_POW, l, r);
}

/* ---- negation and functions ---- */

static Node *rule_func(NodeType t, Node *l)
{
    if (t == N_NEG) {
        if (l->type == N_CONST) {
            double v = -l->value;
            free_node(l);
            return num(v);
        }
        if (l->type == N_NEG)
            return take_left(l);
        return un(N_NEG, l);
    }
    if (t == N_EXP && l->type == N_LN)
        return take_left(l);
    if (t == N_LN && l->type == N_EXP)
        return take_left(l);
    if (t == N_ABS && l->type == N_NEG)
        return un(N_ABS, take_left(l));
    if (l->type == N_CONST) { /* fold only when the result is a whole number */
        Node *tmp = un(t, l);
        double v = eval(tmp, 0.0, false);
        if (isfinite(v) && is_integral_value(v)) {
            free_node(tmp);
            return num(round(v));
        }
        return tmp;
    }
    return un(t, l);
}

static Node *simp_pass(const Node *n)
{
    if (n->type == N_CONST || n->type == N_VAR)
        return cp(n);
    Node *l = simp_pass(n->left);
    Node *r = n->right ? simp_pass(n->right) : NULL;
    switch (n->type) {
    case N_ADD:
    case N_SUB: return rule_sum(n->type, l, r);
    case N_MUL: return rule_mul(l, r);
    case N_DIV: return rule_div(l, r);
    case N_POW: return rule_pow(l, r);
    default: return rule_func(n->type, l);
    }
}

/* Returns a new, simplified tree (repeats until nothing changes). */
static Node *simplify(const Node *n)
{
    Node *cur = cp(n);
    for (int i = 0; i < 30; i++) {
        Node *next = simp_pass(cur);
        bool same = node_equal(cur, next);
        free_node(cur);
        cur = next;
        if (same)
            break;
    }
    return cur;
}

static Node *simplify_owned(Node *n)
{
    Node *s = simplify(n);
    free_node(n);
    return s;
}

/* Presentation only: show x^-n as 1/x^n. The result is never used for
 * further calculus, so it cannot affect correctness. */
static Node *beautify(const Node *n)
{
    if (!n)
        return NULL;
    if (n->type == N_POW && n->right->type == N_CONST && n->right->value < 0.0) {
        double c = -n->right->value;
        Node *base = beautify(n->left);
        return bin(N_DIV, num(1), c == 1.0 ? base : bin(N_POW, base, num(c)));
    }
    Node *l = beautify(n->left);
    Node *r = beautify(n->right);
    return node_new(n->type, n->value, l, r);
}

static void print_pretty(const Node *n)
{
    Node *s = simplify_owned(beautify(n));
    print_node(s, 0);
    free_node(s);
}

static void print_line(const char *label, const Node *n)
{
    printf("  %s", label);
    print_pretty(n);
    putchar('\n');
}

/* ======================================================================== */
/*  8. Symbolic differentiation                                             */
/* ======================================================================== */

static Node *diff(const Node *n)
{
    const Node *l = n->left, *r = n->right;

    switch (n->type) {
    case N_CONST: return num(0);
    case N_VAR: return num(1);
    case N_ADD:
    case N_SUB: return bin(n->type, diff(l), diff(r));
    case N_NEG: return un(N_NEG, diff(l));
    case N_MUL: /* (fg)' = f'g + fg' */
        return bin(N_ADD, bin(N_MUL, diff(l), cp(r)), bin(N_MUL, cp(l), diff(r)));
    case N_DIV: /* (f/g)' = (f'g - fg') / g^2 */
        return bin(N_DIV,
                   bin(N_SUB, bin(N_MUL, diff(l), cp(r)), bin(N_MUL, cp(l), diff(r))),
                   bin(N_POW, cp(r), num(2)));
    case N_POW:
        if (!has_var(r)) /* (u^c)' = c u^(c-1) u' */
            return bin(N_MUL, bin(N_MUL, cp(r), bin(N_POW, cp(l), bin(N_SUB, cp(r), num(1)))), diff(l));
        if (!has_var(l)) /* (c^v)' = c^v ln(c) v' */
            return bin(N_MUL, bin(N_MUL, cp(n), un(N_LN, cp(l))), diff(r));
        /* (u^v)' = u^v (v' ln u + v u'/u) */
        return bin(N_MUL, cp(n),
                   bin(N_ADD, bin(N_MUL, diff(r), un(N_LN, cp(l))),
                       bin(N_DIV, bin(N_MUL, cp(r), diff(l)), cp(l))));
    default: break;
    }

    /* One-argument functions: chain rule with u = argument. */
    const Node *u = l;
    Node *du = diff(l);
    switch (n->type) {
    case N_SIN: return bin(N_MUL, un(N_COS, cp(u)), du);
    case N_COS: return un(N_NEG, bin(N_MUL, un(N_SIN, cp(u)), du));
    case N_TAN: return bin(N_MUL, bin(N_POW, un(N_SEC, cp(u)), num(2)), du);
    case N_SEC: return bin(N_MUL, bin(N_MUL, un(N_SEC, cp(u)), un(N_TAN, cp(u))), du);
    case N_CSC: return un(N_NEG, bin(N_MUL, bin(N_MUL, un(N_CSC, cp(u)), un(N_COT, cp(u))), du));
    case N_COT: return un(N_NEG, bin(N_MUL, bin(N_POW, un(N_CSC, cp(u)), num(2)), du));
    case N_ASIN:
        return bin(N_DIV, du, un(N_SQRT, bin(N_SUB, num(1), bin(N_POW, cp(u), num(2)))));
    case N_ACOS:
        return un(N_NEG, bin(N_DIV, du, un(N_SQRT, bin(N_SUB, num(1), bin(N_POW, cp(u), num(2))))));
    case N_ATAN: return bin(N_DIV, du, bin(N_ADD, num(1), bin(N_POW, cp(u), num(2))));
    case N_ACOT: return un(N_NEG, bin(N_DIV, du, bin(N_ADD, num(1), bin(N_POW, cp(u), num(2)))));
    case N_ASEC:
        return bin(N_DIV, du,
                   bin(N_MUL, un(N_ABS, cp(u)), un(N_SQRT, bin(N_SUB, bin(N_POW, cp(u), num(2)), num(1)))));
    case N_ACSC:
        return un(N_NEG, bin(N_DIV, du,
                             bin(N_MUL, un(N_ABS, cp(u)),
                                 un(N_SQRT, bin(N_SUB, bin(N_POW, cp(u), num(2)), num(1))))));
    case N_LN: return bin(N_DIV, du, cp(u));
    case N_LOG10: return bin(N_DIV, du, bin(N_MUL, cp(u), un(N_LN, num(10))));
    case N_EXP: return bin(N_MUL, un(N_EXP, cp(u)), du);
    case N_SQRT: return bin(N_DIV, du, bin(N_MUL, num(2), un(N_SQRT, cp(u))));
    case N_ABS: return bin(N_DIV, bin(N_MUL, cp(u), du), un(N_ABS, cp(u)));
    default: free_node(du); return num(0);
    }
}

/* ======================================================================== */
/*  9. Symbolic integration                                                 */
/* ======================================================================== */

static Node *integrate(const Node *n, int depth);

/* Is n of the form a*x + b? */
static bool linear_form(const Node *n, double *a, double *b)
{
    if (!has_var(n)) {
        double v = eval(n, 0.0, false);
        if (!isfinite(v))
            return false;
        *a = 0.0;
        *b = v;
        return true;
    }
    double a1, b1, a2, b2;
    switch (n->type) {
    case N_VAR:
        *a = 1.0;
        *b = 0.0;
        return true;
    case N_NEG:
        if (!linear_form(n->left, &a1, &b1))
            return false;
        *a = -a1;
        *b = -b1;
        return true;
    case N_ADD:
    case N_SUB: {
        if (!linear_form(n->left, &a1, &b1) || !linear_form(n->right, &a2, &b2))
            return false;
        double s = n->type == N_ADD ? 1.0 : -1.0;
        *a = a1 + s * a2;
        *b = b1 + s * b2;
        return true;
    }
    case N_MUL:
        if (!linear_form(n->left, &a1, &b1) || !linear_form(n->right, &a2, &b2))
            return false;
        if (a1 != 0.0 && a2 != 0.0)
            return false;
        *a = a1 * b2 + a2 * b1;
        *b = b1 * b2;
        return true;
    case N_DIV:
        if (!linear_form(n->left, &a1, &b1) || !linear_form(n->right, &a2, &b2))
            return false;
        if (a2 != 0.0 || b2 == 0.0)
            return false;
        *a = a1 / b2;
        *b = b1 / b2;
        return true;
    default: return false;
    }
}

static bool is_poly(const Node *n)
{
    switch (n->type) {
    case N_CONST:
    case N_VAR: return true;
    case N_NEG: return is_poly(n->left);
    case N_ADD:
    case N_SUB:
    case N_MUL: return is_poly(n->left) && is_poly(n->right);
    case N_DIV: return is_poly(n->left) && n->right->type == N_CONST;
    case N_POW:
        return is_poly(n->left) && n->right->type == N_CONST && n->right->value >= 0.0 &&
               is_integral_value(n->right->value);
    default: return false;
    }
}

/* Antiderivative F(u) of f(u), for the one-argument function f. */
static Node *antiderivative_table(NodeType f, const Node *u)
{
    switch (f) {
    case N_SIN: return un(N_NEG, un(N_COS, cp(u)));
    case N_COS: return un(N_SIN, cp(u));
    case N_TAN: return un(N_NEG, un(N_LN, un(N_ABS, un(N_COS, cp(u)))));
    case N_COT: return un(N_LN, un(N_ABS, un(N_SIN, cp(u))));
    case N_SEC: return un(N_LN, un(N_ABS, bin(N_ADD, un(N_SEC, cp(u)), un(N_TAN, cp(u)))));
    case N_CSC:
        return un(N_NEG, un(N_LN, un(N_ABS, bin(N_ADD, un(N_CSC, cp(u)), un(N_COT, cp(u))))));
    case N_EXP: return un(N_EXP, cp(u));
    case N_LN: return bin(N_SUB, bin(N_MUL, cp(u), un(N_LN, cp(u))), cp(u));
    case N_LOG10:
        return bin(N_DIV, bin(N_SUB, bin(N_MUL, cp(u), un(N_LN, cp(u))), cp(u)), un(N_LN, num(10)));
    case N_SQRT: return bin(N_DIV, bin(N_MUL, num(2), bin(N_POW, cp(u), num(1.5))), num(3));
    case N_ABS: return bin(N_DIV, bin(N_MUL, cp(u), un(N_ABS, cp(u))), num(2));
    case N_ASIN:
        return bin(N_ADD, bin(N_MUL, cp(u), un(N_ASIN, cp(u))),
                   un(N_SQRT, bin(N_SUB, num(1), bin(N_POW, cp(u), num(2)))));
    case N_ACOS:
        return bin(N_SUB, bin(N_MUL, cp(u), un(N_ACOS, cp(u))),
                   un(N_SQRT, bin(N_SUB, num(1), bin(N_POW, cp(u), num(2)))));
    case N_ATAN:
        return bin(N_SUB, bin(N_MUL, cp(u), un(N_ATAN, cp(u))),
                   bin(N_DIV, un(N_LN, bin(N_ADD, num(1), bin(N_POW, cp(u), num(2)))), num(2)));
    case N_ACOT:
        return bin(N_ADD, bin(N_MUL, cp(u), un(N_ACOT, cp(u))),
                   bin(N_DIV, un(N_LN, bin(N_ADD, num(1), bin(N_POW, cp(u), num(2)))), num(2)));
    default: return NULL;
    }
}

/* Antiderivative of f(u)^2 for the trigonometric functions. */
static Node *antiderivative_square(NodeType f, const Node *u)
{
    switch (f) {
    case N_SIN:
        return bin(N_DIV, bin(N_SUB, cp(u), bin(N_MUL, un(N_SIN, cp(u)), un(N_COS, cp(u)))), num(2));
    case N_COS:
        return bin(N_DIV, bin(N_ADD, cp(u), bin(N_MUL, un(N_SIN, cp(u)), un(N_COS, cp(u)))), num(2));
    case N_TAN: return bin(N_SUB, un(N_TAN, cp(u)), cp(u));
    case N_COT: return un(N_NEG, bin(N_ADD, un(N_COT, cp(u)), cp(u)));
    case N_SEC: return un(N_TAN, cp(u));
    case N_CSC: return un(N_NEG, un(N_COT, cp(u)));
    default: return NULL;
    }
}

static Node *divide_by(Node *f, double a)
{
    return a == 1.0 ? f : bin(N_DIV, f, num(a));
}

static Node *integrate_power(const Node *n, int depth)
{
    const Node *base = n->left, *ex = n->right;
    double a, b;

    if (!has_var(ex)) {
        double c = eval(ex, 0.0, false);
        if (!isfinite(c))
            return NULL;
        if (linear_form(base, &a, &b) && a != 0.0) {
            if (c == -1.0)
                return divide_by(un(N_LN, un(N_ABS, cp(base))), a);
            return bin(N_DIV, bin(N_POW, cp(base), num(c + 1.0)), num((c + 1.0) * a));
        }
        if (c == 2.0 && IS_FUNC(base->type) && linear_form(base->left, &a, &b) && a != 0.0) {
            Node *F = antiderivative_square(base->type, base->left);
            return F ? divide_by(F, a) : NULL;
        }
        return NULL;
    }
    if (!has_var(base)) { /* c^(ax+b) */
        double bv = eval(base, 0.0, false);
        if (bv > 0.0 && bv != 1.0 && linear_form(ex, &a, &b) && a != 0.0)
            return bin(N_DIV, cp(n), bin(N_MUL, num(a), un(N_LN, cp(base))));
    }
    (void)depth;
    return NULL;
}

/* Match k^2 + u^2 (sum_form) or k^2 - u^2 (!sum_form) with linear u. */
static bool match_k2_u2(const Node *d, bool sum_form, double *k, const Node **u, double *a)
{
    const Node *c = NULL, *sq = NULL;
    double b;
    if (d->type == N_ADD && sum_form) {
        if (d->left->type == N_CONST) { c = d->left; sq = d->right; }
        else if (d->right->type == N_CONST) { c = d->right; sq = d->left; }
    } else if (d->type == N_SUB && !sum_form && d->left->type == N_CONST) {
        c = d->left;
        sq = d->right;
    }
    if (!c || c->value <= 0.0 || sq->type != N_POW || !is_c(sq->right, 2.0))
        return false;
    if (!linear_form(sq->left, a, &b) || *a == 0.0)
        return false;
    *k = sqrt(c->value);
    *u = sq->left;
    return true;
}

static Node *integrate_quotient(const Node *n, int depth)
{
    const Node *num_ = n->left, *den = n->right;
    double a, b, k;
    const Node *u;

    if (!has_var(den)) {
        Node *i = integrate(num_, depth);
        return i ? bin(N_DIV, i, cp(den)) : NULL;
    }

    if (!has_var(num_)) { /* c / g(x) */
        if (linear_form(den, &a, &b) && a != 0.0)
            return bin(N_DIV, bin(N_MUL, cp(num_), un(N_LN, un(N_ABS, cp(den)))), num(a));

        if (match_k2_u2(den, true, &k, &u, &a)) /* c/(k^2+u^2) = c/(a k) atan(u/k) */
            return bin(N_DIV, bin(N_MUL, cp(num_), un(N_ATAN, bin(N_DIV, cp(u), num(k)))), num(a * k));

        if (den->type == N_SQRT && match_k2_u2(den->left, false, &k, &u, &a)) /* asin form */
            return bin(N_DIV, bin(N_MUL, cp(num_), un(N_ASIN, bin(N_DIV, cp(u), num(k)))), num(a));

        Node *rewritten = NULL;
        if (den->type == N_POW && den->right->type == N_CONST)
            rewritten = bin(N_MUL, cp(num_), bin(N_POW, cp(den->left), num(-den->right->value)));
        else if (den->type == N_SQRT)
            rewritten = bin(N_MUL, cp(num_), bin(N_POW, cp(den->left), num(-0.5)));
        else if (den->type == N_COS)
            rewritten = bin(N_MUL, cp(num_), un(N_SEC, cp(den->left)));
        else if (den->type == N_SIN)
            rewritten = bin(N_MUL, cp(num_), un(N_CSC, cp(den->left)));
        if (!rewritten)
            return NULL;
        Node *simp = simplify_owned(rewritten);
        Node *res = integrate(simp, depth + 1);
        free_node(simp);
        return res;
    }

    /* f(x) / g(x)  ->  f(x) * g(x)^-1, handled by integration by parts */
    Node *simp = simplify_owned(bin(N_MUL, cp(num_), bin(N_POW, cp(den), num(-1))));
    Node *res = integrate(simp, depth + 1);
    free_node(simp);
    return res;
}

static int rank_of(const Node *n)
{
    switch (n->type) {
    case N_LN:
    case N_LOG10:
    case N_ASIN:
    case N_ACOS:
    case N_ATAN:
    case N_ACOT: return 4;
    default: return is_poly(n) ? 3 : 1;
    }
}

/* integral of u dv = u*v - integral of v du */
static Node *by_parts(const Node *u, const Node *dv, int depth)
{
    Node *v = integrate(dv, depth + 1);
    if (!v)
        return NULL;
    Node *prod = simplify_owned(bin(N_MUL, cp(v), diff(u)));
    Node *rest = integrate(prod, depth + 1);
    free_node(prod);
    if (!rest) {
        free_node(v);
        return NULL;
    }
    return bin(N_SUB, bin(N_MUL, cp(u), v), rest);
}

static Node *integrate_product(const Node *n, int depth)
{
    const Node *f = n->left, *g = n->right;
    if (rank_of(g) > rank_of(f)) {
        const Node *t = f;
        f = g;
        g = t;
    }
    Node *res = by_parts(f, g, depth);
    if (!res)
        res = by_parts(g, f, depth);
    return res;
}

/* Returns an antiderivative (without "+ C") or NULL if none is found. */
static Node *integrate(const Node *n, int depth)
{
    if (depth > MAX_DEPTH)
        return NULL;
    if (!has_var(n))
        return bin(N_MUL, cp(n), var());

    switch (n->type) {
    case N_VAR: return bin(N_DIV, bin(N_POW, var(), num(2)), num(2));
    case N_NEG: {
        Node *i = integrate(n->left, depth);
        return i ? un(N_NEG, i) : NULL;
    }
    case N_ADD:
    case N_SUB: {
        Node *i1 = integrate(n->left, depth);
        if (!i1)
            return NULL;
        Node *i2 = integrate(n->right, depth);
        if (!i2) {
            free_node(i1);
            return NULL;
        }
        return bin(n->type, i1, i2);
    }
    case N_MUL: {
        if (!has_var(n->left)) {
            Node *i = integrate(n->right, depth);
            return i ? bin(N_MUL, cp(n->left), i) : NULL;
        }
        if (!has_var(n->right)) {
            Node *i = integrate(n->left, depth);
            return i ? bin(N_MUL, cp(n->right), i) : NULL;
        }
        return integrate_product(n, depth);
    }
    case N_DIV: return integrate_quotient(n, depth);
    case N_POW: return integrate_power(n, depth);
    default: break;
    }

    double a, b;
    if (IS_FUNC(n->type) && linear_form(n->left, &a, &b) && a != 0.0) {
        Node *F = antiderivative_table(n->type, n->left);
        if (F)
            return divide_by(F, a);
    }
    return NULL;
}


static double adaptive_rec(const Node *f, double a, double b, double fa, double fm, double fb,
                           double whole, double tol, int depth)
{
    double m = (a + b) / 2.0, lm = (a + m) / 2.0, rm = (m + b) / 2.0;
    double flm = eval(f, lm, false), frm = eval(f, rm, false);
    if (!isfinite(flm) || !isfinite(frm)) return NAN;
    double left = (m - a) * (fa + 4.0 * flm + fm) / 6.0;
    double right = (b - m) * (fm + 4.0 * frm + fb) / 6.0;
    double delta = left + right - whole;
    if (depth <= 0 || fabs(delta) <= 15.0 * tol)
        return left + right + delta / 15.0;
    double l = adaptive_rec(f, a, m, fa, flm, fm, left, tol / 2.0, depth - 1);
    double r = adaptive_rec(f, m, b, fm, frm, fb, right, tol / 2.0, depth - 1);
    return isfinite(l) && isfinite(r) ? l + r : NAN;
}

static double adaptive_simpson(const Node *f, double a, double b, double tol)
{
    double m = (a + b) / 2.0, fa = eval(f, a, false), fm = eval(f, m, false), fb = eval(f, b, false);
    if (!isfinite(fa) || !isfinite(fm) || !isfinite(fb)) return NAN;
    double whole = (b - a) * (fa + 4.0 * fm + fb) / 6.0;
    return adaptive_rec(f, a, b, fa, fm, fb, whole, tol, 20);
}

/* ======================================================================== */
/*  10. Menu actions                                                        */
/* ======================================================================== */

/* Print "label = value" (or "undefined"), hiding floating-point dust. */
static void show(const char *label, double v)
{
    if (!isfinite(v)) {
        printf("  %s = undefined\n", label);
        return;
    }
    if (fabs(v) < 1e-12)
        v = 0.0;
    printf("  %s = %.*f\n", label, g_precision, v);
}

static void action_expression(void)
{
    printf("  Enter expressions such as 2+3*4, sin(30), sqrt(2)^3, ans/2.\n");
    printf("  Commands: :history, :recall N, :m+, :m-, :mr, :mc, :precision N\n");
    printf("  Variables: a=5 then b=2*a. Angle mode: %s. Empty line returns.\n", g_deg ? "DEGREES" : "RADIANS");
    for (;;) {
        char buf[MAX_INPUT], err[96];
        if (!read_line("  > ", buf, sizeof buf) || is_blank(buf)) return;
        if (strcmp(buf, ":history") == 0) { action_history(); continue; }
        if (strcmp(buf, ":mr") == 0) { printf("  Memory = %.*f\n", g_precision, g_memory); continue; }
        if (strcmp(buf, ":mc") == 0) { g_memory = 0.0; puts("  Memory cleared."); continue; }
        if (strcmp(buf, ":m+") == 0 || strcmp(buf, ":m-") == 0) {
            if (!g_has_ans) { puts("  No previous result to add to memory."); continue; }
            g_memory += (buf[2] == '+') ? g_ans : -g_ans;
            printf("  Memory = %.*f\n", g_precision, g_memory); continue;
        }
        if (strncmp(buf, ":precision ", 11) == 0) {
            char *ep; long n = strtol(buf + 11, &ep, 10);
            while (isspace((unsigned char)*ep)) ep++;
            if (*ep || n < 0 || n > 12) puts("  Precision must be an integer from 0 to 12.");
            else { g_precision = (int)n; printf("  Display precision set to %d decimal places.\n", g_precision); }
            continue;
        }
        if (strncmp(buf, ":recall ", 8) == 0) {
            char *ep; long n = strtol(buf + 8, &ep, 10);
            while (isspace((unsigned char)*ep)) ep++;
            if (*ep || n < 1 || (size_t)n > g_history_count) { puts("  Invalid history number."); continue; }
            snprintf(buf, sizeof buf, "%s", g_history[n - 1].expr);
            printf("  Recalled: %s\n", buf);
        }
        /* Assignment is a single lowercase letter followed by '='. */
        if (isalpha((unsigned char)buf[0]) && buf[1] == '=' && buf[0] != 'x') {
            char name = (char)tolower((unsigned char)buf[0]);
            double value;
            if (!eval_constant_string(buf + 2, &value)) { puts("  Assignment error: expression is invalid or undefined."); continue; }
            g_vars[name - 'a'].set = true; g_vars[name - 'a'].value = value;
            g_ans = value; g_has_ans = true; history_add(buf, value);
            printf("  %c = %.*f\n", name, g_precision, value); continue;
        }
        Node *t = parse_string(buf, false, err, sizeof err);
        if (!t) { printf("  Parse error: %s\n", err); continue; }
        double v = eval(t, 0.0, g_deg);
        if (!isfinite(v)) {
            const char *why = math_error_message(t);
            printf("  %s\n", why ? why : "Math error: result is undefined, out of range, or outside the function domain.");
            free_node(t);
            continue;
        }
        free_node(t);
        if (fabs(v) < 1e-12) v = 0.0;
        printf("  = %.*f\n", g_precision, v);
        g_ans = v; g_has_ans = true; history_add(buf, v);
    }
}

static Node *read_function(void)
{
    char buf[MAX_INPUT], err[96];
    printf("  Use x as the variable, e.g.  x^2*sin(x)   e^(2x)   ln(x)/x   1/(x^2+4)\n");
    if (!read_line("  f(x) = ", buf, sizeof buf))
        return NULL;
    Node *raw = parse_string(buf, true, err, sizeof err);
    if (!raw) {
        printf("  Error: %s\n", err);
        return NULL;
    }
    return simplify_owned(raw);
}

static void action_derivative(void)
{
    Node *f = read_function();
    if (!f)
        return;
    Node *d = simplify_owned(diff(f));
    print_line("f(x)  = ", f);
    print_line("f'(x) = ", d);

    double x;
    InStatus st = read_number("  Evaluate at x (Enter to skip): ", &x, true);
    if (st == IN_OK) {
        char label[64];
        snprintf(label, sizeof label, "f(%.6g)", x);
        show(label, eval(f, x, false));
        snprintf(label, sizeof label, "f'(%.6g)", x);
        show(label, eval(d, x, false));
    }
    free_node(f);
    free_node(d);
}

static void action_integral(void)
{
    Node *f = read_function();
    if (!f)
        return;
    print_line("f(x) = ", f);

    Node *F = integrate(f, 0);
    if (F) {
        Node *Fs = simplify_owned(F);
        printf("  Indefinite integral:\n");
        print_line("F(x) = ", Fs);
        printf("         + C\n");
        free_node(Fs);
    } else {
        printf("  No closed form found with the supported rules\n"
               "  (a numerical definite integral is still available below).\n");
    }

    double a, b;
    if (read_number("  Lower limit a for a definite integral (Enter to skip): ", &a, true) == IN_OK &&
        read_number("  Upper limit b: ", &b, false) == IN_OK) {
        double v = adaptive_simpson(f, a, b, 1e-9);
        if (isfinite(v))
            printf("  Integral from %.6g to %.6g = %.*f   (adaptive Simpson, tolerance 1e-9)\n", a, b, g_precision, v);
        else
            printf("  Integration error: non-finite sample or singularity in [a, b].\n");
    }
    free_node(f);
}

static void action_power(void)
{
    double x, n;
    if (!read_double("  Base x: ", &x) || !read_double("  Exponent n: ", &n))
        return;
    char label[64];
    snprintf(label, sizeof label, "%.6g^%.6g", x, n);
    show(label, pow(x, n));
}

static void action_sqrt(void)
{
    double x;
    if (!read_double("  Number: ", &x))
        return;
    if (x >= 0.0) {
        char label[64];
        snprintf(label, sizeof label, "sqrt(%.6g)", x);
        show(label, sqrt(x));
    } else {
        printf("  sqrt(%.6g) = %.10gi   (imaginary)\n", x, sqrt(-x));
    }
}

static void action_sqrt_power(void)
{
    double x, n;
    printf("  Computes ((sqrt x)^n)\n");
    if (!read_double("  x: ", &x) || !read_double("  n: ", &n))
        return;
    char label[64];
    snprintf(label, sizeof label, "(sqrt(%.6g))^%.6g", x, n);
    show(label, x < 0.0 ? NAN : pow(sqrt(x), n));
}

static void action_reciprocal(void)
{
    double x;
    if (!read_double("  Number: ", &x))
        return;
    char label[64];
    snprintf(label, sizeof label, "1/%.6g", x);
    show(label, x == 0.0 ? NAN : 1.0 / x);
}

typedef struct {
    const char *name;
    double (*fn)(double);
} MathFn;

static const MathFn TRIG[] = {
    {"sin", my_sin}, {"cos", my_cos}, {"tan", my_tan},
    {"cot", my_cot}, {"sec", my_sec}, {"csc", my_csc},
};

static const MathFn INVERSE_TRIG[] = {
    {"asin", my_asin}, {"acos", my_acos}, {"atan", my_atan},
    {"acot", my_acot}, {"asec", my_asec}, {"acsc", my_acsc},
};

static void action_trig(void)
{
    printf("  1) sin   2) cos   3) tan   4) cot   5) sec   6) csc\n");
    long c;
    if (!read_int("  Function: ", 1, 6, &c))
        return;
    double x;
    if (!read_double(g_deg ? "  Angle (degrees): " : "  Angle (radians): ", &x))
        return;
    char label[64];
    snprintf(label, sizeof label, "%s(%.10g %s)", TRIG[c - 1].name, x, g_deg ? "deg" : "rad");
    show(label, TRIG[c - 1].fn(to_rad(x, g_deg)));
}

static void action_inverse_trig(void)
{
    printf("  1) asin   2) acos   3) atan   4) acot   5) asec   6) acsc\n");
    long c;
    if (!read_int("  Function: ", 1, 6, &c))
        return;
    double x;
    if (!read_double("  Value: ", &x))
        return;
    double r = INVERSE_TRIG[c - 1].fn(x);
    char label[64];
    snprintf(label, sizeof label, "%s(%.10g)", INVERSE_TRIG[c - 1].name, x);
    if (isnan(r)) {
        printf("  %s = undefined (outside the domain)\n", label);
        return;
    }
    printf("  %s = %.10g rad = %.10g deg\n", label, r, rad_to_deg(r));
}

static void action_logs(void)
{
    printf("  1) ln(x)   2) log10(x)   3) e^x   4) 10^x   5) value of e\n");
    long c;
    if (!read_int("  Choice: ", 1, 5, &c))
        return;
    if (c == 5) {
        printf("  e = %.15g\n", my_exp(1.0));
        return;
    }
    double x;
    if (!read_double("  x: ", &x))
        return;
    char label[64];
    switch (c) {
    case 1:
        snprintf(label, sizeof label, "ln(%.10g)", x);
        show(label, my_ln(x));
        break;
    case 2:
        snprintf(label, sizeof label, "log10(%.10g)", x);
        show(label, my_log10(x));
        break;
    case 3:
        snprintf(label, sizeof label, "e^%.10g", x);
        show(label, my_exp(x));
        break;
    default:
        snprintf(label, sizeof label, "10^%.10g", x);
        show(label, my_exp(x * LN10));
        break;
    }
}

static void action_factorial(void)
{
    long n;
    if (!read_int("  n (0 to 170): ", 0, 170, &n))
        return;
    double f = 1.0;
    for (long i = 2; i <= n; i++)
        f *= (double)i;
    if (n <= 22) /* every factorial up to 22! is exactly representable */
        printf("  %ld! = %.0f\n", n, f);
    else
        printf("  %ld! = %.10e\n", n, f);
}

static void action_percentage(void)
{
    double got, total;
    if (!read_double("  Marks obtained: ", &got) || !read_double("  Total marks: ", &total))
        return;
    if (total == 0.0) {
        printf("  Total cannot be zero.\n");
        return;
    }
    printf("  Percentage = %.6g %%\n", got / total * 100.0);
}

/* Graph sampled in an ASCII terminal plot. */
static void action_graph(void)
{
    Node *f = read_function(); if (!f) return;
    double a, b;
    if (!read_double("  x minimum: ", &a) || !read_double("  x maximum: ", &b)) { free_node(f); return; }
    if (!(b > a)) { puts("  Graph error: maximum must exceed minimum."); free_node(f); return; }
    enum { W = 70, H = 21 }; double ys[W], ymin = INFINITY, ymax = -INFINITY;
    for (int i = 0; i < W; ++i) { double x = a + (b-a)*i/(W-1); ys[i] = eval(f, x, false); if (isfinite(ys[i])) { if (ys[i]<ymin)ymin=ys[i]; if(ys[i]>ymax)ymax=ys[i]; } }
    if (!isfinite(ymin)) { puts("  No finite function samples in this interval."); free_node(f); return; }
    if (fabs(ymax-ymin)<1e-12) { ymax += 1; ymin -= 1; }
    char canvas[H][W+1]; for(int r=0;r<H;r++){memset(canvas[r],' ',W);canvas[r][W]='\0';}
    for(int i=0;i<W;i++) if(isfinite(ys[i])) { int r=(int)llround((ymax-ys[i])/(ymax-ymin)*(H-1)); if(r>=0&&r<H)canvas[r][i]='*'; }
    if (a<=0&&b>=0) { int c=(int)llround((0-a)/(b-a)*(W-1)); for(int r=0;r<H;r++) if(canvas[r][c]==' ')canvas[r][c]='|'; }
    if (ymin<=0&&ymax>=0) { int r=(int)llround(ymax/(ymax-ymin)*(H-1)); for(int c=0;c<W;c++) if(canvas[r][c]==' ')canvas[r][c]='-'; }
    printf("  ASCII graph (x: %.5g to %.5g, y: %.5g to %.5g)\n",a,b,ymin,ymax);
    for(int r=0;r<H;r++) puts(canvas[r]);
    free_node(f);
}

static void action_solve(void)
{
    Node *f = read_function(); if (!f) return;
    double a,b;
    if(!read_double("  Search interval start: ",&a)||!read_double("  Search interval end: ",&b)){free_node(f);return;}
    if(a==b){puts("  Solver error: interval endpoints must differ.");free_node(f);return;}
    double fa=eval(f,a,false), fb=eval(f,b,false);
    if(!isfinite(fa)||!isfinite(fb)||fa*fb>0){puts("  No bracketed root: choose endpoints with finite values of opposite signs.");free_node(f);return;}
    for(int i=0;i<200;i++){double m=a+(b-a)/2, fm=eval(f,m,false);if(!isfinite(fm)){puts("  Solver encountered a domain error.");free_node(f);return;}if(fabs(fm)<1e-12||fabs(b-a)<1e-12){printf("  Root x = %.*f, f(x) = %.3g\n",g_precision,m,fm);g_ans=m;g_has_ans=true;free_node(f);return;}if((fa<0&&fm>0)||(fa>0&&fm<0)){b=m;fb=fm;}else{a=m;fa=fm;}}
    printf("  Approximate root x = %.12g\n",(a+b)/2); free_node(f);
}

/* Complex-expression evaluator: arithmetic, powers, i, and common complex functions. */
typedef struct { const char *s; size_t p; char err[96]; } CParser;
static double complex cexpr(CParser *p);
static void cskip(CParser *p){while(isspace((unsigned char)p->s[p->p]))p->p++;}
static double complex catom(CParser *p)
{
    cskip(p); char c=p->s[p->p];
    if(c=='+'||c=='-'){p->p++;double complex z=catom(p);return c=='-'?-z:z;}
    if(c=='('){p->p++;double complex z=cexpr(p);cskip(p);if(p->s[p->p]==')')p->p++;else snprintf(p->err,sizeof p->err,"missing closing parenthesis");return z;}
    if(isdigit((unsigned char)c)||c=='.'){char *end;double v=strtod(p->s+p->p,&end);if(end==p->s+p->p){snprintf(p->err,sizeof p->err,"invalid number");return CMPLX(NAN,NAN);}p->p=(size_t)(end-p->s);return v;}
    if(isalpha((unsigned char)c)){char name[16];size_t n=0;while(isalpha((unsigned char)p->s[p->p])){if(n<15)name[n++]=(char)tolower((unsigned char)p->s[p->p]);p->p++;}name[n]='\0';if(!strcmp(name,"i"))return I;if(!strcmp(name,"pi"))return PI;if(!strcmp(name,"e"))return MY_E;
        cskip(p);if(p->s[p->p]!='('){snprintf(p->err,sizeof p->err,"unknown complex name '%s'",name);return CMPLX(NAN,NAN);}p->p++;double complex z=cexpr(p);cskip(p);if(p->s[p->p]==')')p->p++;else snprintf(p->err,sizeof p->err,"missing ')' after function");
        if(!strcmp(name,"sqrt")) return csqrt(z);
        if(!strcmp(name,"exp")) return cexp(z);
        if(!strcmp(name,"ln")) return clog(z);
        if(!strcmp(name,"sin")) return csin(z);
        if(!strcmp(name,"cos")) return ccos(z);
        if(!strcmp(name,"abs")) return cabs(z);
        snprintf(p->err,sizeof p->err,"unsupported complex function '%s'",name);
        return CMPLX(NAN,NAN);
    }
    snprintf(p->err,sizeof p->err,"unexpected character '%c'",c?c:'?');return CMPLX(NAN,NAN);
}
static double complex cpowexpr(CParser *p){double complex z=catom(p);cskip(p);if(p->s[p->p]=='^'){p->p++;z=cpow(z,cpowexpr(p));}return z;}
static double complex cterm(CParser *p)
{
    double complex z=cpowexpr(p);
    for (;;) {
        cskip(p); char c=p->s[p->p];
        if (c=='*' || c=='/') { p->p++; double complex r=cpowexpr(p); z=c=='*'?z*r:z/r; }
        else if (isalpha((unsigned char)c) || c=='(') { double complex r=cpowexpr(p); z*=r; }
        else break;
    }
    return z;
}
static double complex cexpr(CParser *p){double complex z=cterm(p);for(;;){cskip(p);char c=p->s[p->p];if(c!='+'&&c!='-')break;p->p++;double complex r=cterm(p);z=c=='+'?z+r:z-r;}return z;}
static void action_complex(void)
{
    char buf[MAX_INPUT];puts("  Complex mode supports + - * / ^, i, pi, e, sqrt(), exp(), ln(), sin(), cos(), abs().");
    if(!read_line("  complex> ",buf,sizeof buf)||is_blank(buf)) return;
    CParser p={buf,0,{0}};
    double complex z=cexpr(&p);
    cskip(&p);
    if(p.err[0]||p.s[p.p]||!isfinite(creal(z))||!isfinite(cimag(z))){printf("  Complex expression error: %s\n",p.err[0]?p.err:"undefined or malformed expression");return;}
    printf("  = %.*f %c %.*fi\n",g_precision,creal(z),cimag(z)<0?'-':'+',g_precision,fabs(cimag(z)));
}

static void action_precision(void)
{
    long n;if(!read_int("  Decimal places (0-12): ",0,12,&n))return;g_precision=(int)n;printf("  Display precision set to %d decimal places.\n",g_precision);
}

/* ======================================================================== */
/*  11. Built-in self-test                                                  */
/* ======================================================================== */

static int g_fail = 0, g_pass = 0;

static void report(bool ok, const char *fmt, ...)
{
    va_list ap;
    printf("  [%s] ", ok ? "PASS" : "FAIL");
    va_start(ap, fmt);
    vprintf(fmt, ap);
    va_end(ap);
    putchar('\n');
    if (ok)
        g_pass++;
    else
        g_fail++;
}

static double ref_cot(double x) { return 1.0 / tan(x); }
static double ref_sec(double x) { return 1.0 / cos(x); }
static double ref_csc(double x) { return 1.0 / sin(x); }

static void test_function(const char *name, double (*mine)(double), double (*ref)(double),
                          double lo, double hi)
{
    double worst = 0.0;
    const int steps = 2000;
    for (int i = 0; i <= steps; i++) {
        double x = lo + (hi - lo) * i / steps;
        double a = mine(x), b = ref(x);
        if (isnan(a) && (isnan(b) || fabs(b) > 1e10))
            continue; /* near a pole / outside the domain */
        double err = isnan(a) || isnan(b) ? 1.0 : fabs(a - b) / fmax(1.0, fabs(b));
        if (err > worst)
            worst = err;
    }
    report(worst < 1e-10, "%-8s on [%g, %g]   max error %.2e", name, lo, hi, worst);
}

static void test_derivative(const char *expr, double x)
{
    char err[96];
    Node *raw = parse_string(expr, true, err, sizeof err);
    if (!raw) {
        report(false, "d/dx %s  (parse error: %s)", expr, err);
        return;
    }
    Node *f = simplify_owned(raw);
    Node *d = simplify_owned(diff(f));
    const double h = 1e-5;
    double numeric = (eval(f, x + h, false) - eval(f, x - h, false)) / (2.0 * h);
    double symbolic = eval(d, x, false);
    bool ok = fabs(numeric - symbolic) <= 1e-6 * fmax(1.0, fabs(numeric));
    printf("  [%s] d/dx %-22s = ", ok ? "PASS" : "FAIL", expr);
    print_pretty(d);
    putchar('\n');
    ok ? g_pass++ : g_fail++;
    free_node(f);
    free_node(d);
}

static void test_integral(const char *expr)
{
    char err[96];
    Node *raw = parse_string(expr, true, err, sizeof err);
    if (!raw) {
        report(false, "integral %s  (parse error: %s)", expr, err);
        return;
    }
    Node *f = simplify_owned(raw);
    Node *F = integrate(f, 0);
    if (!F) {
        report(false, "integral %s  (no antiderivative found)", expr);
        free_node(f);
        return;
    }
    Node *Fs = simplify_owned(F);
    const double pts[] = {0.3, 0.7, 1.1}, h = 1e-5;
    bool ok = true;
    for (int i = 0; i < 3; i++) {
        double numeric = (eval(Fs, pts[i] + h, false) - eval(Fs, pts[i] - h, false)) / (2.0 * h);
        double exact = eval(f, pts[i], false);
        if (!(fabs(numeric - exact) <= 1e-6 * fmax(1.0, fabs(exact))))
            ok = false;
    }
    printf("  [%s] int %-20s = ", ok ? "PASS" : "FAIL", expr);
    print_pretty(Fs);
    putchar('\n');
    ok ? g_pass++ : g_fail++;
    free_node(f);
    free_node(Fs);
}

static void test_parser(const char *expr, double expected)
{
    double v;
    bool ok = false;
    char err[96];
    Node *t = parse_string(expr, false, err, sizeof err);
    if (t) {
        v = eval(t, 0.0, false);
        ok = fabs(v - expected) <= 1e-9 * fmax(1.0, fabs(expected));
        free_node(t);
    } else {
        v = NAN;
    }
    report(ok, "%-22s = %.10g (expected %.10g)", expr, v, expected);
}

static bool run_self_tests(void)
{
    g_fail = g_pass = 0;
    printf("Numerical functions vs <math.h>\n");
    test_function("sin", my_sin, sin, -1000, 1000);
    test_function("cos", my_cos, cos, -1000, 1000);
    test_function("tan", my_tan, tan, -10, 10);
    test_function("cot", my_cot, ref_cot, -10, 10);
    test_function("sec", my_sec, ref_sec, -10, 10);
    test_function("csc", my_csc, ref_csc, -10, 10);
    test_function("exp", my_exp, exp, -50, 50);
    test_function("ln", my_ln, log, 1e-6, 1e6);
    test_function("log10", my_log10, log10, 1e-6, 1e6);
    test_function("atan", my_atan, atan, -100, 100);
    test_function("asin", my_asin, asin, -1, 1);
    test_function("acos", my_acos, acos, -1, 1);

    printf("\nExpression parser\n");
    test_parser("2+3*4", 14);
    test_parser("2^3^2", 512);
    test_parser("-2^2", -4);
    test_parser("(1+2)(3+4)", 21);
    test_parser("2pi", 2 * PI);
    test_parser("sin(pi/2)+cos(0)", 2);
    test_parser("sqrt(16)+abs(-3)", 7);
    test_parser("10/4", 2.5);
    test_parser("2e3+1", 2001);
    test_parser("ln(e^2)", 2);
    test_parser("log(1000)", 3);

    printf("\nSymbolic differentiation (checked against central differences)\n");
    test_derivative("sin(x)*x^2", 1.3);
    test_derivative("x^x", 1.7);
    test_derivative("ln(x)/x", 2.2);
    test_derivative("e^(2x)", 0.4);
    test_derivative("atan(x)+asin(x/2)", 0.6);
    test_derivative("sqrt(1+x^2)", 1.1);
    test_derivative("2^x*cos(x)", 0.9);
    test_derivative("tan(x)/x", 0.5);
    test_derivative("acot(x)", 1.2);
    test_derivative("asec(x)", 2.5);
    test_derivative("sec(x)+csc(x)+cot(x)", 0.8);
    test_derivative("log(x^2+1)", 1.4);

    printf("\nSymbolic integration (d/dx of the result must equal the integrand)\n");
    const char *integrals[] = {
        "x^2", "3x+2", "sin(2x+1)", "x*sin(x)", "x*exp(x)", "x^2*cos(x)", "ln(x)",
        "x*ln(x)", "1/x", "1/(x^2+4)", "1/sqrt(4-x^2)", "e^(3x)", "sqrt(x)",
        "(x+1)*(x+2)", "atan(x)", "tan(x)", "sin(x)^2", "2^x", "x/(x+1)^2", "1/x^2",
    };
    for (size_t i = 0; i < sizeof integrals / sizeof integrals[0]; i++)
        test_integral(integrals[i]);

    printf("\n%d passed, %d failed\n", g_pass, g_fail);
    return g_fail == 0;
}

/* ======================================================================== */
/*  12. Main menu                                                           */
/* ======================================================================== */

static void print_menu(void)
{
    printf("\n=========== Scientific Calculator v%s ===========\n", VERSION);
    printf("  Angle mode: %s\n\n", g_deg ? "DEGREES" : "RADIANS");
    printf("   1  Expression calculator (full parser)\n");
    printf("   2  Differentiation (symbolic)\n");
    printf("   3  Integration (symbolic + definite)\n");
    printf("   4  Power               x^n\n");
    printf("   5  Square root\n");
    printf("   6  Square-root power   (sqrt(x))^n\n");
    printf("   7  Reciprocal          1/x\n");
    printf("   8  Trigonometric       sin cos tan cot sec csc\n");
    printf("   9  Inverse trigonometric\n");
    printf("  10  Logarithms and exponentials\n");
    printf("  11  Factorial\n");
    printf("  12  Percentage\n");
    printf("  13  Switch angle mode (degrees / radians)\n");
    printf("  14  Run self-test\n");
    printf("  15  Calculation history\n");
    printf("  16  Display precision\n");
    printf("  17  Function graph (ASCII)\n");
    printf("  18  Solve f(x)=0 (bisection)\n");
    printf("  19  Complex expression mode\n");
    printf("   0  Exit\n");
}

static void run_menu(void)
{
    for (;;) {
        print_menu();
        long choice;
        if (!read_int("\nEnter your choice: ", 0, 19, &choice))
            break;
        putchar('\n');
        switch (choice) {
        case 0: printf("Goodbye!\n"); return;
        case 1: action_expression(); break;
        case 2: action_derivative(); break;
        case 3: action_integral(); break;
        case 4: action_power(); break;
        case 5: action_sqrt(); break;
        case 6: action_sqrt_power(); break;
        case 7: action_reciprocal(); break;
        case 8: action_trig(); break;
        case 9: action_inverse_trig(); break;
        case 10: action_logs(); break;
        case 11: action_factorial(); break;
        case 12: action_percentage(); break;
        case 13:
            g_deg = !g_deg;
            printf("  Angle mode is now %s.\n", g_deg ? "DEGREES" : "RADIANS");
            break;
        case 14: run_self_tests(); break;
        case 15: action_history(); break;
        case 16: action_precision(); break;
        case 17: action_graph(); break;
        case 18: action_solve(); break;
        case 19: action_complex(); break;
        }
        if (g_eof)
            break;
    }
    putchar('\n');
}

int main(int argc, char **argv)
{
    if (argc > 1) {
        if (strcmp(argv[1], "--test") == 0)
            return run_self_tests() ? EXIT_SUCCESS : EXIT_FAILURE;
        printf("Usage: %s [--test]\n"
               "  (no arguments)  start the interactive calculator\n"
               "  --test          run the built-in self-test and exit\n",
               argv[0]);
        return strcmp(argv[1], "--help") == 0 ? EXIT_SUCCESS : EXIT_FAILURE;
    }
    run_menu();
    return EXIT_SUCCESS;
}
