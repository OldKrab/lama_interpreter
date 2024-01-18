
#include <errno.h>
#include <malloc.h>
#include <stdio.h>
#include <string.h>

#include "../lama/runtime/gc.h"
#include "../lama/runtime/runtime.h"

#define TODO(what)                           \
    do                                       \
        failure("Unimplemented " what "\n"); \
    while (0)

#define VA_ARGS(...) , ##__VA_ARGS__
#define ASSERT(cond, fmt, ...)                      \
    do                                              \
        if (!(cond)) {                              \
            failure(fmt "\n" VA_ARGS(__VA_ARGS__)); \
        }                                           \
    while (0)

void* __start_custom_data;
void* __stop_custom_data;

/*  Lama runtime functions  */
extern int Lread();
extern int Lwrite(int n);
extern void* Bstring(void* p);
extern int Llength(void* p);
extern void* Belem(void* p, int i);
extern void* Bsta(void* v, int i, void* x);
extern void* Barray_init_from_end(int bn, const size_t* init);
extern int LtagHash(char*);
extern void* Bsexp_init_from_end(int bn, int tag, size_t* init);
extern int Btag(void* d, int t, int n);
extern void* Lstring(void* p);
extern void* Bclosure_init_from_end(int bn, void* entry, size_t* init);

extern size_t __gc_stack_top, __gc_stack_bottom;

/* The unpacked representation of bytecode file */
typedef struct {
    char* string_ptr;          /* A pointer to the beginning of the string table */
    int* public_ptr;           /* A pointer to the beginning of publics table    */
    char* code_ptr;            /* A pointer to the bytecode itself               */
    int* global_ptr;           /* A pointer to the global area                   */
    int stringtab_size;        /* The size (in bytes) of the string table        */
    int global_area_size;      /* The size (in words) of global area             */
    int public_symbols_number; /* The number of public symbols                   */
    char buffer[0];
} bytefile;

#define STACK_SIZE (1 << 20)

typedef struct {
    size_t* p;
    size_t n;
} slice_t;

typedef struct {
    size_t* begin;
    size_t* sp;
    size_t n;
} stack_t;

typedef struct {
    stack_t stack;
    stack_t cstack;
    slice_t args;
    slice_t locals;
    slice_t closed;
    slice_t globals;
    char* code_start;
    char* string_area;
    char* ip;
    size_t* bp;
    bool is_closure;
} context_t;

/* Context functions */

static inline char* get_string(context_t* c, int idx) { return &c->string_area[idx]; }

static inline int next_code_int(context_t* c) {
    int v = *(int*)c->ip;
    c->ip += sizeof(int);
    return v;
}

static inline char next_code_byte(context_t* c) {
    char v = *c->ip;
    c->ip++;
    return v;
}

static inline void update_gc_stack_variables(context_t* c) { __gc_stack_top = ((size_t)c->stack.sp) - 4; }

// for debug
size_t get_stack_size(context_t* c) { return c->stack.begin + c->stack.n - c->stack.sp; }

// move sp and write value
static inline void push_stack(context_t* c, size_t v) {
    ASSERT(c->stack.sp >= c->stack.begin + sizeof(size_t), "Overflow stack");
    c->stack.sp--;
    *c->stack.sp = v;
    update_gc_stack_variables(c);
}

static inline void push_stack_boxed(context_t* c, size_t v) { push_stack(c, BOX(v)); }

// read value and move sp
static inline size_t pop_stack(context_t* c) {
    ASSERT(c->stack.sp < c->stack.begin + c->stack.n, "Underflow stack");
    size_t v = *c->stack.sp;
    c->stack.sp++;
    update_gc_stack_variables(c);
    return v;
}

static inline void drop_stack_n(context_t* c, size_t n) {
    ASSERT(c->stack.sp + n <= c->stack.begin + c->stack.n, "Underflow stack");
    c->stack.sp += n;
    update_gc_stack_variables(c);
}

static inline size_t pop_stack_unboxed(context_t* c) {
    size_t v = pop_stack(c);
    ASSERT(UNBOXED(v), "expect unboxed");
    return UNBOX(v);
}

static inline size_t is_stack_empty(context_t* c) { return c->stack.sp == c->stack.begin + c->stack.n; }

static inline size_t peek_stack_i(context_t* c, size_t i) {
    ASSERT(c->cstack.sp + i < c->cstack.begin + c->cstack.n, "Out of bounds of stack");
    return c->stack.sp[i];
}

static inline size_t peek_stack(context_t* c) { return peek_stack_i(c, 0); }

// move sp and write value
static inline void push_cstack(context_t* c, size_t v) {
    ASSERT(c->cstack.sp >= c->cstack.begin + sizeof(size_t), "Overflow cstack");
    c->cstack.sp--;
    *c->cstack.sp = v;
}

// read value and move sp
static inline size_t pop_cstack(context_t* c) {
    ASSERT(c->cstack.sp < c->cstack.begin + c->cstack.n, "Underflow cstack");
    size_t v = *c->cstack.sp;
    c->cstack.sp++;
    return v;
}

typedef enum {
    MEM_GLOBAL = 0,
    MEM_LOCAL,
    MEM_ARG,
    MEM_CLOSED,
} MEM;

static inline size_t* get_memory(context_t* c, MEM mem, int idx) {
    ASSERT(idx >= 0, "idx < 0");
    switch (mem) {
        case MEM_GLOBAL:
            ASSERT(idx < c->globals.n, "idx > c->globals.n");
            return &c->globals.p[idx];
        case MEM_LOCAL:
            ASSERT(idx < c->locals.n, "idx > c->locals.n");
            return &c->locals.p[idx];
        case MEM_ARG:
            ASSERT(idx < c->args.n, "idx > c->args.n");
            return &c->args.p[-idx];
        case MEM_CLOSED:
            ASSERT(c->is_closure, "not in closure");
            ASSERT(idx < c->closed.n, "idx > c->closed.n");
            return &c->closed.p[idx];
    }
}

/* handlers of instructions */

static inline int32_t do_binop(int32_t x, int32_t y, char op) {
    // char* ops[] = {"+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "!!"};
    switch (op) {
        case 0:
            return x + y;
        case 1:
            return x - y;
        case 2:
            return x * y;
        case 3:
            return x / y;
        case 4:
            return x % y;
        case 5:
            return x < y;
        case 6:
            return x <= y;
        case 7:
            return x > y;
        case 8:
            return x >= y;
        case 9:
            return x == y;
        case 10:
            return x != y;
        case 11:
            return x && y;
        case 12:
            return x || y;
    }
}

static inline void handle_binop(context_t* c, char l) {
    int32_t y = UNBOX((int32_t)pop_stack(c));
    int32_t x = UNBOX((int32_t)pop_stack(c));
    int32_t res = do_binop(x, y, l - 1);
    push_stack_boxed(c, res);
}

static inline void handle_const(context_t* c) { push_stack_boxed(c, next_code_int(c)); }

static inline void handle_string(context_t* c) {
    int idx = next_code_int(c);
    char* string = Bstring(get_string(c, idx));
    push_stack(c, (size_t)string);
}

static inline void handle_sexp(context_t* c) {
    char* tag = get_string(c, next_code_int(c));
    int n = next_code_int(c);
    void* sexp = Bsexp_init_from_end(BOX(n), LtagHash(tag), c->stack.sp);
    for (int i = 0; i < n; i++)
        pop_stack(c);
    push_stack(c, (size_t)sexp);
}
static inline void handle_sti(context_t* c) {
    // fprintf(f, "STI");
    TODO("STI");
}

static inline void handle_sta(context_t* c) {
    void* value = (void*)pop_stack(c);
    size_t idx_or_var = pop_stack(c);
    void* x = UNBOXED(idx_or_var) ? (void*)pop_stack(c) : (void*)idx_or_var;
    push_stack(c, (size_t)Bsta(value, idx_or_var, x));
}

static inline void handle_ret(context_t* c) {
    // fprintf(f, "RET");
    TODO("RET");
}

static inline void handle_drop(context_t* c) { pop_stack(c); }

static inline void handle_dup(context_t* c) { push_stack(c, peek_stack(c)); }

static inline void handle_swap(context_t* c) {
    // fprintf(f, "SWAP");
    TODO("SWAP");
}

static inline void handle_elem(context_t* c) {
    size_t idx = pop_stack(c);
    void* arr = (void*)pop_stack(c);
    void* elem = Belem(arr, idx);
    push_stack(c, (size_t)elem);
}

static inline void handle_ld(context_t* c, MEM mem) {
    int idx = next_code_int(c);
    size_t* var = get_memory(c, mem, idx);
    push_stack(c, *var);
}

static inline void handle_lda(context_t* c, MEM mem) {
    int idx = next_code_int(c);
    size_t* v = get_memory(c, mem, idx);
    push_stack(c, (size_t)v);
}

static inline void handle_st(context_t* c, MEM mem) {
    int idx = next_code_int(c);
    size_t* var = get_memory(c, mem, idx);
    size_t val = peek_stack(c);
    *var = val;
}

static inline void handle_cjmpz(context_t* c) {
    int offset = next_code_int(c);
    size_t cond = pop_stack_unboxed(c);
    if (cond == 0)
        c->ip = c->code_start + offset;
}

static inline void handle_cjmpnz(context_t* c) {
    int offset = next_code_int(c);
    size_t cond = pop_stack_unboxed(c);
    if (cond != 0)
        c->ip = c->code_start + offset;
}

static inline void handle_jump(context_t* c) {
    int offset = next_code_int(c);
    c->ip = c->code_start + offset;
}

/*
Stack:
        <---- sp
    args
    [closure]

Call stack:
    is_closure_flag
    return addr

will turn into
Stack:
        <---- sp
    ret value
    locals
        <---- bp
    args
    [closure]

Call stack:
    prev bp
    prev locals n
    prev args n
    is_closure_flag
    return addr

*/
static inline void handle_begin(context_t* c) {
    size_t prev_args_n = c->args.n;
    size_t prev_locals_n = c->locals.n;
    size_t* prev_bp = c->bp;
    c->args.n = next_code_int(c);
    c->args.p = c->stack.sp + c->args.n - 1;
    c->locals.n = next_code_int(c);
    c->bp = c->stack.sp;
    for (int i = 0; i < c->locals.n; i++) {
        push_stack_boxed(c, 0);
    }
    c->locals.p = c->stack.sp;

    push_cstack(c, prev_args_n);
    push_cstack(c, prev_locals_n);
    push_cstack(c, (size_t)prev_bp);
}

static inline bool handle_end(context_t* c) {
    size_t ret_value = pop_stack(c);
    if (c->is_closure)
        drop_stack_n(c, c->args.n + c->locals.n + 1);
    else
        drop_stack_n(c, c->args.n + c->locals.n);
    if (is_stack_empty(c))
        return true;  // end from main
    push_stack(c, ret_value);

    c->bp = (size_t*)pop_cstack(c);
    c->locals.n = pop_cstack(c);
    c->args.n = pop_cstack(c);
    c->is_closure = (bool)pop_cstack(c);
    c->ip = (char*)pop_cstack(c);

    c->locals.p = c->bp - c->locals.n;
    c->args.p = c->bp + (c->args.n - 1);
    return false;
}

static inline void handle_callc(context_t* c) {
    int args_n = next_code_int(c);
    void* closure = (void*)peek_stack_i(c, args_n);
    size_t closure_offset = (size_t)Belem(closure, BOX(0));
    push_cstack(c, (size_t)(c->ip));
    push_cstack(c, (size_t)c->is_closure);

    c->ip = c->code_start + closure_offset;
    c->is_closure = true;
}

static inline void handle_call(context_t* c) {
    int offset = next_code_int(c);
    int args_n = next_code_int(c);
    push_cstack(c, (size_t)(c->ip));
    push_cstack(c, (size_t)c->is_closure);

    c->ip = c->code_start + offset;
    c->is_closure = false;
}

static inline void handle_cbegin(context_t* c) {
    // fprintf(f, "CBEGIN\t%d ", INT);
    // fprintf(f, "%d", INT);
    TODO("CBEGIN");
}

static inline void handle_clojure(context_t* c) {
    char* closure_offset = (char*)next_code_int(c);
    int closed_n = next_code_int(c);
    for (int i = 0; i < closed_n; i++) {
        MEM mem = (MEM)next_code_byte(c);
        int idx = next_code_int(c);
        push_stack(c, (size_t)get_memory(c, mem, idx));
    }

    void* clojure = Bclosure_init_from_end(BOX(closed_n), closure_offset, c->stack.sp);

    for (int i = 0; i < closed_n; i++) {
        pop_stack(c);
    }

    push_stack(c, (size_t)clojure);
}

static inline void handle_tag(context_t* c) {
    // check that on stack sexpr with tag and n args
    char* tag = get_string(c, next_code_int(c));
    int n = next_code_int(c);
    void* x = (void*)pop_stack(c);
    int res = Btag(x, LtagHash(tag), BOX(n));
    push_stack(c, res);
}

static inline void handle_array(context_t* c) {
    // fprintf(f, "ARRAY\t%d", INT);
    TODO("ARRAY");
}

static inline void handle_fail(context_t* c) {
    // fprintf(f, "FAIL\t%d", INT);
    // fprintf(f, "%d", INT);
    TODO("FAIL");
}

static inline void handle_line(context_t* c) {
    next_code_int(c);  // ignore
}

static inline void handle_patt(context_t* context, int l) {
    char* pats[] = {"=str", "#string", "#array", "#sexp", "#ref", "#val", "#fun"};
    // fprintf(f, "PATT\t%s", pats[l]);
    TODO("PATT");
}

static inline void handle_call_read(context_t* c) {
    int v = Lread();
    push_stack(c, v);
}

static inline void handle_call_write(context_t* c) {
    int res = Lwrite(pop_stack(c));
    push_stack(c, res);
}

static inline void handle_call_length(context_t* c) {
    void* str = (void*)pop_stack(c);
    int size = Llength(str);
    push_stack(c, size);
}

static inline void handle_call_string(context_t* c) {
    void* v = (void*)pop_stack(c);
    void* str = Lstring(v);
    push_stack(c, (size_t)str);
}

static inline void handle_call_array(context_t* c) {
    int n = next_code_int(c);
    void* arr = Barray_init_from_end(BOX(n), c->stack.sp);
    for (int i = 0; i < n; i++)
        pop_stack(c);
    push_stack(c, (size_t)arr);
}

/* Disassembles the bytecode pool */
void disassemble(FILE* f, bytefile* bf) {
#define FAIL failure("ERROR: invalid opcode %d-%d\n", h, l)

    __init();  // init lama gc
    context_t context;
    context.stack.begin = malloc(STACK_SIZE * sizeof(int));
    context.stack.n = STACK_SIZE;
    context.stack.sp = context.stack.begin + context.stack.n;

    context.cstack.begin = malloc(STACK_SIZE * sizeof(int));
    context.cstack.n = STACK_SIZE;
    context.cstack.sp = context.cstack.begin + context.cstack.n;

    context.ip = bf->code_ptr;
    context.code_start = bf->code_ptr;
    context.globals.p = (size_t*)bf->global_ptr;
    context.globals.n = bf->global_area_size;

    context.string_area = bf->string_ptr;
    context.is_closure = false;

    __gc_stack_bottom = (size_t)context.stack.sp;
    update_gc_stack_variables(&context);

    push_stack_boxed(&context, 0);
    push_stack_boxed(&context, 0);  // because main's BEGIN 2 0
    context.bp = context.stack.sp;

    do {
        char x = next_code_byte(&context), h = (x & 0xF0) >> 4, l = x & 0x0F;

        switch (h) {
            case 15:
                return;

            /* BINOP */
            case 0:
                handle_binop(&context, l);
                break;

            case 1:
                switch (l) {
                    case 0:
                        handle_const(&context);
                        break;
                    case 1:
                        handle_string(&context);
                        break;
                    case 2:
                        handle_sexp(&context);
                        break;
                    case 3:
                        handle_sti(&context);
                        break;
                    case 4:
                        handle_sta(&context);
                        break;
                    case 5:
                        handle_jump(&context);
                        break;
                    case 6:
                        if (handle_end(&context))
                            return;
                        break;
                    case 7:
                        handle_ret(&context);
                        break;
                    case 8:
                        handle_drop(&context);
                        break;
                    case 9:
                        handle_dup(&context);
                        break;
                    case 10:
                        handle_swap(&context);
                        break;
                    case 11:
                        handle_elem(&context);
                        break;
                    default:
                        FAIL;
                }
                break;

            case 2:
                handle_ld(&context, l);
                break;
            case 3:
                handle_lda(&context, l);
                break;
            case 4:
                handle_st(&context, l);
                break;

            case 5:
                switch (l) {
                    case 0:
                        handle_cjmpz(&context);
                        break;
                    case 1:
                        handle_cjmpnz(&context);
                        break;
                    case 2:
                        handle_begin(&context);
                        break;
                    case 3:
                        handle_cbegin(&context);
                        break;
                    case 4:
                        handle_clojure(&context);
                        break;
                    case 5:
                        handle_callc(&context);
                        break;
                    case 6:
                        handle_call(&context);
                        break;
                    case 7:
                        handle_tag(&context);
                        break;
                    case 8:
                        handle_array(&context);
                        break;
                    case 9:
                        handle_fail(&context);
                        break;
                    case 10:
                        handle_line(&context);
                        break;
                    default:
                        FAIL;
                }
                break;

            case 6:
                handle_patt(&context, l);
                break;

            case 7: {
                switch (l) {
                    case 0:
                        handle_call_read(&context);
                        break;
                    case 1:
                        handle_call_write(&context);
                        break;
                    case 2:
                        handle_call_length(&context);
                        break;
                    case 3:
                        handle_call_string(&context);
                        break;
                    case 4:
                        handle_call_array(&context);
                        break;
                    default:
                        FAIL;
                }
            } break;

            default:
                FAIL;
        }

    } while (1);
}

/* Reads a binary bytecode file by name and unpacks it */
bytefile* read_file(char* fname) {
    FILE* f = fopen(fname, "rb");
    long size;
    bytefile* file;

    if (f == 0) {
        failure("%s\n", strerror(errno));
    }

    if (fseek(f, 0, SEEK_END) == -1) {
        failure("%s\n", strerror(errno));
    }

    file = (bytefile*)malloc(sizeof(int) * 4 + (size = ftell(f)));

    if (file == 0) {
        failure("*** FAILURE: unable to allocate memory.\n");
    }

    rewind(f);

    if (size != fread(&file->stringtab_size, 1, size, f)) {
        failure("%s\n", strerror(errno));
    }

    fclose(f);

    file->string_ptr = &file->buffer[file->public_symbols_number * 2 * sizeof(int)];
    file->public_ptr = (int*)file->buffer;
    file->code_ptr = &file->string_ptr[file->stringtab_size];
    file->global_ptr = (int*)malloc(file->global_area_size * sizeof(int));

    return file;
}

int main(int argc, char* argv[]) {
    if (argc != 2) {
        printf("Specify file with bytecode!");
        return 1;
    }
    bytefile* f = read_file(argv[1]);
    disassemble(stdout, f);
    free(f);
    return 0;
}
