
#include <errno.h>
#include <malloc.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "../lama/runtime/gc.h"
#include "../lama/runtime/runtime.h"
#include "../lama/runtime/runtime_common.h"

#define TODO(what)                           \
    do                                       \
        failure("Unimplemented " what "\n"); \
    while (0)

#ifndef NDEBUG
#define VA_ARGS(...) , ##__VA_ARGS__
#define ASSERT(cond, fmt, ...)                      \
    do                                              \
        if (!(cond)) {                              \
            failure(fmt "\n" VA_ARGS(__VA_ARGS__)); \
        }                                           \
    while (0)
#else
#define ASSERT(...) 
#endif

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
extern int Bstring_patt(void* x, void* y);
extern int Barray_patt(void* d, int n);
extern int Bclosure_tag_patt(void* x);
extern int Bstring_tag_patt(void* x);
extern int Barray_tag_patt(void* x);
extern int Bsexp_tag_patt(void* x);
extern int Bboxed_patt(void* x);
extern int Bunboxed_patt(void* x);

extern size_t __gc_stack_top, __gc_stack_bottom;

/* The unpacked representation of bytecode file */
typedef struct {
    char* string_ptr;          /* A pointer to the beginning of the string table */
    int* public_ptr;           /* A pointer to the beginning of publics table    */
    char* code_ptr;            /* A pointer to the bytecode itself               */
    size_t code_size;          /* A size of the bytecode                         */
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
    uint8_t* p;
    size_t n;
} byte_slice_t;

typedef struct {
    char* p;
    size_t n;
} char_slice_t;

typedef struct {
    size_t* begin;
    size_t* sp;
    size_t n;
} stack_t;

typedef struct {
    slice_t stack;
    stack_t cstack;
    slice_t args;
    slice_t locals;
    slice_t closed;
    slice_t globals;
    byte_slice_t code;
    char_slice_t string_area;
    uint8_t* ip;
    size_t* bp;
    bool is_closure;
} context_t;

/* Context functions */

static inline char* get_string(context_t* c, int idx) {
    ASSERT(0 <= idx && idx < c->string_area.n, "Out of bounds string area");
    return &c->string_area.p[idx];
}

static inline void set_ip(context_t* c, uint8_t* to) {
    ASSERT(c->code.p <= to && to < c->code.p + c->code.n, "Out of bounds bytecode");
    c->ip = to;
}

static inline int next_code_int(context_t* c) {
    int v = *(int*)c->ip;
    set_ip(c, c->ip + sizeof(int));
    return v;
}

static inline uint8_t next_code_byte(context_t* c) {
    uint8_t v = *c->ip;
    set_ip(c, c->ip + 1);
    return v;
}

static inline size_t* get_stack_sp() { return (size_t*)(__gc_stack_top + 4); }

static inline void set_stack_sp(context_t* c, const size_t* to) {
    ASSERT(c->stack.p <= to, "Overflow stack");
    ASSERT(to <= c->stack.p + c->stack.n, "Underflow stack");

    __gc_stack_top = (size_t)to - 4;
}

static inline void* get_closure_from_stack(context_t* c) {
    ASSERT(c->is_closure, "not in closure");
    return (void*)c->args.p[1];
}

static inline void init_closed(context_t* c) {
    void* closure = get_closure_from_stack(c);
    c->closed.n = LEN(TO_DATA(closure)->data_header) - 1;
    c->closed.p = (size_t*)closure + 1;
}

size_t get_stack_size(context_t* c) { return c->stack.p + c->stack.n - get_stack_sp(); }

// move sp and write value
static inline void push_stack(context_t* c, size_t v) {
    size_t* sp = get_stack_sp();
    set_stack_sp(c, sp - 1);
    *(sp - 1) = v;
}

static inline void push_stack_boxed(context_t* c, size_t v) { push_stack(c, BOX(v)); }

// read value and move sp
static inline size_t pop_stack(context_t* c) {
    size_t* sp = get_stack_sp();
    size_t v = *sp;
    set_stack_sp(c, sp + 1);
    return v;
}

static inline void drop_stack_n(context_t* c, size_t n) { set_stack_sp(c, get_stack_sp() + n); }

static inline size_t pop_stack_unboxed(context_t* c) {
    size_t v = pop_stack(c);
    ASSERT(UNBOXED(v), "expect unboxed");
    return UNBOX(v);
}

static inline size_t is_stack_empty(context_t* c) { return get_stack_size(c) == 0; }

static inline size_t peek_stack_i(context_t* c, size_t i) {
    size_t* p = get_stack_sp() + i;
    ASSERT(c->stack.p < p && p < c->stack.p + c->stack.n, "Out of bounds stack");
    return *p;
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

static inline int32_t do_binop(int32_t x, int32_t y, uint8_t op) {
    const int OP_ADD = 0;
    const int OP_SUBTRACT = 1;
    const int OP_MULTIPLY = 2;
    const int OP_DIVIDE = 3;
    const int OP_MODULO = 4;
    const int OP_LESS_THAN = 5;
    const int OP_LESS_THAN_OR_EQUAL = 6;
    const int OP_GREATER_THAN = 7;
    const int OP_GREATER_THAN_OR_EQUAL = 8;
    const int OP_EQUAL = 9;
    const int OP_NOT_EQUAL = 10;
    const int OP_AND = 11;
    const int OP_OR = 12;
    switch (op) {
        case OP_ADD:
            return x + y;
        case OP_SUBTRACT:
            return x - y;
        case OP_MULTIPLY:
            return x * y;
        case OP_DIVIDE:
            return x / y;
        case OP_MODULO:
            return x % y;
        case OP_LESS_THAN:
            return x < y;
        case OP_LESS_THAN_OR_EQUAL:
            return x <= y;
        case OP_GREATER_THAN:
            return x > y;
        case OP_GREATER_THAN_OR_EQUAL:
            return x >= y;
        case OP_EQUAL:
            return x == y;
        case OP_NOT_EQUAL:
            return x != y;
        case OP_AND:
            return x && y;
        case OP_OR:
            return x || y;
    }
    failure("Unknown operation");
    return 0;
}

static inline void handle_binop(context_t* c, uint8_t l) {
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
    void* sexp = Bsexp_init_from_end(BOX(n), LtagHash(tag), get_stack_sp());
    drop_stack_n(c, n);
    push_stack(c, (size_t)sexp);
}

static inline void handle_sti(context_t* c) {
    size_t value = pop_stack(c);
    size_t var = pop_stack(c);
    *(size_t *)var = value;
}

static inline void handle_sta(context_t* c) {
    void* value = (void*)pop_stack(c);
    size_t idx_or_var = pop_stack(c);
    void* x = UNBOXED(idx_or_var) ? (void*)pop_stack(c) : (void*)idx_or_var;
    push_stack(c, (size_t)Bsta(value, idx_or_var, x));
}

static inline void handle_drop(context_t* c) { pop_stack(c); }

static inline void handle_dup(context_t* c) { push_stack(c, peek_stack(c)); }

static inline void handle_swap(context_t* c) {
    size_t x = pop_stack(c);
    size_t y = pop_stack(c);
    push_stack(c, x);
    push_stack(c, y);
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
        set_ip(c, c->code.p + offset);
}

static inline void handle_cjmpnz(context_t* c) {
    int offset = next_code_int(c);
    size_t cond = pop_stack_unboxed(c);
    if (cond != 0)
        set_ip(c, c->code.p + offset);
}

static inline void handle_jump(context_t* c) {
    int offset = next_code_int(c);
    set_ip(c, c->code.p + offset);
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
    c->bp = get_stack_sp();
    c->args.n = next_code_int(c);
    c->args.p = c->bp + c->args.n - 1;
    c->locals.n = next_code_int(c);
    for (int i = 0; i < c->locals.n; i++) {
        push_stack_boxed(c, 0);
    }
    c->locals.p = get_stack_sp();
    c->closed.n = 0;
    c->closed.p = 0;

    push_cstack(c, prev_args_n);
    push_cstack(c, prev_locals_n);
    push_cstack(c, (size_t)prev_bp);
}

static inline void handle_cbegin(context_t* c) {
    handle_begin(c);
    init_closed(c);
}

/*
Stack:
        <---- sp
    ret val
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
    set_ip(c, (uint8_t*)pop_cstack(c));

    c->locals.p = c->bp - c->locals.n;
    c->args.p = c->bp + (c->args.n - 1);

    if (c->is_closure)
        init_closed(c);

    return false;
}

static inline void handle_callc(context_t* c) {
    int args_n = next_code_int(c);
    void* closure = (void*)peek_stack_i(c, args_n);
    size_t closure_offset = (size_t)Belem(closure, BOX(0));
    push_cstack(c, (size_t)(c->ip));
    push_cstack(c, (size_t)c->is_closure);

    set_ip(c, c->code.p + closure_offset);
    c->is_closure = true;
}

static inline void handle_call(context_t* c) {
    int offset = next_code_int(c);
    int args_n = next_code_int(c);
    push_cstack(c, (size_t)(c->ip));
    push_cstack(c, (size_t)c->is_closure);

    set_ip(c, c->code.p + offset);
    c->is_closure = false;
}

static inline void handle_ret(context_t* c) {
    handle_end(c); // they same in lama ocaml realisation
}

static inline void handle_clojure(context_t* c) {
    uint8_t* closure_offset = (uint8_t*)next_code_int(c);
    int closed_n = next_code_int(c);
    for (int i = 0; i < closed_n; i++) {
        MEM mem = (MEM)next_code_byte(c);
        int idx = next_code_int(c);
        push_stack(c, *get_memory(c, mem, idx));
    }

    void* closure = Bclosure_init_from_end(BOX(closed_n), closure_offset, get_stack_sp());

    drop_stack_n(c, closed_n);

    push_stack(c, (size_t)closure);
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
    int n = next_code_int(c);
    void* x = (void*)pop_stack(c);
    size_t res = Barray_patt(x, BOX(n));
    push_stack(c, res);
}

static inline void handle_fail(context_t* c) {
    int x = next_code_int(c);
    int y = next_code_int(c);
    failure("fail: %d, %d");
}

static inline void handle_line(context_t* c) {
    next_code_int(c);  // ignore
}

static inline size_t do_patt(context_t* c, int op) {
    const int OPERATION_STRING_PATT = 0;
    const int OPERATION_STRING_TAG_PATT = 1;
    const int OPERATION_ARRAY_TAG_PATT = 2;
    const int OPERATION_SEXP_TAG_PATT = 3;
    const int OPERATION_BOXED_PATT = 4;
    const int OPERATION_UNBOXED_PATT = 5;
    const int OPERATION_CLOSURE_TAG_PATT = 6;

    void* x = (void*)pop_stack(c);
    switch (op) {
        case OPERATION_STRING_PATT: {
            void* y = (void*)pop_stack(c);
            return Bstring_patt(x, y);
        }
        case OPERATION_STRING_TAG_PATT:
            return Bstring_tag_patt(x);
        case OPERATION_ARRAY_TAG_PATT:
            return Barray_tag_patt(x);
        case OPERATION_SEXP_TAG_PATT:
            return Bsexp_tag_patt(x);
        case OPERATION_BOXED_PATT:
            return Bboxed_patt(x);
        case OPERATION_UNBOXED_PATT:
            return Bunboxed_patt(x);
        case OPERATION_CLOSURE_TAG_PATT:
            return Bclosure_tag_patt(x);
    }
}

static inline void handle_patt(context_t* c, int l) {
    size_t res = do_patt(c, l);
    push_stack(c, res);
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
    void* arr = Barray_init_from_end(BOX(n), get_stack_sp());
    drop_stack_n(c, n);
    push_stack(c, (size_t)arr);
}

/* Disassembles the bytecode pool */
void disassemble(FILE* f, bytefile* bf) {
#define FAIL failure("ERROR: invalid opcode %d-%d\n", h, l)
    const int INSTRUCTION_EXIT = 15;
    const int INSTRUCTION_BINOP = 0;
    const int INSTRUCTION_DATA = 1;
    const int INSTRUCTION_LD = 2;
    const int INSTRUCTION_LDA = 3;
    const int INSTRUCTION_ST = 4;
    const int INSTRUCTION_CONTROL = 5;
    const int INSTRUCTION_PATT = 6;
    const int INSTRUCTION_CALL = 7;

    const int DATA_CONST = 0;
    const int DATA_STRING = 1;
    const int DATA_SEXP = 2;
    const int DATA_STI = 3;
    const int DATA_STA = 4;
    const int DATA_JUMP = 5;
    const int DATA_END = 6;
    const int DATA_RET = 7;
    const int DATA_DROP = 8;
    const int DATA_DUP = 9;
    const int DATA_SWAP = 10;
    const int DATA_ELEM = 11;

    const int CONTROL_CJMPZ = 0;
    const int CONTROL_CJMPNZ = 1;
    const int CONTROL_BEGIN = 2;
    const int CONTROL_CBEGIN = 3;
    const int CONTROL_CLOJURE = 4;
    const int CONTROL_CALLC = 5;
    const int CONTROL_CALL = 6;
    const int CONTROL_TAG = 7;
    const int CONTROL_ARRAY = 8;
    const int CONTROL_FAIL = 9;
    const int CONTROL_LINE = 10;

    const int CALL_READ = 0;
    const int CALL_WRITE = 1;
    const int CALL_LENGTH = 2;
    const int CALL_STRING = 3;
    const int CALL_ARRAY = 4;

    __init();  // init lama gc
    context_t context;
    size_t global_size = bf->global_area_size;
    size_t* data_mem = malloc(STACK_SIZE * sizeof(size_t) * 2 + global_size * sizeof(size_t));
    context.cstack.begin = data_mem;
    context.cstack.n = STACK_SIZE;
    context.cstack.sp = context.cstack.begin + context.cstack.n;

    context.stack.p = data_mem + STACK_SIZE;
    context.stack.n = STACK_SIZE;

    context.globals.p = data_mem + STACK_SIZE * 2;
    context.globals.n = global_size;
    for (int i = 0; i < global_size; i++)
        context.globals.p[i] = 0;

    context.code.p = (uint8_t*)bf->code_ptr;
    context.code.n = bf->code_size;
    set_ip(&context, context.code.p);

    context.string_area.p = bf->string_ptr;
    context.string_area.n = bf->stringtab_size;
    context.is_closure = false;

    set_stack_sp(&context, context.stack.p + context.stack.n);
    __gc_stack_bottom = (size_t)(data_mem + STACK_SIZE * 2 + global_size);

    push_stack_boxed(&context, 0);
    push_stack_boxed(&context, 0);  // because main's BEGIN 2 0
    context.bp = get_stack_sp();

    do {
        uint8_t x = next_code_byte(&context), h = (x & 0xF0) >> 4, l = x & 0x0F;

        switch (h) {
            case INSTRUCTION_EXIT:
                return;

            case INSTRUCTION_BINOP:
                handle_binop(&context, l);
                break;

            case INSTRUCTION_DATA:
                switch (l) {
                    case DATA_CONST:
                        handle_const(&context);
                        break;
                    case DATA_STRING:
                        handle_string(&context);
                        break;
                    case DATA_SEXP:
                        handle_sexp(&context);
                        break;
                    case DATA_STI:
                        handle_sti(&context);
                        break;
                    case DATA_STA:
                        handle_sta(&context);
                        break;
                    case DATA_JUMP:
                        handle_jump(&context);
                        break;
                    case DATA_END:
                        if (handle_end(&context))
                            return;
                        break;
                    case DATA_RET:
                        handle_ret(&context);
                        break;
                    case DATA_DROP:
                        handle_drop(&context);
                        break;
                    case DATA_DUP:
                        handle_dup(&context);
                        break;
                    case DATA_SWAP:
                        handle_swap(&context);
                        break;
                    case DATA_ELEM:
                        handle_elem(&context);
                        break;
                    default:
                        FAIL;
                }
                break;

            case INSTRUCTION_LD:
                handle_ld(&context, l);
                break;
            case INSTRUCTION_LDA:
                handle_lda(&context, l);
                break;
            case INSTRUCTION_ST:
                handle_st(&context, l);
                break;

            case INSTRUCTION_CONTROL:
                switch (l) {
                    case CONTROL_CJMPZ:
                        handle_cjmpz(&context);
                        break;
                    case CONTROL_CJMPNZ:
                        handle_cjmpnz(&context);
                        break;
                    case CONTROL_BEGIN:
                        handle_begin(&context);
                        break;
                    case CONTROL_CBEGIN:
                        handle_cbegin(&context);
                        break;
                    case CONTROL_CLOJURE:
                        handle_clojure(&context);
                        break;
                    case CONTROL_CALLC:
                        handle_callc(&context);
                        break;
                    case CONTROL_CALL:
                        handle_call(&context);
                        break;
                    case CONTROL_TAG:
                        handle_tag(&context);
                        break;
                    case CONTROL_ARRAY:
                        handle_array(&context);
                        break;
                    case CONTROL_FAIL:
                        handle_fail(&context);
                        break;
                    case CONTROL_LINE:
                        handle_line(&context);
                        break;
                    default:
                        FAIL;
                }
                break;

            case INSTRUCTION_PATT:
                handle_patt(&context, l);
                break;

            case INSTRUCTION_CALL:
                switch (l) {
                    case CALL_READ:
                        handle_call_read(&context);
                        break;
                    case CALL_WRITE:
                        handle_call_write(&context);
                        break;
                    case CALL_LENGTH:
                        handle_call_length(&context);
                        break;
                    case CALL_STRING:
                        handle_call_string(&context);
                        break;
                    case CALL_ARRAY:
                        handle_call_array(&context);
                        break;
                    default:
                        FAIL;
                }
                break;

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

    file = (bytefile*)malloc(sizeof(bytefile) + (size = ftell(f)));

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
    file->code_size = size - (file->public_symbols_number * 2 * sizeof(int)) - file->stringtab_size;

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
