/* Exact induced-subgraph incidence scanner for R(4,4,12).
 * Dependency-free C ABI: build with Lean's clang using -O3 -mbmi2.
 */
typedef unsigned char u8;
typedef signed short i16;
typedef unsigned short u16;
typedef unsigned int u32;
typedef unsigned long long u64;
typedef unsigned long long usize;
typedef struct _iobuf FILE;

extern FILE *fopen(const char *, const char *);
extern int fclose(FILE *);
extern char *fgets(char *, int, FILE *);
extern usize fread(void *, usize, usize, FILE *);
extern usize fwrite(const void *, usize, usize, FILE *);
extern int printf(const char *, ...);
extern int strcmp(const char *, const char *);
extern usize strlen(const char *);
extern void *malloc(usize);
extern void *calloc(usize, usize);
extern void free(void *);
extern void *memset(void *, int, usize);
extern __declspec(dllimport) u64 __stdcall GetTickCount64(void);

#define MAX_CANDIDATES 1024
#define MAX_LINE 128
#define MAP8_LOG2 24
#define MAP8_SIZE (1U << MAP8_LOG2)
#define MAP8_EMPTY 0xffffffffU

typedef struct { u64 lo; u8 hi; } EdgeMask66;
typedef struct {
    int order;
    char record[24];
    u16 adj[8];
} Candidate;
typedef struct {
    Candidate candidates[MAX_CANDIDATES];
    int count;
    int count7;
    int count8;
    i16 *map7;
    u32 *map8_keys;
    u16 *map8_values;
    u64 map8_unique;
    u64 map8_duplicates;
} Catalogue;

static void fail(const char *message) {
    printf("ERROR %s\n", message);
    __builtin_trap();
}

static int popcount64(u64 value) { return __builtin_popcountll(value); }
static int ctz64(u64 value) { return __builtin_ctzll(value); }
static u64 pext64(u64 value, u64 mask) {
    return __builtin_ia32_pext_di(value, mask);
}

/* graph6 orders edge bits by columns: 01,02,12,03,13,23,... */
static int edge_position(int i, int j) {
    if (i > j) { int t = i; i = j; j = t; }
    return j * (j - 1) / 2 + i;
}

static int parse_graph6(const char *record, int *order, EdgeMask66 *mask, u16 *adj) {
    usize length = strlen(record);
    int n, edge_count, k;
    while (length && (record[length - 1] == '\n' || record[length - 1] == '\r')) --length;
    if (!length || record[0] == '~' || (u8)record[0] < 63 || (u8)record[0] > 125) return 0;
    n = (int)((u8)record[0] - 63);
    edge_count = n * (n - 1) / 2;
    if (length < (usize)(1 + (edge_count + 5) / 6)) return 0;
    mask->lo = 0; mask->hi = 0;
    if (adj) { int i; for (i = 0; i < n; ++i) adj[i] = 0; }
    for (k = 0; k < edge_count; ++k) {
        int payload = (int)((u8)record[1 + k / 6] - 63);
        if ((payload >> (5 - k % 6)) & 1) {
            if (k < 64) mask->lo |= 1ULL << k;
            else mask->hi |= (u8)(1U << (k - 64));
            if (adj) {
                int j = 1;
                int i;
                while (j * (j + 1) / 2 <= k) ++j;
                i = k - j * (j - 1) / 2;
                adj[i] |= (u16)(1U << j);
                adj[j] |= (u16)(1U << i);
            }
        }
    }
    *order = n;
    return 1;
}

static int copy_record(char *destination, const char *source) {
    int i = 0;
    while (source[i] && source[i] != '\r' && source[i] != '\n' && source[i] != ' ' && source[i] != '\t') {
        if (i == 22) return 0;
        destination[i] = source[i];
        ++i;
    }
    destination[i] = 0;
    return i;
}

static u32 permutation_mask(const Candidate *candidate, const u8 *permutation) {
    u32 result = 0;
    int i, j, k = 0;
    for (j = 1; j < candidate->order; ++j) {
        for (i = 0; i < j; ++i) {
            if (candidate->adj[permutation[i]] & (u16)(1U << permutation[j])) result |= 1U << k;
            ++k;
        }
    }
    return result;
}

static u32 hash8(u32 key) {
    key ^= key >> 16; key *= 0x7feb352dU;
    key ^= key >> 15; key *= 0x846ca68bU;
    return key ^ (key >> 16);
}

static void insert8(Catalogue *catalogue, u32 key, u16 value) {
    u32 slot = hash8(key) & (MAP8_SIZE - 1U);
    for (;;) {
        if (catalogue->map8_keys[slot] == MAP8_EMPTY) {
            catalogue->map8_keys[slot] = key;
            catalogue->map8_values[slot] = value;
            ++catalogue->map8_unique;
            return;
        }
        if (catalogue->map8_keys[slot] == key) {
            if (catalogue->map8_values[slot] != value) fail("isomorphic order-8 candidate records");
            ++catalogue->map8_duplicates;
            return;
        }
        slot = (slot + 1U) & (MAP8_SIZE - 1U);
    }
}

static int lookup8(const Catalogue *catalogue, u32 key) {
    u32 slot = hash8(key) & (MAP8_SIZE - 1U);
    for (;;) {
        if (catalogue->map8_keys[slot] == MAP8_EMPTY) return -1;
        if (catalogue->map8_keys[slot] == key) return (int)catalogue->map8_values[slot];
        slot = (slot + 1U) & (MAP8_SIZE - 1U);
    }
}

static void add_permutations(Catalogue *catalogue, int id, u8 *permutation, int position) {
    Candidate *candidate = &catalogue->candidates[id];
    int i;
    if (position == candidate->order) {
        u32 mask = permutation_mask(candidate, permutation);
        if (candidate->order == 7) {
            int old = (int)catalogue->map7[mask];
            if (old >= 0 && old != id) fail("isomorphic order-7 candidate records");
            catalogue->map7[mask] = (i16)id;
        } else insert8(catalogue, mask, (u16)id);
        return;
    }
    for (i = position; i < candidate->order; ++i) {
        u8 t = permutation[position]; permutation[position] = permutation[i]; permutation[i] = t;
        add_permutations(catalogue, id, permutation, position + 1);
        t = permutation[position]; permutation[position] = permutation[i]; permutation[i] = t;
    }
}

static void load_candidates(Catalogue *catalogue, const char *path) {
    FILE *stream = fopen(path, "rb");
    char line[MAX_LINE];
    int phase8 = 0;
    if (!stream) fail("cannot open candidate list");
    while (fgets(line, MAX_LINE, stream)) {
        Candidate *candidate;
        EdgeMask66 mask;
        int declared, order, offset = 0, i;
        if (line[0] == '#' || line[0] == '\r' || line[0] == '\n') continue;
        if (line[0] == '7') declared = 7;
        else if (line[0] == '8') declared = 8;
        else fail("candidate line must start with order 7 or 8");
        while (line[offset] && line[offset] != ' ' && line[offset] != '\t') ++offset;
        while (line[offset] == ' ' || line[offset] == '\t') ++offset;
        if (catalogue->count == MAX_CANDIDATES) fail("too many candidates");
        candidate = &catalogue->candidates[catalogue->count];
        if (!copy_record(candidate->record, line + offset)) fail("invalid candidate graph6 field");
        if (!parse_graph6(candidate->record, &order, &mask, candidate->adj) || order != declared) {
            fail("candidate order mismatch");
        }
        candidate->order = order;
        if (order == 7) {
            if (phase8) fail("order-7 candidates must precede order-8 candidates");
            ++catalogue->count7;
        } else { phase8 = 1; ++catalogue->count8; }
        ++catalogue->count;
        (void)i;
    }
    fclose(stream);
    if (!catalogue->count) fail("at least one candidate is required");
}

static void initialize_catalogue(Catalogue *catalogue, const char *path) {
    int i;
    u8 permutation[8];
    memset(catalogue, 0, sizeof(*catalogue));
    catalogue->map7 = (i16 *)malloc((usize)(1U << 21) * sizeof(i16));
    catalogue->map8_keys = (u32 *)malloc((usize)MAP8_SIZE * sizeof(u32));
    catalogue->map8_values = (u16 *)malloc((usize)MAP8_SIZE * sizeof(u16));
    if (!catalogue->map7 || !catalogue->map8_keys || !catalogue->map8_values) fail("map allocation failed");
    memset(catalogue->map7, -1, (usize)(1U << 21) * sizeof(i16));
    memset(catalogue->map8_keys, 0xff, (usize)MAP8_SIZE * sizeof(u32));
    load_candidates(catalogue, path);
    for (i = 0; i < catalogue->count; ++i) {
        int j;
        for (j = 0; j < catalogue->candidates[i].order; ++j) permutation[j] = (u8)j;
        add_permutations(catalogue, i, permutation, 0);
    }
}

static void combination_rec(int choose, int start, int depth, u8 *vertices, EdgeMask66 *out, int *count) {
    int v;
    if (depth == choose) {
        EdgeMask66 mask = {0, 0};
        int i, j;
        for (j = 1; j < choose; ++j) for (i = 0; i < j; ++i) {
            int position = edge_position(vertices[i], vertices[j]);
            if (position < 64) mask.lo |= 1ULL << position;
            else mask.hi |= (u8)(1U << (position - 64));
        }
        out[(*count)++] = mask;
        return;
    }
    for (v = start; v <= 12 - (choose - depth); ++v) {
        vertices[depth] = (u8)v;
        combination_rec(choose, v + 1, depth + 1, vertices, out, count);
    }
}

static int combination_masks(int choose, EdgeMask66 *output) {
    u8 vertices[12];
    int count = 0;
    combination_rec(choose, 0, 0, vertices, output, &count);
    return count;
}

static u32 extract_induced(const EdgeMask66 *graph, const EdgeMask66 *subset) {
    u64 low = pext64(graph->lo, subset->lo);
    u64 high = pext64((u64)graph->hi, (u64)subset->hi);
    return (u32)(low | (high << popcount64(subset->lo)));
}

static u64 count_records(const char *path, u64 limit) {
    FILE *stream = fopen(path, "rb");
    char line[MAX_LINE];
    u64 count = 0;
    if (!stream) fail("cannot open R(4,4,12) catalogue");
    while ((!limit || count < limit) && fgets(line, MAX_LINE, stream)) ++count;
    fclose(stream);
    return count;
}

static void scan(
    const Catalogue *catalogue, const char *path, u64 graph_count,
    u64 words, u64 *coverage, u8 *witness
) {
    EdgeMask66 subsets7[792], subsets8[495];
    FILE *stream = fopen(path, "rb");
    char line[MAX_LINE];
    u64 index = 0;
    int count7 = combination_masks(7, subsets7);
    int count8 = combination_masks(8, subsets8);
    if (!stream) fail("cannot open R(4,4,12) catalogue");
    if (count7 != 792 || count8 != 495) fail("subset enumeration mismatch");
    while (index < graph_count && fgets(line, MAX_LINE, stream)) {
        EdgeMask66 graph;
        int order, i;
        if (!parse_graph6(line, &order, &graph, (u16 *)0) || order != 12) fail("invalid order-12 graph6");
        for (i = 0; i < count7; ++i) {
            int id = (int)catalogue->map7[extract_induced(&graph, &subsets7[i])];
            if (id >= 0) {
                coverage[(u64)id * words + index / 64] |= 1ULL << (index % 64);
                if (witness && witness[3 * index] == 0xff) {
                    witness[3 * index] = (u8)id;
                    witness[3 * index + 1] = (u8)(i & 0xff);
                    witness[3 * index + 2] = (u8)((i >> 8) & 0xff);
                }
            }
        }
        for (i = 0; i < count8; ++i) {
            int id = lookup8(catalogue, extract_induced(&graph, &subsets8[i]));
            if (id >= 0) coverage[(u64)id * words + index / 64] |= 1ULL << (index % 64);
        }
        if (witness && witness[3 * index] == 0xff) fail("candidate list does not cover graph");
        ++index;
        if (index % 200000ULL == 0) printf("PROGRESS %llu/%llu\n", index, graph_count);
    }
    fclose(stream);
    if (index != graph_count) fail("order-12 catalogue ended early");
}

static void write_u32(FILE *stream, u32 value) { if (fwrite(&value, 4, 1, stream) != 1) fail("write failed"); }
static void write_u64(FILE *stream, u64 value) { if (fwrite(&value, 8, 1, stream) != 1) fail("write failed"); }

static void write_incidence(const Catalogue *catalogue, const char *path, u64 graph_count, u64 words, const u64 *coverage) {
    static const char magic[8] = {'R','4','4','C','O','V','1',0};
    FILE *stream = fopen(path, "wb");
    int i;
    if (!stream) fail("cannot create incidence file");
    if (fwrite(magic, 8, 1, stream) != 1) fail("write failed");
    write_u64(stream, graph_count);
    write_u64(stream, words);
    write_u64(stream, catalogue->map8_unique);
    write_u64(stream, catalogue->map8_duplicates);
    write_u32(stream, (u32)catalogue->count);
    write_u32(stream, (u32)catalogue->count7);
    write_u32(stream, (u32)catalogue->count8);
    write_u32(stream, 0);
    for (i = 0; i < catalogue->count; ++i) {
        char record[24];
        memset(record, 0, 24);
        copy_record(record, catalogue->candidates[i].record);
        if (fwrite(record, 24, 1, stream) != 1) fail("write failed");
    }
    if (fwrite(coverage, 8, (usize)catalogue->count * words, stream) != (usize)catalogue->count * words) {
        fail("coverage write failed");
    }
    fclose(stream);
}

static void write_witness(
    const Catalogue *catalogue, const char *path,
    u64 graph_count, const u8 *witness
) {
    static const char magic[8] = {'R','4','4','W','I','T','1',0};
    FILE *stream = fopen(path, "wb");
    int i;
    if (!stream) fail("cannot create witness file");
    if (fwrite(magic, 8, 1, stream) != 1) fail("write failed");
    write_u64(stream, graph_count);
    write_u32(stream, (u32)catalogue->count);
    write_u32(stream, 792U);
    for (i = 0; i < catalogue->count; ++i) {
        char record[24];
        memset(record, 0, 24);
        copy_record(record, catalogue->candidates[i].record);
        if (fwrite(record, 24, 1, stream) != 1) fail("write failed");
    }
    if (fwrite(witness, 3, (usize)graph_count, stream) != (usize)graph_count) {
        fail("witness write failed");
    }
    fclose(stream);
}
static int parse_u64(const char *text, u64 *value) {
    u64 result = 0;
    if (!*text) return 0;
    while (*text) { if (*text < '0' || *text > '9') return 0; result = result * 10 + (u64)(*text++ - '0'); }
    *value = result;
    return 1;
}

static int self_test(void) {
    EdgeMask66 complete, subsets[792];
    int order, count, i;
    if (!parse_graph6("K~~~~~~~~~~~", &order, &complete, (u16 *)0) || order != 12) return 1;
    if (popcount64(complete.lo) + popcount64((u64)complete.hi) != 66) return 2;
    count = combination_masks(7, subsets);
    if (count != 792) return 3;
    for (i = 0; i < count; ++i) if (popcount64(extract_induced(&complete, &subsets[i])) != 21) return 4;
    count = combination_masks(8, subsets);
    if (count != 495) return 5;
    for (i = 0; i < count; ++i) if (popcount64(extract_induced(&complete, &subsets[i])) != 28) return 6;
    printf("SELF_TEST_PASS\n");
    return 0;
}

int main(int argc, char **argv) {
    const char *candidate_path = (const char *)0, *graph_path = (const char *)0;
    const char *output_path = (const char *)0, *witness_path = (const char *)0;
    u64 limit = 0, graph_count, words, started, elapsed;
    u64 *coverage;
    u8 *witness = (u8 *)0;
    Catalogue catalogue;
    int i;
    if (argc == 2 && strcmp(argv[1], "--self-test") == 0) return self_test();
    for (i = 1; i < argc; ++i) {
        if (strcmp(argv[i], "--candidates") == 0 && i + 1 < argc) candidate_path = argv[++i];
        else if (strcmp(argv[i], "--r44-12") == 0 && i + 1 < argc) graph_path = argv[++i];
        else if (strcmp(argv[i], "--output") == 0 && i + 1 < argc) output_path = argv[++i];
        else if (strcmp(argv[i], "--witness") == 0 && i + 1 < argc) witness_path = argv[++i];
        else if (strcmp(argv[i], "--limit") == 0 && i + 1 < argc) {
            if (!parse_u64(argv[++i], &limit)) fail("invalid limit");
        } else { printf("usage: r44_cover_scan --candidates FILE --r44-12 FILE --output FILE [--limit N]\n"); return 2; }
    }
    if (!candidate_path || !graph_path || !output_path) { printf("missing required argument\n"); return 2; }
    started = GetTickCount64();
    initialize_catalogue(&catalogue, candidate_path);
    if (witness_path && (catalogue.count > 255 || catalogue.count8 != 0)) {
        fail("witness mode requires at most 255 order-7 candidates and no order-8 candidates");
    }
    graph_count = count_records(graph_path, limit);
    words = (graph_count + 63) / 64;
    coverage = (u64 *)calloc((usize)catalogue.count * words, sizeof(u64));
    if (!coverage) fail("coverage allocation failed");
    if (witness_path) {
        witness = (u8 *)malloc((usize)graph_count * 3);
        if (!witness) fail("witness allocation failed");
        memset(witness, 0xff, (usize)graph_count * 3);
    }
    printf("POOL order7=%d order8=%d map8_unique=%llu graphs=%llu\n",
        catalogue.count7, catalogue.count8, catalogue.map8_unique, graph_count);
    scan(&catalogue, graph_path, graph_count, words, coverage, witness);
    write_incidence(&catalogue, output_path, graph_count, words, coverage);
    if (witness_path) write_witness(&catalogue, witness_path, graph_count, witness);
    elapsed = GetTickCount64() - started;
    printf("SCAN_PASS graphs=%llu elapsed_ms=%llu output=%s\n", graph_count, elapsed, output_path);
    free(witness); free(coverage); free(catalogue.map7); free(catalogue.map8_keys); free(catalogue.map8_values);
    return 0;
}
