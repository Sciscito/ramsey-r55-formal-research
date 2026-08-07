/* Mixed order-7/order-8 witness scanner.
 *
 * Reuse the audited native scanner implementation in one translation unit,
 * but emit an order-aware witness format.  R44WIT1 cannot represent this
 * unambiguously because its header hard-codes 792 order-7 subsets.
 */
#define main r44_original_main_not_used
#include "../r45_d12_structural_cover/r44_cover_scan.c"
#undef main

static void scan_mixed(
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
        if (!parse_graph6(line, &order, &graph, (u16 *)0) || order != 12) {
            fail("invalid order-12 graph6");
        }
        for (i = 0; i < count7; ++i) {
            int id = (int)catalogue->map7[extract_induced(&graph, &subsets7[i])];
            if (id >= 0) {
                coverage[(u64)id * words + index / 64] |= 1ULL << (index % 64);
                if (witness[3 * index] == 0xff) {
                    witness[3 * index] = (u8)id;
                    witness[3 * index + 1] = (u8)(i & 0xff);
                    witness[3 * index + 2] = (u8)((i >> 8) & 0xff);
                }
            }
        }
        for (i = 0; i < count8; ++i) {
            int id = lookup8(catalogue, extract_induced(&graph, &subsets8[i]));
            if (id >= 0) {
                coverage[(u64)id * words + index / 64] |= 1ULL << (index % 64);
                if (witness[3 * index] == 0xff) {
                    witness[3 * index] = (u8)id;
                    witness[3 * index + 1] = (u8)(i & 0xff);
                    witness[3 * index + 2] = (u8)((i >> 8) & 0xff);
                }
            }
        }
        if (witness[3 * index] == 0xff) fail("candidate list does not cover graph");
        ++index;
        if (index % 200000ULL == 0) printf("PROGRESS %llu/%llu\n", index, graph_count);
    }
    fclose(stream);
    if (index != graph_count) fail("order-12 catalogue ended early");
}

static void write_mixed_witness(
    const Catalogue *catalogue, const char *path,
    u64 graph_count, const u8 *witness
) {
    static const char magic[8] = {'R','4','4','M','W','I','1',0};
    FILE *stream = fopen(path, "wb");
    int i;
    if (!stream) fail("cannot create mixed witness file");
    if (fwrite(magic, 8, 1, stream) != 1) fail("write failed");
    write_u64(stream, graph_count);
    write_u32(stream, (u32)catalogue->count);
    write_u32(stream, 792U);
    write_u32(stream, 495U);
    write_u32(stream, 24U);
    for (i = 0; i < catalogue->count; ++i) {
        u8 order = (u8)catalogue->candidates[i].order;
        char record[23];
        memset(record, 0, 23);
        copy_record(record, catalogue->candidates[i].record);
        if (fwrite(&order, 1, 1, stream) != 1) fail("write failed");
        if (fwrite(record, 23, 1, stream) != 1) fail("write failed");
    }
    if (fwrite(witness, 3, (usize)graph_count, stream) != (usize)graph_count) {
        fail("mixed witness write failed");
    }
    fclose(stream);
}

int main(int argc, char **argv) {
    const char *candidate_path = (const char *)0, *graph_path = (const char *)0;
    const char *output_path = (const char *)0, *witness_path = (const char *)0;
    u64 graph_count, words, started, elapsed;
    u64 *coverage;
    u8 *witness;
    Catalogue catalogue;
    int i;
    if (argc == 2 && strcmp(argv[1], "--self-test") == 0) return self_test();
    for (i = 1; i < argc; ++i) {
        if (strcmp(argv[i], "--candidates") == 0 && i + 1 < argc) candidate_path = argv[++i];
        else if (strcmp(argv[i], "--r44-12") == 0 && i + 1 < argc) graph_path = argv[++i];
        else if (strcmp(argv[i], "--output") == 0 && i + 1 < argc) output_path = argv[++i];
        else if (strcmp(argv[i], "--witness") == 0 && i + 1 < argc) witness_path = argv[++i];
        else { printf("usage: mixed_witness_scan --candidates FILE --r44-12 FILE --output FILE --witness FILE\n"); return 2; }
    }
    if (!candidate_path || !graph_path || !output_path || !witness_path) return 2;
    started = GetTickCount64();
    initialize_catalogue(&catalogue, candidate_path);
    if (catalogue.count > 255) fail("mixed witness supports at most 255 candidates");
    graph_count = count_records(graph_path, 0);
    words = (graph_count + 63) / 64;
    coverage = (u64 *)calloc((usize)catalogue.count * words, sizeof(u64));
    witness = (u8 *)malloc((usize)graph_count * 3);
    if (!coverage || !witness) fail("allocation failed");
    memset(witness, 0xff, (usize)graph_count * 3);
    printf("POOL order7=%d order8=%d graphs=%llu\n", catalogue.count7, catalogue.count8, graph_count);
    scan_mixed(&catalogue, graph_path, graph_count, words, coverage, witness);
    write_incidence(&catalogue, output_path, graph_count, words, coverage);
    write_mixed_witness(&catalogue, witness_path, graph_count, witness);
    elapsed = GetTickCount64() - started;
    printf("MIXED_SCAN_PASS graphs=%llu elapsed_ms=%llu\n", graph_count, elapsed);
    free(witness); free(coverage); free(catalogue.map7); free(catalogue.map8_keys); free(catalogue.map8_values);
    return 0;
}
