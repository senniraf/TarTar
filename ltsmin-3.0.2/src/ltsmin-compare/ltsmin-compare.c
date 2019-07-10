// -*- tab-width:4 ; indent-tabs-mode:nil -*-
#include <hre/config.h>

#include <hre/user.h>
#include <lts-io/user.h>
#include <lts-lib/lts.h>
#include <lts-lib/lowmem.h>
#include <ltsmin-lib/ltsmin-standard.h>

typedef enum {
	Undefined = 0, Strong, Branching, Trace, Lumping, Weak
} task_t;

static task_t task = Undefined;
static int divergence_sensitive = 0;
static int stuttering = 0;

static void trace_compare(lts_t lts) {
	if (stuttering) {
		Print(info, "reducing modulo silent step bisimulation");
		if (lts->label != NULL && lts->properties == NULL) {
			lts_silent_compress(lts, tau_step, NULL);
		} else if (lts->label == NULL && lts->properties != NULL) {
			lts_silent_compress(lts, stutter_step, NULL);
		} else {
			Abort(
					"silent step compression requires either state labels or edge labels");
		}
	} else {
		Print(info, "reducing modulo strong bisimulation");
		lowmem_strong_reduce(lts);
	}
	Print(info, "result has %u roots, %u states and %u transitions",
			lts->root_count, lts->states, lts->transitions);
	if (lts->root_count == 1)
		return;
	Print(info, "determinizing");
	lts_mkdet(lts);
	Print(info, "result has %u roots, %u states and %u transitions",
			lts->root_count, lts->states, lts->transitions);
	if (lts->root_count == 1)
		return;
	Print(info, "reducing modulo strong bisimulation");
	lowmem_strong_reduce(lts);
	Print(info, "result has %u roots, %u states and %u transitions",
			lts->root_count, lts->states, lts->transitions);
}

static struct poptOption options[] = { { "strong", 's', POPT_ARG_VAL, &task,
		Strong, "compare modulo strong bisimulation", NULL }, { "branching",
		'b', POPT_ARG_VAL, &task, Branching,
		"compare modulo branching bisimulation", NULL }, { "weak", 'w',
		POPT_ARG_VAL, &task, Weak, "compare modulo weak bisimulation", NULL }, {
		"divergence", 0, POPT_ARG_VAL, &divergence_sensitive, 1,
		"make branching bisimulation divergence sensitive", NULL }, { "lump",
		'l', POPT_ARG_VAL, &task, Lumping, "compare modulo lumping of CTMC",
		NULL }, { "trace", 't', POPT_ARG_VAL, &task, Trace,
		"compare modulo trace equivalence", NULL }, { "stutter", 0,
		POPT_ARG_VAL, &stuttering, 1,
		"allow stuttering during trace equivalence", NULL },
POPT_TABLEEND };

static const size_t BUFLEN = 65536;

lts_t ta_lts_encode_edge(lts_t lts) {
	lts_t res = lts_create();
	lts_set_type(res, LTS_LIST);
	lts_set_sig(res, single_action_type());
	lts_set_type(lts, LTS_LIST);
	uint32_t temp = lts->transitions + lts->root_count;
	int V = lts_type_get_state_length(lts->ltstype) - 2;
	if (V)
		temp += lts->states;
	int N = lts_type_get_state_label_count(lts->ltstype) - 2;
	if (N)
		temp += lts->states;
	//ignore DBM matrix -> -2
	int K = lts_type_get_edge_label_count(lts->ltstype) - 2;
	lts_set_size(res, 1, lts->states + 1, temp);
	res->root_list[0] = 0;
	Print(infoShort, "init");
	int init = VTputChunk(res->values[0], chunk_str("init"));
	uint32_t edge = 0;
	for (uint32_t i = 0; i < lts->root_count; i++) {
		res->src[edge] = 0;
		res->dest[edge] = lts->root_list[i] + 1;
		res->label[edge] = init;
		edge++;
	}
	if (V) {
		int typeno[V];
		data_format_t format[V];
		for (int i = 0; i < V; i++) {
			typeno[i] = lts_type_get_state_typeno(lts->ltstype, i);
			format[i] = lts_type_get_format(lts->ltstype, typeno[i]);
		}
		int vector[V];
		for (uint32_t i = 0; i < lts->states; i++) {
			char label[BUFLEN];
			char *current = label;
			current += snprintf(current, BUFLEN, "state");
			TreeUnfold(lts->state_db, i, vector);
			for (int j = 0; j < V; j++) {
				switch (format[j]) {
				case LTStypeDirect:
				case LTStypeRange:
				case LTStypeSInt32: {
					char* label = "";
					int count = lts_type_get_state_label_count(lts->ltstype);
					//if(vector[j]<count)
					//	label = lts_type_get_state_label_name(lts->ltstype,count);
					printf("vertex2 %d %s\n", vector[j], label);
					printf("count %d\n", count);
					current += snprintf(current, BUFLEN, "|%d", vector[j]);
					break;
				}
				case LTStypeChunk:
				case LTStypeEnum: {
					chunk label_c = VTgetChunk(lts->values[typeno[j]],
							vector[j]);
					char label_s[label_c.len * 2 + 6];
					chunk2string(label_c, sizeof label_s, label_s);
					current += snprintf(current, BUFLEN, "|%s", label_s);
					break;
				}
				case LTStypeBool: // fall through
				case LTStypeTrilean: {
					char* value = NULL;
					switch (vector[j]) {
					case 0: {
						value = "false";
						break;
					}
					case 1: {
						value = "true";
						break;
					}
					case 2: {
						value = "maybe";
						break;
					}
					default: {
						Abort("Invalid value: %d", vector[j]);
					}
					}
					current += snprintf(current, BUFLEN, "|%s", value);
					break;
				}
				}
			}
			printf("Vertex: %s %s\n", label, current);
			res->src[edge] = i + 1;
			res->dest[edge] = i + 1;
			res->label[edge] = VTputChunk(res->values[0], chunk_str(label));
			;
			edge++;
		}
	}
	if (N) {
		int typeno[N];
		data_format_t format[N];
		for (int i = 0; i < N; i++) {
			typeno[i] = lts_type_get_state_label_typeno(lts->ltstype, i);
			format[i] = lts_type_get_format(lts->ltstype, typeno[i]);
		}
		int vector[N];
		for (uint32_t i = 0; i < lts->states; i++) {

			char label[BUFLEN];
			char *current = label;
			current += snprintf(current, BUFLEN, "prop");
			if (N == 1)
				vector[0] = lts->properties[i];
			if (N > 1) {
				TreeUnfold(lts->prop_idx, lts->properties[i], vector);
			}
			for (int j = 0; j < N; j++) {
				switch (format[j]) {
				case LTStypeDirect:
				case LTStypeRange:
				case LTStypeSInt32:
					current += snprintf(current, BUFLEN, "|%d", vector[j]);
					break;
				case LTStypeChunk:
				case LTStypeEnum: {
					chunk label_c = VTgetChunk(lts->values[typeno[j]],
							vector[j]);
					char label_s[label_c.len * 2 + 6];
					chunk2string(label_c, sizeof label_s, label_s);
					current += snprintf(current, BUFLEN, "|%s", label_s);
					break;
				}
				case LTStypeBool:
				case LTStypeTrilean: {
					char* value = NULL;
					switch (vector[j]) {
					case 0: {
						value = "false";
						break;
					}
					case 1: {
						value = "true";
						break;
					}
					case 2: {
						value = "maybe";
						break;
					}
					default: {
						Abort("Invalid value: %d", vector[j]);
					}
					}
					current += snprintf(current, BUFLEN, "|%s", value);
					break;
				}
				}
			}
			printf("Prop %s %s\n", label, current);
			res->src[edge] = i + 1;
			res->dest[edge] = i + 1;
			res->label[edge] = VTputChunk(res->values[0], chunk_str(label));
			edge++;
		}
	}

	{
		int typeno[K];
		data_format_t format[K];
		for (int i = 0; i < K; i++) {
			typeno[i] = lts_type_get_edge_label_typeno(lts->ltstype, i);
			format[i] = lts_type_get_format(lts->ltstype, typeno[i]);
		}
		int vector[K];
		for (uint32_t i = 0; i < lts->transitions; i++) {
			char label[BUFLEN];
			char *current = label;
			if (K == 1)
				vector[0] = lts->label[i];
			current += snprintf(current, BUFLEN, "edge");
			if (K > 1) {
				TreeUnfold(lts->edge_idx, lts->label[i], vector);
			}
			for (int j = 0; j < K; j++) {
				switch (format[j]) {
				case LTStypeDirect:
				case LTStypeRange:
				case LTStypeSInt32:
					current += snprintf(current, BUFLEN, "|%d", vector[j]);
					break;
				case LTStypeChunk:
				case LTStypeEnum: {
					chunk label_c = VTgetChunk(lts->values[typeno[j]],
							vector[j]);
					char label_s[label_c.len * 2 + 6];
					chunk2string(label_c, sizeof label_s, label_s);
					current += snprintf(current, BUFLEN, "|%s", label_s);
					break;
				}
				case LTStypeBool:
				case LTStypeTrilean: {
					char* value = NULL;
					switch (vector[j]) {
					case 0: {
						value = "false";
						break;
					}
					case 1: {
						value = "true";
						break;
					}
					case 2: {
						value = "maybe";
						break;
					}
					default: {
						Abort("Invalid value: %d", vector[j]);
					}
					}
					current += snprintf(current, BUFLEN, "|%s", value);
					break;
				}
				}
			}
			int count =  lts_type_get_edge_label_count(lts->ltstype);
			printf("Edge max %d \n", count);
			printf("Edge %s %d %s \n", label, current, current);
			res->src[edge] = lts->src[i] + 1;
			res->dest[edge] = lts->dest[i] + 1;
			res->label[edge] = VTputChunk(res->values[0], chunk_str(label));
			edge++;
		}
	}
	return res;
}

lts_t exchangeLabels(lts_t org) {
	if (org->state_db == 0)
		return org;

	return ta_lts_encode_edge(org);
	/*lts_t abs = lts_create();

	 //abs->

	 lts_free(org);
	 return abs;*/
}

int main(int argc, char *argv[]) {
	HREinitBegin(argv[0]);
	HREaddOptions(options, "Tool for comparing LTSs\n\nOptions");
	char *files[2];
	lts_lib_setup();
	HREinitStart(&argc, &argv, 2, 2, files, "<input 1> <input 2>");
	if (task == Undefined) {
		Abort("please specify equivalence");
	}
	lts_t lts1 = lts_create();
	Print(infoShort, "reading %s", files[0]);
	lts_read(files[0], lts1);
	Print(infoShort, "first LTS has %u states and %u transitions", lts1->states,
			lts1->transitions);
	if (lts1->root_count != 1)
		Abort("First LTS must have 1 initial state");
	lts_t lts2 = lts_create();
	Print(infoShort, "reading %s", files[1]);
	lts_read(files[1], lts2);
	Print(infoShort, "second LTS has %u states and %u transitions",
			lts2->states, lts2->transitions);
	if (lts2->root_count != 1)
		Abort("Second LTS must have 1 initial state");

	lts1 = exchangeLabels(lts1);
	lts2 = exchangeLabels(lts2);

	Print(info, "merging the two LTSs");
	lts_merge(lts1, lts2);
	Print(info, "reducing merged LTS");

	switch (task) {
	case Strong: {
		lowmem_strong_reduce(lts1);
		break;
	}
	case Weak: {
		setbased_weak_reduce(lts1);
		break;
	}
	case Branching: {
		bitset_t divergence = NULL;
		if (divergence_sensitive) {
			divergence = bitset_create(256, 256);
			lts_find_divergent(lts1, tau_step, NULL, divergence);
		}
		lowmem_branching_reduce(lts1, divergence);
		break;
	}
	case Lumping: {
		lowmem_lumping_reduce(lts1);
		break;
	}
	case Trace: {
		trace_compare(lts1);
		break;
	}
	default:
		Abort("missing case")
		;
	}

	if (lts1->root_count == 1) {
		Print(infoShort, "LTSs are equivalent");
		//printf("LTSs are equivalent");
		HREexit(LTSMIN_EXIT_SUCCESS);
	} else {
		Print(infoShort, "LTSs are distinguishable");
		//printf("LTSs are distinguishable");
		HREexit(LTSMIN_EXIT_COUNTER_EXAMPLE);
	}
}
