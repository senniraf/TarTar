#include <pins2lts-mc/algorithm/buchi.h>

#include <pins-lib/pins-util.h>

char* printStateNames(model_t model, state_info_t *state) {
	int value = 0;
	int max = 0;
	chunk val;
	int all = pins_get_state_variable_count(model);
	printf("all %d\n", all);
	int process_count = all - 2;
	for (int i = 1; i <= process_count; i++) {
		state_data_t data = state_info_pins_state(state);
		value = ((int*) data)[i - 1];
		max = pins_chunk_count(model, i);
		if (value < max) {
			val = pins_chunk_get(model, i, value);
			printf("State: %d %d %s\n", i, value, val.data);
		}
	}
	return "state";
}

char* getStateName(model_t model, state_data_t *state, int proc_idx) {
	int max = pins_chunk_count(model, proc_idx + 1);
	int value = ((int*) state)[proc_idx];
	if (value < max) {
		chunk name = pins_chunk_get(model, proc_idx + 1, value);
		return name.data;
	}
	return "";
}

int var_count = 0;
int first = 1;
void Buchi_addState(model_t model, state_data_t* state) {
	if (var_count == 0) {
		int all = pins_get_state_variable_count(model);
		var_count = all - 2;
	}
	int values[var_count];
	for (int i = 0; i < var_count; i++) {
		values[i] = ((int*) state)[i];
	}
	if (first == 1) {
		first = 0;
		xml_write_state(var_count, values);
	}
	xml_write_zone(values[var_count], values[var_count + 1]);
}

void Buchi_addTransition(model_t model, state_info_t *state,
		transition_info_t *ti, state_info_t *successor) {

	const char* msg = "";
	if (ti->labels != 0)
		for (int i = 0; i < 1; i++) {
			int idx = ti->labels[i];
			if (idx == 0)
				break;
			int len = lts_type_get_edge_label_count(GBgetLTStype(model));
			if (idx >= len)
				break;
			msg = lts_type_get_edge_label_name(GBgetLTStype(model), idx);
			//xml_write_edge("", label, "");
		}

	char* from = "";
	char* to = "";

	state_data_t data1 = state_info_pins_state(state);
	state_data_t data2 = state_info_pins_state(successor);

	/*for (int i = 0; i < var_count; i++) {
		int val1 = ((int*) data1)[i];
		int val2 = ((int*) data2)[i];
		char* from2 = getStateName(model, data1, i);
		printf("suc1: %d %s\n", i, from2);
		char* to2 = getStateName(model, data2, i);
		printf("suc2: %d %s\n", i, to2);
		if ((val1 > var_count) || (val2 > var_count)) {
			continue;
		}
		if (val1 != val2) {
			from = getStateName(model, data1, i);
			to = getStateName(model, data2, i);
			break;
		}
	}
	//self transition do not have a name
	if (strcmp(from, "") == 0) {
		from = getStateName(model, data1, 0);
		to = getStateName(model, data2, 0);
	}*/
	xml_write_edge_open();
	xml_write_edge_state("from", var_count, data1);
	xml_write_edge_state("to", var_count, data2);
	xml_write_edge(from, msg, to);
}

void Buchi_printTransitions() {
}

void Buchi_end() {
//printf("ende");
}
