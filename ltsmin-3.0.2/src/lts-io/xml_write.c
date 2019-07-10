#include <hre/config.h>

#include <assert.h>
#include <libgen.h>
#include <string.h>

#include <hre/dir_ops.h>
#include <hre-io/user.h>
#include <lts-io/internal.h>
#include <pins-lib/pins.h>

#include <stdio.h>
#include <stdlib.h>

//extern chunk pins_chunk_get (model_t model, int type_no, int index);

model_t model = 0;
FILE* xmlFile = 0;

const char* xml_file_open(const char* name) {
	xmlFile = fopen(name, "w");
	printf("xml open");
	fprintf(xmlFile, "<lts>");
	return "3state.gcf";
}

void xml_set_init(model_t model_p, void* init_state) {
	model = model_p;
	//fprintf(xmlFile, "<state init=\"true\" />\n");
	//printf("state init");
}

void xml_write_state(int count, int values[]) {
//void xml_write_state(lts_file_t lts, int all, void* state, int* labels) {
	if (xmlFile == 0)
		return;
	fprintf(xmlFile, "<state>");
	for (int i = 0; i < count; i++)
		if (i == 0)
			fprintf(xmlFile, "%d", values[i]);
		else
			fprintf(xmlFile, ",%d", values[i]);
	fprintf(xmlFile, "</state>\n");
	//int** label = (int**) labels;
	//(void) (*label);
}

void xml_write_zone(int* zone1, int* zone2) {
//	xml_write_state(count, values);
}

void xml_write_edge_state(const char* attr, int count, int values[])
{
	if (xmlFile == 0)
		return;
	fprintf(xmlFile, attr);
	fprintf(xmlFile, "='");
	for (int i = 0; i < count; i++)
		if (i == 0)
			fprintf(xmlFile, "%d", values[i]);
		else
			fprintf(xmlFile, ",%d", values[i]);
	fprintf(xmlFile, "' ");
}

void xml_write_edge_open()
{
	if (xmlFile == 0)
		return;
	fprintf(xmlFile, "<edge ");
}

void xml_write_edge(char* from, char* msg, char* to) {
	if (xmlFile == 0)
		return;

	//fprintf(xmlFile, "from=\"%s\" ", from);
	//fprintf(xmlFile, "to=\"%s\" ", to);
	fprintf(xmlFile, "label=\"%s\"", msg);

	fprintf(xmlFile, " />\n");
	//printf("xml edge");
}


void xml_file_close() {
	if (xmlFile == 0)
		return;
	fprintf(xmlFile, "</lts>");
	fclose(xmlFile);
	xmlFile = 0;
	printf("xml close");
}

