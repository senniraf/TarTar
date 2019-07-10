#ifndef BUCHI_2947854_H
#define BUCHI_2947854_H

#include <pins-lib/pins.h>
//#include <pins-lib/modules/opaal-pins.h>
#include <pins2lts-mc/parallel/state-info.h>
//#include <pins2lts-mc/parallel/run.h>

extern void Buchi_addState(model_t model, state_data_t* state);

extern void Buchi_addTransition(model_t model, state_info_t *state, transition_info_t *ti, state_info_t *successor);

extern void Buchi_printTransitions();

extern void Buchi_end();

#endif //BUCHI_H
