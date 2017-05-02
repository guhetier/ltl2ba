
/* This file contains the function required to
   print a Büchi automaton in C, and the analysis function
   to determine the stutter acceptance from a give state.
*/

#include "ltl2ba.h"

extern FILE* tl_out;

extern int accept;
extern BState *bstates;

int n_ba_state; /* Number of states in the ba */

/* Count the number of state in a BA */
int
count_ba_states() {
    BState *s;
    int n = 0;
    for (s = bstates->prv; s != bstates; s = s->prv)
        n++;
    return n;
}

/* Print a set of predicates */
void
c_print_set(int* pos, int* neg) {
    spin_print_set(pos, neg);
}

/* Print an enumeration containing the ba states */
void
print_c_states_definition() {
    BState *s;

    fprintf(tl_out, "typedef enum {\n");
    for (s = bstates->prv; s != bstates; s = s->prv)
        fprintf(tl_out, "\t_ltl2ba_state_%i_%i,\n", s->id + 1, s->final);
    fprintf(tl_out, "} _ltl2ba_sate;\n\n");
}

/* Print the transition function of the ba */
void
print_c_transition_function() {
    BState *s;
    BTrans *t;

    fprintf(tl_out, "void\n_ltl2ba_transition() {\n");

    /* If the automaton is empty (no states) */
    if (bstates->nxt == bstates) {
        fprintf(tl_out, "\tassume(0);\n}\n");
        return;
    }

    fprintf(tl_out, "\tint choice = NON_DET();\n");
    fprintf(tl_out, "\tswitch (_ltl2ba_state_var) {\n");

    for(s = bstates->prv; s != bstates; s = s->prv) {
        fprintf(tl_out, "\tcase _ltl2ba_sate_%i_%i:\n", s->id + 1, s->final);

        /* The state of id 0 is an accepting well.
           Every word will be accepted and the state will no longer change
        */
        if(s->id == 0) {
            fprintf(tl_out, "\t\tassert(false, \"Error sure\");\n");
            fprintf(tl_out, "\t\tbreak;\n");
            continue;
        }

        /* If there is no transition from this state */
        t = s->trans->nxt;
        if(t == s->trans) {
            fprintf(tl_out, "\t\tassume(0);\n");
            continue;
        }

        /* First transition from the current state */
        fprintf(tl_out, "\t\tif (choice == 0) {\n");
        fprintf(tl_out, "\t\t\tassume(");
        c_print_set(t->pos, t->neg);
        fprintf(tl_out, ");\n");
        fprintf(tl_out, "\t\t\t_ltl2ba_sate_var = _ltl2ba_state_%i_%i;\n",
                t->to->id + 1, t->to->final);
        fprintf(tl_out, "\t\t}");

        /* Other transition from the current state */
        int trans_num;
        for(trans_num = 1, t = s->trans->nxt->nxt; t != s->trans; t = t->nxt, trans_num++) {
            fprintf(tl_out, " else if (choice == %i) {\n", trans_num);
            fprintf(tl_out, "\t\t\tassume(");
            c_print_set(t->pos, t->neg);
            fprintf(tl_out, ");\n");
            fprintf(tl_out, "\t\t\t_ltl2ba_sate_var = _ltl2ba_state_%i_%i;\n",
                    t->to->id + 1, t->to->final);
            fprintf(tl_out, "\t\t}");
        }
        /* Prune other choices */
        fprintf(tl_out, " else {\n");
        fprintf(tl_out, "\t\t\tassume(0);\n");
        fprintf(tl_out, "\t\t}");

        fprintf(tl_out, "\n\t\tbreak;\n");
    }

    fprintf(tl_out, "\t}\n}\n\n");
}

/* Print the table indicating if from the current state,
   every word will be accepted (whatever the suffix)
*/
void
print_c_surely_accept_sate_table() {
    BState *s;

    fprintf(tl_out, "_Bool _ltl2ba_surely_accept[%i] = {", n_ba_state);

    /* No states in the ba */
    if (bstates->prv == bstates) {
        fprintf(tl_out, "};\n");
        return;
    }

    /* First state */
    s = bstates->prv;
    if (s->id == 0)
        fprintf(tl_out, "1");
    else
        fprintf(tl_out, "0");

    /* Following states */
    for (s = s->prv; s != bstates; s = s->prv) {
        /* TODO : is this true ??? It is the case only if the automaton is in reduced form... */
        /* As the automaton is in reduced form, only an accepting well
           will accept every words whatever the suffix.
           Accepting well have an id = 0 */
        if (s->id == 0)
            fprintf(tl_out, ", 1");
        else
            fprintf(tl_out, ", 0");
    }
    fprintf(tl_out, "};\n");
}

/* Print the table indicating if from the current state,
   every word will be rejected (whatever the suffix)
*/
void
print_c_surely_reject_sate_table() {
    BState *s;

    fprintf(tl_out, "_Bool _ltl2ba_surely_reject[%i] = {", n_ba_state);

    /* No states in the ba */
    if (bstates->prv == bstates) {
        fprintf(tl_out, "};\n");
        return;
    }

    /* First state */
    s = bstates->prv;
    fprintf(tl_out, "0");

    /* Following states */
    for (s = s->prv; s != bstates; s = s->prv) {
        /* TODO : is this true ??? It is the case only if the automaton is in reduced form... */
        /* As the automaton is in reduced form,
           no sate will reject every suffix (elsewhere, this sate would have been removed
           from the automaton) */
        fprintf(tl_out, ", 0");
    }
    fprintf(tl_out, "};\n");
}

void
print_c_buchi() {
    n_ba_state = count_ba_states();

    BTrans *t;
    BState *s;

    fprintf(tl_out, "/* ");
    put_uform();
    fprintf(tl_out, " */\n");

    print_c_states_definition();

    /* Declare and initialize the global variable that will maintain the state
       of the automaton.
       The initial sate has always an id of -1 (+1 in the name) and a final of 0.
    */
    fprintf(tl_out, "_ltl2ba_state _ltl2ba_state_var = _ltl2ba_sate_0_0;\n\n");

    print_c_transition_function();

    /* TODO: Surely accepting states are currently built under the assumption
       the automaton is in reduced form
    */
    print_c_surely_accept_sate_table();

    /* TODO: Surely rejecting states are currently built under the assumption
       the automaton is in reduced form
    */
    print_c_surely_reject_sate_table();

    /****** Print the array of stutter acceptance *****/
    fprintf(tl_out, "_Bool _ltl2ba_stutter_accept[%i][%i] = {\n", n_ba_state, 0/*TODO : program state count*/);
    for (s = bstates->prv; s != bstates; s = s->prv) {
        if (0 /* TODO */)
            fprintf(tl_out, "\t1,\n");
        else
            fprintf(tl_out, "\t0,\n");
    }
    fprintf(tl_out, "\t};\n");

    /****** Print the conclusion function ******/


}
