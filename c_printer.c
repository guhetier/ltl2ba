
/* This file contains the function required to
   print a Büchi automaton in C, and the analysis function
   to determine the stutter acceptance from a give state.
*/

#include "ltl2ba.h"

extern FILE* tl_out;

extern int accept;
extern BState *bstates;

extern int sym_id, sym_size, mod;
extern char** sym_table;

const char* assume_str = "__ESBMC_assume";
const char* assert_str = "__ESBMC_assert";
const char* nondet_str = "nondet_uint";

int n_ba_state; /* Number of states in the ba */
BScc *scc_stack; /* Stack used for automaton explorations */
_Bool *stutter_acceptance_table;

/* Count the number of state in a BA */
int
count_ba_states() {
    BState *s;
    int n = 0;
    for (s = bstates->prv; s != bstates; s = s->prv)
        n++;
    return n;
}

/* Return true if the transition t can be used with
   a valuation prop_state of the atomic propositions
*/
_Bool
is_transition_valid(BTrans *t, int *prop_state) {
    int i;
    for (i = 0; i < sym_size; i++) {
        if ((t->pos[i] & prop_state[i]) != t->pos[i])
            return 0;
        if ((t->neg[i] & ~prop_state[i]) != t->neg[i])
            return 0;
    }
    return 1;
}

/* Determine whether the stutter extension of a word is accepted,
   given a state and a final program state (i.e a predicate valuation).
   WARNING : Use of the incoming field, does not anymore represent the scc...
   Explore the automaton using only the transition compatibles with the final program state.
   When a cycle containing a final state is found, mark all states leading to it
   as stutter accepting.
*/
void
stutter_acceptance_state(BState *s, int *stutter_state) {

    BTrans *t;
    BScc *c;
    BScc *scc = (BScc *)tl_emalloc(sizeof(BScc));

    /* Mark the state and add it in the stack */
    s->incoming = 1;
    scc->bstate = s;
    scc->nxt = scc_stack;

    /* Invariant : It is possible to reach the current state from
       every state on the stack */
    scc_stack = scc;

    /* Visit every successors reachable with the program state */
    for (t = s->trans->nxt; t != s->trans; t = t->nxt) {
        if (! is_transition_valid(t, stutter_state))
            continue;

        /* The successor have not been reached already */
        if (t->to->incoming == 0) {
            stutter_acceptance_state(t->to, stutter_state);
            /* If the successor is stutter-accepted */
            if (t->to->incoming == 3) {
                s->incoming = 3;
                scc_stack = scc_stack->nxt;
                return;
            }
        /* The successor is currently being visited : we found a cycle */
        } else if (t->to->incoming == 1) {
            /* Search for a final state in the cycle */
            _Bool final_cycle = 0;
            for(c = scc_stack; c != 0; c = c->nxt) {
                if (c->bstate->final == accept || c->bstate->id == 0)
                    final_cycle = 1;
                if (c->bstate == t->to)
                    break;
            }
            /* If there is final state in the cycle, all the state in the cycle are
               accepted. We mark the current one, others will be marked recursively */
            if (final_cycle) {
                s->incoming = 3;
                scc_stack = scc_stack->nxt;
                return;
            }
        /* The successor has already been visited */
        } else {
            /* If the successor lead to a final cycle, marks all the state as accepting */
            if (t->to->incoming == 3) {
                s->incoming = 3;
                scc_stack = scc_stack->nxt;
                return;
            }
        }
    }

    /* If no final cycle have been found, there is none from this state */
    if (s->incoming == 1) {
        s->incoming = 2;
        scc_stack = scc_stack->nxt;
    }
}

/* Compute the stutter acceptance for all automaton state and all final
   program state */
void
stutter_acceptance() {
    BState *s;
    scc_stack = 0;
    int i, k;
    int stutter_state[sym_size];

    if (sym_size > 1)
        fatal("c_printer, stutter_acceptance", "sym_size > 1 : too many states for an exploration");

    if(bstates == bstates->nxt)
        return;

    for (k = 0; k < (1 << sym_id); k++) {
        stutter_state[0] = k;

        /* Unmark all states */
        for (s = bstates->nxt; s != bstates; s = s->nxt)
            s->incoming = 0;

        /* Explore the graph from every state */
        for (s = bstates->nxt; s != bstates; s = s->nxt) {
            if (s->incoming == 0)
                stutter_acceptance_state(s, stutter_state);
        }

        /* Collect the results */
        for (s = bstates->nxt, i=0; s != bstates; s = s->nxt, i++) {
            if (s->incoming == 3)
                stutter_acceptance_table[k * n_ba_state + i] = 1;
            else
                stutter_acceptance_table[k * n_ba_state + i] = 0;
        }
    }
}

/* Print the condition of a transition */
void
c_print_set(int* pos, int* neg) {

    int i, j, start = 1;
    for(i = 0; i < sym_size; i++)
        for(j = 0; j < mod; j++) {
            if(pos[i] & (1 << j)) {
                if(!start)
                    fprintf(tl_out, " && ");
                fprintf(tl_out, "_ltl2ba_atomic_%s", sym_table[mod * i + j]);
                start = 0;
            }
            if(neg[i] & (1 << j)) {
                if(!start)
                    fprintf(tl_out, " && ");
                fprintf(tl_out, "!_ltl2ba_atomic_%s", sym_table[mod * i + j]);
                start = 0;
            }
        }
    if(start)
        fprintf(tl_out, "1");
}

/* Print variables for each atomic predicate */
void
print_c_atomics_definition() {
    int i;
    for (i = 0; i < sym_id; i++) {
        fprintf(tl_out, "_Bool _ltl2ba_atomic_%s = 0;\n", sym_table[i]);
    }
    fprintf(tl_out, "\n");
}

/* Print an enumeration containing the ba states */
void
print_c_states_definition() {
    BState *s;

    fprintf(tl_out, "typedef enum {\n");
    for (s = bstates->prv; s != bstates; s = s->prv)
        fprintf(tl_out, "\t_ltl2ba_state_%i_%i,\n", s->id + 1, s->final);
    fprintf(tl_out, "} _ltl2ba_state;\n\n");
}

/* Print the transition function of the ba */
void
print_c_transition_function() {
    BState *s;
    BTrans *t;

    fprintf(tl_out, "void\n_ltl2ba_transition() {\n");

    /* If the automaton is empty (no states) */
    if (bstates->nxt == bstates) {
        fprintf(tl_out, "\t%s(0);\n}\n", assume_str);
        return;
    }

    fprintf(tl_out, "\tint choice = %s();\n", nondet_str);
    fprintf(tl_out, "\tswitch (_ltl2ba_state_var) {\n");

    for(s = bstates->prv; s != bstates; s = s->prv) {
        fprintf(tl_out, "\tcase _ltl2ba_state_%i_%i:\n", s->id + 1, s->final);

        /* The state of id 0 is an accepting well.
           Every word will be accepted and the state will no longer change
        */
        if(s->id == 0) {
            fprintf(tl_out, "\t\t%s(0, \"Error sure\");\n", assert_str);
            fprintf(tl_out, "\t\tbreak;\n");
            continue;
        }

        /* If there is no transition from this state */
        t = s->trans->nxt;
        if(t == s->trans) {
            fprintf(tl_out, "\t\t%s(0);\n", assume_str);
            continue;
        }

        /* First transition from the current state */
        fprintf(tl_out, "\t\tif (choice == 0) {\n");
        fprintf(tl_out, "\t\t\t%s(", assume_str);
        c_print_set(t->pos, t->neg);
        fprintf(tl_out, ");\n");
        fprintf(tl_out, "\t\t\t_ltl2ba_state_var = _ltl2ba_state_%i_%i;\n",
                t->to->id + 1, t->to->final);
        fprintf(tl_out, "\t\t}");

        /* Other transition from the current state */
        int trans_num;
        for(trans_num = 1, t = s->trans->nxt->nxt; t != s->trans; t = t->nxt, trans_num++) {
            fprintf(tl_out, " else if (choice == %i) {\n", trans_num);
            fprintf(tl_out, "\t\t\t%s(", assume_str);
            c_print_set(t->pos, t->neg);
            fprintf(tl_out, ");\n");
            fprintf(tl_out, "\t\t\t_ltl2ba_state_var = _ltl2ba_state_%i_%i;\n",
                    t->to->id + 1, t->to->final);
            fprintf(tl_out, "\t\t}");
        }
        /* Prune other choices */
        fprintf(tl_out, " else {\n");
        fprintf(tl_out, "\t\t\t%s(0);\n", assume_str);
        fprintf(tl_out, "\t\t}");

        fprintf(tl_out, "\n\t\tbreak;\n");
    }

    fprintf(tl_out, "\t}\n}\n\n");
}

/* Print the table indicating if from the current state,
   every word will be accepted (whatever the suffix)
*/
void
print_c_surely_accept_state_table() {
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
print_c_surely_reject_state_table() {
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
           no state will reject every suffix (elsewhere, this state would have been removed
           from the automaton) */
        fprintf(tl_out, ", 0");
    }
    fprintf(tl_out, "};\n");
}

void
print_c_stutter_acceptance_table() {
    BState *s;
    int i, k;

    fprintf(tl_out, "_Bool _ltl2ba_stutter_accept[%i] = {",
            n_ba_state * (1 << sym_id));

    /* Other states */
    for (k = 0; k < (1 << sym_id); k++) {
        fprintf(tl_out, "\n\t");
        for (s = bstates->prv, i = n_ba_state - 1; s != bstates; s = s->prv, i--)
            fprintf(tl_out, "%i,", stutter_acceptance_table[k * n_ba_state + i]);
    }

    fprintf(tl_out, "\n};\n");
}

/* Print a C function that build a program state id from the value of atomic predicates */
void print_c_sym_to_id_function() {

    int i;
    fprintf(tl_out, "unsigned int\n");
    fprintf(tl_out, "_ltl2ba_sym_to_id() {\n");

    fprintf(tl_out, "\tunsigned int id = 0;\n\n");

    for (i = 0; i < sym_id; i++) {
        fprintf(tl_out, "\tid |= (_ltl2ba_atomic_%s << %i);\n", sym_table[i], i);
    }
    fprintf(tl_out, "\treturn id;\n");
    fprintf(tl_out, "};\n\n");
}

void
print_c_conclusion_function() {

    fprintf(tl_out, "void\n");
    fprintf(tl_out, "_ltl2ba_result() {\n");

    fprintf(tl_out, "\t_Bool reject_sure = _ltl2ba_surely_reject[_ltl2ba_state_var];\n");
    fprintf(tl_out, "\t%s(!reject_sure);\n\n", assume_str);

    fprintf(tl_out, "\t_Bool accept_sure = _ltl2ba_surely_accept[_ltl2ba_state_var];\n");
    fprintf(tl_out, "\t%s(!accept_sure, \"ERROR SURE\");\n\n", assert_str);

    fprintf(tl_out, "\tunsigned int id = _ltl2ba_sym_to_id();\n");
    fprintf(tl_out,
            "\t_Bool accept_stutter = _ltl2ba_stutter_accept[id * %i + _ltl2ba_state_var];\n",
            n_ba_state);

    fprintf(tl_out, "\t%s(!accept_stutter, \"ERROR MAYBE\");\n", assert_str);

    fprintf(tl_out, "\t%s(accept_stutter, \"VALID MAYBE\");\n", assert_str);

    fprintf(tl_out, "}\n\n");
}

void
print_c_buchi() {

    n_ba_state = count_ba_states();
    stutter_acceptance_table = (_Bool *)tl_emalloc(n_ba_state * (1 << sym_id) * sizeof(_Bool));
    stutter_acceptance();

    fprintf(tl_out, "/* ");
    put_uform();
    fprintf(tl_out, " */\n\n");

    print_c_atomics_definition();
    fprintf(tl_out, "\n");
    print_c_states_definition();

    /* Declare and initialize the global variable that will maintain the state
       of the automaton.
       The initial state has always an id of -1 (+1 in the name).
    */
    BState *s;
    for(s = bstates->prv; s != bstates; s = s->prv) {
        if (s->id == -1) {
            fprintf(tl_out, "_ltl2ba_state _ltl2ba_state_var = _ltl2ba_state_0_%d;\n\n", s->final);
            break;
        }
    }

    print_c_transition_function();

    /* TODO: Surely accepting states are currently built under the assumption
       the automaton is in reduced form
    */
    print_c_surely_accept_state_table();

    /* TODO: Surely rejecting states are currently built under the assumption
       the automaton is in reduced form
    */
    print_c_surely_reject_state_table();

    /* TODO: Under the assumption there is no more than sizeof(int)*8 symbols */
    print_c_stutter_acceptance_table();

    /* Print the conclusion function */
    print_c_sym_to_id_function();
    print_c_conclusion_function();

}
