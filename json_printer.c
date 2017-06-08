
/* This file contains the function required to
  print a Büchi automaton in json.
*/

#include "ltl2ba.h"

extern FILE* tl_out;

extern int accept;
extern BState *bstates;

extern int sym_id, sym_size, mod;
extern char** sym_table;

/* Current level of indentation */
static int c_indent = 0;

/* Print indentation corresponding to `c_indent` level */
void
print_indent() {
  int i;
  for (i = 0; i < c_indent; i++)
    fprintf(tl_out, "\t");
}

/* Print a transition in json */
void
print_json_trans(BTrans *t) {

  int i, j;

  print_indent();
  fprintf(tl_out, "{\n");

  c_indent++;
  /* Transition destination */
  print_indent();
  fprintf(tl_out, "\"dest\": %d,\n", t->to->label);

  /* List of positive predicate on the transition */
  print_indent();
  fprintf(tl_out, "\"pos\": [");
  for(i = 0; i < sym_size; i++) {
    for(j = 0; j < mod; j++) {
      if(t->pos[i] & (1 << j))
        fprintf(tl_out, "\"%s\", ", sym_table[mod * i + j]);
    }
  }
  fprintf(tl_out, "],\n");

  /* List of positive negative on the transition */
  print_indent();
  fprintf(tl_out, "\"neg\": [");
  for(i = 0; i < sym_size; i++) {
    for(j = 0; j < mod; j++) {
      if(t->neg[i] & (1 << j))
        fprintf(tl_out, "\"%s\", ", sym_table[mod * i + j]);
    }
  }
  fprintf(tl_out, "],\n");

  c_indent--;
  print_indent();
  fprintf(tl_out, "},\n");

}

/* Print a state in json */
void
print_json_state(BState *s) {
  BTrans *t;
  int is_final = (s->final == accept || s->id == 0);

  print_indent();
  fprintf(tl_out, "{\n");

  c_indent++;
  /* State name */
  print_indent();
  fprintf(tl_out, "\"label\": %d,\n", s->label);

  /* Is the sate final */
  print_indent();
  fprintf(tl_out, "\"final\": %s,\n", is_final ? "true" : "false");

  /* List of state outgoing transitions */
  print_indent();
  fprintf(tl_out, "\"trans\": [\n");
  c_indent++;

  for (t = s->trans->nxt; t != s->trans; t = t->nxt) {
    print_json_trans(t);
  }

  c_indent--;
  print_indent();
  fprintf(tl_out, "],\n");
  c_indent--;
  print_indent();
  fprintf(tl_out, "},\n");

}

/* Print a buchi automaton in json format */
void
print_json_buchi() {

  BState *s;
  int nb_states = 0;
  int init_id;

  /* Give an id to every state and count them */
  for (s = bstates->prv; s != bstates; s = s->prv, nb_states++) {
    if (s->id == -1)
      init_id = nb_states;
    s->label = nb_states;
  }

  print_indent();
  fprintf(tl_out, "{\n");

  c_indent++;
  /* Print the number of states */
  print_indent();
  fprintf(tl_out, "\"nb_state\": %d,\n", nb_states);

  /* Print the id of the initial state */
  print_indent();
  fprintf(tl_out, "\"init_state\": %d,\n", init_id);

  /* Print the list of states */
  print_indent();
  fprintf(tl_out, "\"states\": [\n");

  c_indent++;
  for (s = bstates->prv; s != bstates; s = s->prv) {
    print_json_state(s);
  }

  c_indent--;
  print_indent();
  fprintf(tl_out, "],\n");
  c_indent--;
  print_indent();
  fprintf(tl_out, "}\n");

}
