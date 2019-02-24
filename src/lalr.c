/* Compute lookahead criteria for Bison.

   Copyright (C) 1984, 1986, 1989, 2000-2015, 2018-2019 Free Software
   Foundation, Inc.

   This file is part of Bison, the GNU Compiler Compiler.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */


/* Find which rules need lookahead in each state, and which lookahead
   tokens they accept.  */

#include <config.h>
#include "system.h"

#include <bitset.h>
#include <bitsetv.h>

#include "chain.h"
#include "complain.h"
#include "closure.h"
#include "derives.h"
#include "getargs.h"
#include "gram.h"
#include "lalr.h"
#include "lr0.h"
#include "muscle-tab.h"
#include "nullable.h"
#include "reader.h"
#include "relation.h"
#include "symtab.h"

/* goto_map[nterm - NTOKENS] -> number of gotos.  */
goto_number *goto_map = NULL;
goto_number ngotos = 0;
state_number *from_state = NULL;
state_number *to_state = NULL;
symbol_number *on_label = NULL;
bitsetv goto_follows = NULL;

/* Linked list of goto numbers.  */
typedef struct goto_list
{
  struct goto_list *next;
  goto_number value;
} goto_list;

static goto_list *
goto_list_new (goto_number value, struct goto_list *next)
{
  goto_list *res = xmalloc (sizeof *res);
  res->next = next;
  res->value = value;
  return res;
}

/* LA is an nLA by NTOKENS matrix of bits.  LA[l, i] is 1 if the rule
   LArule[l] is applicable in the appropriate state when the next
   token is symbol i.  If LA[l, i] and LA[l, j] are both 1 for i != j,
   it is a conflict.  */

static bitsetv LA = NULL;
size_t nLA;


/* "(p, A) includes (p', B)" iff
   B → βAγ, γ nullable, and p'-- β --> p (i.e., state p' reaches p on label β).

   Definition p.621 [DeRemer 1982].

   INCLUDES[(p, A)] = [(p', B),...] */
static goto_number **includes;

/* "(q, A → ω) lookback (p, A)" iff state p reaches state q on label ω.

   Definition p.621 [DeRemer 1982]. */
static goto_list **lookback;

static void
goto_print (goto_number i, FILE *out)
{
  const state_number src = from_state[i];
  const state_number dst = to_state[i];
  const char *lbl = symbols[on_label[i]]->tag;
  fprintf (out, "goto[%ld] = (%d, %s, %d)", i, src, lbl, dst);
}

void
set_goto_map (void)
{
  /* Count the number of gotos (ngotos) per nterm (goto_map). */
  goto_map = xcalloc (nvars + 1, sizeof *goto_map);
  ngotos = 0;
  for (state_number s = 0; s < nstates; ++s)
    {
      transitions *trans = states[s]->transitions;
      if (trace_flag & trace_automaton)
        {
          fprintf (stderr, "Checking transitions:\n");
          state_transitions_print (states[s], stderr);
        }
      for (int i = trans->num - 1; 0 <= i; --i)
        if (transition_is_goto (trans, i))
          {
            const symbol_number label = TRANSITION_SYMBOL (trans, i);
            for (symbol_number anc = 0; anc < nsyms; ++anc)
              if (bitset_test (descendants[anc], label)
                  && !ISTOKEN (anc))
                {
                  ngotos++;
                  if (trace_flag & trace_automaton)
                    fprintf (stderr, "Accepting %d on %s\n",
                             i, symbols[anc]->tag);
                  /* Abort if (ngotos + 1) would overflow.  */
                  aver (ngotos != GOTO_NUMBER_MAXIMUM);
                  goto_map[anc - ntokens]++;
                }
          }
    }

  goto_number *temp_map = xnmalloc (nvars + 1, sizeof *temp_map);
  {
    goto_number k = 0;
    for (symbol_number i = ntokens; i < nsyms; ++i)
      {
        temp_map[i - ntokens] = k;
        k += goto_map[i - ntokens];
      }

    for (symbol_number i = ntokens; i < nsyms; ++i)
      goto_map[i - ntokens] = temp_map[i - ntokens];

    goto_map[nsyms - ntokens] = ngotos;
    temp_map[nsyms - ntokens] = ngotos;
  }

  from_state = xcalloc (ngotos, sizeof *from_state);
  on_label = xcalloc (ngotos, sizeof *on_label);
  to_state = xcalloc (ngotos, sizeof *to_state);

  for (state_number s = 0; s < nstates; ++s)
    {
      const transitions *trans = states[s]->transitions;
      for (int i = trans->num - 1; 0 <= i; --i)
        if (transition_is_goto (trans, i))
        {
          const symbol_number label = TRANSITION_SYMBOL (trans, i);
          for (symbol_number anc = 0; anc < nsyms; ++anc)
            if (bitset_test (descendants[anc], label)
                && !ISTOKEN (anc))
              {
                goto_number k = temp_map[anc - ntokens]++;
                from_state[k] = s;
                on_label[k] = anc;
                to_state[k] = trans->states[i]->number;
              }
        }
    }

  free (temp_map);

  if (trace_flag & trace_automaton)
    for (int i = 0; i < ngotos; ++i)
      {
        goto_print (i, stderr);
        fputc ('\n', stderr);
      }
}


goto_number
map_goto (state_number src, symbol_number sym)
{
  if (trace_flag & trace_automaton)
    fprintf (stderr, "Looking for goto(%d, %s)\n", src, symbols[sym]->tag);
  goto_number res = -1;
  if (feature_flag & feature_eliminate_chains)
    {
      /* Look from a goto from SRC whose label is a descendant of
         SYM. */
      for (goto_number i = 0; i < ngotos; ++i)
        if (from_state[i] == src && on_label[i] == sym)
          {
            res = i;
            break;
          }
    }
  else
    {
      /* Optimized dichotomic search.  */
      goto_number low = goto_map[sym - ntokens];
      goto_number high = goto_map[sym - ntokens + 1] - 1;
      for (;;)
        {
          if (high < low)
            break;
          goto_number middle = (low + high) / 2;
          state_number s = from_state[middle];
          if (s == src)
            {
              res = middle;
              break;
            }
          else if (s < src)
            low = middle + 1;
          else
            high = middle - 1;
        }
    }
  assert (res != -1);
  return res;
}

/* Print FOLLOWS for debugging.  */
static void
follows_print (const char* title, FILE *out)
{
  fprintf (out, "%s:\n", title);
  for (goto_number i = 0; i < ngotos; ++i)
    {
      fputs ("    FOLLOWS[", out);
      goto_print (i, out);
      fputs ("] =", out);
      bitset_iterator iter;
      symbol_number sym;
      BITSET_FOR_EACH (iter, goto_follows[i], sym, 0)
        fprintf (out, " %s", symbols[sym]->tag);
      fputc ('\n', out);
    }
  fputc ('\n', out);
}

/* Build goto_follows. */
static void
initialize_goto_follows (void)
{
  goto_number **reads = xnmalloc (ngotos, sizeof *reads);
  goto_number *edge = xnmalloc (ngotos, sizeof *edge);

  goto_follows = bitsetv_create (ngotos, ntokens, BITSET_FIXED);

  for (goto_number i = 0; i < ngotos; ++i)
    {
      if (trace_flag & trace_automaton)
        {
          fprintf (stderr, "initialize_goto_follows: ");
          goto_print (i, stderr);
          fputc ('\n', stderr);
        }
      state_number dst = to_state[i];
      const state *s = states[dst];

      {
        closure (s->items, s->nitems);
        for (size_t j = 0; j < nitemset; ++j)
          {
            item_number *sp1 = ritem + itemset[j];
            if (trace_flag & trace_automaton)
              {
                item_print (sp1, NULL, stderr);
                fprintf (stderr, "\n");
              }
            if (item_number_is_symbol_number (*(sp1-1))
                && item_number_as_symbol_number (*(sp1-1)) == on_label[i]
                && item_number_is_symbol_number (*sp1))
              {
                /* FIXME: here, we want to be able to iterate over the
                   firsts of a symbol.  Currently the firsts (in the
                   conventional sense) is not available in Bison:
                   firsts in closure.c is something different.  */
                symbol_number sym = item_number_as_symbol_number (*sp1);
                if (ISTOKEN (sym))
                  {
                    if (trace_flag & trace_automaton)
                      {
                        fprintf (stderr, "Add %s as shift1 for ", symbols[sym]->tag);
                        goto_print (i, stderr);
                        fprintf (stderr, "\n");
                      }
                    bitset_set (goto_follows[i], sym);
                  }
                else
                  {
                    bitset_iterator iter;
                    rule_number r;
                    BITSET_FOR_EACH (iter, FDERIVES (sym), r, 0)
                      {
                        if (item_number_is_symbol_number (rules[r].rhs[0])
                            && ISTOKEN (rules[r].rhs[0]))
                          {
                            if (trace_flag & trace_automaton)
                              {
                                fprintf (stderr, "Add %s as shift2 for ",
                                         symbols[rules[r].rhs[0]]->tag);
                                goto_print (i, stderr);
                                fprintf (stderr, "\n");
                              }
                            bitset_set (goto_follows[i], rules[r].rhs[0]);
                          }
                      }
                  }
              }
          }
      }

      const transitions *trans = s->transitions;
      /* Shifts outgoing from DST. */
      int j;
      FOR_EACH_SHIFT (trans, j)
        continue; // bitset_set (goto_follows[i], TRANSITION_SYMBOL (trans, j));

      /* Gotos outgoing from DST. */
      goto_number nedges = 0;
      for (; j < trans->num; ++j)
        {
          symbol_number sym = TRANSITION_SYMBOL (trans, j);
          if (nullable[sym - ntokens])
            {
              assert (nedges < ngotos);
              edge[nedges++] = map_goto (dst, sym);
            }
        }

      if (nedges == 0)
        reads[i] = NULL;
      else
        {
          reads[i] = xnmalloc (nedges + 1, sizeof reads[i][0]);
          memcpy (reads[i], edge, nedges * sizeof edge[0]);
          reads[i][nedges] = END_NODE;
        }
    }
  if (trace_flag & trace_automaton)
    {
      follows_print ("follows after shifts", stderr);
      relation_print ("reads", reads, ngotos, goto_print, stderr);
    }

  relation_digraph (reads, ngotos, goto_follows);
  if (trace_flag & trace_automaton)
    follows_print ("follows after read", stderr);

  for (goto_number i = 0; i < ngotos; ++i)
    free (reads[i]);
  free (reads);
  free (edge);
}


/* Find the state which LOOKBACK[LOOKBACK_INDEX] is about.  */
static const state *
lookback_find_state (int lookback_index)
{
  state *res = NULL;
  for (int j = 0; j < nstates; ++j)
    if (states[j]->reductions
        && states[j]->reductions->lookahead_tokens)
      {
        if (states[j]->reductions->lookahead_tokens - LA > lookback_index)
          /* Went too far. */
          break;
        else
          res = states[j];
      }
  /* Pacify "potential null pointer dereference" warning.  */
  if (!res)
    abort ();
  return res;
}

/* Print LOOKBACK for debugging.  */
static void
lookback_print (FILE *out)
{
  fputs ("lookback:\n", out);
  for (int i = 0; i < nLA; ++i)
    if (lookback[i])
    {
      fprintf (out, "   %3d = ", i);
      const state *s = lookback_find_state (i);
      int rnum = i - (s->reductions->lookahead_tokens - LA);
      const rule *r = s->reductions->rules[rnum];
      fprintf (out, "(%3d, ", s->number);
      rule_print (r, NULL, out);
      fputs (") ->", out);
      for (goto_list *sp = lookback[i]; sp; sp = sp->next)
        {
          fputc (' ', out);
          goto_print (sp->value, out);
        }
      fputc ('\n', out);
    }
  fputc ('\n', out);
}

/* Add (S, R) -> GOTONO to LOOKBACK.

   "(q, A → ω) lookback (p, A)" iff state p reaches state q on label ω.

   The goto number GOTONO, whose source is S (which is
   inconsistent), */
static void
add_lookback_edge (state *s, rule const *r, goto_number gotono)
{
  if (trace_flag & trace_automaton)
    fprintf (stderr, "add_lookback_edge(s = %d, r = %d, g = %ld)\n",
             s->number, r->number, gotono);
  int ri = state_reduction_find (s, r);
  if (ri == -1)
    {
      if (trace_flag & trace_automaton)
        fprintf (stderr, "******************* Skipping add_lookback_edge\n");
      //abort ();
    }
  else
    {
      int idx = (s->reductions->lookahead_tokens - LA) + ri;
      lookback[idx] = goto_list_new (gotono, lookback[idx]);
    }
}

static void
build_path (goto_number gotono,
            rule const *r,
            state_number *path, int length,
            goto_number *edge, int *nedges)
{
  item_number n = r->rhs[length-1];
  if (item_number_is_symbol_number (n))
    {
      symbol_number sym = item_number_as_symbol_number (n);
      state *s = states[path[length-1]];
      transitions *trans = s->transitions;
      for (int i = 0; i < trans->num; ++i)
        if (bitset_test(descendants[sym], TRANSITION_SYMBOL (trans, i)))
          {
            path[length] = trans->states[i]->number;
            build_path (gotono, r, path, length+1, edge, nedges);
          }
    }
  else
    {
      /* We reached the end of the path.  */
      if (trace_flag & trace_automaton)
        {
          goto_print (gotono, stderr);
          fputs (": ", stderr);
          rule_print (r, NULL, stderr);
          fputs (", path =", stderr);
          for (int j = 0; j < length; ++j)
            fprintf (stderr, "%s %d", j ? "," : "", path[j]);
          fputc ('\n', stderr);
        }

      /* The end of PATH.  */
      state *s = states[path[length-1]];
      if (!s->consistent)
        add_lookback_edge (s, r, gotono);

      /* Walk back PATH from penultimate to beginning.

         The "0 <= p" part is actually useless: each rhs ends in a
         rule number (for which ISVAR(...) is false), and there is
         a sentinel (ritem[-1]=0) before the first rhs.  */
      for (int p = length - 2; 0 <= p && ISVAR (r->rhs[p]); --p)
        {
          symbol_number sym = item_number_as_symbol_number (r->rhs[p]);
          goto_number g = map_goto (path[p], sym);
          if (g == GOTO_NUMBER_MAXIMUM)
            {
              fprintf (stderr, "*************** SKIPPED\n");
              abort ();
            }
          else
            {
              /* Insert G if not already in EDGE.
                 FIXME: linear search.  A bitset instead?  */
              {
                bool found = false;
                for (int j = 0; !found && j < *nedges; ++j)
                  found = edge[j] == g;
                if (!found)
                  {
                    if (trace_flag & trace_automaton)
                      {
                        fprintf (stderr, "new includes edge: ");
                        goto_print (g, stderr);
                        fprintf (stderr, " -> ");
                        goto_print (gotono, stderr);
                        fputs (" via ", stderr);
                        rule_print (r, NULL, stderr);
                        fprintf (stderr, "\n");
                      }
                    assert (*nedges < ngotos);
                    edge[(*nedges)++] = g;
                  }
              }
            }
          if (!nullable[sym - ntokens])
            break;
        }
    }
}

/* Compute INCLUDES and LOOKBACK.  Corresponds to step E in Sec. 6 of
   [DeRemer 1982].  */
static void
build_relations (void)
{
  goto_number *edge = xnmalloc (ngotos, sizeof *edge);
  state_number *path = xnmalloc (ritem_longest_rhs () + 1, sizeof *path);

  includes = xnmalloc (ngotos, sizeof *includes);

  /* For each goto (from SRC to DST labeled by nterm VAR), iterate
     over each rule with VAR as LHS, and find the path PATH from SRC
     labeled with the RHS of the rule. */
  for (goto_number i = 0; i < ngotos; ++i)
    {
      if (trace_flag & trace_automaton)
        {
          fprintf (stderr, "\n\n============= Looking at ");
          goto_print (i, stderr);
          fprintf (stderr, "\n");
        }
      const state_number src = from_state[i];
      const symbol_number var = on_label[i];

      /* Size of EDGE.  */
      int nedges = 0;
      if (trace_flag & trace_automaton)
        {
          fprintf (stderr, "\n==== Looking at ");
          goto_print (i, stderr);
          fprintf (stderr, " with symbol %s\n", symbols[var]->tag);
        }
      for (rule **rulep = derives[var - ntokens]; *rulep; ++rulep)
        {
          rule const *r = *rulep;
          if (trace_flag & trace_automaton)
            {
              fprintf (stderr, "---- Looking at rule ");
              rule_print (r, NULL, stderr);
              fprintf (stderr, "\n");
            }
          if (false
              && feature_flag & feature_eliminate_chains
              && rule_useless_chain_p (r))
            {
              if (trace_flag & trace_automaton)
                fprintf (stderr, "************************** rule disabled, skipping\n");
              continue;
            }

          if (trace_flag & trace_automaton)
            {
              fputs ("build_relations for ", stderr);
              goto_print (i, stderr);
              fputs (": ", stderr);
              rule_print (r, NULL, stderr);
              fputc ('\n', stderr);
            }
          state *s = states[src];
          path[0] = s->number;  /* == SRC. */

          /* Length of PATH.  */
          int length = 1;
          build_path (i, r,
                      path, length,
                      edge, &nedges);
        }

      if (trace_flag & trace_automaton)
        {
          goto_print (i, stderr);
          fputs (" edges = ", stderr);
          for (int j = 0; j < nedges; ++j)
            {
              fputc (' ', stderr);
              goto_print (edge[j], stderr);
            }
          fputc ('\n', stderr);
        }

      if (nedges == 0)
        includes[i] = NULL;
      else
        {
          includes[i] = xnmalloc (nedges + 1, sizeof includes[i][0]);
          for (int j = 0; j < nedges; ++j)
            includes[i][j] = edge[j];
          includes[i][nedges] = END_NODE;
        }
    }

  free (edge);
  free (path);

  relation_transpose (&includes, ngotos);
  if (trace_flag & trace_automaton)
    relation_print ("includes", includes, ngotos, goto_print, stderr);
}

/* Compute FOLLOWS from INCLUDES, and free INCLUDES.  */
static void
compute_follows (void)
{
  relation_digraph (includes, ngotos, goto_follows);
  if (trace_flag & trace_sets)
    follows_print ("follows after includes", stderr);
  for (goto_number i = 0; i < ngotos; ++i)
    free (includes[i]);
  free (includes);
}


static void
compute_lookahead_tokens (void)
{
  if (trace_flag & trace_automaton)
      lookback_print (stderr);

  for (size_t i = 0; i < nLA; ++i)
    for (goto_list *sp = lookback[i]; sp; sp = sp->next)
      bitset_or (LA[i], LA[i], goto_follows[sp->value]);

  /* Free LOOKBACK. */
  for (size_t i = 0; i < nLA; ++i)
    LIST_FREE (goto_list, lookback[i]);
  free (lookback);
}


/*----------------------------------------------------.
| Count the number of lookahead tokens required for S |
| (N_LOOKAHEAD_TOKENS member).                        |
`----------------------------------------------------*/

static int
state_lookahead_tokens_count (state *s, bool default_reduction_only_for_accept)
{
  const reductions *reds = s->reductions;
  const transitions *trans = s->transitions;

  /* Transitions are only disabled during conflict resolution, and that
     hasn't happened yet, so there should be no need to check that
     transition 0 hasn't been disabled before checking if it is a shift.
     However, this check was performed at one time, so we leave it as an
     aver.  */
  aver (trans->num == 0 || !TRANSITION_IS_DISABLED (trans, 0));

  /* We need a lookahead either to distinguish different reductions
     (i.e., there are two or more), or to distinguish a reduction from a
     shift.  Otherwise, it is straightforward, and the state is
     'consistent'.  However, do not treat a state with any reductions as
     consistent unless it is the accepting state (because there is never
     a lookahead token that makes sense there, and so no lookahead token
     should be read) if the user has otherwise disabled default
     reductions.  */
  s->consistent =
    !(reds->num > 1
      || (reds->num == 1 && trans->num && transition_is_shift (trans, 0))
      || (reds->num == 1 && reds->rules[0]->number != 0
          && default_reduction_only_for_accept));

  return s->consistent ? 0 : reds->num;
}


/*----------------------------------------------------.
| Compute LA, NLA, and the lookahead_tokens members.  |
`----------------------------------------------------*/

void
initialize_LA (void)
{
  bool default_reduction_only_for_accept;
  {
    char *default_reductions =
      muscle_percent_define_get ("lr.default-reduction");
    default_reduction_only_for_accept = STREQ (default_reductions, "accepting");
    free (default_reductions);
  }

  /* Compute the total number of reductions requiring a lookahead.  */
  nLA = 0;
  for (state_number i = 0; i < nstates; ++i)
    nLA +=
      state_lookahead_tokens_count (states[i],
                                    default_reduction_only_for_accept);
  /* Avoid having to special case 0.  */
  if (!nLA)
    nLA = 1;

  bitsetv pLA = LA = bitsetv_create (nLA, ntokens, BITSET_FIXED);

  /* Initialize the members LOOKAHEAD_TOKENS for each state whose reductions
     require lookahead tokens.  */
  for (state_number i = 0; i < nstates; ++i)
    {
      int count =
        state_lookahead_tokens_count (states[i],
                                      default_reduction_only_for_accept);
      if (count)
        {
          states[i]->reductions->lookahead_tokens = pLA;
          pLA += count;
        }
    }
}


/*---------------------------------------------.
| Output the lookahead tokens for each state.  |
`---------------------------------------------*/

static void
lookahead_tokens_print (FILE *out)
{
  fputs ("Lookaheads:\n", out);
  for (state_number i = 0; i < nstates; ++i)
    {
      const reductions *reds = states[i]->reductions;
      if (reds->num)
        {
          fprintf (out, "  State %d:\n", i);
          for (int j = 0; j < reds->num; ++j)
            {
              fprintf (out, "    rule %d:", reds->rules[j]->number);
              if (reds->lookahead_tokens)
              {
                bitset_iterator iter;
                int k;
                BITSET_FOR_EACH (iter, reds->lookahead_tokens[j], k, 0)
                  fprintf (out, " %s", symbols[k]->tag);
              }
              fputc ('\n', out);
            }
        }
    }
  fputc ('\n', out);
}

void
lalr (void)
{
  if (trace_flag & trace_automaton)
    {
      fputc ('\n', stderr);
      begin_use_class ("trace0", stderr);
      fprintf (stderr, "lalr: begin");
      end_use_class ("trace0", stderr);
      fputc ('\n', stderr);
    }
  initialize_LA ();
  set_goto_map ();
  initialize_goto_follows ();
  lookback = xcalloc (nLA, sizeof *lookback);
  build_relations ();
  compute_follows ();
  compute_lookahead_tokens ();

  if (trace_flag & trace_sets)
    lookahead_tokens_print (stderr);
  if (trace_flag & trace_automaton)
    {
      begin_use_class ("trace0", stderr);
      fprintf (stderr, "lalr: done");
      end_use_class ("trace0", stderr);
      fputc ('\n', stderr);
    }
}


void
lalr_update_state_numbers (state_number old_to_new[], state_number nstates_old)
{
  goto_number ngotos_reachable = 0;
  symbol_number nonterminal = 0;
  aver (nsyms == nvars + ntokens);

  for (goto_number i = 0; i < ngotos; ++i)
    {
      while (i == goto_map[nonterminal])
        goto_map[nonterminal++] = ngotos_reachable;
      /* If old_to_new[from_state[i]] = nstates_old, remove this goto
         entry.  */
      if (old_to_new[from_state[i]] != nstates_old)
        {
          /* from_state[i] is not removed, so it and thus to_state[i] are
             reachable, so to_state[i] != nstates_old.  */
          aver (old_to_new[to_state[i]] != nstates_old);
          from_state[ngotos_reachable] = old_to_new[from_state[i]];
          to_state[ngotos_reachable] = old_to_new[to_state[i]];
          ++ngotos_reachable;
        }
    }
  while (nonterminal <= nvars)
    {
      aver (ngotos == goto_map[nonterminal]);
      goto_map[nonterminal++] = ngotos_reachable;
    }
  ngotos = ngotos_reachable;
}


void
lalr_free (void)
{
  for (state_number s = 0; s < nstates; ++s)
    states[s]->reductions->lookahead_tokens = NULL;
  bitsetv_free (LA);
}
