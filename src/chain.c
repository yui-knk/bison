/* Eliminating useless chain rules.

   Copyright (C) 2019 Free Software Foundation, Inc.

   This file is part of Bison, the GNU Compiler Compiler.

   This program is free software: you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation, either version 3 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see
   <http://www.gnu.org/licenses/>.  */

#include <config.h>
#include "chain.h"

#include <assert.h>
#include <stdlib.h> /* abort */

#include "getargs.h"
#include "gram.h"

bitsetv descendants = NULL;

static void
chain_descendants_print (FILE *out)
{
  bitsetv_matrix_dump (out, "descendants", descendants);

  fprintf (out, "DESCENDANTS\n");
  for (symbol_number sym = ntokens; sym < nsyms; ++sym)
    {
      fprintf (out, "  %s:", symbols[sym]->tag);
      bitset_iterator iter;
      symbol_number des;
      BITSET_FOR_EACH (iter, descendants[sym], des, 0)
        fprintf (out, " %s", symbols[des]->tag);
      fputc ('\n', out);
    }
  fprintf (out, "\n");

  fprintf (out, "LEAVES\n");
  for (symbol_number sym = ntokens; sym < nsyms; ++sym)
    fprintf (out, "  %s: %s\n",
             symbols[sym]->tag, symbols[chain_leaf (sym)]->tag);
  fprintf (out, "\n");
}

void
chain_compute_ancestors (void)
{
  assert (!descendants);
  descendants = bitsetv_create (nsyms, nsyms, BITSET_FIXED);
  if (feature_flag & feature_eliminate_chains)
    for (rule_number r = 0; r < nrules; ++r)
      if (rule_useless_chain_p (&rules[r]))
        {
          symbol_number lhs = rules[r].lhs->number;
          symbol_number rhs = rules[r].rhs[0];
          bitset_set (descendants[lhs], rhs);
        }
  bitsetv_reflexive_transitive_closure (descendants);
  if (trace_flag & trace_sets)
    chain_descendants_print (stderr);
}

size_t
chain_ancestors_count (symbol_number sym)
{
  size_t res = 0;
  for (symbol_number anc = 0; anc < nsyms; ++anc)
    res += bitset_test (descendants[anc], sym);
  return res;
}

bool
is_leaf (symbol_number sym)
{
  assert (descendants);
  return bitset_count (descendants[sym]) == 1;
}

symbol_number
chain_leaf (symbol_number sym)
{
  assert (descendants);
  if (is_leaf (sym))
    return sym;
  else
    {
      bitset_iterator iter;
      symbol_number des;
      BITSET_FOR_EACH (iter, descendants[sym], des, 0)
        if (des != sym)
          return symbols[des]->content->number;
      abort ();
    }
}

void
chain_free (void)
{
  bitsetv_free (descendants);
  descendants = NULL;
}
