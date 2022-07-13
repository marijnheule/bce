#include <stdio.h>
#include <stdlib.h>

//#define DEBUG
//#define PRINT_STACK
//#define PRINT_FLIPS
//#define PRINT_SOLUTION
//#define PRINT_NEG_SOLUTION
//#define PRINT_SORTED_CNF
//#define BRANCH_SEQUENCE
//#define DECOMPOSITION
#define SIMPLIFY

int main (int argc, char** argv) {
  int i, j, k, tmp;
  int nVars, nLemmas;
  int **lemmas, *big;
  int *sizes, *occurrences;
  int *marks, **lookup;
  int *touched, *active;
  int *stack, stack_size = 0;
  int **blocking, *blocked;
  int *assignment;
  int *assigned;
  int *seen;
  int *label;
  int *lemscore, **litscore;

  FILE* input = fopen(argv[1], "r");

  do { tmp = fscanf (input, " p cnf %i %i \n", &nVars, &nLemmas);
    if (tmp > 0 && tmp != EOF) break; tmp = fscanf (input, "%*s\n"); }
  while (tmp != 2 && tmp != EOF);

//  printf("p cnf %i %i\n", nVars, nLemmas);

  stack       = (int* ) malloc (sizeof(int ) * ( nLemmas ));
  active      = (int* ) malloc (sizeof(int ) * ( nLemmas ));
  touched     = (int* ) malloc (sizeof(int ) * ( nLemmas ));
  big         = (int* ) malloc (sizeof(int ) * (100000000));
  lemmas      = (int**) malloc (sizeof(int*) * ( nLemmas ));
  blocking    = (int**) malloc (sizeof(int*) * ( nLemmas ));
  litscore    = (int**) malloc (sizeof(int*) * ( nLemmas ));
  lemscore    = (int* ) malloc (sizeof(int ) * ( nLemmas ));
  label       = (int* ) malloc (sizeof(int ) * ( nLemmas ));
  blocked     = (int* ) malloc (sizeof(int ) * ( nLemmas ));
  sizes       = (int* ) malloc (sizeof(int ) * ( nLemmas ));
  occurrences = (int* ) malloc (sizeof(int ) * (2*nVars+1)); occurrences += nVars;
  marks       = (int* ) malloc (sizeof(int ) * (2*nVars+1)); marks       += nVars;
  lookup      = (int**) malloc (sizeof(int*) * (2*nVars+1)); lookup      += nVars;
  assignment  = (int* ) malloc (sizeof(int ) * (  nVars+1));
  assigned    = (int* ) malloc (sizeof(int ) * (  nVars+1));
  seen        = (int* ) malloc (sizeof(int ) * (  nVars+1));

  int filled = 0, size = 0, nParsed = 0;
  while (nParsed < nLemmas) {
    if (!size) lemmas[ nParsed ] = &big[ filled ];
    int lit; tmp = fscanf (input, " %i ", &lit);
    lemmas[ nParsed ][ size++ ] = lit;
    if (!lit) { sizes[ nParsed ] = size - 1; nParsed++;
                filled += size; size = 0; }
    else occurrences[ lit ]++;
  }

  int *lookup_mem   = (int*) malloc (sizeof(int) * filled);
  int *blocking_mem = (int*) malloc (sizeof(int) * filled);
  int *litscore_mem = (int*) malloc (sizeof(int) * filled);

  for (i = 0; i < filled; ++i) blocking_mem[ i ] = 0;

  tmp = 0;
  for (i = -nVars; i <= nVars; ++i) { lookup  [ i ] = lookup_mem   + tmp;
                                      tmp += occurrences[ i ];
                                      occurrences[ i ] = 0; }

  tmp = 0;
  for (i = 0; i < nLemmas; ++i) {
    int *lemma = lemmas[ i ];
    while (*lemma) { int lit = *(lemma++); lookup[ lit ][ occurrences[ lit ]++ ] = i; }
  }

  tmp = 0;
  for (i = 0; i < nLemmas; ++i) {
    label   [ i ] = 0;  // fro BCD
    blocked [ i ] = 0;
    blocking[ i ] = blocking_mem + tmp;
    litscore[ i ] = litscore_mem + tmp;
    tmp += sizes[ i ];
  }

  int nActive = 0;
  for (i = 0;  i < nLemmas; i++)  { touched[ i ] = 1; active[ nActive++ ] = i; }

  for (i = -nVars; i <= nVars; ++i) marks[ i ] = -1;

  int nRemoved = 0;
  int iterate_flag;
BCE:
  iterate_flag = 1;
  while (iterate_flag) {
    iterate_flag = 0;

    for (i = 0; i < nLemmas; ++i) {
      if (touched[ i ] == 0) continue;
      iterate_flag = 1;

      int super_flag = 0;
      int *lemma = lemmas[ i ];
      touched[ i ] = 0;
      while (*lemma) { int lit = *(lemma++); marks[ -lit ] = i; }

      int pos  = 0;
      lemma = lemmas[ i ];
      while (*lemma) {
        int flag = 1;
        int lit  = *(lemma++);
        for (j = 0; j < occurrences[ -lit ]; ++j) {
          int count  = 0;
	  int *check = lemmas[ lookup[ -lit ][ j ] ];
	  while (*check) {
	    if (marks[ *(check++) ] == i) count++;
            if (count == 2) goto next_check;
          }
          flag = 0;
          next_check:;
        }
        if (flag) {
//          printf("clause %i is blocked on %i\n", i, lit);
	  label   [ i ]        = 1;
	  blocked [ i ]        = 1;
          blocking[ i ][ pos ] = 1;
          if (super_flag == 0) stack[ stack_size++ ] = i;
        }
        super_flag |= flag;
        pos++;
      }
      if (super_flag) {  // found a blocked clause, update data-structures
        nRemoved++;
        lemma = lemmas[ i ];
        while (*lemma) {
        int lit  = *(lemma++);
        for (j = 0; j < occurrences[ lit ]; ++j)
	  if (lookup[ lit ][ j ] == i)
	  {  //printf("removing clause %i (%i)\n", i, lit);
	     lookup[ lit ][ j-- ] = lookup[ lit ][ --occurrences[ lit ] ]; }

        for (j = 0; j < occurrences[ -lit ]; ++j)
	  touched[ lookup[ -lit ][ j ] ] = 1;
        }
      }
    }
  }

#ifdef DECOMPOSITION
    for (i = 0; i < nLemmas; ++i) {
      if (label[ i ]) continue; // lemma is already in one of the sets;
      int pos = 0;
      int *lemma = lemmas[ i ];
      lemscore[ i ] = 0;
      while (*lemma) { litscore[ i ][ pos++ ] = 0; lemma++; }
    }

    for (i = 0; i < nLemmas; ++i) {
      if (label[ i ]) continue; // lemma is already in one of the sets;
      int *lemma = lemmas[ i ];

      while (*lemma) { int lit = *(lemma++); marks[ -lit ] = i; }

      lemma = lemmas[ i ];
      while (*lemma) {
        int lit  = *(lemma++);
        for (j = 0; j < occurrences[ -lit ]; ++j) {
          int pos = 0;
          int count = 0;
          int cls = lookup[ -lit ][ j ];
	  int *check = lemmas[ cls ];
	  while (*check) {
	    if (marks[ *(check++) ] == i) count++;
	    if (count == 0) pos++;
            if (count == 2) goto next_check_bcd;
          }
          litscore[ cls ][ pos ]++;
          next_check_bcd:;
        }
      }
    }

    int min_taut = 1000000;
    for (i = 0; i < nLemmas; ++i) {
      if (label[ i ]) continue; // lemma is already in one of the sets;
      int pos = 0;
      int *lemma = lemmas[ i ];
      while (*lemma) {
        if (litscore[ i ][ pos ] < min_taut) min_taut = litscore[ i ][ pos ];
        pos++; lemma++; }
    }

    int maxscore = 0;
    int decision = -1;
    for (i = 0; i < nLemmas; ++i) {
      if (label[ i ]) continue; // lemma is already in one of the sets;
      int pos = 0;
      int *lemma = lemmas[ i ];
      while (*lemma) {
        if (litscore[ i ][ pos ] == min_taut) {
          int lit = lemmas[ i ][ pos ];
          for (j = 0; j < occurrences[ -lit ]; ++j) {
            int count = 0;
            int cls = lookup[ -lit ][ j ];
	    int *check = lemmas[ cls ];
	    while (*check) {
	      if (marks[ *(check++) ] == i) count++;
            }
	    if (count == 1) lemscore[ cls ]++;
	    if (lemscore[ cls ] > maxscore) {
	      maxscore = lemscore[ cls ]; decision = cls;
	    }
          }
        }
        pos++; lemma++; }
    }
/*
    printf("c min-taut = %i\n", min_taut);
    for (i = 0; i < nLemmas; ++i) {
      if (label[ i ]) continue; // lemma is already in one of the sets;
      if (lemscore[ i ] == 0) continue;
      printf("%i %i : ", i, lemscore[ i ]);
      int pos = 0;
      int *lemma = lemmas[ i ];
      while (*lemma) {
        printf("%i (%i)", *lemma, litscore[ i ][ pos ] );
        pos++; lemma++; }
      printf("\n");
    }
*/
      if (decision >= 0) {
        printf("c moving clause %i to F_2\n", decision);
        label[ decision ] = 2;
        nRemoved++;
        int* lemma = lemmas[ decision ];
        while (*lemma) {
        int lit  = *(lemma++);
        for (j = 0; j < occurrences[ lit ]; ++j)
	  if (lookup[ lit ][ j ] == decision)
	  {  //printf("removing clause %i (%i)\n", i, lit);
	     lookup[ lit ][ j-- ] = lookup[ lit ][ --occurrences[ lit ] ]; }

        for (j = 0; j < occurrences[ -lit ]; ++j)
	  touched[ lookup[ -lit ][ j ] ] = 1;
        }
        goto BCE;
      }
#endif

#ifdef PRINT_SORTED_CNF
  printf("p cnf %i %i\n", nVars, nLemmas);
  for (i = stack_size - 1; i >= 0; --i) {
    int *lemma = lemmas[ stack[ i ] ];
    while (*lemma) printf("%i ", *(lemma++));
    printf("0\n");
  }
#endif
#ifdef PRINT_STACK
  for (i = 0; i < stack_size; ++i) {
    printf("stack[ %i ] = %i : (", i, stack[ i ]);
    int pos = 0;
    int *lemma = lemmas[ stack[ i ] ];
    while (*lemma) {
      printf(" %i", *lemma);
      if( blocking[ stack[i] ][ pos ] ) printf("*");
      lemma++; pos++;
    }
    printf(" )\n");
  }
#endif

#ifdef SIMPLIFY
  printf("p cnf %i %i\n", nVars, nLemmas - nRemoved);
    for (i = 0; i < nLemmas; ++i)
      if (blocked[i] == 0) {
        int *lemma = lemmas[ i ];
        while (*lemma)
          printf("%i ", *(lemma++));
        printf("0\n");
      }
#endif

  if (nLemmas != stack_size) exit(1);

  for (i = 1; i <= nVars; ++i) assignment[ i ] = i;

  for (i = stack_size - 1; i >= 0; --i) {
    int pos = 0;
    int blocking_literal = 0;
    int *lemma = lemmas[ stack[ i ] ];
    while (*lemma) {
      if (assignment[ abs(*lemma) ] == *lemma) goto next_clause;
      if (blocking[ stack[ i ] ][ pos ] ) blocking_literal = *lemma;
      lemma++; pos++;
    }
#ifdef PRINT_FLIPS
    printf("flipping %i to true (stack_pos %i)\n", blocking_literal, i);
#endif
    assignment[ abs(blocking_literal) ] *= -1;
    next_clause :;
  }

#ifdef DEBUG
  for (i = 0; i < stack_size; ++i) {
    int pos = 0;
    int sat_count = 0;
    int blocking_literal = 0;
    int *lemma = lemmas[ stack[ i ] ];
    while (*lemma) {
      if (assignment[ abs(*lemma) ] == *lemma) {
         sat_count++;
         if (blocking[ stack[ i ] ][ pos ] ) blocking_literal = *lemma;
      }
      lemma++; pos++;
    }
    printf("SAT count %i\n", sat_count);
    if (sat_count == 1) printf("blocking literal %i\n", blocking_literal);
  }
#endif

  for (i = stack_size - 1; i >= 0; --i) {
    int pos = 0;
    int blocking_literal = 0;
    int *lemma = lemmas[ stack[ i ] ];
    while (*lemma) {
      if (assignment[ abs(*lemma) ] == *lemma) goto next_clause_error;
      if (blocking[ stack[ i ] ][ pos ] ) blocking_literal = *lemma;
      lemma++; pos++;
    }

    printf("ERROR forcing %i to true (stack_pos %i)\n", blocking_literal, i);
    exit(0);
    next_clause_error :;
  }

  for (i = 1; i <= nVars; ++i)  { assigned[ i ] = 1; seen[ i ] = 0; }

#ifdef BRANCH_SEQUENCE
  printf("b ");
  int time = 1;
  for (i = stack_size - 1; i >= 0; --i) {
    int pos = 0;
    int *lemma = lemmas[ stack[ i ] ];
    while (*lemma) {
      if (blocking[ stack[ i ] ][ pos ])
        seen[ abs( *(lemma) ) ] = time;
      lemma++; time++; pos++;
    }
  }
  time = 1;
  for (i = stack_size - 1; i >= 0; --i) {
    int *lemma = lemmas[ stack[ i ] ];
    while (*lemma) {
      if (seen[ abs( *lemma ) ] == time)
         printf("%i ", abs(*lemma) );
      lemma++; time++;
    }
  }
  printf("0\n");
#endif

//  for (i = stack_size - 1; i >= 0 ; --i) {
  for (i = 0; i < stack_size; ++i) {
    int pos = 0;
    int sat_count = 0;
    int blocking_literal = 0;
    int *lemma = lemmas[ stack[ i ] ];
    while (*lemma) {
      if (assignment[ abs(*lemma) ] == *lemma) {
         sat_count++;
         if (blocking[ stack[ i ] ][ pos ]) blocking_literal = *lemma;
      }
//      else if (assignment[ abs(*lemma) ] == 0)  goto next_lemma;
//      else if (blocking[ stack[ i ] ][ pos ])   goto next_lemma;

      lemma++; pos++;
    }
//    printf("%i %i %i\n", i, sat_count, blocking_literal);
    if (sat_count == 1) assigned[ abs(blocking_literal) ] = 0;
    next_lemma:;
  }
#ifdef PRINT_SOLUTION
  for (i = 1; i <= nVars; ++i) if (assigned[ i ]) printf("%i ", assignment[ i ]);
  printf("0\n");
#endif
#ifdef PRINT_NEG_SOLUTION
  for (i = 1; i <= nVars; ++i) if(assigned[ i ]) printf("%i ", -assignment[ i ]);
  printf("0\n");
#endif

//  printf("c nLemmas %i nRemoved %i\n", nLemmas, nRemoved);

  exit(1);
}
