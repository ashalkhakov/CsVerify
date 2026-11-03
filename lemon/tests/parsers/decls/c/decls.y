/* Declarations of nested lists, summed: an extra argument, a multiterminal, empty rules, left and right recursion
** (the C version). */
%include {
#include <stdio.h>
}
%token_type {int}
%extra_argument {int *total}
%type value {int}
%type items {int}
%type more {int}
%syntax_error { printf("syntax error\n"); }
%parse_failure { printf("parse failed\n"); }
%parse_accept { printf("total %d\n", *total); }

program ::= decls.
decls ::= .
decls ::= decls decl.
decl ::= ID|NAME(N) EQ value(V) SEMI. { printf("%d = %d\n", N, V); *total += V; }
value(A) ::= NUM(B). { A = B; }
value(A) ::= LBRACE items(B) RBRACE. { A = B; }
items(A) ::= . { A = 0; }
items(A) ::= value(B) more(C). { A = B + C; }
more(A) ::= . { A = 0; }
more(A) ::= COMMA value(B) more(C). { A = B + C; }
