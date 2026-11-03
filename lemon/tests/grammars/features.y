// Directives: names, types, destructors, fallback, wildcard, token classes, %ifdef, codes.
%name Feat
%token_prefix TK_
%extra_argument {int *pCount}
%token_type {const char*}
%default_type {int}
%type expr {long}
%type list {void*}
%destructor list { free($$); }
%default_destructor { (void)$$; }
%token_destructor { (void)$$; }
%syntax_error { *pCount += 1; }
%parse_failure { *pCount = -1; }
%parse_accept { *pCount += 100; }
%stack_overflow { *pCount = -2; }
%stack_size 50
%include {
#include <stdlib.h>
/* include block */
}
%code {
/* extra code at the end */
}
%fallback ID KEYWORD OTHER.
%wildcard ANY.
%token_class number INTEGER|FLOAT.
%start_symbol program
program ::= list(L). { (void)L; }
list(A) ::= . { A = 0; }
list(A) ::= list(B) item. { A = B; }
item ::= expr(E) SEMI. { (void)E; }
item ::= KEYWORD ANY.
expr(A) ::= number(N). { A = (long)N; }
expr(A) ::= ID(X). { A = X ? 1 : 0; }
expr(A) ::= LP expr(B) RP. { A = B; }
%ifdef WITH_PLUS
expr(A) ::= expr(B) PLUS expr(C). { A = B + C; }
%else
expr(A) ::= expr(B) MINUS expr(C). { A = B - C; }
%endif
%if WITH_TIMES || WITH_ALL
expr(A) ::= expr(B) TIMES expr(C). { A = B * C; }
%endif
