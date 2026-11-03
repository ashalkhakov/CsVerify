/* An integer calculator: statements of expressions, with precedence (the C version: lemon, C actions). */
%include {
#include <stdio.h>
}
%token_type {int}
%type expr {int}
%left PLUS MINUS.
%left TIMES DIVIDE.
%right UMINUS.
%syntax_error { printf("syntax error\n"); }
%parse_failure { printf("parse failed\n"); }
%parse_accept { printf("accepted\n"); }

program ::= stmts.
stmts ::= .
stmts ::= stmts stmt.
stmt ::= expr(A) SEMI. { printf("%d\n", A); }
expr(A) ::= expr(B) PLUS expr(C). { A = B + C; }
expr(A) ::= expr(B) MINUS expr(C). { A = B - C; }
expr(A) ::= expr(B) TIMES expr(C). { A = B * C; }
expr(A) ::= expr(B) DIVIDE expr(C). { A = C != 0 ? B / C : 0; }
expr(A) ::= MINUS expr(B). [UMINUS] { A = -B; }
expr(A) ::= LPAREN expr(B) RPAREN. { A = B; }
expr(A) ::= NUM(B). { A = B; }
