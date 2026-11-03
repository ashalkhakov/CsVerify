/* Declarations of nested lists, summed: an extra argument, a multiterminal, empty rules, left and right recursion
** (the C# version). */
%include {
using System;
}
%token_type {int}
%extra_argument {Totals total}
%type value {int}
%type items {int}
%type more {int}
%syntax_error { Console.Write("syntax error\n"); }
%parse_failure { Console.Write("parse failed\n"); }
%parse_accept { Console.Write("total " + total.Sum + "\n"); }
%code {
    public sealed class Totals { public int Sum; }
}

program ::= decls.
decls ::= .
decls ::= decls decl.
decl ::= ID|NAME(N) EQ value(V) SEMI. { Console.Write(N + " = " + V + "\n"); total.Sum += V; }
value(A) ::= NUM(B). { A = B; }
value(A) ::= LBRACE items(B) RBRACE. { A = B; }
items(A) ::= . { A = 0; }
items(A) ::= value(B) more(C). { A = B + C; }
more(A) ::= . { A = 0; }
more(A) ::= COMMA value(B) more(C). { A = B + C; }
