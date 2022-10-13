From MetaCoq.Template Require Import Ast Loader.
From MetaCoq.Template Require Import utils.bytestring.



Print Ast.term.

Locate bytestring.String.
Print Ast.term.
MetaCoq Quote Recursively Definition qterm := Ast.term.
Print qterm.
