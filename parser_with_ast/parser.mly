(*
Jacques-Henri Jourdan, Inria Paris
François Pottier, Inria Paris

Copyright (c) 2016-2017, Inria
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of Inria nor the
      names of its contributors may be used to endorse or promote products
      derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL INRIA BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(* WARNING. When processing this grammar, Menhir should announce that
   ONE shift/reduce conflict was silently solved and that ONE state
   has 3 reduce/reduce conflicts on RPAREN, LPAREN, and LBRACK. If you
   modify the grammar, you should check that this is still the case. *)

%{
  open Context
  open Declarator
  open Ast_defs
  open Preast
%}

%token<string> NAME
%token VARIABLE TYPE
%token<Ast_defs.constant> CONSTANT
%token<Ast_defs.string_literal> STRING_LITERAL

%token ALIGNAS "_Alignas"
%token ALIGNOF "_Alignof"
%token ATOMIC "_Atomic"
%token AUTO "auto"
%token BOOL "_Bool"
%token BREAK "break"
%token CASE "case"
%token CHAR "char"
%token COMPLEX "_Complex"
%token CONST "const"
%token CONTINUE "continue"
%token DEFAULT "default"
%token DO "do"
%token DOUBLE "double"
%token ELSE "else"
%token ENUM "enum"
%token EXTERN "extern"
%token FLOAT "float"
%token FOR "for"
%token GENERIC "_Generic"
%token GOTO "goto"
%token IF "if"
%token IMAGINARY "_Imaginary"
%token INLINE "inline"
%token INT "int"
%token LONG "long"
%token NORETURN "_Noreturn"
%token REGISTER "register"
%token RESTRICT "restrict"
%token RETURN "return"
%token SHORT "short"
%token SIGNED "signed"
%token SIZEOF "sizeof"
%token STATIC "static"
%token STATIC_ASSERT "_Static_assert"
%token STRUCT "struct"
%token SWITCH "switch"
%token THREAD_LOCAL "_Thread_local"
%token TYPEDEF "typedef"
%token UNION "union"
%token UNSIGNED "unsigned"
%token VOID "void"
%token VOLATILE "volatile"
%token WHILE "while"

%token ELLIPSIS "..."
%token ADD_ASSIGN "+="
%token SUB_ASSIGN "-="
%token MUL_ASSIGN "*="
%token DIV_ASSIGN "/="
%token MOD_ASSIGN "%="
%token OR_ASSIGN "|="
%token AND_ASSIGN "&="
%token XOR_ASSIGN "^="
%token LEFT_ASSIGN "<<="
%token RIGHT_ASSIGN ">>="
%token LEFT "<<"
%token RIGHT ">>"
%token EQEQ "=="
%token NEQ "!="
%token LEQ "<="
%token GEQ ">="
%token EQ "="
%token LT "<"
%token GT ">"
%token INC "++"
%token DEC "--"
%token PTR "->"
%token PLUS "+"
%token MINUS "-"
%token STAR "*"
%token SLASH "/"
%token PERCENT "%"
%token BANG "!"
%token ANDAND "&&"
%token BARBAR "||"
%token AND "&"
%token BAR "|"
%token HAT "^"
%token QUESTION "?"
%token COLON ":"
%token TILDE "~"
%token LBRACE "{"
%token RBRACE "}"
%token LBRACK "["
%token RBRACK "]"
%token LPAREN "("
%token RPAREN ")"
%token SEMICOLON ";"
%token COMMA ","
%token DOT "."

(* ATOMIC_LPAREN is "special"; it's used for left parentheses that
   follow the ["_Atomic"] keyword. It isn't given a token alias *)
%token ATOMIC_LPAREN

%token EOF

%type<Context.context> save_context
%type<Context.context * _> parameter_type_list
%type<string Ast_defs.node> typedef_name var_name general_identifier
%type<Declarator.declarator * _> declarator direct_declarator

%type<Preast.expression> expression primary_expression postfix_expression
(* There is a reduce/reduce conflict in the grammar. It corresponds to the
   conflict in the second declaration in the following snippet:

     typedef int T;
     int f(int(T));

   It is specified by 6.7.6.3 11: 'T' should be taken as the type of the
   parameter of the anonymous function taken as a parameter by f (thus,
   f has type (T -> int) -> int).

   The reduce/reduce conflict is solved by letting menhir reduce the production
   appearing first in this file. This is the reason why we have the
   [typedef_name_spec] proxy: it is here just to make sure the conflicting
   production appears before the other (which concerns [general_identifier]). *)

(* These precedence declarations solve the dangling else conflict. *)
%nonassoc below_ELSE
%nonassoc ELSE

%start<Preast.translation_unit> translation_unit_file
%start<unit> dummy

%%

(* A list of A's and B's that contains exactly one A: *)

list_eq1(A, B):
| A B*
    { ($1, $2) }
| B list_eq1(A, B)
    { let (a, b) = $2 in (a, $1 :: b) }

(* A list of A's and B's that contains at least one A: *)

list_ge1(A, B):
| A B*
    { ([$1], $2) }
| A list_ge1(A, B)
    { let (a, b) = $2 in ($1 :: a, b) }
| B list_ge1(A, B)
    { let (a, b) = $2 in (a, $1 :: b) }

(* A list of A's, B's and C's that contains exactly one A and exactly one B: *)

list_eq1_eq1(A, B, C):
| A list_eq1(B, C)
    { let (b, c) = $2 in ($1, b, c) }
| B list_eq1(A, C)
    { let (a, c) = $2 in (a, $1, c) }
| C list_eq1_eq1(A, B, C)
    { let (a, b, c) = $2 in (a, b, $1 :: c) }

(* A list of A's, B's and C's that contains exactly one A and at least one B: *)

list_eq1_ge1(A, B, C):
| A list_ge1(B, C)
    { let (b, c) = $2 in ($1, b, c) }
| B list_eq1(A, C)
    { let (a, c) = $2 in (a, [$1], c) }
| B list_eq1_ge1(A, B, C)
    { let (a, b, c) = $2 in (a, $1 :: b, c) }
| C list_eq1_ge1(A, B, C)
    { let (a, b, c) = $2 in (a, b, $1 :: c) }

(* Comma list *)

comma_list_(X):
| X { [$1] }
| comma_list_(X) "," X { $3 :: $1 }

%inline comma_list(X):
| comma_list_(X) { List.rev $1 }

opt_comma_list(X):
| (* empty *)    { [] }
| comma_list_(X) { List.rev $1 }

comma_list_comma(X):
| comma_list_(X)
| comma_list_(X) ","
  { List.rev $1 }

(* Store position *)

%inline pos(X):
| X
    { ($startofs, $endofs) }

%inline inode(X):
| X
    { { t = $1; p = ($startofs, $endofs) } }

node(X):
| inode(X)
    { $1 }

(* Upon finding an identifier, the lexer emits two tokens. The first token,
   [NAME], indicates that a name has been found; the second token, either [TYPE]
   or [VARIABLE], tells what kind of name this is. The classification is
   performed only when the second token is demanded by the parser. *)

typedef_name: i = inode(NAME) TYPE { i }

var_name: i = inode(NAME) VARIABLE { i }

(* [typedef_name_spec] must be declared before [general_identifier], so that the
   reduce/reduce conflict is solved the right way. *)

typedef_name_spec: typedef_name { $1 }

general_identifier:
| i = typedef_name
| i = var_name
    { i }

save_context:
| (* empty *)
    { save_context () }

scoped(X):
| ctx = save_context x = X
    { restore_context ctx; x }

(* [declarator_varname] and [declarator_typedefname] are like [declarator]. In
   addition, they have the side effect of introducing the declared identifier as
   a new variable or typedef name in the current context. *)

declarator_varname:
| d = declarator { declare_varname (identifier (fst d)); d }

declarator_typedefname:
| d = declarator { declare_typedefname (identifier (fst d)); d }

(* End of the helpers, and beginning of the grammar proper: *)

primary_expression:
  "(" expression ")" { $2 } | inode(primary_expression_) { $1 }
%inline primary_expression_:
| var_name
    { Expression_var $1 }
| inode(CONSTANT)
    { Expression_constant $1 }
| inode(STRING_LITERAL)+
    { Expression_string $1 }
| generic_selection
    { $1 }

generic_selection:
| "_Generic" "(" assignment_expression "," comma_list(inode(generic_association)) ")"
    { Expression_generic_selection ($3, $5) }

generic_association:
| type_name ":" assignment_expression
    { Generic_association_type ($1, $3) }
| "default" ":" assignment_expression
    { Generic_association_default (($startofs($1), $endofs($1)), $3) }

postfix_expression: primary_expression | inode(postfix_expression_) { $1 }
%inline postfix_expression_:
| postfix_expression "[" expression "]"
    { Expression_index ($1, $3) }
| postfix_expression "(" opt_comma_list(assignment_expression) ")"
    { Expression_call ($1, $3) }
| postfix_expression "." general_identifier
    { Expression_dot ($1, $3) }
| postfix_expression "->" general_identifier
    { Expression_arrow ($1, $3) }
| postfix_expression inode("++" {U_post_inc})
    { Expression_unary_op ($2, $1) }
| postfix_expression inode("--" {U_post_dec})
    { Expression_unary_op ($2, $1) }
| "(" type_name ")" "{" comma_list_comma(inode(initializer_)) "}"
    { Expression_initializer ($2, $5) }

unary_expression: postfix_expression | inode(unary_expression_) { $1 }
%inline unary_expression_:
| inode("++" {U_pre_inc}) unary_expression
    { Expression_unary_op ($1, $2) }
| inode("--" {U_pre_dec}) unary_expression
    { Expression_unary_op ($1, $2) }
| inode(unary_operator) cast_expression
    { Expression_unary_op ($1, $2) }
| "sizeof" unary_expression
    { Expression_sizeof_expr $2 }
| "sizeof" "(" type_name ")"
    { Expression_sizeof_type $3 }
| "_Alignof" "(" type_name ")"
    { Expression_alignof_type $3 }

unary_operator:
| "&" { U_address_of }
| "*" { U_dereference }
| "+" { U_plus }
| "-" { U_minus }
| "~" { U_bitwise_negation }
| "!" { U_logical_negation }

cast_expression: unary_expression | inode(cast_expression_) { $1 }
%inline cast_expression_:
| "(" type_name ")" cast_expression
    { Expression_cast ($2, $4) }

multiplicative_operator:
| "*" { B_multiply }
| "/" { B_divise }
| "%" { B_modulus }

multiplicative_expression:
  cast_expression | inode(multiplicative_expression_) { $1 }
%inline multiplicative_expression_:
| multiplicative_expression inode(multiplicative_operator) cast_expression
    { Expression_binary_op ($2, $1, $3) }

additive_operator:
| "+" { B_add }
| "-" { B_subtract }

additive_expression:
  multiplicative_expression | inode(additive_expression_) { $1 }
%inline additive_expression_:
| additive_expression inode(additive_operator) multiplicative_expression
    { Expression_binary_op ($2, $1, $3) }

shift_operator:
| "<<" { B_shift_left }
| ">>" { B_shift_right }

shift_expression: additive_expression | inode(shift_expression_) { $1 }
%inline shift_expression_:
| shift_expression inode(shift_operator) additive_expression
    { Expression_binary_op ($2, $1, $3) }

relational_operator:
| "<"  { R_less }
| ">"  { R_greater }
| "<=" { R_less_or_equal }
| ">=" { R_greater_or_equal }

relational_expression: shift_expression | inode(relational_expression_) { $1 }
%inline relational_expression_:
| relational_expression inode(relational_operator) shift_expression
    { Expression_relation_op ($2, $1, $3) }

equality_operator:
| "==" { R_equal }
| "!=" { R_not_equal }

equality_expression: relational_expression | inode(equality_expression_) { $1 }
%inline equality_expression_:
| equality_expression inode(equality_operator) relational_expression
    { Expression_relation_op ($2, $1, $3) }

and_expression: equality_expression | inode(and_expression_) { $1 }
%inline and_expression_:
| and_expression inode("&" {B_bitwise_and}) equality_expression
    { Expression_binary_op ($2, $1, $3) }

exclusive_or_expression: and_expression | inode(exclusive_or_expression_) { $1 }
%inline exclusive_or_expression_:
| exclusive_or_expression inode("^" {B_bitwise_xor}) and_expression
    { Expression_binary_op ($2, $1, $3) }

inclusive_or_expression:
  exclusive_or_expression | inode(inclusive_or_expression_) { $1 }
%inline inclusive_or_expression_:
| inclusive_or_expression inode("|" {B_bitwise_or}) exclusive_or_expression
    { Expression_binary_op ($2, $1, $3) }

logical_and_expression:
  inclusive_or_expression | inode(logical_and_expression_) { $1 }
%inline logical_and_expression_:
| logical_and_expression inode("&&" {R_logical_and}) inclusive_or_expression
    { Expression_relation_op ($2, $1, $3) }

logical_or_expression:
  logical_and_expression | inode(logical_or_expression_) { $1 }
%inline logical_or_expression_:
| logical_or_expression inode("||" {R_logical_or}) logical_and_expression
    { Expression_relation_op ($2, $1, $3) }

conditional_expression:
  logical_or_expression | inode(conditional_expression_) { $1 }
%inline conditional_expression_:
| logical_or_expression "?" expression ":" conditional_expression
    { Expression_conditional { cond = $1; then_ = $3; else_ = $5 } }

assignment_expression:
  conditional_expression | inode(assignment_expression_) { $1 }
%inline assignment_expression_:
| unary_expression inode(assignment_operator) assignment_expression
    { Expression_assignment ($1, $2, $3) }

assignment_operator:
| "="   { None               }
| "*="  { Some B_multiply    }
| "/="  { Some B_divise      }
| "%="  { Some B_modulus     }
| "+="  { Some B_add         }
| "-="  { Some B_subtract    }
| "<<=" { Some B_shift_left  }
| ">>=" { Some B_shift_right }
| "&="  { Some B_bitwise_and }
| "^="  { Some B_bitwise_xor }
| "|="  { Some B_bitwise_or  }

expression: assignment_expression | inode(expression_) { $1 }
%inline expression_:
| expression "," assignment_expression
    { Expression_comma ($1, $3) }

constant_expression:
| conditional_expression
    { $1 }

(* We separate type declarations, which contain an occurrence of ["typedef"], and
   normal declarations, which do not. This makes it possible to distinguish /in
   the grammar/ whether a declaration introduces typedef names or variables in
   the context. *)

declaration: inode(declaration_) { $1 }
%inline declaration_:
| declaration_specifiers init_declarator_list(declarator_varname) ";"
    { Declaration_var ($1, $2) }
| declaration_specifiers_typedef init_declarator_list(declarator_typedefname) ";"
    { Declaration_typedef ($1, $2) }
| static_assert_declaration
    { Declaration_static_assert $1 }

(* [declaration_specifier] corresponds to one declaration specifier in the C18
   standard, deprived of "typedef" and of type specifiers. *)

declaration_specifier:
| storage_class_specifier (* deprived of "typedef" *)
| type_qualifier
| function_specifier
| alignment_specifier
    { ($1 :> declaration_specifier) }

(* [declaration_specifiers] requires that at least one type specifier be
   present, and, if a unique type specifier is present, then no other type
   specifier be present. In other words, one should have either at least one
   nonunique type specifier, or exactly one unique type specifier.

   This is a weaker condition than 6.7.2 2. Encoding this condition in the
   grammar is necessary to disambiguate the example in 6.7.7 6:

     typedef signed int t;
     struct tag {
     unsigned t:4;
     const t:5;
     };

   The first field is a named t, while the second is unnamed of type t.

   [declaration_specifiers] forbids the ["typedef"] keyword. *)

declaration_specifiers:
| list_eq1(type_specifier_unique,    declaration_specifier)
    { let ts, ds = $1 in (Ts_unique ts, ds) }
| list_ge1(type_specifier_nonunique, declaration_specifier)
    { let ts, ds = $1 in (Ts_nonunique ts, ds) }

(* [declaration_specifiers_typedef] is analogous to [declaration_specifiers],
   but requires the ["typedef"] keyword to be present (exactly once). *)

declaration_specifiers_typedef:
| list_eq1_eq1("typedef", type_specifier_unique,    declaration_specifier)
    { let _, ts, ds = $1 in (Ts_unique ts, ds) }
| list_eq1_ge1("typedef", type_specifier_nonunique, declaration_specifier)
    { let _, ts, ds = $1 in (Ts_nonunique ts, ds) }

(* The parameter [declarator] in [init_declarator_list] and [init_declarator]
   is instantiated with [declarator_varname] or [declarator_typedefname]. *)

init_declarator_list(declarator):
  opt_comma_list(inode(init_declarator(declarator))) { $1 }

init_declarator(declarator):
| declarator
    { snd $1, None }
| declarator "=" inode(c_initializer)
    { snd $1, Some $3 }

(* [storage_class_specifier] corresponds to storage-class-specifier in the
   C18 standard, deprived of ["typedef"] (which receives special treatment). *)

storage_class_specifier: inode(storage_class_specifier_) { $1 }
%inline storage_class_specifier_:
| "extern"        { `extern        }
| "static"        { `static        }
| "_Thread_local" { `_Thread_local }
| "auto"          { `auto          }
| "register"      { `register      }

(* A type specifier which can appear together with other type specifiers. *)

type_specifier_nonunique: inode(type_specifier_nonunique_) { $1 }
%inline type_specifier_nonunique_:
| "char"     { Tsnu_char     }
| "short"    { Tsnu_short    }
| "int"      { Tsnu_int      }
| "long"     { Tsnu_long     }
| "float"    { Tsnu_float    }
| "double"   { Tsnu_double   }
| "signed"   { Tsnu_signed   }
| "unsigned" { Tsnu_unsigned }
| "_Complex" { Tsnu__Complex }

(* A type specifier which cannot appear together with other type specifiers. *)

type_specifier_unique: inode(type_specifier_unique_) { $1 }
%inline type_specifier_unique_:
| "void"                    { Tsu_void       }
| "_Bool"                   { Tsu__Bool      }
| atomic_type_specifier     { Tsu__Atomic $1 }
| struct_or_union_specifier { Tsu_struct  $1 }
| enum_specifier            { Tsu_enum    $1 }
| typedef_name_spec         { Tsu_typedef $1 }

%inline struct_or_union_specifier: inode(struct_or_union_specifier_) { $1 }
struct_or_union_specifier_:
| inode(struct_or_union) general_identifier? "{" struct_declaration_list "}"
    { Struct_def ($1, $2, $4 ) }
| inode(struct_or_union) general_identifier
    { Struct_ref ($1, $2) }

struct_or_union:
| "struct" { `Struct }
| "union"  { `Union }

%inline struct_declaration_list: struct_declaration_list_ { List.rev $1 }
struct_declaration_list_:
| struct_declaration
    { [$1] }
| struct_declaration_list_ struct_declaration
    { $2 :: $1 }

struct_declaration:
| specifier_qualifier_list opt_comma_list(struct_declarator) ";"
    { Struct_declaration (fst $1, snd $1, $2) }
| static_assert_declaration
    { Struct_assert $1 }

(* [specifier_qualifier_list] is as in the standard, except it also encodes the
   same constraint as [declaration_specifiers] (see above). *)

specifier_qualifier_list:
| list_eq1(type_specifier_unique, specifier_qualifier_list_flag)
    { (Ts_unique (fst $1), snd $1) }
| list_ge1(type_specifier_nonunique, specifier_qualifier_list_flag)
    { (Ts_nonunique (fst $1), snd $1) }

specifier_qualifier_list_flag:
| type_qualifier | alignment_specifier
    { ($1 :> specifier_qualifier) }

struct_declarator:
| declarator                         { Field_declarator (snd $1) }
| ":" constant_expression            { Field_width (None, $2) }
| declarator ":" constant_expression { Field_width (Some (snd $1), $3) }

%inline enum_specifier: inode(enum_specifier_) { $1 }
enum_specifier_:
| "enum" general_identifier? "{" comma_list_comma(inode(enumerator)) "}"
    { Enum_definition { name = $2; members = $4 } }
| "enum" general_identifier
    { Enum_name $2 }

enumerator:
| general_identifier                         { declare_varname $1.t; ($1, None) }
| general_identifier "=" constant_expression { declare_varname $1.t; ($1, Some $3) }

atomic_type_specifier:
| "_Atomic" "(" type_name ")"
| "_Atomic" ATOMIC_LPAREN type_name ")"
    { $3 }

type_qualifier: inode(type_qualifier_) { $1 }
%inline type_qualifier_:
| "const"     { `const    }
| "restrict"  { `restrict }
| "volatile"  { `volatile }
| "_Atomic"   { `_Atomic  }


function_specifier: inode(function_specifier_) { $1 }
function_specifier_:
| "inline"    { `inline    }
| "_Noreturn" { `_Noreturn }

alignment_specifier: inode(alignment_specifier_) { $1 }
alignment_specifier_:
| "_Alignas" "(" type_name ")"
    { `Align_as_type $3 }
| "_Alignas" "(" constant_expression ")"
    { `Align_as_expr $3 }

declarator:
| direct_declarator
    { let d, dd = $1 in other_declarator d, dd }
| pointer direct_declarator
    { let d, dd = $2 in other_declarator d, Declarator_pointer ($1, dd) }

(* The occurrences of [save_context] inside [direct_declarator] and
   [direct_abstract_declarator] seem to serve no purpose. In fact, they are
   required in order to avoid certain conflicts. In other words, we must save
   the context at this point because the LR automaton is exploring multiple
   avenues in parallel and some of them do require saving the context. *)

direct_declarator:
| general_identifier
    { identifier_declarator $1.t, Declarator_identifier $1 }
| "(" save_context declarator ")"
    { $3 }
| direct_declarator "[" array_declarator "]"
    { let d, dd = $1 in d, Declarator_array (dd, $3) }
| direct_declarator "(" scoped(parameter_type_list) ")"
    { let d, dd = $1 in
      let ctx, parameters = $3 in
      function_declarator d ctx, Declarator_function (dd, parameters) }
| direct_declarator "(" save_context comma_list(var_name) ")"
    { let d, dd = $1 in other_declarator d, Declarator_other (dd, $4) }

array_declarator:
| type_qualifier*
  { Array_simple $1 }
| type_qualifier* assignment_expression
  { Array_expr ($1, $2) }
| pos("static") type_qualifier* assignment_expression
  { Array_static_expr ($1, $2, $3) }
| type_qualifier+ pos("static") assignment_expression
  { Array_static_expr ($2, $1, $3) }
| type_qualifier* pos("*")
  { Array_star ($1, $2) }

pointer:
| pos("*") type_qualifier* pointer?
    { Pointer ($1, $2, $3) }

parameter_type_list:
| save_context (* empty *) { $1, Parameters_fixed [] }
| comma_list(parameter_declaration) save_context
    { $2, Parameters_fixed $1 }
| comma_list(parameter_declaration) "," pos("...") save_context
    { $4, Parameters_variadic ($1, $3) }

parameter_declaration: inode(parameter_declaration_) { $1 }
%inline parameter_declaration_:
| declaration_specifiers declarator_varname
    { Parameter_named ($1, snd $2) }
| declaration_specifiers abstract_declarator?
    { Parameter_abstract ($1, $2) }

type_name: inode(type_name_) { $1 }
%inline type_name_:
| specifier_qualifier_list abstract_declarator?
    { Type_name (fst $1, snd $1, $2) }

abstract_declarator:
| direct_abstract_declarator  { $1 }
| inode(abstract_declarator_) { $1 }

%inline abstract_declarator_:
| pointer ioption(direct_abstract_declarator)
    { Abstract_declarator_pointer ($1, $2) }

direct_abstract_declarator:
| "(" save_context abstract_declarator ")" { $3 }
| inode(direct_abstract_declarator_)       { $1 }

%inline direct_abstract_declarator_:
| direct_abstract_declarator? "[" array_declarator "]"
    { Abstract_declarator_array ($1, $3) }
| ioption(direct_abstract_declarator) "(" scoped(parameter_type_list) ")"
    { Abstract_declarator_function ($1, snd $3) }

c_initializer:
| assignment_expression
    { Init_expr $1 }
| "{" comma_list_comma(inode(initializer_)) "}"
    { Init_list $2 }

%inline initializer_:
| designation inode(c_initializer)
    { { init_designator = $1; init_expr = $2 } }

designation:
| (* empty *) { [] }
| inode(designator)+ "=" { $1 }

designator:
| "[" constant_expression "]" { Design_index $2 }
| "." general_identifier      { Design_dot $2 }

static_assert_declaration:
| "_Static_assert" "(" constant_expression "," inode(STRING_LITERAL)+ ")" ";"
    { Static_assert ($3, $5) }

statement: inode(statement_) { $1 }
%inline statement_:
| labeled_statement
| scoped(compound_statement)
| expression_statement
| scoped(selection_statement)
| scoped(iteration_statement)
| jump_statement
    { $1 }

labeled_statement:
| general_identifier ":" statement
    { Statement_label { name = $1; body = $3 } }
| "case" constant_expression ":" statement
    { Statement_case { case = $2; body = $4 } }
| pos("default") ":" statement
    { Statement_default { default = $1; body = $3 } }

compound_statement:
| "{" block_item* "}"
    { Statement_compound $2 }

block_item:
| inode(declaration { Statement_declaration $1 })
| statement         { $1 }

expression_statement:
| ";"            { Statement_skip }
| expression ";" { Statement_expression $1 }

selection_statement:
| "if" "(" expression ")" scoped(statement) "else" scoped(statement)
    { Statement_if {cond = $3; then_ = $5; else_ = Some $7 } }
| "if" "(" expression ")" scoped(statement) %prec below_ELSE
    { Statement_if {cond = $3; then_ = $5; else_ = None } }
| "switch" "(" expression ")" scoped(statement)
    { Statement_switch { scrutinee = $3; body = $5 } }

iteration_statement:
| "while" "(" expression ")" scoped(statement)
    { Statement_while { cond = $3; body = $5 } }
| "do" scoped(statement) "while" "(" expression ")" ";"
    { Statement_do_while { body = $2; cond = $5 } }
| "for" "(" expression? ";" expression? ";" expression? ")" scoped(statement)
    { Statement_for { pre = $3; cond = $5; post = $7; body = $9 } }
| "for" "(" declaration expression? ";" expression? ")" scoped(statement)
    { Statement_for_decl { decl = $3; cond = $4; post = $6; body = $8 } }

jump_statement:
| "goto" general_identifier ";"
    { Statement_goto $2 }
| "continue" ";"
    { Statement_continue }
| "break" ";"
    { Statement_break }
| "return" expression? ";"
    { Statement_return $2 }

translation_unit_file:
  inode(external_declaration)* EOF { $1 }

(* Silence warning *)
dummy: IMAGINARY { () }

external_declaration:
| function_definition { Top_function_definition $1 }
| declaration         { Top_declaration $1 }

function_definition1:
| declaration_specifiers declarator_varname
    { let ctx = save_context () in
      reinstall_function_context (fst $2);
      (ctx, $1, $2) }

function_definition:
| function_definition1 declaration* inode(compound_statement)
    { let (ctx, spec, (_, declarator)) = $1 in
      restore_context ctx;
      Function_definition (spec, declarator, $2, $3) }
