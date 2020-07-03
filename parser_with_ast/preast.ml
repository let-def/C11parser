open Utils
open Ast_defs

type statement = statement_ node
[@@deriving show { with_path = false }]

and statement_ =
  | Statement_label of { name: identifier; body: statement }
  | Statement_case of { case: expression; body: statement }
  | Statement_default of { default: position; body: statement }
  | Statement_if of { cond: expression; then_: statement; else_: statement option }
  | Statement_switch of { scrutinee: expression; body: statement }
  | Statement_skip
  | Statement_expression of expression
  | Statement_while of { cond: expression; body: statement }
  | Statement_do_while of { body: statement; cond: expression }
  | Statement_for of { pre: expression option;
                       cond: expression option;
                       post: expression option;
                       body: statement;
                     }
  | Statement_for_decl of { decl: declaration;
                            cond: expression option;
                            post: expression option;
                            body: statement;
                          }
  | Statement_compound of statement list
  | Statement_goto of identifier
  | Statement_continue
  | Statement_break
  | Statement_return of expression option
  | Statement_declaration of declaration

and expression = expression_ node
and expression_ =
  | Expression_var of identifier
  | Expression_constant of constant node
  | Expression_string of string_literal node list
  | Expression_generic_selection of expression * generic_association list
  | Expression_index of expression * expression
  | Expression_call of expression * expression list
  | Expression_dot of expression * identifier
  | Expression_arrow of expression * identifier
  | Expression_unary_op of unary_op node * expression
  | Expression_binary_op of binary_op node * expression * expression
  | Expression_relation_op of relation_op node * expression * expression
  | Expression_conditional of { cond: expression; then_: expression; else_: expression}
  | Expression_cast of type_name * expression
  | Expression_initializer of type_name * initializer_ list
  | Expression_comma of expression * expression
  | Expression_assignment of expression * binary_op option node * expression
  | Expression_sizeof_expr of expression
  | Expression_sizeof_type of type_name
  | Expression_alignof_type of type_name

and generic_association = generic_association_ node
and generic_association_ =
  | Generic_association_type of type_name * expression
  | Generic_association_default of position * expression

and initializer_ = initializer__ node
and initializer__ = {
  init_designator: designator list;
  init_expr: init_expr;
}

and init_expr = init_expr_ node
and init_expr_ =
  | Init_expr of expression
  | Init_list of initializer_ list

and designator = designator_ node
and designator_ =
  | Design_dot of identifier
  | Design_index of expression

and identifier = identifier_ node
and identifier_ = string

and type_name = type_name_ node
and type_name_ =
  Type_name of type_specifier * specifier_qualifier list * abstract_declarator option

and declaration = declaration_ node
and declaration_ =
  | Declaration_static_assert of static_assert
  | Declaration_var of declaration_specifiers * declaration_item list
  | Declaration_typedef of declaration_specifiers * declaration_item list

and declaration_item = declaration_item_ node
and declaration_item_ = declarator * init_expr option

and static_assert =
  Static_assert of expression * string_literal node list

and translation_unit = top_declaration list
and top_declaration = top_declaration_ node
and top_declaration_ =
  | Top_function_definition of function_definition
  | Top_declaration of declaration

and enum_specifier = enum_specifier_ node
and enum_specifier_ =
  | Enum_name of identifier
  | Enum_definition of {
      name: identifier option;
      members: (identifier * expression option) node list;
    }

and struct_specifier = struct_specifier_ node
and struct_specifier_ =
  | Struct_ref of struct_or_union * identifier
  | Struct_def of struct_or_union * identifier option * struct_declaration list

and struct_or_union = [ `Struct | `Union ] node

and struct_declaration =
  | Struct_assert of static_assert
  | Struct_declaration of type_specifier * specifier_qualifier list * struct_declarator list

and struct_declarator =
  | Field_declarator of declarator
  | Field_width of declarator option * expression

and specifier_qualifier =
  [ type_qualifier | (expression, type_name) alignment_specifier ] node

and parameter_type_list =
  | Parameters_fixed of parameter_declaration list
  | Parameters_variadic of parameter_declaration list * position

and parameter_declaration = parameter_declaration_ node
and parameter_declaration_ =
  | Parameter_named of declaration_specifiers * declarator
  | Parameter_abstract of declaration_specifiers * abstract_declarator option

and abstract_declarator = abstract_declarator_ node
and abstract_declarator_ =
  | Abstract_declarator_array of abstract_declarator option * array_declarator
  | Abstract_declarator_function of abstract_declarator option * parameter_type_list
  | Abstract_declarator_pointer of pointer * abstract_declarator option

and atomic_type_specifier = atomic_type_specifier_ node
and atomic_type_specifier_ =
  | Atomic_type of type_name

and type_qualifiers = type_qualifier node list

and pointer =
  Pointer of position * type_qualifiers * pointer option

and declarator =
  | Declarator_identifier of identifier
  | Declarator_array of declarator * array_declarator
  | Declarator_function of declarator * parameter_type_list
  | Declarator_other of declarator * identifier list
  | Declarator_pointer of pointer * declarator

and array_declarator =
  | Array_simple of type_qualifiers
  | Array_expr of type_qualifiers * expression
  | Array_static_expr of position * type_qualifiers * expression
  | Array_star of type_qualifiers * position

and declaration_specifiers =
  type_specifier * declaration_specifier list

and declaration_specifier = [
  | storage_class_specifier
  | type_qualifier
  | function_specifier
  | (expression, type_name) alignment_specifier
] node

and type_specifier =
  | Ts_unique of type_specifier_unique
  | Ts_nonunique of type_specifier_nonunique list

and type_specifier_unique = type_specifier_unique_ node
and type_specifier_unique_ =
  | Tsu_void
  | Tsu__Bool
  | Tsu__Atomic of type_name
  | Tsu_struct of struct_specifier
  | Tsu_enum of enum_specifier
  | Tsu_typedef of identifier

and type_specifier_nonunique = type_specifier_nonunique_ node
and type_specifier_nonunique_ =
  | Tsnu_char
  | Tsnu_short
  | Tsnu_int
  | Tsnu_long
  | Tsnu_float
  | Tsnu_double
  | Tsnu_signed
  | Tsnu_unsigned
  | Tsnu__Complex

and function_definition =
    Function_definition of
      declaration_specifiers * declarator * declaration list * statement
