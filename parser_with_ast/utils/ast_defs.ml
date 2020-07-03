open Utils

type 'a node = {
  p: position;
  t: 'a;
}
[@@deriving show { with_path = false }]

type unary_op =
  | U_pre_inc
  | U_pre_dec
  | U_post_inc
  | U_post_dec
  | U_address_of
  | U_dereference
  | U_plus
  | U_minus
  | U_bitwise_negation
  | U_logical_negation
[@@deriving show { with_path = false }]

type binary_op =
  | B_add
  | B_subtract
  | B_multiply
  | B_divise
  | B_modulus
  | B_shift_left
  | B_shift_right
  | B_bitwise_and
  | B_bitwise_xor
  | B_bitwise_or
[@@deriving show { with_path = false }]

type relation_op =
  | R_less
  | R_less_or_equal
  | R_greater
  | R_greater_or_equal
  | R_equal
  | R_not_equal
  | R_logical_and
  | R_logical_or
[@@deriving show { with_path = false }]

type function_specifier = [
  | `inline
  | `_Noreturn
]
[@@deriving show { with_path = false }]

type storage_class_specifier = [
  | `extern
  | `static
  | `_Thread_local
  | `auto
  | `register
]
[@@deriving show { with_path = false }]

type ('exp, 'typ) alignment_specifier = [
  | `Align_as_expr of 'exp
  | `Align_as_type of 'typ
]
[@@deriving show { with_path = false }]

type type_spec = [
  | `char
  | `short
  | `int
  | `long
  | `float
  | `double
  | `signed
  | `unsigned
  | `_Complex
]
[@@deriving show { with_path = false }]

type type_qualifier = [
  | `const
  | `restrict
  | `volatile
  | `_Atomic
]
[@@deriving show { with_path = false }]

type constant =
  | Cst_char of string
  | Cst_integer of string
  | Cst_decimal_float of string
  | Cst_hexadecimal_float of string
[@@deriving show { with_path = false }]

type string_literal =
  | Str_literal of string
[@@deriving show { with_path = false }]

type int_size = [`short | `default | `long | `long_long]
[@@deriving show { with_path = false }]

type float_size = [`single | `double | `long_double]
[@@deriving show { with_path = false }]

type signedness = [`signed | `unsigned]
[@@deriving show { with_path = false }]

