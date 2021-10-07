// A Bison parser, made by GNU Bison 3.8.1.

// Skeleton interface for Bison LALR(1) parsers in C++

// Copyright (C) 2002-2015, 2018-2021 Free Software Foundation, Inc.

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

// As a special exception, you may create a larger work that contains
// part or all of the Bison parser skeleton and distribute that work
// under terms of your choice, so long as that work isn't itself a
// parser generator using the skeleton or a modified version thereof
// as a parser skeleton.  Alternatively, if you modify or redistribute
// the parser skeleton itself, you may (at your option) remove this
// special exception, which will cause the skeleton and the resulting
// Bison output files to be licensed under the GNU General Public
// License without this special exception.

// This special exception was added by the Free Software Foundation in
// version 2.2 of Bison.


/**
 ** \file ../../mli-root/src/database-parser.hh
 ** Define the mli::parser class.
 */

// C++ LALR(1) parser skeleton written by Akim Demaille.

// DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
// especially those whose name start with YY_ or yy_.  They are
// private implementation details that can be changed or removed.

#ifndef YY_MLI_MLI_ROOT_SRC_DATABASE_PARSER_HH_INCLUDED
# define YY_MLI_MLI_ROOT_SRC_DATABASE_PARSER_HH_INCLUDED
// "%code requires" blocks.
#line 42 "../../mli-root/src/database-parser.yy"

  #include "MLI.hh"
  #include "database.hh"
  #include "basictype.hh"

  #include "location-type.hh"


  // #define YYERROR_VERBOSE 1

  #ifndef yyFlexLexer
    #define yyFlexLexer mliFlexLexer

    #include <FlexLexer.h>
  #endif


  namespace mli {

    class semantic_type {
    public:
      long number = 0;
      std::string text;
      mli::ref<mli::unit> object;

      semantic_type() {}
    };


    class database_lexer : public yyFlexLexer {
    public:
      mli::semantic_type* yylvalp = nullptr;
      mli::location_type* yyllocp = nullptr;

      database_lexer() {};

      database_lexer(std::istream& is, std::ostream& os) : yyFlexLexer(&is, &os) {}

      int yylex(); // Defined in database-lexer.cc.

      std::istream& in() { return yyin; }

      int operator()(mli::semantic_type* x) { yylvalp = x;  return yylex(); }
      int operator()(mli::semantic_type* x, mli::location_type* y) { yylvalp = x;  yyllocp = y;  return yylex(); }
    };

  } // namespace mli


#line 99 "../../mli-root/src/database-parser.hh"


# include <cstdlib> // std::abort
# include <iostream>
# include <stdexcept>
# include <string>
# include <vector>

#if defined __cplusplus
# define YY_CPLUSPLUS __cplusplus
#else
# define YY_CPLUSPLUS 199711L
#endif

// Support move semantics when possible.
#if 201103L <= YY_CPLUSPLUS
# define YY_MOVE           std::move
# define YY_MOVE_OR_COPY   move
# define YY_MOVE_REF(Type) Type&&
# define YY_RVREF(Type)    Type&&
# define YY_COPY(Type)     Type
#else
# define YY_MOVE
# define YY_MOVE_OR_COPY   copy
# define YY_MOVE_REF(Type) Type&
# define YY_RVREF(Type)    const Type&
# define YY_COPY(Type)     const Type&
#endif

// Support noexcept when possible.
#if 201103L <= YY_CPLUSPLUS
# define YY_NOEXCEPT noexcept
# define YY_NOTHROW
#else
# define YY_NOEXCEPT
# define YY_NOTHROW throw ()
#endif

// Support constexpr when possible.
#if 201703 <= YY_CPLUSPLUS
# define YY_CONSTEXPR constexpr
#else
# define YY_CONSTEXPR
#endif



#ifndef YY_ATTRIBUTE_PURE
# if defined __GNUC__ && 2 < __GNUC__ + (96 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_PURE __attribute__ ((__pure__))
# else
#  define YY_ATTRIBUTE_PURE
# endif
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# if defined __GNUC__ && 2 < __GNUC__ + (7 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_UNUSED __attribute__ ((__unused__))
# else
#  define YY_ATTRIBUTE_UNUSED
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YY_USE(E) ((void) (E))
#else
# define YY_USE(E) /* empty */
#endif

/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
#if defined __GNUC__ && ! defined __ICC && 406 <= __GNUC__ * 100 + __GNUC_MINOR__
# if __GNUC__ * 100 + __GNUC_MINOR__ < 407
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")
# else
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")              \
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# endif
# define YY_IGNORE_MAYBE_UNINITIALIZED_END      \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif

#if defined __cplusplus && defined __GNUC__ && ! defined __ICC && 6 <= __GNUC__
# define YY_IGNORE_USELESS_CAST_BEGIN                          \
    _Pragma ("GCC diagnostic push")                            \
    _Pragma ("GCC diagnostic ignored \"-Wuseless-cast\"")
# define YY_IGNORE_USELESS_CAST_END            \
    _Pragma ("GCC diagnostic pop")
#endif
#ifndef YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_END
#endif

# ifndef YY_CAST
#  ifdef __cplusplus
#   define YY_CAST(Type, Val) static_cast<Type> (Val)
#   define YY_REINTERPRET_CAST(Type, Val) reinterpret_cast<Type> (Val)
#  else
#   define YY_CAST(Type, Val) ((Type) (Val))
#   define YY_REINTERPRET_CAST(Type, Val) ((Type) (Val))
#  endif
# endif
# ifndef YY_NULLPTR
#  if defined __cplusplus
#   if 201103L <= __cplusplus
#    define YY_NULLPTR nullptr
#   else
#    define YY_NULLPTR 0
#   endif
#  else
#   define YY_NULLPTR ((void*)0)
#  endif
# endif

/* Debug traces.  */
#ifndef MLIDEBUG
# if defined YYDEBUG
#if YYDEBUG
#   define MLIDEBUG 1
#  else
#   define MLIDEBUG 0
#  endif
# else /* ! defined YYDEBUG */
#  define MLIDEBUG 1
# endif /* ! defined YYDEBUG */
#endif  /* ! defined MLIDEBUG */

#line 22 "../../mli-root/src/database-parser.yy"
namespace mli {
#line 243 "../../mli-root/src/database-parser.hh"




  /// A Bison parser.
  class database_parser
  {
  public:
#ifdef MLISTYPE
# ifdef __GNUC__
#  pragma GCC message "bison: do not #define MLISTYPE in C++, use %define api.value.type"
# endif
    typedef MLISTYPE value_type;
#else
    /// Symbol semantic values.
    typedef mli::semantic_type value_type;
#endif
    /// Backward compatibility (Bison 3.8).
    typedef value_type semantic_type;
    /// Symbol locations.
    typedef location_t location_type;

    /// Syntax errors thrown from user actions.
    struct syntax_error : std::runtime_error
    {
      syntax_error (const location_type& l, const std::string& m)
        : std::runtime_error (m)
        , location (l)
      {}

      syntax_error (const syntax_error& s)
        : std::runtime_error (s.what ())
        , location (s.location)
      {}

      ~syntax_error () YY_NOEXCEPT YY_NOTHROW;

      location_type location;
    };

    /// Token kinds.
    struct token
    {
      enum token_kind_type
      {
        MLIEMPTY = -2,
    MLIEOF = 0,                    // "end of file"
    MLIerror = 256,                // error
    MLIUNDEF = 257,                // "invalid token"
    token_error = 258,             // "token error"
    include_key = 259,             // "include"
    theory_key = 260,              // "theory"
    end_key = 261,                 // "end"
    formal_system_key = 262,       // "formal system"
    definition_key = 263,          // "definition"
    postulate_key = 264,           // "postulate"
    axiom_key = 265,               // "axiom"
    rule_key = 266,                // "rule"
    conjecture_key = 267,          // "conjecture"
    theorem_key = 268,             // "theorem"
    proof_key = 269,               // "proof"
    end_of_proof_key = 270,        // "∎"
    by_key = 271,                  // "by"
    premise_key = 272,             // "premise"
    result_key = 273,              // "result"
    metainfer_key = 274,           // "⊩"
    metaor_key = 275,              // "or"
    metaand_key = 276,             // "and"
    metanot_key = 277,             // "not"
    infer_key = 278,               // "⊢"
    object_identical_key = 279,    // "≡"
    object_not_identical_key = 280, // "≢"
    meta_identical_key = 281,      // "≣"
    meta_not_identical_key = 282,  // "≣̷"
    fail_key = 283,                // "fail"
    succeed_key = 284,             // "succeed"
    free_for_key = 285,            // "free for"
    metain_key = 286,              // "in"
    free_in_key = 287,             // "free in"
    use_key = 288,                 // "use"
    defined_by_key = 289,          // "≔"
    defines_key = 290,             // "≕"
    defined_equal_key = 291,       // "≝"
    plain_name = 292,              // "name"
    label_key = 293,               // "label"
    metapredicate_constant = 294,  // "metapredicate constant"
    function_key = 295,            // "function"
    predicate_key = 296,           // "predicate"
    predicate_constant = 297,      // "predicate constant"
    atom_constant = 298,           // "atom constant"
    function_constant = 299,       // "function constant"
    term_constant = 300,           // "term constant"
    metaformula_variable = 301,    // "metaformula variable"
    object_formula_variable = 302, // "object formula variable"
    predicate_variable = 303,      // "predicate variable"
    atom_variable = 304,           // "atom variable"
    prefix_formula_variable = 305, // "prefix formula variable"
    function_variable = 306,       // "function variable"
    object_variable = 307,         // "object variable"
    code_variable = 308,           // "code variable"
    all_variable = 309,            // "all variable"
    exist_variable = 310,          // "exist variable"
    function_map_variable = 311,   // "function map variable"
    is_set_variable = 312,         // "Set variable"
    set_variable = 313,            // "set variable"
    set_variable_definition = 314, // "set variable definition"
    implicit_set_variable = 315,   // "implicit set variable"
    identifier_constant_key = 316, // "identifier constant"
    identifier_variable_key = 317, // "identifier variable"
    identifier_function_key = 318, // "identifier function"
    all_key = 319,                 // "∀"
    exist_key = 320,               // "∃"
    logical_not_key = 321,         // "¬"
    logical_and_key = 322,         // "∧"
    logical_or_key = 323,          // "∨"
    implies_key = 324,             // "⇒"
    impliedby_key = 325,           // "⇐"
    equivalent_key = 326,          // "⇔"
    prefix_not_key = 327,          // prefix_not_key
    prefix_and_key = 328,          // prefix_and_key
    prefix_or_key = 329,           // prefix_or_key
    prefix_implies_key = 330,      // prefix_implies_key
    prefix_equivalent_key = 331,   // prefix_equivalent_key
    less_key = 332,                // "<"
    greater_key = 333,             // ">"
    less_or_equal_key = 334,       // "≤"
    greater_or_equal_key = 335,    // "≥"
    not_less_key = 336,            // "≮"
    not_greater_key = 337,         // "≯"
    not_less_or_equal_key = 338,   // "≰"
    not_greater_or_equal_key = 339, // "≱"
    equal_key = 340,               // "="
    not_equal_key = 341,           // "≠"
    mapsto_key = 342,              // "↦"
    Mapsto_key = 343,              // "⤇"
    function_map_prefix_key = 344, // "𝛌"
    degree_key = 345,              // "°"
    bullet_key = 346,              // "•"
    subscript_x_key = 347,         // "ₓ"
    natural_number_value = 348,    // "natural number value"
    integer_value = 349,           // "integer value"
    subscript_natural_number_value = 350, // "subscript natural number value"
    subscript_integer_value = 351, // "subscript integer value"
    superscript_natural_number_value = 352, // "superscript natural number value"
    superscript_integer_value = 353, // "superscript integer value"
    factorial_key = 354,           // "!"
    mult_key = 355,                // "⋅"
    plus_key = 356,                // "+"
    minus_key = 357,               // "-"
    is_set_key = 358,              // "Set"
    power_set_key = 359,           // "Pow"
    empty_set_key = 360,           // "∅"
    in_key = 361,                  // "∈"
    not_in_key = 362,              // "∉"
    set_complement_key = 363,      // "∁"
    set_union_key = 364,           // "∪"
    set_intersection_key = 365,    // "∩"
    set_difference_key = 366,      // "∖"
    set_union_operator_key = 367,  // "⋃"
    set_intersection_operator_key = 368, // "⋂"
    subset_key = 369,              // "⊆"
    proper_subset_key = 370,       // "⊊"
    superset_key = 371,            // "⊇"
    proper_superset_key = 372,     // "⊋"
    colon_key = 373,               // ":"
    semicolon_key = 374,           // ";"
    comma_key = 375,               // ","
    period_key = 376,              // "."
    left_parenthesis_key = 377,    // "("
    right_parenthesis_key = 378,   // ")"
    left_bracket_key = 379,        // "["
    right_bracket_key = 380,       // "]"
    left_angle_bracket_key = 381,  // "⟨"
    right_angle_bracket_key = 382, // "⟩"
    superscript_left_parenthesis_key = 383, // "⁽"
    superscript_right_parenthesis_key = 384, // "⁾"
    subscript_left_parenthesis_key = 385, // "₍"
    subscript_right_parenthesis_key = 386, // "₎"
    left_brace_key = 387,          // "{"
    vertical_line_key = 388,       // "|"
    right_brace_key = 389,         // "}"
    tilde_key = 390,               // "~"
    slash_key = 391,               // "/"
    backslash_key = 392,           // "\\"
    if_key = 393,                  // "if"
    then_key = 394,                // "then"
    else_key = 395,                // "else"
    while_key = 396,               // "while"
    do_key = 397,                  // "do"
    loop_key = 398,                // "loop"
    for_key = 399,                 // "for"
    break_key = 400,               // "break"
    continue_key = 401,            // "continue"
    throw_key = 402,               // "throw"
    try_key = 403,                 // "try"
    catch_key = 404,               // "catch"
    unary_minus = 406              // unary_minus
      };
      /// Backward compatibility alias (Bison 3.6).
      typedef token_kind_type yytokentype;
    };

    /// Token kind, as returned by yylex.
    typedef token::yytokentype token_kind_type;

    /// Backward compatibility alias (Bison 3.6).
    typedef token_kind_type token_type;

    /// Symbol kinds.
    struct symbol_kind
    {
      enum symbol_kind_type
      {
        YYNTOKENS = 152, ///< Number of tokens.
        S_YYEMPTY = -2,
        S_YYEOF = 0,                             // "end of file"
        S_YYerror = 1,                           // error
        S_YYUNDEF = 2,                           // "invalid token"
        S_token_error = 3,                       // "token error"
        S_include_key = 4,                       // "include"
        S_theory_key = 5,                        // "theory"
        S_end_key = 6,                           // "end"
        S_formal_system_key = 7,                 // "formal system"
        S_definition_key = 8,                    // "definition"
        S_postulate_key = 9,                     // "postulate"
        S_axiom_key = 10,                        // "axiom"
        S_rule_key = 11,                         // "rule"
        S_conjecture_key = 12,                   // "conjecture"
        S_theorem_key = 13,                      // "theorem"
        S_proof_key = 14,                        // "proof"
        S_end_of_proof_key = 15,                 // "∎"
        S_by_key = 16,                           // "by"
        S_premise_key = 17,                      // "premise"
        S_result_key = 18,                       // "result"
        S_metainfer_key = 19,                    // "⊩"
        S_metaor_key = 20,                       // "or"
        S_metaand_key = 21,                      // "and"
        S_metanot_key = 22,                      // "not"
        S_infer_key = 23,                        // "⊢"
        S_object_identical_key = 24,             // "≡"
        S_object_not_identical_key = 25,         // "≢"
        S_meta_identical_key = 26,               // "≣"
        S_meta_not_identical_key = 27,           // "≣̷"
        S_fail_key = 28,                         // "fail"
        S_succeed_key = 29,                      // "succeed"
        S_free_for_key = 30,                     // "free for"
        S_metain_key = 31,                       // "in"
        S_free_in_key = 32,                      // "free in"
        S_use_key = 33,                          // "use"
        S_defined_by_key = 34,                   // "≔"
        S_defines_key = 35,                      // "≕"
        S_defined_equal_key = 36,                // "≝"
        S_plain_name = 37,                       // "name"
        S_label_key = 38,                        // "label"
        S_metapredicate_constant = 39,           // "metapredicate constant"
        S_function_key = 40,                     // "function"
        S_predicate_key = 41,                    // "predicate"
        S_predicate_constant = 42,               // "predicate constant"
        S_atom_constant = 43,                    // "atom constant"
        S_function_constant = 44,                // "function constant"
        S_term_constant = 45,                    // "term constant"
        S_metaformula_variable = 46,             // "metaformula variable"
        S_object_formula_variable = 47,          // "object formula variable"
        S_predicate_variable = 48,               // "predicate variable"
        S_atom_variable = 49,                    // "atom variable"
        S_prefix_formula_variable = 50,          // "prefix formula variable"
        S_function_variable = 51,                // "function variable"
        S_object_variable = 52,                  // "object variable"
        S_code_variable = 53,                    // "code variable"
        S_all_variable = 54,                     // "all variable"
        S_exist_variable = 55,                   // "exist variable"
        S_function_map_variable = 56,            // "function map variable"
        S_is_set_variable = 57,                  // "Set variable"
        S_set_variable = 58,                     // "set variable"
        S_set_variable_definition = 59,          // "set variable definition"
        S_implicit_set_variable = 60,            // "implicit set variable"
        S_identifier_constant_key = 61,          // "identifier constant"
        S_identifier_variable_key = 62,          // "identifier variable"
        S_identifier_function_key = 63,          // "identifier function"
        S_all_key = 64,                          // "∀"
        S_exist_key = 65,                        // "∃"
        S_logical_not_key = 66,                  // "¬"
        S_logical_and_key = 67,                  // "∧"
        S_logical_or_key = 68,                   // "∨"
        S_implies_key = 69,                      // "⇒"
        S_impliedby_key = 70,                    // "⇐"
        S_equivalent_key = 71,                   // "⇔"
        S_prefix_not_key = 72,                   // prefix_not_key
        S_prefix_and_key = 73,                   // prefix_and_key
        S_prefix_or_key = 74,                    // prefix_or_key
        S_prefix_implies_key = 75,               // prefix_implies_key
        S_prefix_equivalent_key = 76,            // prefix_equivalent_key
        S_less_key = 77,                         // "<"
        S_greater_key = 78,                      // ">"
        S_less_or_equal_key = 79,                // "≤"
        S_greater_or_equal_key = 80,             // "≥"
        S_not_less_key = 81,                     // "≮"
        S_not_greater_key = 82,                  // "≯"
        S_not_less_or_equal_key = 83,            // "≰"
        S_not_greater_or_equal_key = 84,         // "≱"
        S_equal_key = 85,                        // "="
        S_not_equal_key = 86,                    // "≠"
        S_mapsto_key = 87,                       // "↦"
        S_Mapsto_key = 88,                       // "⤇"
        S_function_map_prefix_key = 89,          // "𝛌"
        S_degree_key = 90,                       // "°"
        S_bullet_key = 91,                       // "•"
        S_subscript_x_key = 92,                  // "ₓ"
        S_natural_number_value = 93,             // "natural number value"
        S_integer_value = 94,                    // "integer value"
        S_subscript_natural_number_value = 95,   // "subscript natural number value"
        S_subscript_integer_value = 96,          // "subscript integer value"
        S_superscript_natural_number_value = 97, // "superscript natural number value"
        S_superscript_integer_value = 98,        // "superscript integer value"
        S_factorial_key = 99,                    // "!"
        S_mult_key = 100,                        // "⋅"
        S_plus_key = 101,                        // "+"
        S_minus_key = 102,                       // "-"
        S_is_set_key = 103,                      // "Set"
        S_power_set_key = 104,                   // "Pow"
        S_empty_set_key = 105,                   // "∅"
        S_in_key = 106,                          // "∈"
        S_not_in_key = 107,                      // "∉"
        S_set_complement_key = 108,              // "∁"
        S_set_union_key = 109,                   // "∪"
        S_set_intersection_key = 110,            // "∩"
        S_set_difference_key = 111,              // "∖"
        S_set_union_operator_key = 112,          // "⋃"
        S_set_intersection_operator_key = 113,   // "⋂"
        S_subset_key = 114,                      // "⊆"
        S_proper_subset_key = 115,               // "⊊"
        S_superset_key = 116,                    // "⊇"
        S_proper_superset_key = 117,             // "⊋"
        S_colon_key = 118,                       // ":"
        S_semicolon_key = 119,                   // ";"
        S_comma_key = 120,                       // ","
        S_period_key = 121,                      // "."
        S_left_parenthesis_key = 122,            // "("
        S_right_parenthesis_key = 123,           // ")"
        S_left_bracket_key = 124,                // "["
        S_right_bracket_key = 125,               // "]"
        S_left_angle_bracket_key = 126,          // "⟨"
        S_right_angle_bracket_key = 127,         // "⟩"
        S_superscript_left_parenthesis_key = 128, // "⁽"
        S_superscript_right_parenthesis_key = 129, // "⁾"
        S_subscript_left_parenthesis_key = 130,  // "₍"
        S_subscript_right_parenthesis_key = 131, // "₎"
        S_left_brace_key = 132,                  // "{"
        S_vertical_line_key = 133,               // "|"
        S_right_brace_key = 134,                 // "}"
        S_tilde_key = 135,                       // "~"
        S_slash_key = 136,                       // "/"
        S_backslash_key = 137,                   // "\\"
        S_if_key = 138,                          // "if"
        S_then_key = 139,                        // "then"
        S_else_key = 140,                        // "else"
        S_while_key = 141,                       // "while"
        S_do_key = 142,                          // "do"
        S_loop_key = 143,                        // "loop"
        S_for_key = 144,                         // "for"
        S_break_key = 145,                       // "break"
        S_continue_key = 146,                    // "continue"
        S_throw_key = 147,                       // "throw"
        S_try_key = 148,                         // "try"
        S_catch_key = 149,                       // "catch"
        S_150_ = 150,                            // "⊣"
        S_unary_minus = 151,                     // unary_minus
        S_YYACCEPT = 152,                        // $accept
        S_file = 153,                            // file
        S_file_contents = 154,                   // file_contents
        S_command = 155,                         // command
        S_156_1 = 156,                           // $@1
        S_metaformula_substitution_sequence = 157, // metaformula_substitution_sequence
        S_substitution_for_metaformula = 158,    // substitution_for_metaformula
        S_metaformula_substitution = 159,        // metaformula_substitution
        S_formula_substitution_sequence = 160,   // formula_substitution_sequence
        S_substitution_for_formula = 161,        // substitution_for_formula
        S_formula_substitution = 162,            // formula_substitution
        S_term_substitution_sequence = 163,      // term_substitution_sequence
        S_term_substitution = 164,               // term_substitution
        S_predicate_function_application = 165,  // predicate_function_application
        S_166_2 = 166,                           // $@2
        S_term_function_application = 167,       // term_function_application
        S_168_3 = 168,                           // $@3
        S_theory = 169,                          // theory
        S_170_4 = 170,                           // $@4
        S_end_theory_name = 171,                 // end_theory_name
        S_include_theories = 172,                // include_theories
        S_include_theory = 173,                  // include_theory
        S_theory_name = 174,                     // theory_name
        S_theory_body = 175,                     // theory_body
        S_formal_system = 176,                   // formal_system
        S_177_5 = 177,                           // $@5
        S_formal_system_body = 178,              // formal_system_body
        S_formal_system_body_item = 179,         // formal_system_body_item
        S_theory_body_list = 180,                // theory_body_list
        S_theory_body_item = 181,                // theory_body_item
        S_postulate = 182,                       // postulate
        S_183_6 = 183,                           // $@6
        S_184_7 = 184,                           // $@7
        S_185_8 = 185,                           // $@8
        S_conjecture = 186,                      // conjecture
        S_187_9 = 187,                           // $@9
        S_definition_labelstatement = 188,       // definition_labelstatement
        S_189_10 = 189,                          // $@10
        S_statement_name = 190,                  // statement_name
        S_theorem = 191,                         // theorem
        S_theorem_statement = 192,               // theorem_statement
        S_theorem_head = 193,                    // theorem_head
        S_proof = 194,                           // proof
        S_195_11 = 195,                          // $@11
        S_196_compound_proof = 196,              // compound-proof
        S_proof_head = 197,                      // proof_head
        S_proof_lines = 198,                     // proof_lines
        S_statement_label = 199,                 // statement_label
        S_proof_line = 200,                      // proof_line
        S_201_12 = 201,                          // $@12
        S_subproof = 202,                        // subproof
        S_subproof_statement = 203,              // subproof_statement
        S_proof_of_conclusion = 204,             // proof_of_conclusion
        S_205_optional_result = 205,             // optional-result
        S_find_statement = 206,                  // find_statement
        S_find_statement_list = 207,             // find_statement_list
        S_find_statement_sequence = 208,         // find_statement_sequence
        S_find_definition_sequence = 209,        // find_definition_sequence
        S_find_statement_item = 210,             // find_statement_item
        S_find_statement_name = 211,             // find_statement_name
        S_212_13 = 212,                          // @13
        S_statement = 213,                       // statement
        S_definition_statement = 214,            // definition_statement
        S_identifier_declaration = 215,          // identifier_declaration
        S_declarator_list = 216,                 // declarator_list
        S_declarator_identifier_list = 217,      // declarator_identifier_list
        S_identifier_function_list = 218,        // identifier_function_list
        S_identifier_function_name = 219,        // identifier_function_name
        S_220_14 = 220,                          // $@14
        S_221_15 = 221,                          // $@15
        S_identifier_constant_list = 222,        // identifier_constant_list
        S_identifier_constant_name = 223,        // identifier_constant_name
        S_identifier_variable_list = 224,        // identifier_variable_list
        S_identifier_variable_name = 225,        // identifier_variable_name
        S_definition = 226,                      // definition
        S_metaformula_definition = 227,          // metaformula_definition
        S_object_formula_definition = 228,       // object_formula_definition
        S_term_definition = 229,                 // term_definition
        S_metaformula = 230,                     // metaformula
        S_pure_metaformula = 231,                // pure_metaformula
        S_optional_varied_variable_matrix = 232, // optional_varied_variable_matrix
        S_varied_variable_conclusions = 233,     // varied_variable_conclusions
        S_varied_variable_conclusion = 234,      // varied_variable_conclusion
        S_varied_variable_premises = 235,        // varied_variable_premises
        S_varied_variable_premise = 236,         // varied_variable_premise
        S_varied_variable_set = 237,             // varied_variable_set
        S_varied_variable = 238,                 // varied_variable
        S_optional_varied_in_reduction_variable_matrix = 239, // optional_varied_in_reduction_variable_matrix
        S_varied_in_reduction_variable_conclusions = 240, // varied_in_reduction_variable_conclusions
        S_varied_in_reduction_variable_conclusion = 241, // varied_in_reduction_variable_conclusion
        S_varied_in_reduction_variable_premises = 242, // varied_in_reduction_variable_premises
        S_varied_in_reduction_variable_premise = 243, // varied_in_reduction_variable_premise
        S_varied_in_reduction_variable_set = 244, // varied_in_reduction_variable_set
        S_varied_in_reduction_variable = 245,    // varied_in_reduction_variable
        S_simple_metaformula = 246,              // simple_metaformula
        S_atomic_metaformula = 247,              // atomic_metaformula
        S_special_metaformula = 248,             // special_metaformula
        S_meta_object_free = 249,                // meta_object_free
        S_metapredicate = 250,                   // metapredicate
        S_metapredicate_function = 251,          // metapredicate_function
        S_metapredicate_argument = 252,          // metapredicate_argument
        S_metapredicate_argument_body = 253,     // metapredicate_argument_body
        S_object_formula = 254,                  // object_formula
        S_hoare_triple = 255,                    // hoare_triple
        S_code_statement = 256,                  // code_statement
        S_code_sequence = 257,                   // code_sequence
        S_code_term = 258,                       // code_term
        S_very_simple_formula = 259,             // very_simple_formula
        S_quantized_formula = 260,               // quantized_formula
        S_simple_formula = 261,                  // simple_formula
        S_quantized_body = 262,                  // quantized_body
        S_atomic_formula = 263,                  // atomic_formula
        S_predicate = 264,                       // predicate
        S_265_16 = 265,                          // $@16
        S_266_17 = 266,                          // $@17
        S_predicate_expression = 267,            // predicate_expression
        S_predicate_identifier = 268,            // predicate_identifier
        S_optional_superscript_natural_number_value = 269, // optional_superscript_natural_number_value
        S_logic_formula = 270,                   // logic_formula
        S_prefix_logic_formula = 271,            // prefix_logic_formula
        S_quantizer_declaration = 272,           // quantizer_declaration
        S_quantized_variable_list = 273,         // quantized_variable_list
        S_all_variable_list = 274,               // all_variable_list
        S_exist_variable_list = 275,             // exist_variable_list
        S_all_identifier_list = 276,             // all_identifier_list
        S_277_18 = 277,                          // $@18
        S_exist_identifier_list = 278,           // exist_identifier_list
        S_279_19 = 279,                          // $@19
        S_optional_in_term = 280,                // optional_in_term
        S_tuple = 281,                           // tuple
        S_tuple_body = 282,                      // tuple_body
        S_term = 283,                            // term
        S_simple_term = 284,                     // simple_term
        S_term_identifier = 285,                 // term_identifier
        S_variable_exclusion_set = 286,          // variable_exclusion_set
        S_variable_exclusion_list = 287,         // variable_exclusion_list
        S_bound_variable = 288,                  // bound_variable
        S_function_term = 289,                   // function_term
        S_set_term = 290,                        // set_term
        S_implicit_set_identifier_list = 291,    // implicit_set_identifier_list
        S_292_20 = 292,                          // $@20
        S_293_21 = 293,                          // $@21
        S_set_member_list = 294,                 // set_member_list
        S_function_term_identifier = 295         // function_term_identifier
      };
    };

    /// (Internal) symbol kind.
    typedef symbol_kind::symbol_kind_type symbol_kind_type;

    /// The number of tokens.
    static const symbol_kind_type YYNTOKENS = symbol_kind::YYNTOKENS;

    /// A complete symbol.
    ///
    /// Expects its Base type to provide access to the symbol kind
    /// via kind ().
    ///
    /// Provide access to semantic value and location.
    template <typename Base>
    struct basic_symbol : Base
    {
      /// Alias to Base.
      typedef Base super_type;

      /// Default constructor.
      basic_symbol ()
        : value ()
        , location ()
      {}

#if 201103L <= YY_CPLUSPLUS
      /// Move constructor.
      basic_symbol (basic_symbol&& that)
        : Base (std::move (that))
        , value (std::move (that.value))
        , location (std::move (that.location))
      {}
#endif

      /// Copy constructor.
      basic_symbol (const basic_symbol& that);
      /// Constructor for valueless symbols.
      basic_symbol (typename Base::kind_type t,
                    YY_MOVE_REF (location_type) l);

      /// Constructor for symbols with semantic value.
      basic_symbol (typename Base::kind_type t,
                    YY_RVREF (value_type) v,
                    YY_RVREF (location_type) l);

      /// Destroy the symbol.
      ~basic_symbol ()
      {
        clear ();
      }

      /// Destroy contents, and record that is empty.
      void clear () YY_NOEXCEPT
      {
        Base::clear ();
      }

      /// The user-facing name of this symbol.
      std::string name () const YY_NOEXCEPT
      {
        return database_parser::symbol_name (this->kind ());
      }

      /// Backward compatibility (Bison 3.6).
      symbol_kind_type type_get () const YY_NOEXCEPT;

      /// Whether empty.
      bool empty () const YY_NOEXCEPT;

      /// Destructive move, \a s is emptied into this.
      void move (basic_symbol& s);

      /// The semantic value.
      value_type value;

      /// The location.
      location_type location;

    private:
#if YY_CPLUSPLUS < 201103L
      /// Assignment operator.
      basic_symbol& operator= (const basic_symbol& that);
#endif
    };

    /// Type access provider for token (enum) based symbols.
    struct by_kind
    {
      /// Default constructor.
      by_kind ();

#if 201103L <= YY_CPLUSPLUS
      /// Move constructor.
      by_kind (by_kind&& that);
#endif

      /// Copy constructor.
      by_kind (const by_kind& that);

      /// The symbol kind as needed by the constructor.
      typedef token_kind_type kind_type;

      /// Constructor from (external) token numbers.
      by_kind (kind_type t);

      /// Record that this symbol is empty.
      void clear () YY_NOEXCEPT;

      /// Steal the symbol kind from \a that.
      void move (by_kind& that);

      /// The (internal) type number (corresponding to \a type).
      /// \a empty when empty.
      symbol_kind_type kind () const YY_NOEXCEPT;

      /// Backward compatibility (Bison 3.6).
      symbol_kind_type type_get () const YY_NOEXCEPT;

      /// The symbol kind.
      /// \a S_YYEMPTY when empty.
      symbol_kind_type kind_;
    };

    /// Backward compatibility for a private implementation detail (Bison 3.6).
    typedef by_kind by_type;

    /// "External" symbols: returned by the scanner.
    struct symbol_type : basic_symbol<by_kind>
    {};

    /// Build a parser object.
    database_parser (mli::theory_database& yypval_yyarg, mli::database_lexer& mlilex_yyarg);
    virtual ~database_parser ();

#if 201103L <= YY_CPLUSPLUS
    /// Non copyable.
    database_parser (const database_parser&) = delete;
    /// Non copyable.
    database_parser& operator= (const database_parser&) = delete;
#endif

    /// Parse.  An alias for parse ().
    /// \returns  0 iff parsing succeeded.
    int operator() ();

    /// Parse.
    /// \returns  0 iff parsing succeeded.
    virtual int parse ();

#if MLIDEBUG
    /// The current debugging stream.
    std::ostream& debug_stream () const YY_ATTRIBUTE_PURE;
    /// Set the current debugging stream.
    void set_debug_stream (std::ostream &);

    /// Type for debugging levels.
    typedef int debug_level_type;
    /// The current debugging level.
    debug_level_type debug_level () const YY_ATTRIBUTE_PURE;
    /// Set the current debugging level.
    void set_debug_level (debug_level_type l);
#endif

    /// Report a syntax error.
    /// \param loc    where the syntax error is found.
    /// \param msg    a description of the syntax error.
    virtual void error (const location_type& loc, const std::string& msg);

    /// Report a syntax error.
    void error (const syntax_error& err);

    /// The user-facing name of the symbol whose (internal) number is
    /// YYSYMBOL.  No bounds checking.
    static std::string symbol_name (symbol_kind_type yysymbol);



    class context
    {
    public:
      context (const database_parser& yyparser, const symbol_type& yyla);
      const symbol_type& lookahead () const YY_NOEXCEPT { return yyla_; }
      symbol_kind_type token () const YY_NOEXCEPT { return yyla_.kind (); }
      const location_type& location () const YY_NOEXCEPT { return yyla_.location; }

      /// Put in YYARG at most YYARGN of the expected tokens, and return the
      /// number of tokens stored in YYARG.  If YYARG is null, return the
      /// number of expected tokens (guaranteed to be less than YYNTOKENS).
      int expected_tokens (symbol_kind_type yyarg[], int yyargn) const;

    private:
      const database_parser& yyparser_;
      const symbol_type& yyla_;
    };

  private:
#if YY_CPLUSPLUS < 201103L
    /// Non copyable.
    database_parser (const database_parser&);
    /// Non copyable.
    database_parser& operator= (const database_parser&);
#endif

    /// Check the lookahead yytoken.
    /// \returns  true iff the token will be eventually shifted.
    bool yy_lac_check_ (symbol_kind_type yytoken) const;
    /// Establish the initial context if no initial context currently exists.
    /// \returns  true iff the token will be eventually shifted.
    bool yy_lac_establish_ (symbol_kind_type yytoken);
    /// Discard any previous initial lookahead context because of event.
    /// \param event  the event which caused the lookahead to be discarded.
    ///               Only used for debbuging output.
    void yy_lac_discard_ (const char* event);

    /// Stored state numbers (used for stacks).
    typedef short state_type;

    /// The arguments of the error message.
    int yy_syntax_error_arguments_ (const context& yyctx,
                                    symbol_kind_type yyarg[], int yyargn) const;

    /// Generate an error message.
    /// \param yyctx     the context in which the error occurred.
    virtual std::string yysyntax_error_ (const context& yyctx) const;
    /// Compute post-reduction state.
    /// \param yystate   the current state
    /// \param yysym     the nonterminal to push on the stack
    static state_type yy_lr_goto_state_ (state_type yystate, int yysym);

    /// Whether the given \c yypact_ value indicates a defaulted state.
    /// \param yyvalue   the value to check
    static bool yy_pact_value_is_default_ (int yyvalue);

    /// Whether the given \c yytable_ value indicates a syntax error.
    /// \param yyvalue   the value to check
    static bool yy_table_value_is_error_ (int yyvalue);

    static const short yypact_ninf_;
    static const short yytable_ninf_;

    /// Convert a scanner token kind \a t to a symbol kind.
    /// In theory \a t should be a token_kind_type, but character literals
    /// are valid, yet not members of the token_type enum.
    static symbol_kind_type yytranslate_ (int t);

    /// Convert the symbol name \a n to a form suitable for a diagnostic.
    static std::string yytnamerr_ (const char *yystr);

    /// For a symbol, its name in clear.
    static const char* const yytname_[];


    // Tables.
    // YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
    // STATE-NUM.
    static const short yypact_[];

    // YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
    // Performed when YYTABLE does not specify something else to do.  Zero
    // means the default is an error.
    static const short yydefact_[];

    // YYPGOTO[NTERM-NUM].
    static const short yypgoto_[];

    // YYDEFGOTO[NTERM-NUM].
    static const short yydefgoto_[];

    // YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
    // positive, shift that token.  If negative, reduce the rule whose
    // number is the opposite.  If YYTABLE_NINF, syntax error.
    static const short yytable_[];

    static const short yycheck_[];

    // YYSTOS[STATE-NUM] -- The symbol kind of the accessing symbol of
    // state STATE-NUM.
    static const short yystos_[];

    // YYR1[RULE-NUM] -- Symbol kind of the left-hand side of rule RULE-NUM.
    static const short yyr1_[];

    // YYR2[RULE-NUM] -- Number of symbols on the right-hand side of rule RULE-NUM.
    static const signed char yyr2_[];


#if MLIDEBUG
    // YYRLINE[YYN] -- Source line where rule number YYN was defined.
    static const short yyrline_[];
    /// Report on the debug stream that the rule \a r is going to be reduced.
    virtual void yy_reduce_print_ (int r) const;
    /// Print the state stack on the debug stream.
    virtual void yy_stack_print_ () const;

    /// Debugging level.
    int yydebug_;
    /// Debug stream.
    std::ostream* yycdebug_;

    /// \brief Display a symbol kind, value and location.
    /// \param yyo    The output stream.
    /// \param yysym  The symbol.
    template <typename Base>
    void yy_print_ (std::ostream& yyo, const basic_symbol<Base>& yysym) const;
#endif

    /// \brief Reclaim the memory associated to a symbol.
    /// \param yymsg     Why this token is reclaimed.
    ///                  If null, print nothing.
    /// \param yysym     The symbol.
    template <typename Base>
    void yy_destroy_ (const char* yymsg, basic_symbol<Base>& yysym) const;

  private:
    /// Type access provider for state based symbols.
    struct by_state
    {
      /// Default constructor.
      by_state () YY_NOEXCEPT;

      /// The symbol kind as needed by the constructor.
      typedef state_type kind_type;

      /// Constructor.
      by_state (kind_type s) YY_NOEXCEPT;

      /// Copy constructor.
      by_state (const by_state& that) YY_NOEXCEPT;

      /// Record that this symbol is empty.
      void clear () YY_NOEXCEPT;

      /// Steal the symbol kind from \a that.
      void move (by_state& that);

      /// The symbol kind (corresponding to \a state).
      /// \a symbol_kind::S_YYEMPTY when empty.
      symbol_kind_type kind () const YY_NOEXCEPT;

      /// The state number used to denote an empty symbol.
      /// We use the initial state, as it does not have a value.
      enum { empty_state = 0 };

      /// The state.
      /// \a empty when empty.
      state_type state;
    };

    /// "Internal" symbol: element of the stack.
    struct stack_symbol_type : basic_symbol<by_state>
    {
      /// Superclass.
      typedef basic_symbol<by_state> super_type;
      /// Construct an empty symbol.
      stack_symbol_type ();
      /// Move or copy construction.
      stack_symbol_type (YY_RVREF (stack_symbol_type) that);
      /// Steal the contents from \a sym to build this.
      stack_symbol_type (state_type s, YY_MOVE_REF (symbol_type) sym);
#if YY_CPLUSPLUS < 201103L
      /// Assignment, needed by push_back by some old implementations.
      /// Moves the contents of that.
      stack_symbol_type& operator= (stack_symbol_type& that);

      /// Assignment, needed by push_back by other implementations.
      /// Needed by some other old implementations.
      stack_symbol_type& operator= (const stack_symbol_type& that);
#endif
    };

    /// A stack with random access from its top.
    template <typename T, typename S = std::vector<T> >
    class stack
    {
    public:
      // Hide our reversed order.
      typedef typename S::iterator iterator;
      typedef typename S::const_iterator const_iterator;
      typedef typename S::size_type size_type;
      typedef typename std::ptrdiff_t index_type;

      stack (size_type n = 200)
        : seq_ (n)
      {}

#if 201103L <= YY_CPLUSPLUS
      /// Non copyable.
      stack (const stack&) = delete;
      /// Non copyable.
      stack& operator= (const stack&) = delete;
#endif

      /// Random access.
      ///
      /// Index 0 returns the topmost element.
      const T&
      operator[] (index_type i) const
      {
        return seq_[size_type (size () - 1 - i)];
      }

      /// Random access.
      ///
      /// Index 0 returns the topmost element.
      T&
      operator[] (index_type i)
      {
        return seq_[size_type (size () - 1 - i)];
      }

      /// Steal the contents of \a t.
      ///
      /// Close to move-semantics.
      void
      push (YY_MOVE_REF (T) t)
      {
        seq_.push_back (T ());
        operator[] (0).move (t);
      }

      /// Pop elements from the stack.
      void
      pop (std::ptrdiff_t n = 1) YY_NOEXCEPT
      {
        for (; 0 < n; --n)
          seq_.pop_back ();
      }

      /// Pop all elements from the stack.
      void
      clear () YY_NOEXCEPT
      {
        seq_.clear ();
      }

      /// Number of elements on the stack.
      index_type
      size () const YY_NOEXCEPT
      {
        return index_type (seq_.size ());
      }

      /// Iterator on top of the stack (going downwards).
      const_iterator
      begin () const YY_NOEXCEPT
      {
        return seq_.begin ();
      }

      /// Bottom of the stack.
      const_iterator
      end () const YY_NOEXCEPT
      {
        return seq_.end ();
      }

      /// Present a slice of the top of a stack.
      class slice
      {
      public:
        slice (const stack& stack, index_type range)
          : stack_ (stack)
          , range_ (range)
        {}

        const T&
        operator[] (index_type i) const
        {
          return stack_[range_ - i];
        }

      private:
        const stack& stack_;
        index_type range_;
      };

    private:
#if YY_CPLUSPLUS < 201103L
      /// Non copyable.
      stack (const stack&);
      /// Non copyable.
      stack& operator= (const stack&);
#endif
      /// The wrapped container.
      S seq_;
    };


    /// Stack type.
    typedef stack<stack_symbol_type> stack_type;

    /// The stack.
    stack_type yystack_;
    /// The stack for LAC.
    /// Logically, the yy_lac_stack's lifetime is confined to the function
    /// yy_lac_check_. We just store it as a member of this class to hold
    /// on to the memory and to avoid frequent reallocations.
    /// Since yy_lac_check_ is const, this member must be mutable.
    mutable std::vector<state_type> yylac_stack_;
    /// Whether an initial LAC context was established.
    bool yy_lac_established_;


    /// Push a new state on the stack.
    /// \param m    a debug message to display
    ///             if null, no trace is output.
    /// \param sym  the symbol
    /// \warning the contents of \a s.value is stolen.
    void yypush_ (const char* m, YY_MOVE_REF (stack_symbol_type) sym);

    /// Push a new look ahead token on the state on the stack.
    /// \param m    a debug message to display
    ///             if null, no trace is output.
    /// \param s    the state
    /// \param sym  the symbol (for its value and location).
    /// \warning the contents of \a sym.value is stolen.
    void yypush_ (const char* m, state_type s, YY_MOVE_REF (symbol_type) sym);

    /// Pop \a n symbols from the stack.
    void yypop_ (int n = 1);

    /// Constants.
    enum
    {
      yylast_ = 1741,     ///< Last index in yytable_.
      yynnts_ = 144,  ///< Number of nonterminal symbols.
      yyfinal_ = 6 ///< Termination state number.
    };


    // User arguments.
    mli::theory_database& yypval;
    mli::database_lexer& mlilex;

  };


#line 22 "../../mli-root/src/database-parser.yy"
} // mli
#line 1296 "../../mli-root/src/database-parser.hh"


// "%code provides" blocks.
#line 93 "../../mli-root/src/database-parser.yy"


  namespace mli {

    // Symbol table: Pushed & popped at lexical environment boundaries.
    // For statements (theorems, definitions), pushed before the symbol declarations
    // (after the label), and if there is a proof, popped where it ends:

    using symbol_table_t = mli::table_stack<std::string, std::pair<mli::database_parser::token_type, mli::ref<mli::unit>>>;

    extern symbol_table_t symbol_table;

    extern depth proof_depth;

    extern database_parser::token_type bound_variable_type;

    constexpr database_parser::token_type free_variable_context = database_parser::token_type(0);

    database_parser::token_type define_variable(semantic_type& yylval);

    extern kleenean unused_variable;

    int directive_read(std::istream& is, mli::location_type& loc);
    int directive_read(const std::string& str, mli::location_type&);

  } // namespace mli


#line 1329 "../../mli-root/src/database-parser.hh"


#endif // !YY_MLI_MLI_ROOT_SRC_DATABASE_PARSER_HH_INCLUDED
