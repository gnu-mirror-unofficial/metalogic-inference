/* Copyright (C) 2017 Hans Åberg.

   This file is part of MLI, MetaLogic Inference.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

%skeleton "lalr1.cc"                          /*  -*- C++ -*- */
%require "3.0.4"
%defines

%define api.namespace {mli}
%define parser_class_name {mli_parser}

%parse-param {parse_type& yypval} {mlilex_f& mlilex} {std::istream& isp}


%code requires {

  #include "MLI.hh"
  #include "database.hh"
  #include "basictype.hh"

  // #define YYERROR_VERBOSE 1

  #ifndef yyFlexLexer
  #define yyFlexLexer mliFlexLexer
  #endif

  #ifndef mliFlexLexer
  #include "FlexLexer.h"
  #endif


  struct mlilex_f {
    yyFlexLexer& lp;
    std::istream& isp;

    mlilex_f(yyFlexLexer& x, std::istream& is) : lp(x), isp(is) {}

    int operator()(mli::semantic_type* x) { return lp.yylex(*x); }
  };

  namespace mli {

    typedef mli::theory_database parse_type;

    class semantic_type {
    public:
      long number_;
      std::string text_;
      mli::ref<mli::object> object_;

      semantic_type() : number_(0) {}
    };

    #define YYSTYPE mli::semantic_type

  } // namespace mli

} // %code requires


%code {

// #define YYDEBUG 1


  /* MetaLogic Inference Parser. */

#include <algorithm>
#include <fstream>
#include <iostream>
#include <iterator>
#include <map>
#include <sstream>
#include <stack>
#include <vector>
#include <utility>

//#include <algobase.h>

//#include "parser.hh"


#include "database.hh"
#include "definition.hh"
#include "proposition.hh"
#include "substitution.hh"
#include "metacondition.hh"

#include "precedence.hh"


namespace mli {
  void help(std::ostream&);
} // namespace mli

extern bool declaration_context;
extern bool binder_declaration_context;
extern bool maybe_set_declaration_context;
extern bool proofline_database_context;
extern int bracket_depth;

extern int declared_token;
extern int declared_type;

extern std::set<std::string> clp_parser_variables;
extern mli::table_stack<std::string, std::pair<int, mli::ref<mli::object> > > mli_table_stack_;
#define table_stack_insert(text_, token_, object_) \
  mli_table_stack_.insert(text_, std::pair<int, ref<object> >(token_, object_))
#define table_stack_insert_below(text_, token_, object_) \
  mli_table_stack_.insert_below(text_, std::pair<int, ref<object> >(token_, object_))

using namespace mli;

std::set<ref<variable> > labelstatement_variables_;

ref<theory> theory_;  // Theory to enter propositions into.
ref<database> theorem_theory_;  // Theory used for a theorem proof.

  // Stacks to handle nested statements and their proofs:
std::stack<ref<labelstatement> > labelstatement_stack_; // Pushed & popped at statement boundaries.
  // Pushed & popped at proof boundaries:
mli::table_stack<std::string, ref<labelstatement> > proofline_stack_;
std::stack<bool> has_labelstatement_stack_;

depth proof_depth = 0; // Inc-/de-cremented at (sub)theorem & proof boundaries.

mli::mli_parser::token_type to_token(variable::type t) {
  switch (t) {
    case variable::metaformula_:   return mli::mli_parser::token::metaformula_variable;
    case variable::formula_:       return mli::mli_parser::token::object_formula_variable;
    case variable::predicate_:     return mli::mli_parser::token::predicate_variable;
    case variable::atom_:          return mli::mli_parser::token::atom_variable;
    case variable::term_:          return mli::mli_parser::token::term_variable;
    case variable::function_:      return mli::mli_parser::token::function_variable;
    case variable::constant_:      return mli::mli_parser::token::constant_variable;
    case variable::metaobject_:    return mli::mli_parser::token::metaobjectvariable;
    case variable::object_:        return mli::mli_parser::token::object_variable;
    default:                       return mli::mli_parser::token::token_error;
  }
}

} // %code


%token token_error "token error"

%token level_max_key "level_max"
%token sublevel_max_key "sublevel_max"
%token unify_count_max_key "unify_count_max"

%token goal_key "goal"
%token unification_key "unification"
%token substitution_key "substitution"
%token type_key "type"

%token if_key ":-"
%token cut_key "!"

%token solve_key "solve"
%token verify_key "verify"

%token include_key "include"
%token theory_key "theory"
%token end_key "end"

%token formal_system_key "formal system"

%token definition_key "definition"

%token postulate_key "postulate"
%token axiom_key "axiom"
%token rule_key "rule"
%token conjecture_key "conjecture"

%token theorem_key "theorem"
%token proof_key "proof"
%token claim_key "claim"
%token premise_key "premise"
%token by_key "by"
%token conclusion_key "conclusion"
%token proof_complete_key "∎"

/* Metalogic symbols: */
%token infer_key "⊢"
%token infered_by_key "⊣"

%token object_identical_key "≡"
%token object_not_identical_key "≢"
%token meta_identical_key "≣"
%token meta_not_identical_key "≣̷"

%token fail_key "fail"
%token succeed_key "succeed"

/* Metalogic */
%token free_for_key "free for"
%token metain_key "in"
%token free_in_key "free in"
%token use_key "use"
%token meta_not_key "not"

%token defined_by_key "≔"
%token defines_key "≕"
%token defined_equal_key "≝"

/* Sub-/super-script */
%token subscript_key "↓"
%token superscript_key "↑"

/* Identifiers & labels: */
%token plain_name "name"
%token maybe_name "name or object"
%token label_key "label"

/* Metaconstants: */
%token metapredicate_constant "metapredicate constant"

/* Logic (object, non-term) constants: */
%token predicate_constant "predicate constant"
%token atom_constant "atom constant"

/* Terms constants: */
%token function_constant "function constant"
%token term_constant "term constant"

/* Metavariables: */

%token metaformula_variable "metaformula variable"
%token object_formula_variable "object formula variable"
%token predicate_variable "predicate variable"
%token atom_variable "atom variable"

%token term_variable "term variable"
%token metaobjectvariable "metaobjectvariable"
%token function_variable "function variable"
%token constant_variable "constant variable"

/* Object variables: */

%token object_variable "object variable"

%token all_variable "all variable"
%token exist_variable "exist variable"
%token is_set_variable "Set variable"
%token set_variable "set variable"
%token implicit_set_variable "implicit set variable"

/* Declarators: constants and variables. */
  /* Generic tokens, returned for any idenitified constant or variable.
     The exact type is then sorted out by the token type stored lookup table,
     and returned in the semantic value. */
%token identifier_constant_key "identifier constant"
%token identifier_variable_key "identifier variable"
  /* Keys for labeling identifiers constant or variable.
%token constant_key "constant"
%token variable_key "variable"
*/

/* Declarators: quantifiers. */
%token all_key "∀"
%token exist_key "∃"

/* Formula logic: */
%token not_key "¬"
%token and_key "∧"
%token or_key "∨"
%token implies_key "⇒"
%token impliedby_key "⇐"
%token equivalent_key "⇔"

%token substitution_begin_key "~["
%token substitution_end_key "~]"   /* Must be here because of a bug in Bison 1.75 */

/* Formula functions: */

%token equal_key "="
%token not_equal_key "≠"

%token unsigned_integer_value
%token signed_integer_value
%token list_concat "++"
%token mult_key "*"
%token plus_key "+"
%token minus_key "-"

/* Set theory: */
%token is_set_key "Set"
%token in_key "∈"
%token subset_key "⊂"
%token proper_subset_key "⊊"


/* Miscellaneous symbols: */

%token colon_key ":"
%token semicolon_key ";"
%token comma_key ","
%token period_key "."

%token left_parenthesis_key "("
%token right_parenthesis_key ")"
%token left_bracket_key "["
%token right_bracket_key "]"
%token left_angle_bracket_key "⟨"
%token right_angle_bracket_key "⟩"

%token left_brace_key "{"
%token vertical_line_key "|"
%token right_brace_key "}"

%token tilde_key "~"

%token slash_key "/"
%token backslash_key "\\"


/* Precedence rules: Lower to higher; values used for writing.
   Sign negative <-> non-associative. */

  /* Metalogic. */
%nonassoc "⊣" "⊢"
%left ":"
%left "|"
%left ";"
%left ","
%right "~"

%nonassoc "free in" "free for" "in"
%right "not"

%nonassoc "≔" "≕" "≝"

%nonassoc "≡" "≢" "≣" "≣̷"

%right unary_quantifier

%left "⇔"
%nonassoc "⇒" "⇐"

%left "∨"
%left "∧"
%right "¬"

%nonassoc "∈"
%nonassoc "⊂"
%nonassoc "⊊"

%nonassoc "="
%nonassoc "≠"

%left "++"
%left "+" "-"
%left "*" "/"
%right unary_minus

%%
file:
    file_contents {}
  |               {}
  | error {
      declaration_context = false;
      binder_declaration_context = false;
      YYABORT;
    }
;

file_contents:
    file_contents command {}
  | command               {}
;

command:
    level_max_key unsigned_integer_value "." {
      level_max = cast_reference<integer>($2.object_).get_ui();
    }
  | sublevel_max_key unsigned_integer_value "." {
      sublevel_max = cast_reference<integer>($2.object_).get_ui();
    }
  | unify_count_max_key unsigned_integer_value "." {
      unify_count_max = cast_reference<integer>($2.object_).get_ui();
    }
  | { mli_table_stack_.clear(); } theory {}
;

declared_formula:
    metaformula { $$.object_ = ref<object>(ref<formula>($1.object_)->set_bind()); }
  | identifier_declaration metaformula {
      $$.object_ = ref<object>(ref<formula>($2.object_)->set_bind());
    }
;

metaformula_substitution_sequence:
    substitution_for_metaformula { $$.object_ = $1.object_; }
  | metaformula_substitution_sequence substitution_for_metaformula {
      $$.object_ = ref<object>(ref<substitution>($2.object_) + ref<substitution>($1.object_));
    }
;

substitution_for_metaformula:
    metaformula_substitution { $$.object_ = $1.object_; }
  | formula_substitution { $$.object_ = $1.object_; }
  | term_substitution { $$.object_ = $1.object_; }
;


metaformula_substitution:
    "[" metaformula_variable "." metaformula "]" {
      ref<variable> v($2.object_);
      ref<formula> f($4.object_);
      $$.object_ = ref<object>(explicit_free_occurrences_substitution(v, f));
    }
;

formula_substitution_sequence:
    substitution_for_formula { $$.object_ = $1.object_; }
  | formula_substitution_sequence substitution_for_formula {
      $$.object_ = ref<object>(ref<substitution>($2.object_) + ref<substitution>($1.object_));
    }
;

substitution_for_formula:
    formula_substitution { $$.object_ = $1.object_; }
  | term_substitution { $$.object_ = $1.object_; }
;

formula_substitution:
    "[" object_formula_variable "." object_formula "]" {
      ref<variable> v($2.object_);
      ref<formula> f($4.object_);
      $$.object_ = ref<object>(explicit_free_occurrences_substitution(v, f));
    }
  | "[" predicate_variable "." predicate "]" {
      ref<variable> v($2.object_);
      ref<formula> f($4.object_);
      $$.object_ = ref<object>(explicit_free_occurrences_substitution(v, f));
    }
  | "[" atom_variable "." atom_constant "]" {
      ref<variable> v($2.object_);
      ref<formula> f($4.object_);
      $$.object_ = ref<object>(explicit_free_occurrences_substitution(v, f));
    }
;

term_substitution_sequence:
    term_substitution { $$.object_ = $1.object_; }
  | term_substitution_sequence term_substitution {
      $$.object_ = ref<object>(ref<substitution>($2.object_) + ref<substitution>($1.object_));
    }
;

term_substitution:
    "[" term_identifier "." term "]" {
      ref<variable> v($2.object_);
      ref<formula> f($4.object_);
      $$.object_ = ref<object>(explicit_free_occurrences_substitution(v, f));
    }
;

theory:
    "theory" statement_name
    "." { theory_ = new theory($2.text_);
          yypval.insert(theory_);
          mli_table_stack_.push_level(); }
    include_theory
    theory_body
    "end" "theory" statement_name "." {
      if ($2.text_ != $9.text_) {
        std::cerr << "Name mismatch, theory " << $2.text_
          << ", end theory " << $9.text_ << "." << std::endl;
        YYERROR;
      }
      mli_table_stack_.pop_level(); }
;

include_theory:
    /* empty */ {}
  | "include" "theory" theory_name "." {}
;

theory_name:
    "name" {
      maybe<ref<theory> > th = yypval.find($1.text_);
      if (!th) {
        mli::mli_parser::error("Include theory " + $1.text_ + " not found.");
        YYERROR;
      }
      theory_->insert(*th);
    }
;

theory_body:
    theory_body_list {}
  | formal_system theory_body_list {}
;

formal_system:
    "formal system" "."
    { mli_table_stack_.push_level(); }
    formal_system_body
    "end" "formal system" "." { mli_table_stack_.pop_level(); }
;

formal_system_body:
      {}
  | formal_system_body formal_system_body_item {}
;

formal_system_body_item:
    identifier_declaration {}
  | postulate { theory_->insert(ref<labelstatement>($1.object_)); }
  | definition_labelstatement { theory_->insert(ref<labelstatement>($1.object_)); }
;

theory_body_list:
    {}
  | theory_body_list theory_body_item {}
;

/* Postulates are not included here, as metatheorems such as the
   deduction theorem cannot then be localized to the same namespace:
   Such metatheorems are only true with respect to a fixed set of
   postulates, so if more postualtes are added after the metatheorem,
   it becomes not true with respect to all postulates in the theory. */
theory_body_item:
    theorem { theory_->insert(ref<labelstatement>($1.object_)); }
  | identifier_declaration {}
  | definition_labelstatement { theory_->insert(ref<labelstatement>($1.object_)); }
;

postulate:
    "postulate" statement_name
    "." { mli_table_stack_.push_level(); }
    statement "." {
      mli_table_stack_.pop_level();
      inference& cl = cast_reference<inference>($5.object_);
      $$.object_ = new supposition(supposition::postulate_, $2.text_, cl, true);
    }
  | "axiom" statement_name
    "." { mli_table_stack_.push_level(); }
    statement "." {
      mli_table_stack_.pop_level();
      inference& cl = cast_reference<inference>($5.object_);
      if (!cl.body_.is_null()) {
        mli::mli_parser::error("Axiom with non-empty body.");
        YYERROR;
      }
      $$.object_ = new supposition(supposition::postulate_, $2.text_, cl);
    }
  | "rule" statement_name
    "." { mli_table_stack_.push_level(); }
    statement "." {
      mli_table_stack_.pop_level();
      inference& cl = cast_reference<inference>($5.object_);
      if (cl.body_.is_null()) {
        mli::mli_parser::error("Rule with empty body.");
        YYERROR;
      }
      $$.object_ = new supposition(supposition::postulate_, $2.text_, cl);
    }
;

definition_labelstatement:
    "definition" statement_name
    "." { mli_table_stack_.push_level(); }
    definition_statement "." {
      mli_table_stack_.pop_level();
      definition& d = cast_reference<definition>($5.object_);
      $$.object_ = new named_definition($2.text_, d);
    }
;

statement_name:
    "name" { $$.text_ = $1.text_; }
  | "label" { $$.text_ = $1.text_; }
  | unsigned_integer_value { $$.text_ = $1.text_; }
;

theorem:
    theorem_statement proof {
      $$.object_ = ref<object>(labelstatement_stack_.top());
      ref<labelstatement> t($$.object_); // The theorem.
      t->prove();     // Attempt to prove the theorem.
      mli_table_stack_.pop_level();
      labelstatement_stack_.pop();
    }
;

theorem_statement:
    theorem_head statement "." {
      inference& inf = cast_reference<inference>($2.object_);
      std::map<std::string, std::pair<int, ref<object> > >& top = mli_table_stack_.top();
      theorem* tp = new theorem(
        theorem::type($1.number_), $1.text_, inf, theory_, proof_depth);
      labelstatement_stack_.top() = tp;
      theorem_theory_ = tp->get_theory();
    }
;

theorem_head:
    "theorem" statement_name "." {
      $$.text_ = $2.text_;
      $$.number_ = $1.number_;
      mli_table_stack_.push_level();
      labelstatement_stack_.push(ref<labelstatement>());
    }
;

proof:
    proof_head proof_lines proof_of_conclusion "∎" {
      --proof_depth;
      mli_table_stack_.pop_level();
      proofline_stack_.pop_level();
      has_labelstatement_stack_.pop(); }
;

proof_head:
    "proof" "." {
      ++proof_depth;
      mli_table_stack_.push_level();
      proofline_stack_.push_level();
      has_labelstatement_stack_.push(false);
    }
;

proof_lines:
    {}
  | proof_lines proof_line {}
;

proof_line:
    proof_line_head declared_formula "by" find_statement "." {
      proofline_database_context = false;
      theorem& t = cast_reference<theorem>(labelstatement_stack_.top());
      if (ref<formula>(t.head()) == ref<formula>($2.object_)) {
        if (has_labelstatement_stack_.top()) {
          mli::mli_parser::error("Duplicate proof statement line.");
          YYERROR;
        } else  has_labelstatement_stack_.top() = true;
      }
      if (!has_labelstatement_stack_.top() && $1.text_ == "conclusion") {
        mli::mli_parser::error("Proof line name `conclusion' used when not the theorem conclusion.");
        YYERROR;
      }
      std::map<std::string, std::pair<int, ref<object> > >& top = mli_table_stack_.top();
      ref<labelstatement> proof_line =
        t.push_back(
          $1.text_, ref<formula>($2.object_), ref<database>($4.object_),
          has_labelstatement_stack_.top(), proof_depth);
      mli_table_stack_.pop_level();
      if (!proofline_stack_.insert($1.text_, proof_line)) {
        if ($1.text_.empty())
          mli::mli_parser::error("Proof line name `' used.");
        else
          mli::mli_parser::error("Proof line name " + $1.text_  + " already given to a proof line.");
        YYERROR;
      }
    }
  | subproof {
      theorem& t = cast_reference<theorem>(labelstatement_stack_.top());
      ref<labelstatement> proof_line = t.push_back(ref<labelstatement>($1.object_));
      if (!proofline_stack_.insert($1.text_, proof_line)) {
        if ($1.text_.empty())
          mli::mli_parser::error("Proof line name `' used.");
        else
          mli::mli_parser::error("Proof line name " + $1.text_  + " already given to a proof line.");
        YYERROR;
      }
    }
  | identifier_declaration {}
  | definition_labelstatement {
      theorem& t = cast_reference<theorem>(labelstatement_stack_.top());
      ref<labelstatement> proof_line = t.push_back(ref<labelstatement>($1.object_));
      if (!proofline_stack_.insert($1.text_, proof_line)) {
        if ($1.text_.empty())
          mli::mli_parser::error("Proof line name `' used.");
        else
          mli::mli_parser::error("Proof line name " + $1.text_  + " already given to a proof line.");
        YYERROR;
      }
    }
;

subproof:
    subproof_statement "." proof {
      $$.text_ = $1.text_;
      $$.object_ = ref<object>(labelstatement_stack_.top());
      mli_table_stack_.pop_level();
      labelstatement_stack_.pop();
    }
;

subproof_statement:
    subproof_head statement {
      $$.text_ = $1.text_;
      inference& inf = cast_reference<inference>($2.object_);
      std::map<std::string, std::pair<int, ref<object> > >& top = mli_table_stack_.top();
      theorem* tp = new theorem(theorem::claim_, $1.text_, inf, theory_, proof_depth);
      labelstatement_stack_.top() = tp;
    }
;

subproof_head:
    "claim" statement_name "." {
      $$.text_ = $2.text_;
      $$.number_ = $1.number_;
      mli_table_stack_.push_level();
      labelstatement_stack_.push(ref<labelstatement>());
    }
;

proof_line_head:
  statement_name "." {
    $$.text_ = $1.text_;
    mli_table_stack_.push_level();
  }
;

proof_of_conclusion:
    "conclusion" "by" find_statement "." {
      proofline_database_context = false;
      if (has_labelstatement_stack_.top()) {
        mli::mli_parser::error("Duplicate proof conclusion line.");
        YYERROR;
      }
      theorem& t = cast_reference<theorem>(labelstatement_stack_.top());
      ref<labelstatement> proof_line =
        t.push_back($1.text_, t.head(), ref<database>($3.object_), true, proof_depth);
      if (!proofline_stack_.insert($1.text_, proof_line)) {
        mli::mli_parser::error("Proof conclusion line not inserted as the name `conclusion' already given to a proof line.");
        YYERROR;
      }
    }
;

find_statement:
    find_statement_list { $$.object_ = $1.object_; }
  | find_statement ";" find_statement {
      $$.object_ = 
        new leveled_database(ref<database>($1.object_), ref<database>($3.object_));
    }
;

find_statement_list:
    find_statement_item {
      $$.object_ = $1.object_; }
  | find_statement_list "," find_statement_item {
      $$.object_ = ref<object>(ref<database>($1.object_) + ref<database>($3.object_));
    }
;

find_statement_item:
    find_statement_name {
      ref<database> d(new sequential_database());
      d->insert(ref<labelstatement>($1.object_));
      $$.object_ = ref<object>(d);
    }
  | "premise" {
      database* dp = new sequential_database();
      ref<database> d(dp);
      dp->insert(new premise(labelstatement_stack_.top()));
      $$.object_ = ref<object>(d);
    }
;

find_statement_name:
    statement_name {
      // Accept also non-proved statements (as actual proving will come later):
      maybe<ref<labelstatement> > st;
      st = proofline_stack_.find($1.text_);
      if (!st)  st = theorem_theory_->find($1.text_, 0, false);
      if (!st) {
        mli::mli_parser::error("statement name " + $1.text_
          + " not found earlier in proof, in premises or theory.");
        YYERROR;
      }
      $$.object_ = ref<object>(*st);
    }
  | statement_name {
      // Accept also non-proved statements (as actual proving will come later):
      maybe<ref<labelstatement> > st;
      st = proofline_stack_.find($1.text_);
      if (!st)  st = theorem_theory_->find($1.text_, 0, false);
      if (!st) {
        mli::mli_parser::error("statement name " + $1.text_
          + " not found earlier in proof, in premises or theory.");
        YYERROR;
      }
      $$.object_ = ref<object>(*st);
      // Find the variables of *st and record them for use in the substitution domain checks:
      labelstatement* pp = (labelstatement*)(*st); 
      labelstatement_variables_.clear();
      pp->declared(labelstatement_variables_);
      // Then push the declared *st variables & constants onto mli_table_stack_
      // making them usable in substitution codomains:
      mli_table_stack_.push_level();
      std::set<ref<variable> >::iterator i, i0 = labelstatement_variables_.begin(),
        i1 = labelstatement_variables_.end();
      for (i = i0; i != i1; ++i) {
        const variable* vp = (const variable*)(*i);
        // Insert correct declared_token value:
        table_stack_insert(vp->name, to_token(vp->type_), ref<object>(*i));
      }
    }
    metaformula_substitution_sequence {
      // The try-catch checks whether the labelstatement-substitution is legal:
      ref<labelstatement> p($2.object_);
      ref<substitution> s($3.object_);
      try {
        $$.object_ = new labelstatement_substitution(p, s);
      } catch (substitute_error&) {
        mli::mli_parser::error("Proposition substitute error.");
        p->write(std::cerr,
          write_style(write_name | write_type | write_statement));
        std::cerr << "\n  " << s << std::endl;
        YYERROR;        
      }
      mli_table_stack_.pop_level();
    }
;

statement:
    statement_body { $$.object_ = ref<object>(ref<formula>($1.object_)->set_bind()); }
  | identifier_declaration statement_body {
      $$.object_ = ref<object>(ref<formula>($2.object_)->set_bind());
    }
;

definition_statement:
    definition { $$.object_ = ref<object>(ref<formula>($1.object_)->set_bind()); }
  | identifier_declaration definition {
      $$.object_ = ref<object>(ref<formula>($2.object_)->set_bind());
    }
;

identifier_declaration:
    declarator_list "." {}
;

declarator_list:
    declarator_identifier_list {}
  | declarator_list declarator_identifier_list {}
;

declarator_identifier_list: /* Declarator followed by an identifier list. */
    identifier_constant_key identifier_constant_list {}
  | identifier_variable_key identifier_variable_list {}
;

identifier_constant_list:
    "name" {
      table_stack_insert_below($1.text_, declared_token,
        new constant($1.text_, formula_type(declared_type))); }
  | identifier_constant_list "," "name" {
      table_stack_insert_below($3.text_, declared_token, 
        new constant($3.text_, formula_type(declared_type))); }
;

identifier_variable_list:
    "name" {
       table_stack_insert($1.text_, declared_token, 
         new variable($1.text_, variable::type(declared_type), proof_depth)); }
  | identifier_variable_list "," "name"
      { table_stack_insert($3.text_, declared_token,
          new variable($3.text_, variable::type(declared_type), proof_depth)); }
;

statement_body:
    metaformula {
      inference* ip = cast_pointer<inference>($1.object_);
      if (ip != 0)
        $$.object_ = $1.object_;
      else
        $$.object_ = new inference(ref<formula>($1.object_));
    }
;

definition:
    metaformula_definition { $$.object_ = $1.object_; }
  | object_formula_definition { $$.object_ = $1.object_; }
  | term_definition { $$.object_ = $1.object_; }
;

metaformula_definition:
    pure_metaformula "≔" pure_metaformula {
      $$.object_ = new definition(ref<formula>($1.object_), ref<formula>($3.object_), ref<formula>(),
        object_formula_type_, formula_definition_oprec); }
  | pure_metaformula "≕" pure_metaformula {
      $$.object_ = new definition(ref<formula>($3.object_), ref<formula>($1.object_), ref<formula>(),
        object_formula_type_, formula_definition_oprec); }
/*
  | metaformula "⊢" metaformula "≔" metaformula {
      $$.object_ = new definition(ref<formula>($3.object_), ref<formula>($5.object_), ref<formula>($1.object_),
        object_formula_type_, formula_definition_oprec); }
*/
;

object_formula_definition:
    object_formula "≔" object_formula {
      $$.object_ = new definition(ref<formula>($1.object_), ref<formula>($3.object_), ref<formula>(),
        object_formula_type_, formula_definition_oprec); }
  | object_formula "≕" object_formula {
      $$.object_ = new definition(ref<formula>($3.object_), ref<formula>($1.object_), ref<formula>(),
        object_formula_type_, formula_definition_oprec); }
/*
  | metaformula "⊢" object_formula "≔" object_formula {
      $$.object_ = new definition(ref<formula>($3.object_), ref<formula>($5.object_), ref<formula>($1.object_),
        object_formula_type_, formula_definition_oprec); }
*/
;

term_definition:
    term "≔" term {
      $$.object_ = new definition(ref<formula>($1.object_), ref<formula>($3.object_), ref<formula>(),
        term_type_, term_definition_oprec); }
  | metaformula "⊢" term "≔" term {
      $$.object_ = new definition(ref<formula>($3.object_), ref<formula>($5.object_), ref<formula>($1.object_),
        term_type_, term_definition_oprec); }
  | term "≕" term {
      $$.object_ = new definition(ref<formula>($3.object_), ref<formula>($1.object_), ref<formula>(),
        term_type_, term_definition_oprec); }
;

metaformula:
    pure_metaformula { $$.object_ = $1.object_; }
  | object_formula { $$.object_ = $1.object_; }
;

pure_metaformula:
    atomic_metaformula { $$.object_ = $1.object_; }
  | special_metaformula { $$.object_ = $1.object_; }
  | "~" metaformula {
      $$.object_ = ref<object>(new metanot(ref<formula>($2.object_)));
    }
  | metaformula "," metaformula {
      $$.object_ = ref<object>(
        mli::concatenate(ref<formula>($1.object_), ref<formula>($3.object_), metaand_));
    }
  | metaformula "|" metaformula {
      $$.object_ = ref<object>(
        mli::concatenate(ref<formula>($1.object_), ref<formula>($3.object_), metaor_));
    }
  | metaformula "⊢" metaformula {
      $$.object_ =
        new inference(ref<formula>($3.object_), ref<formula>($1.object_), inference::infer_);
    }
  | metaformula "⊣" metaformula {
      $$.object_ =
        new inference(ref<formula>($1.object_), ref<formula>($3.object_), inference::infered_by_);
    }
  | "⊢" metaformula { $$.object_ = new inference(ref<formula>($2.object_)); }
  | metaformula "⊣" { $$.object_ = new inference(ref<formula>($1.object_)); }
  | "(" pure_metaformula ")" { $$.object_ = $2.object_; }
  | simple_metaformula metaformula_substitution_sequence {
      $$.object_ = new substitution_formula(ref<substitution>($2.object_), ref<formula>($1.object_)); }
;

simple_metaformula:
    metaformula_variable { $$.object_ = $1.object_; }
  | "(" pure_metaformula ")" { $$.object_ = $2.object_; }
;

atomic_metaformula:
    metaformula_variable { $$.object_ = $1.object_; }
  | metapredicate { $$.object_ = $1.object_; }
;

special_metaformula:
    "fail" { $$.object_ = new succeed_fail(false); }
  | "succeed" { $$.object_ = new succeed_fail(true); }
  | meta_object_free "≡" meta_object_free {
      $$.object_ = new objectidentical(ref<variable>($1.object_), ref<variable>($3.object_), true);
    }
  | meta_object_free "≢" meta_object_free {
      $$.object_ = new objectidentical(ref<variable>($1.object_), ref<variable>($3.object_), false);
    }
  | meta_object_free "free in" object_formula {
      $$.object_ = new free_in_object(ref<variable>($1.object_), ref<formula>($3.object_), true);
    }
  | meta_object_free "free in" term {
      $$.object_ = new free_in_object(ref<variable>($1.object_), ref<formula>($3.object_), true);
    }
  | meta_object_free "not" "free in" object_formula {
      $$.object_ = new free_in_object(ref<variable>($1.object_), ref<formula>($4.object_), false);
    }
  | meta_object_free "not" "free in" term {
      $$.object_ = new free_in_object(ref<variable>($1.object_), ref<formula>($4.object_), false);
    }
  | term "free for" meta_object_free "in" object_formula {
      $$.object_ = new free_for_object(
        ref<formula>($1.object_), ref<variable>($3.object_), ref<formula>($5.object_), true);
    }
  | term "free for" meta_object_free "in" term {
      $$.object_ = new free_for_object(
        ref<formula>($1.object_), ref<variable>($3.object_), ref<formula>($5.object_), true);
    }
;

meta_object_free:
    metaobjectvariable { $$.object_ = $1.object_; }
  | object_variable { $$.object_ = $1.object_; }
;

metapredicate:
    metapredicate_function { $$.object_ = $1.object_; }
  | object_formula "≣" object_formula {
      $$.object_ = new identical(ref<formula>($1.object_), ref<formula>($3.object_), true);
    }
  | object_formula "≣̷" object_formula {
      $$.object_ = new identical(ref<formula>($1.object_), ref<formula>($3.object_), false);
    }
  | term "≣" term {
      $$.object_ = new identical(ref<formula>($1.object_), ref<formula>($3.object_), true);
    }
  | term "≣̷" term {
      $$.object_ = new identical(ref<formula>($1.object_), ref<formula>($3.object_), false);
    }
;

metapredicate_function:
    metapredicate_constant metapredicate_argument {
      $$.object_ = new structure(ref<formula>($1.object_), ref<formula>($2.object_),
        structure::metapredicate, structure::postargument, operator_precedence()); }
  | metaformula_variable metapredicate_argument {
      $$.object_ = new structure(ref<formula>($1.object_), ref<formula>($2.object_),
        structure::metapredicate, structure::postargument, operator_precedence()); }
;

metapredicate_argument:
    "(" metapredicate_argument_body ")" { $$.object_ = $2.object_; }
;

metapredicate_argument_body:
    object_formula {
      sequence* vp
        = new sequence(metapredicate_argument_);
      $$.object_ = vp;
      vp->push_back(ref<formula>($1.object_)); }
  | metapredicate_argument_body "," object_formula {
      $$.object_ = $1.object_;
      sequence& vp = cast_reference<sequence>($$.object_);
      vp.push_back(ref<formula>($3.object_)); }
;

object_formula:
    atomic_formula { $$.object_ = $1.object_; }
  | very_simple_formula formula_substitution_sequence {
      $$.object_ = new substitution_formula(ref<substitution>($2.object_), ref<formula>($1.object_));
    }
  | logic_formula { $$.object_ = $1.object_; }
  | "(" object_formula ")" { $$.object_ = $2.object_; }
  | quantized_formula { $$.object_ = $1.object_; }
;

very_simple_formula:
    object_formula_variable { $$.object_ = $1.object_; }
  | atom_variable { $$.object_ = $1.object_; }
  | "(" object_formula ")" { $$.object_ = $2.object_; }
;

quantized_formula:
    quantizer_declaration quantized_body {
      mli_table_stack_.pop_level();
      variable_list* vsp = cast_pointer<variable_list>($1.object_);
      $$.object_ = new bound_formula(*vsp, ref<formula>($2.object_));
    }
  | quantizer_declaration ":" object_formula {
      mli_table_stack_.pop_level();
      variable_list* vsp = cast_pointer<variable_list>($1.object_);
      $$.object_ = new bound_formula(*vsp, ref<formula>($3.object_));
    }
;

simple_formula:
    object_formula_variable { $$.object_ = $1.object_; }
  | atom_variable { $$.object_ = $1.object_; }
  | predicate_function { $$.object_ = $1.object_; }
  | "(" object_formula ")" { $$.object_ = $2.object_; }
  | quantized_formula { $$.object_ = $1.object_; }
;

quantized_body: /* No quantizer or logic in top level. */
    atomic_formula { $$.object_ = $1.object_; }
  | "(" object_formula ")" { $$.object_ = $2.object_; }
;

atomic_formula:
    atom_constant { $$.object_ = $1.object_; }
  | object_formula_variable { $$.object_ = $1.object_; }
  | atom_variable { $$.object_ = $1.object_; }
  | predicate { $$.object_ = $1.object_; }
;

    /* Predicates */
predicate:
    predicate_function { $$.object_ = $1.object_; }
  | term "=" term {
      structure* cp = new structure($2.text_, structure::predicate);
      $$.object_ = cp;
      cp->push_back(ref<formula>($1.object_));
      cp->push_back(ref<formula>($3.object_));
      cp->set(structure::infix);  /* Binary infix predicate. */
      cp->set(equal_oprec); }
  | term "≠" term {
      structure* cp = new structure($2.text_, structure::predicate);
      $$.object_ = cp;
      cp->push_back(ref<formula>($1.object_));
      cp->push_back(ref<formula>($3.object_));
      cp->set(structure::infix);  /* Binary infix predicate. */
      cp->set(equal_oprec); }
  | term "∈" term {
      structure* cp = new structure($2.text_, structure::predicate);
      $$.object_ = cp;
      cp->push_back(ref<formula>($1.object_));
      cp->push_back(ref<formula>($3.object_));
      cp->set(structure::infix);  /* Binary infix predicate. */
      cp->set(in_oprec); }
  | term "⊂" term {
      structure* cp = new structure($2.text_, structure::predicate);
      $$.object_ = cp;
      cp->push_back(ref<formula>($1.object_));
      cp->push_back(ref<formula>($3.object_));
      cp->set(structure::infix);  /* Binary infix predicate. */
      cp->set(subset_oprec); }
  | term "⊊" term {
      structure* cp = new structure($2.text_, structure::predicate);
      $$.object_ = cp;
      cp->push_back(ref<formula>($1.object_));
      cp->push_back(ref<formula>($3.object_));
      cp->set(structure::infix);  /* Binary infix predicate. */
      cp->set(psubset_oprec); }
  | "Set" { mli_table_stack_.push_level(); }
    "↓" is_set_identifier simple_formula {
      mli_table_stack_.pop_level();
      $$.object_ = new bound_formula(
        ref<variable>($4.object_), ref<formula>($5.object_), bound_formula::is_set_);
    }
;

is_set_identifier:
    "name" {
      binder_declaration_context = false;
      $$.object_ = new variable($1.text_, variable::object_, 0);
      table_stack_insert($1.text_, token::is_set_variable, $$.object_);
    }
  | metaobjectvariable {
      binder_declaration_context = false;
      $$.object_ = $1.object_;
      table_stack_insert($1.text_, token::metaobjectvariable, $1.object_);
    }
;

predicate_function:
    predicate_constant predicate_argument {
      $$.object_ = new structure(ref<formula>($1.object_), ref<formula>($2.object_),
        structure::predicate, structure::postargument, operator_precedence()); }
  | predicate_variable predicate_argument {
      $$.object_ = new structure(ref<formula>($1.object_), ref<formula>($2.object_),
        structure::predicate, structure::postargument, operator_precedence()); }
;

    /* Logic */
logic_formula:
    "¬" object_formula {
      structure* cp = new structure($1.text_, structure::logic);
      $$.object_ = cp;
      cp->push_back(ref<formula>($2.object_));
      cp->set(structure::prefix);
      cp->set(not_oprec); }
  | object_formula "∨" object_formula {
      structure* cp = new structure($2.text_, structure::logic);
      $$.object_ = cp;
      cp->push_back(ref<formula>($1.object_));
      cp->push_back(ref<formula>($3.object_));
      cp->set(structure::infix);
      cp->set(or_oprec); }
  | object_formula "∧" object_formula {
      structure* cp = new structure($2.text_, structure::logic);
      $$.object_ = cp;
      cp->push_back(ref<formula>($1.object_));
      cp->push_back(ref<formula>($3.object_));
      cp->set(structure::infix);
      cp->set(and_oprec); }
  | object_formula "⇒" object_formula {
      structure* cp = new structure($2.text_, structure::logic);
      $$.object_ = cp;
      cp->push_back(ref<formula>($1.object_));
      cp->push_back(ref<formula>($3.object_));
      cp->set(structure::infix);
      cp->set(implies_oprec); }
  | object_formula "⇐" object_formula {
      structure* cp = new structure($2.text_, structure::logic);
      $$.object_ = cp;
      cp->push_back(ref<formula>($1.object_));
      cp->push_back(ref<formula>($3.object_));
      cp->set(structure::infix);
      cp->set(impliedby_oprec); }
  | object_formula "⇔" object_formula {
      structure* cp = new structure($2.text_, structure::logic);
      $$.object_ = cp;
      cp->push_back(ref<formula>($1.object_));
      cp->push_back(ref<formula>($3.object_));
      cp->set(structure::infix);
      cp->set(equivalent_oprec); }
;

quantizer_declaration:
    { mli_table_stack_.push_level(); }
    quantized_variable_list { $$.object_ = $2.object_; }
;

quantized_variable_list:
    all_variable_list { $$.object_ = $1.object_; }
  | exist_variable_list { $$.object_ = $1.object_; }
  | quantized_variable_list all_variable_list {
      $$.object_ = $1.object_;
      variable_list* vsp = cast_pointer<variable_list>($$.object_);
      variable_list* vsp2 = cast_pointer<variable_list>($2.object_);
      vsp->push_back(*vsp2);
    }
  | quantized_variable_list exist_variable_list {
      $$.object_ = $1.object_;
      variable_list* vsp = cast_pointer<variable_list>($$.object_);
      variable_list* vsp2 = cast_pointer<variable_list>($2.object_);
      vsp->push_back(*vsp2);
    }
;

all_variable_list:
    "∀" all_identifier_list { $$.object_ = $2.object_; }
  | "∀" all_identifier_list in_set { $$.object_ = $2.object_; /* Add $3. */ }
;

exist_variable_list:
    "∃" exist_identifier_list { $$.object_ = $2.object_; }
  | "∃" exist_identifier_list in_set { $$.object_ = $2.object_; /* Add $3. */ }
;

all_identifier_list:
    all_identifier {
      binder_declaration_context = false;
      $$.object_ = new variable_list(ref<variable>($1.object_), bound_formula::all_);
    }
  | all_identifier_list { binder_declaration_context = true; }
      "," all_identifier {
      binder_declaration_context = false;
      $$.object_ = $1.object_;
      cast_pointer<variable_list>($$.object_)
        ->push_back(ref<variable>($4.object_), bound_formula::all_);
    }
;

all_identifier:
    "name" {
      ref<object> v = new variable($1.text_, variable::object_, 0);
      table_stack_insert($1.text_, token::all_variable, v);
      $$.object_ = v;
    }
  | metaobjectvariable {
      $$.object_ = $1.object_;
      table_stack_insert($1.text_, token::metaobjectvariable, $1.object_);
    }
;

exist_identifier_list:
    exist_identifier {
      binder_declaration_context = false;
      $$.object_ = new variable_list(ref<variable>($1.object_), bound_formula::exist_);
    }
  | exist_identifier_list { binder_declaration_context = true; }
      "," exist_identifier {
      binder_declaration_context = false;
      $$.object_ = $1.object_;
      cast_pointer<variable_list>($$.object_)
        ->push_back(ref<variable>($4.object_), bound_formula::exist_);
    }
;

exist_identifier:
    "name" {
      ref<object> v = new variable($1.text_, variable::object_, 0);
      table_stack_insert($1.text_, token::exist_variable, v);
      $$.object_ = v;
    }
  | metaobjectvariable {
      $$.object_ = $1.object_;
      table_stack_insert($1.text_, token::metaobjectvariable, $1.object_);
    }
;

in_set:
    "∈" set_identifier {
#if 0
      std::set<std::string>::iterator i = clp_parser_variables.begin(), i1 = clp_parser_variables.end();
      for (; i != i1; ++i) {
        $1.termlist.push_back(new variable(*i, variable::free_), 0));
        $$.termlist.push_back(
          new structure($2.object_, $1.termlist));
        $1.termlist.clear();
      }
#endif
    }
;

set_identifier:
    term_constant { $$.object_ = $1.object_; }
  | object_variable { $$.object_ = $1.object_; }
;

    /* Terms */
predicate_argument:
    "(" predicate_argument_body ")" { $$.object_ = $2.object_; }
;

predicate_argument_body:
    term {
      sequence* vp = new sequence(predicate_argument_);
      $$.object_ = vp;
      vp->push_back(ref<formula>($1.object_)); }
  | predicate_argument_body "," term {
      $$.object_ = $1.object_;
      sequence& vp = cast_reference<sequence>($$.object_);
      vp.push_back(ref<formula>($3.object_)); }
;

function_argument:
    "(" function_argument_body ")" { $$.object_ = $2.object_; }
;

function_argument_body:
    term {
      sequence* vp = new sequence(function_argument_);
      $$.object_ = vp;
      vp->push_back(ref<formula>($1.object_)); }
  | function_argument_body "," term {
      $$.object_ = $1.object_;
      sequence& vp = cast_reference<sequence>($$.object_);
      vp.push_back(ref<formula>($3.object_)); }
;

term:
    simple_term { $$.object_ = $1.object_; }
  | function_term { $$.object_ = $1.object_; }
  | simple_term term_substitution_sequence {
      $$.object_ = new substitution_formula(ref<substitution>($2.object_), ref<formula>($1.object_));
    }
;

simple_term:
    term_constant   { $$.object_ = $1.object_; }
  | unsigned_integer_value { $$.object_ = $1.object_; }
  | signed_integer_value { $$.object_ = $1.object_; }
  | term_identifier { $$.object_ = $1.object_; }
  | "(" term ")"    { $$.object_ = $2.object_; }
;

term_identifier:
    /* Meta: */
    term_variable      { $$.object_ = $1.object_; }
  | object_variable      { $$.object_ = $1.object_; }
  | function_variable  { $$.object_ = $1.object_; }
  | constant_variable  { $$.object_ = $1.object_; }
  | metaobjectvariable { $$.object_ = $1.object_; }
    /* Object: */
  | all_variable       { $$.object_ = $1.object_; }
  | exist_variable     { $$.object_ = $1.object_; }
  | is_set_variable    { $$.object_ = $1.object_; }
  | set_variable       { $$.object_ = $1.object_; }
  | implicit_set_variable { $$.object_ = $1.object_; }
;

function_term:
    function_term_identifier function_argument {
      $$.object_ = new structure(ref<formula>($1.object_), ref<formula>($2.object_),
        structure::function, structure::postargument, operator_precedence()); }
/*  | term "++" term { $$.object_ = new list_concatenation(ref<formula>($1.object_), ref<formula>($3.object_)); } */
  | term "+" term { // $$.object_ = new integer_addition(ref<formula>($1.object_), ref<formula>($3.object_));
      structure* cp = new structure($2.text_, structure::function);
      $$.object_ = cp;
      cp->push_back(ref<formula>($1.object_));
      cp->push_back(ref<formula>($3.object_));
      cp->set(structure::infix);
      cp->set(plus_oprec); }
  | term "-" term { // $$.object_ = new integer_addition(ref<formula>($1.object_), new integer_negative(ref<formula>($3.object_)));
      structure* cp = new structure($2.text_, structure::function);
      $$.object_ = cp;
      cp->push_back(ref<formula>($1.object_));
      cp->push_back(ref<formula>($3.object_));
      cp->set(structure::infix);
      cp->set(minus_oprec); }
  | "-" term  %prec unary_minus { // $$.object_ = new integer_negative(ref<formula>($2.object_)); }
      structure* cp = new structure($2.text_, structure::function);
      $$.object_ = cp;
      cp->push_back(ref<formula>($2.object_));
      cp->set(structure::prefix);
      cp->set(unary_minus_oprec); }
  | term "*" term {
      structure* cp = new structure($2.text_, structure::function);
      $$.object_ = cp;
      cp->push_back(ref<formula>($1.object_));
      cp->push_back(ref<formula>($3.object_));
      cp->set(structure::infix);
      cp->set(mult_oprec); }
  | term "/" term {
      structure* cp = new structure($2.text_, structure::function);
      $$.object_ = cp;
      cp->push_back(ref<formula>($1.object_));
      cp->push_back(ref<formula>($3.object_));
      cp->set(structure::infix);
      cp->set(divide_oprec); }
  | set_term { $$.object_ = $1.object_; }
;

set_term:
    "{" "}" { $$.object_ = new sequence(member_list_set_); }
  | "{" set_member_list "}" { $$.object_ = $2.object_; }
  | "{" set_single_identifier_variable "|" object_formula "}" {
      mli_table_stack_.pop_level();
      $$.object_ = new bound_formula(
        ref<variable>($2.object_), ref<formula>($4.object_), bound_formula::set_);
    }
  | "{" { mli_table_stack_.push_level(); }
    "↓" implicit_set_identifier_list term "|" object_formula "}" {
      mli_table_stack_.pop_level();
      variable_list* vsp = cast_pointer<variable_list>($4.object_);
      sequence* sp =
        new sequence(ref<formula>($5.object_), implicit_set_);
      sp->push_back(ref<formula>($7.object_));
      $$.object_ =
        new bound_formula(*vsp, ref<formula>(sp));
    }
;

set_single_identifier_variable:
    "name" {
      mli_table_stack_.push_level();
      $$.object_ = new variable($1.text_, variable::object_, 0);
      table_stack_insert($1.text_, token::set_variable, $$.object_);
    }
  | metaobjectvariable {
      mli_table_stack_.push_level();
      $$.object_ = $1.object_;
      table_stack_insert($1.text_, token::metaobjectvariable, $1.object_);
    }
;

implicit_set_identifier_list:
    implicit_set_identifier {
      binder_declaration_context = false;
      $$.object_ = new variable_list(ref<variable>($1.object_), bound_formula::implicit_set_);
    }
  | implicit_set_identifier_list { binder_declaration_context = true; }
      "," implicit_set_identifier {
      binder_declaration_context = false;
      $$.object_ = $1.object_;
      cast_pointer<variable_list>($$.object_)->push_back(ref<variable>($4.object_), bound_formula::implicit_set_);
    }
;

implicit_set_identifier:
    "name" {
      ref<object> v = new variable($1.text_, variable::object_, 0);
      table_stack_insert($1.text_, token::implicit_set_variable, v);
      $$.object_ = v;
    }
  | metaobjectvariable {
      $$.object_ = $1.object_;
      table_stack_insert($1.text_, token::metaobjectvariable, $1.object_);
    }
;

set_member_list:
    term {
      sequence* vp = new sequence(member_list_set_);
      $$.object_ = vp;
      vp->push_back(ref<formula>($1.object_)); }
  | set_member_list "," term {
      $$.object_ = $1.object_;
      sequence& vp = cast_reference<sequence>($$.object_);
      vp.push_back(ref<formula>($3.object_));
    }
;

function_term_identifier:
    function_constant { $$.object_ = $1.object_; }
  | function_variable { $$.object_ = $1.object_; }
;

%%

namespace mli {

  void mli_parser::error(const std::string& errstr) {
    std::cerr << "Error line " << mlilex.lp.lineno() << ": " << errstr << std::endl;
  }

  void theory_database::read(std::istream& is) {
    yyFlexLexer lexer(&is, &std::cout);
    mlilex_f lex0(lexer, is);

    mli::mli_parser p(*this, lex0, is);
    if (p.parse() != 0)
      is.setstate(std::ios::failbit);
    else
      is.clear(is.rdstate() & ~(std::ios::failbit | std::ios::badbit));
  }

} // namespace mli

