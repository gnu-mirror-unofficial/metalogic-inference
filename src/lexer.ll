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

%{

#include "parser.hh"

#if 0
#define yylval mlilval
#endif

#include <codecvt>
#include <iostream>
#include <fstream>
#include <locale>
#include <set>
#include <stack>
#include <string>
#include <sstream>
#include <vector>

#include "proposition.hh"
#include "basictype.hh"


#undef YY_DECL
#define YY_DECL  int mliFlexLexer::yylex(mli::semantic_type& yylval)

#define YYERRCODE	256

#define get_text yylval.text_ = std::string(yytext, yyleng)
#define get_text_bounds(pos, red)  .text_ = std::string(yytext + (pos), yyleng - (pos + red))

std::vector<std::string> dirs; // Directories to search for included files.

bool verbose = false;

int mlilineno0 = 0;
int comment_level = 0;
bool declaration_context = false;
bool binder_declaration_context = false;
bool meta_context = false;
bool maybe_set_declaration_context = false;
bool proofline_database_context = false;
bool labelstatement_substitution_context = false;
int bracket_depth = 0;
int declared_token = 0;
int declared_type = 0;

int current_token = 0;


mli::table_stack<std::string, std::pair<int, mli::ref<mli::object> > > mli_table_stack_;

std::stack<YY_BUFFER_STATE> include_stack;
std::stack<int> yylineno_stack;
std::stack<std::string> filename_stack;

%}

%option noyywrap
%option c++
%option yylineno

%x comment
%x any_identifier
%x C_string
%x find_set_variable
%x find_vertical_line
%x include_file

identifier  ([[:alpha:]]+|"𝕗"|"𝕥"|"𝑨"|"𝑩"|"𝒕"|"𝒙")
label       [[:alnum:]]+

comment_begin "[*"
comment_end   "*]"

eol  \n

%%
  if (current_token != 0) { int tok = current_token; current_token = 0; return tok; }

[ \f\r\t\v]+ {}
\n+          {}

"level_max"        { return mli::mli_parser::token::level_max_key; }
"sublevel_max"     { return mli::mli_parser::token::sublevel_max_key; }
"unify_count_max"  { return mli::mli_parser::token::unify_count_max_key; }

"trace_all"      { mli::trace_value = ~0; }
"untrace_all"    { mli::trace_value = 0; }

"trace_null"              { mli::trace_value |= mli::trace_null; }
"untrace_null"            { mli::trace_value &= ~mli::trace_null; }
"trace_result"            { mli::trace_value |= mli::trace_result; }
"untrace_result"          { mli::trace_value &= ~mli::trace_result; }
"trace_proof"             { mli::trace_value |= mli::trace_proof; }
"untrace_proof"           { mli::trace_value &= ~mli::trace_proof; }
"trace_prooftree"         { mli::trace_value |= mli::trace_prooftree; }
"untrace_prooftree"       { mli::trace_value &= ~mli::trace_prooftree; }
"trace_unify"             { mli::trace_value |= mli::trace_unify; }
"untrace_unify"           { mli::trace_value &= ~mli::trace_unify; }
"trace_split"             { mli::trace_value |= mli::trace_split; }
"untrace_split"           { mli::trace_value &= ~mli::trace_split; }
"trace_substitute"        { mli::trace_value |= mli::trace_substitute; }
"untrace_substitute"      { mli::trace_value &= ~mli::trace_substitute; }
"trace_cut"               { mli::trace_value |= mli::trace_cut; }
"untrace_cut"             { mli::trace_value &= ~mli::trace_cut; }
"trace_labelstatement"    { mli::trace_value |= mli::trace_labelstatement; }
"untrace_labelstatement"  { mli::trace_value &= ~mli::trace_labelstatement; }
"trace_database"          { mli::trace_value |= mli::trace_database; }
"untrace_database"        { mli::trace_value &= ~mli::trace_database; }
"trace_formula_type"      { mli::trace_value |= mli::trace_formula_type; }
"untrace_formula_type"    { mli::trace_value &= ~mli::trace_formula_type; }
"trace_variable_type"     { mli::trace_value |= mli::trace_variable_type; }
"untrace_variable_type"   { mli::trace_value &= ~mli::trace_variable_type; }
"trace_bind"              { mli::trace_value |= mli::trace_bind; }
"untrace_bind"            { mli::trace_value &= ~mli::trace_bind; }
"trace_structure_type"    { mli::trace_value |= mli::trace_structure_type; }
"untrace_structure_type"  { mli::trace_value &= ~mli::trace_structure_type; }


"insert"    { BEGIN(include_file); }

<include_file>[[:space:]]*      /* eat the whitespace */
<include_file>[[:^space:]]+|(\".+\")  { /* Get the include file name. */
  include_stack.push(YY_CURRENT_BUFFER);
  std::string str;
  if (yytext[0] == '"')
    str.append(yytext + 1, yyleng - 2);
  else
    str.append(yytext, yyleng);

  yyin = new std::ifstream(str);

  if (!*yyin) {
    delete yyin;
    yyin = nullptr;

    for (auto& i: dirs) {
      std::string path = (i.back() == '/')? i : i + "/";
      path += str;
      yyin = new std::ifstream(path);
      if (!*yyin) {
        delete yyin;
        yyin = nullptr;
        continue;
      }
      break;
    }

    if (yyin == nullptr) {
      std::cerr << "File " << str << " not found." << std::endl;
      return EXIT_FAILURE;
    }
  }

  std::cout << "Begin reading file " << str << std::endl;
  yylineno_stack.push(yylineno);
  yylineno = 1;
  filename_stack.push(str);
  yy_switch_to_buffer(yy_create_buffer(yyin, YY_BUF_SIZE));
  BEGIN(INITIAL);
}


"solve"      { get_text; return mli::mli_parser::token::solve_key; }
"verify"     { get_text; return mli::mli_parser::token::verify_key; }

"by"         { get_text;
               proofline_database_context = true;
               bracket_depth = 0;
               labelstatement_substitution_context = false;
               return mli::mli_parser::token::by_key; }

"include"    { get_text; return mli::mli_parser::token::include_key; }
"end"        { get_text; return mli::mli_parser::token::end_key; }

"formal"[[:space:]]+"system" { get_text; return mli::mli_parser::token::formal_system_key; }
"theory"     { get_text; return mli::mli_parser::token::theory_key; }

"postulate"  { get_text; return mli::mli_parser::token::postulate_key; }
"axiom"      { get_text; return mli::mli_parser::token::axiom_key; }
"rule"       { get_text; return mli::mli_parser::token::rule_key; }
"conjecture" { get_text; return mli::mli_parser::token::conjecture_key; }

"definition" { get_text; return mli::mli_parser::token::definition_key; }

"lemma"       { get_text; yylval.number_ = mli::theorem::lemma_; return mli::mli_parser::token::theorem_key; }
"proposition" { get_text; yylval.number_ = mli::theorem::proposition_; return mli::mli_parser::token::theorem_key; }
"theorem"     { get_text; yylval.number_ = mli::theorem::theorem_; return mli::mli_parser::token::theorem_key; }
"corollary"   { get_text; yylval.number_ = mli::theorem::corollary_; return mli::mli_parser::token::theorem_key; }
"claim"       { get_text; return mli::mli_parser::token::claim_key; }
"proof"       { get_text; return mli::mli_parser::token::proof_key; }
"conclusion"  { get_text; return mli::mli_parser::token::conclusion_key; }
"premise"     { get_text; return mli::mli_parser::token::premise_key; }
"∎"      { get_text; return mli::mli_parser::token::proof_complete_key; }

"⊢"        { return mli::mli_parser::token::infer_key; }
"⊣"        { return mli::mli_parser::token::infered_by_key; }

"≡"   { get_text; return mli::mli_parser::token::object_identical_key; }
"≢"   { get_text; return mli::mli_parser::token::object_not_identical_key; }
"≣"   { get_text; return mli::mli_parser::token::meta_identical_key; }
"≣̷"  { get_text; return mli::mli_parser::token::meta_not_identical_key; }

"fail"    { get_text; return mli::mli_parser::token::fail_key; }
"succeed" { get_text; return mli::mli_parser::token::succeed_key; }

"free"[[:space:]]+"for" { get_text; meta_context = true; return mli::mli_parser::token::free_for_key; }
"free"[[:space:]]+"in"  { get_text; return mli::mli_parser::token::free_in_key; }

"in"     { get_text; meta_context = false; return mli::mli_parser::token::metain_key; }

"not"  { get_text; return mli::mli_parser::token::meta_not_key; }


"use" { get_text; return mli::mli_parser::token::use_key; }

"≔"        { return mli::mli_parser::token::defined_by_key; }
"≕"        { return mli::mli_parser::token::defines_key; }
"≝"        { return mli::mli_parser::token::defined_equal_key; }

"~formula" { declaration_context = true; declared_token = mli::mli_parser::token::metaformula_variable;
            declared_type = mli::variable::metaformula_; return mli::mli_parser::token::identifier_variable_key; }
"formula" { declaration_context = true; declared_token = mli::mli_parser::token::object_formula_variable;
            declared_type = mli::variable::formula_; return mli::mli_parser::token::identifier_variable_key; }
"predicate"[[:space:]]+"variable" {
             declaration_context = true; declared_token = mli::mli_parser::token::predicate_variable;
             declared_type = mli::variable::predicate_; return mli::mli_parser::token::identifier_variable_key; }
"atom"[[:space:]]+"variable" {
             declaration_context = true; declared_token = mli::mli_parser::token::atom_variable;
             declared_type = mli::variable::atom_; return mli::mli_parser::token::identifier_variable_key; }

"term"     { declaration_context = true; declared_token = mli::mli_parser::token::term_variable;
             declared_type = mli::variable::term_; return mli::mli_parser::token::identifier_variable_key; }
"metaobject" { declaration_context = true; declared_token = mli::mli_parser::token::metaobjectvariable;
             declared_type = mli::variable::metaobject_;
             return mli::mli_parser::token::identifier_variable_key; }
"function"[[:space:]]+"variable" {
             declaration_context = true; declared_token = mli::mli_parser::token::function_variable;
             declared_type = mli::variable::function_; return mli::mli_parser::token::identifier_variable_key; }
"constant"[[:space:]]+"variable" {
             declaration_context = true; declared_token = mli::mli_parser::token::constant_variable;
             declared_type = mli::variable::constant_; return mli::mli_parser::token::identifier_variable_key; }

"object"  { declaration_context = true; declared_token = mli::mli_parser::token::object_variable;
            declared_type = mli::variable::object_; return mli::mli_parser::token::identifier_variable_key; }

"∀"   { binder_declaration_context = true; return mli::mli_parser::token::all_key; }
"∃"   { binder_declaration_context = true; return mli::mli_parser::token::exist_key; }

"~predicate" { declaration_context = true; declared_token = mli::mli_parser::token::metapredicate_constant;
               declared_type = mli::metaformula_type_; return mli::mli_parser::token::identifier_constant_key; }
"predicate"  { declaration_context = true; declared_token = mli::mli_parser::token::predicate_constant;
               declared_type = mli::object_formula_type_; return mli::mli_parser::token::identifier_constant_key; }
"atom"       { declaration_context = true; declared_token = mli::mli_parser::token::atom_constant;
               declared_type = mli::object_formula_type_; return mli::mli_parser::token::identifier_constant_key; }

"function"   { declaration_context = true; declared_token = mli::mli_parser::token::function_constant;
               declared_type = mli::term_type_; return mli::mli_parser::token::identifier_constant_key; }
"constant"   { declaration_context = true; declared_token = mli::mli_parser::token::term_constant;
               declared_type = mli::term_type_; return mli::mli_parser::token::identifier_constant_key; }

"⇒"   { get_text; return mli::mli_parser::token::implies_key; }
"⇐"   { get_text; return mli::mli_parser::token::impliedby_key; }
"⇔"  { get_text; return mli::mli_parser::token::equivalent_key; }

"∧"  { get_text; return mli::mli_parser::token::and_key; }
"∨"   { get_text; return mli::mli_parser::token::or_key; }
"¬"   { get_text; return mli::mli_parser::token::not_key; }

":"  { declaration_context = false;
       binder_declaration_context = false;
       return mli::mli_parser::token::colon_key; }
","  { return mli::mli_parser::token::comma_key; }
"."  { declaration_context = false;
       binder_declaration_context = false;
       return mli::mli_parser::token::period_key; }

";"  { return mli::mli_parser::token::semicolon_key; }

"="  { get_text; return mli::mli_parser::token::equal_key; }
"≠"  { get_text; return mli::mli_parser::token::not_equal_key; }

"("  { return mli::mli_parser::token::left_parenthesis_key; }
")"  { return mli::mli_parser::token::right_parenthesis_key; }

"~[" { return mli::mli_parser::token::substitution_begin_key; }
"["  { if (proofline_database_context)
         ++bracket_depth;
       if (bracket_depth == 1)
         labelstatement_substitution_context = true;
       return mli::mli_parser::token::left_bracket_key; }
"]"  { if (proofline_database_context)
         --bracket_depth;
       return mli::mli_parser::token::right_bracket_key; }

"⟨"  { return mli::mli_parser::token::left_angle_bracket_key; }
"⟩"  { return mli::mli_parser::token::right_angle_bracket_key; }

"{"  { maybe_set_declaration_context = true;
       BEGIN(find_set_variable);
       return mli::mli_parser::token::left_brace_key; }
"|"  { return mli::mli_parser::token::vertical_line_key; }
"}"  { return mli::mli_parser::token::right_brace_key; }

"~"  { return mli::mli_parser::token::tilde_key; }

<find_set_variable>{
  [ \f\r\t\v]+ {}
  \n+          {}
}

<find_vertical_line>{
  [ \f\r\t\v]+ {}
  \n+          {}
  "|" { current_token = mli::mli_parser::token::vertical_line_key;
        maybe_set_declaration_context = false;
        BEGIN(INITIAL);
        if (yylval.number_ == mli::mli_parser::token::metaobjectvariable)
          return mli::mli_parser::token::metaobjectvariable;
        return mli::mli_parser::token::plain_name; }
  .   { yyless(0); BEGIN(INITIAL); maybe_set_declaration_context = false;
        int tok = current_token;  current_token = 0; return tok; }
}

"Set"  { binder_declaration_context = true; get_text; return mli::mli_parser::token::is_set_key; }
"∈"    { get_text; return mli::mli_parser::token::in_key; }
"⊂"    { get_text; return mli::mli_parser::token::subset_key; }
"⊊"    { get_text; return mli::mli_parser::token::proper_subset_key; }

"/"   { get_text; return mli::mli_parser::token::slash_key; }
"\\"  { get_text; return mli::mli_parser::token::backslash_key; }

"!"   { get_text; return mli::mli_parser::token::plain_name; return mli::mli_parser::token::cut_key; }

"++"  { get_text; return mli::mli_parser::token::list_concat; }
"*"|"·"   { get_text; return mli::mli_parser::token::mult_key; }
"+"   { get_text; return mli::mli_parser::token::plus_key; }
"-"   { get_text; return mli::mli_parser::token::minus_key; }

"_"|"↓"  { get_text; return mli::mli_parser::token::subscript_key; }
"^"|"↑"  { get_text; return mli::mli_parser::token::superscript_key; }

[[:digit:]]+ {
  get_text;
  mli::integer* ip = new mli::integer(yytext);
  yylval.object_ = ip;
  return mli::mli_parser::token::unsigned_integer_value;
}

[+-][[:digit:]]+ {
  get_text;
  mli::integer* ip = new mli::integer(yytext);
  yylval.object_ = ip;
  return mli::mli_parser::token::signed_integer_value;
}

<INITIAL,find_set_variable>{identifier} {
  get_text;
  if (labelstatement_substitution_context) {
    labelstatement_substitution_context = false;
    mli::maybe<std::pair<int, mli::ref<mli::object> > > x = mli_table_stack_.find_top(yylval.text_);
    if (!x)  return mli::mli_parser::token::plain_name;
    yylval.object_ = x->second;
    yylval.number_ = x->first;
    return x->first;
  }
  if (declaration_context)  return mli::mli_parser::token::plain_name;
  mli::maybe<std::pair<int, mli::ref<mli::object> > > x = mli_table_stack_.find(yylval.text_);
  if (!x)  return mli::mli_parser::token::plain_name;
  yylval.object_ = x->second;
  yylval.number_ = x->first;
  if (binder_declaration_context) {
    if (yylval.number_ == mli::mli_parser::token::metaobjectvariable)
      return mli::mli_parser::token::metaobjectvariable;
    return mli::mli_parser::token::plain_name;
  }
  if (maybe_set_declaration_context) {
    current_token = x->first;
    BEGIN(find_vertical_line);
    YY_BREAK;
  }
  return x->first;
}

{label} { get_text; return mli::mli_parser::token::label_key; }


<INITIAL,find_set_variable>"“" { yylval.text_.clear(); BEGIN(any_identifier); }

<any_identifier>{
  "”" { /* Closing quote - all done. Text now in yylval.text_. */
    BEGIN(INITIAL);
    if (declaration_context)  return mli::mli_parser::token::plain_name;
    mli::maybe<std::pair<int, mli::ref<mli::object>>> x = mli_table_stack_.find(yylval.text_);
    if (!x)  return mli::mli_parser::token::plain_name;
    yylval.object_ = x->second;
    yylval.number_ = x->first;
    if (binder_declaration_context) {
      if (yylval.number_ == mli::mli_parser::token::metaobjectvariable)
        return mli::mli_parser::token::metaobjectvariable;
      return mli::mli_parser::token::plain_name;
    }
    if (maybe_set_declaration_context) {
      current_token = x->first;
      BEGIN(find_vertical_line);
      YY_BREAK;
    }
    return x->first;
  }

  "“"    { std::cerr << "Error: string with “; an earlier string might be unterminated.\n";
           BEGIN(INITIAL); return YYERRCODE; }
  "\\“"  { yylval.text_ += "“"; }
  "\\”"  { yylval.text_ += "”"; }

	\\[0-7]{1,3} { /* Octal escape sequence. */
	  int result;
	  std::sscanf(yytext + 1, "%o", &result);
	  if (result > 0xff) {
      std::cerr << "Error: string octal escape " << std::string(yytext, yyleng)
        << " is out-of-bounds, must be ≤ \\377." << std::endl;
      BEGIN(INITIAL); return YYERRCODE;
    }
	  yylval.text_ += (char)result;
	}

	\\x[[:xdigit:]]{1,2} { /* Hexadecimal escape sequence. */
	  int result;
	  std::sscanf(yytext + 2, "%x", &result);
	  if (result > 0xff) {
      std::cerr << "Error: string hexadecimal escape " << std::string(yytext, yyleng)
        << " is out-of-bounds, must be ≤ \\xff." << std::endl;
      BEGIN(INITIAL); return YYERRCODE;
    }
	  yylval.text_ += (char)result;
	}

	\\[uU][[:xdigit:]]{1,8} { /* Hexadecimal escape sequence to give UTF-8 characters. */
    int result;
    std::sscanf(yytext + 2, "%x", &result);

    // Throws exception if conversion to UTF-8 fails:
    std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> u32convert;
    std::string str = u32convert.to_bytes((char32_t)result);
	  yylval.text_ += str;
	}

  \\[0-9]+   { std::cerr << "Error: bad string escape sequence "
    << std::string(yytext, yyleng) << std::endl; BEGIN(INITIAL); return YYERRCODE; }

  \\{2}   { yylval.text_ += '\\'; }
  \\&     { ; /* Non-character, used to delimit numeric escapes */ }

  \\a     { yylval.text_ += '\a'; }
  \\b     { yylval.text_ += '\b'; }
  \\f     { yylval.text_ += '\f'; }
  \\n     { yylval.text_ += '\n'; }
  \\r     { yylval.text_ += '\r'; }
  \\t     { yylval.text_ += '\t'; }
  \\v     { yylval.text_ += '\v'; }

  .     { yylval.text_ += std::string(yytext, yyleng); }
  \n    { std::cerr << "Error: newline in string." << std::endl; BEGIN(INITIAL); return YYERRCODE; }
}


<find_set_variable>{
  .   { yyless(0); BEGIN(INITIAL); maybe_set_declaration_context = false; }
}

"\""              { yylval.text_.clear(); BEGIN(C_string); }

"--".*\n        {}

"[*"  { BEGIN(comment); comment_level = 1; mlilineno0 = yylineno; }
<comment>{ /* Comments. */
  "*]" { /* End of the comment. */
    if (--comment_level == 0) {
	    BEGIN INITIAL;
    }
  }

  "[*"        { comment_level++; }
  [^*[\n]+    {}
  \n+   	    {}
  .           { /* Stray `*' and `['. */ }

  <<EOF>> {
    std::cerr << "Error: Nested comments not properly closed at end of file.\n";
    BEGIN(INITIAL); return YYERRCODE;
    /* exit_set (exit_scan); */
  }
}
"*]"  { std::cerr << "Error: Too many comment closings *].\n";
        BEGIN(INITIAL); return YYERRCODE; }

<C_string>{
  "\""   { /* Closing quote - all done. */ BEGIN(INITIAL); return mli::mli_parser::token::plain_name; }
  \n     { std::cerr << "Error: unterminated C-string.\n";
           BEGIN(INITIAL); yyless(1); --yylineno; return YYERRCODE; }

	\\[0-7]{1,3} { /* Octal escape sequence. */
	  int result;
	  std::sscanf(yytext + 1, "%o", &result);
	  if (result > 0xff) {
      std::cerr << "Error: string octal escape " << std::string(yytext, yyleng)
        << " is out-of-bounds, must be ≤ \\377." << std::endl;
      BEGIN(INITIAL); return YYERRCODE;
    }
	  yylval.text_ += (char)result;
	}

	\\x[[:xdigit:]]{1,2} { /* Hexadecimal escape sequence. */
	  int result;
	  std::sscanf(yytext + 2, "%x", &result);
	  if (result > 0xff) {
      std::cerr << "Error: string hexadecimal escape " << std::string(yytext, yyleng)
        << " is out-of-bounds, must be ≤ \\xff." << std::endl;
      BEGIN(INITIAL); return YYERRCODE;
    }
	  yylval.text_ += (char)result;
	}

  \\[0-9]+    { std::cerr << "Error: bad string escape sequence "
    << std::string(yytext, yyleng) << std::endl; BEGIN(INITIAL); return YYERRCODE; }

  \\{2}   { yylval.text_ += '\\'; }
  \\&     { ; /* Non-character, used to delimit numeric escapes */ }

  \\a     { yylval.text_ += '\a'; }
  \\b     { yylval.text_ += '\b'; }
  \\f     { yylval.text_ += '\f'; }
  \\n     { yylval.text_ += '\n'; }
  \\r     { yylval.text_ += '\r'; }
  \\t     { yylval.text_ += '\t'; }
  \\v     { yylval.text_ += '\v'; }

  \\(.|\n)    { yylval.text_ += yytext[1]; }
  [^\\\n\"]+  { /* " */ yylval.text_ += std::string(yytext, yyleng); }
}

.                 { return yytext[0]; }

<<EOF>> {
  if (include_stack.empty())
    return EOF;

  delete yyin; // yyin is not deleted by yy_delete_buffer.
  yyin = nullptr;

  yy_delete_buffer(YY_CURRENT_BUFFER);
  yy_switch_to_buffer(include_stack.top());
  include_stack.pop();
  yylineno = yylineno_stack.top();
  yylineno_stack.pop();
  std::cout << "End reading file " << filename_stack.top() << std::endl;
  filename_stack.pop();
  if (!filename_stack.empty())
    std::cout << "Continue reading file " << filename_stack.top()
      << ", line " << yylineno << "." << std::endl;
}

%%

