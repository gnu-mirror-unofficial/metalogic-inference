/* Copyright (C) 2017, 2021-2022 Hans Γberg.

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

#include "directive-parser.hh"

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


#define YYERRCODE	256

#define the_text std::string(yytext, yyleng)
#define get_text yylval.text = std::string(yytext, yyleng)

int directive_comment_level = 0;
bool directive_declaration_context = false;
mli::directive_parser::token_type directive_declared_token = mli::free_variable_context;
int directive_declared_type = 0;

int directive_current_token = 0;

extern std::istream::pos_type current_position, line_position;

std::vector<std::string> directive_strs;
mli::kleenean directive_directive_type = false;

%}

%option noyywrap
%option c++
%option yyclass="mli::directive_lexer"

%x comment
%x line_comment
%x block_comment
%x directive

%x any_identifier
%x C_string
%x find_set_variable
%x find_vertical_line
%x include_file
%x logic_prefix


bold-upper  "π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"
bold-lower  "π"|"π"|"π"|"π"|"π"|"π"|"π "|"π‘"|"π’"|"π£"|"π€"|"π₯"|"π¦"|"π§"|"π¨"|"π©"|"πͺ"|"π«"|"π¬"|"π­"|"π?"|"π―"|"π°"|"π±"|"π²"|"π³"
bold-digit  "π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"

bold    {bold-upper}|{bold-lower}


italic-upper  "π΄"|"π΅"|"πΆ"|"π·"|"πΈ"|"πΉ"|"πΊ"|"π»"|"πΌ"|"π½"|"πΎ"|"πΏ"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"
italic-lower  "π"|"π"|"π"|"π"|"π"|"π"|"π"|"β"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π "|"π‘"|"π’"|"π£"|"π€"|"π₯"|"π¦"|"π§"

italic    {italic-upper}|{italic-lower}


bold-italic-upper   "π¨"|"π©"|"πͺ"|"π«"|"π¬"|"π­"|"π?"|"π―"|"π°"|"π±"|"π²"|"π³"|"π΄"|"π΅"|"πΆ"|"π·"|"πΈ"|"πΉ"|"πΊ"|"π»"|"πΌ"|"π½"|"πΎ"|"πΏ"|"π"|"π"
bold-italic-lower   "π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"

bold-italic  {bold-italic-upper}|{bold-italic-lower}


script-upper   "π"|"β¬"|"π"|"π"|"β°"|"β±"|"π’"|"β"|"β"|"π₯"|"π¦"|"β"|"β³"|"π©"|"πͺ"|"π«"|"π¬"|"β"|"π?"|"π―"|"π°"|"π±"|"π²"|"π³"|"π΄"|"π΅"
script-lower   "πΆ"|"π·"|"πΈ"|"πΉ"|"β―"|"π»"|"β"|"π½"|"πΎ"|"πΏ"|"π"|"π"|"π"|"π"|"β΄"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"

script  {script-upper}|{script-lower}


script-bold-upper   "π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π "|"π‘"|"π’"|"π£"|"π€"|"π₯"|"π¦"|"π§"|"π¨"|"π©"
script-bold-lower   "πͺ"|"π«"|"π¬"|"π­"|"π?"|"π―"|"π°"|"π±"|"π²"|"π³"|"π΄"|"π΅"|"πΆ"|"π·"|"πΈ"|"πΉ"|"πΊ"|"π»"|"πΌ"|"π½"|"πΎ"|"πΏ"|"π"|"π"|"π"|"π"

script-bold  {script-bold-upper}|{script-bold-lower}


fraktur-upper   "π"|"π"|"β­"|"π"|"π"|"π"|"π"|"β"|"β"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"β"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"β¨"
fraktur-lower   "π"|"π"|"π "|"π‘"|"π’"|"π£"|"π€"|"π₯"|"π¦"|"π§"|"π¨"|"π©"|"πͺ"|"π«"|"π¬"|"π­"|"π?"|"π―"|"π°"|"π±"|"π²"|"π³"|"π΄"|"π΅"|"πΆ"|"π·"

fraktur  {fraktur-upper}|{fraktur-lower}


fraktur-bold-upper  "π¬"|"π­"|"π?"|"π―"|"π°"|"π±"|"π²"|"π³"|"π΄"|"π΅"|"πΆ"|"π·"|"πΈ"|"πΉ"|"πΊ"|"π»"|"πΌ"|"π½"|"πΎ"|"πΏ"|"π"|"π"|"π"|"π"|"π"|"π"
fraktur-bold-lower  "π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"

fraktur-bold  {fraktur-bold-upper}|{fraktur-bold-lower}


double-struck-upper   "πΈ"|"πΉ"|"β"|"π»"|"πΌ"|"π½"|"πΎ"|"β"|"π"|"π"|"π"|"π"|"π"|"β"|"π"|"β"|"β"|"β"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"β€"
double-struck-lower   "π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π "|"π‘"|"π’"|"π£"|"π€"|"π₯"|"π¦"|"π§"|"π¨"|"π©"|"πͺ"|"π«"
double-struck-digit   "π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π "|"π‘"

double-struck   {double-struck-upper}|{double-struck-lower}


greek-upper  "Ξ"|"Ξ"|"Ξ"|"Ξ"|"Ξ"|"Ξ"|"Ξ"|"Ξ"|"Ξ"|"Ξ"|"Ξ"|"Ξ"|"Ξ"|"Ξ"|"Ξ"|"Ξ "|"Ξ‘"|"Ο΄"|"Ξ£"|"Ξ€"|"Ξ₯"|"Ξ¦"|"Ξ§"|"Ξ¨"|"Ξ©"
greek-lower  "Ξ±"|"Ξ²"|"Ξ³"|"Ξ΄"|"Ξ΅"|"ΞΆ"|"Ξ·"|"ΞΈ"|"ΞΉ"|"ΞΊ"|"Ξ»"|"ΞΌ"|"Ξ½"|"ΞΎ"|"ΞΏ"|"Ο"|"Ο"|"Ο"|"Ο"|"Ο"|"Ο"|"Ο"|"Ο"|"Ο"|"Ο"|"Ο΅"|"Ο"|"Ο°"|"Ο"|"Ο±"|"Ο"

greek  {greek-upper}|{greek-lower}


greek-bold-upper    "π¨"|"π©"|"πͺ"|"π«"|"π¬"|"π­"|"π?"|"π―"|"π°"|"π±"|"π²"|"π³"|"π΄"|"π΅"|"πΆ"|"π·"|"πΈ"|"πΉ"|"πΊ"|"π»"|"πΌ"|"π½"|"πΎ"|"πΏ"|"π"
greek-bold-lower    "π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π "|"π‘"

greek-bold  {greek-bold-upper}|{greek-bold-lower}


greek-italic-upper  "π’"|"π£"|"π€"|"π₯"|"π¦"|"π§"|"π¨"|"π©"|"πͺ"|"π«"|"π¬"|"π­"|"π?"|"π―"|"π°"|"π±"|"π²"|"π³"|"π΄"|"π΅"|"πΆ"|"π·"|"πΈ"|"πΉ"|"πΊ"
greek-italic-lower  "πΌ"|"π½"|"πΎ"|"πΏ"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"

greek-italic  {greek-italic-upper}|{greek-italic-lower}


greek-bold-italic-upper   "π"|"π"|"π"|"π"|"π "|"π‘"|"π’"|"π£"|"π€"|"π₯"|"π¦"|"π§"|"π¨"|"π©"|"πͺ"|"π«"|"π¬"|"π­"|"π?"|"π―"|"π°"|"π±"|"π²"|"π³"|"π΄"
greek-bold-italic-lower   "πΆ"|"π·"|"πΈ"|"πΉ"|"πΊ"|"π»"|"πΌ"|"π½"|"πΎ"|"πΏ"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"|"π"

greek-bold-italic  {greek-bold-italic-upper}|{greek-bold-italic-lower}


identifier  ([[:alpha:]]+|{bold}+|{italic}+|{bold-italic}+|{script}+|{script-bold}+|{fraktur}+|{fraktur-bold}+|{double-struck}+|{greek}+|{greek-bold}+|{greek-italic}+|{greek-bold-italic}+)

logic_prefix_identifier  ([[:alpha:]]|{bold}|{italic}|{bold-italic}|{script}|{script-bold}|{fraktur}|{fraktur-bold}|{double-struck}|{greek}|{greek-bold}|{greek-italic}|{greek-bold-italic})

label       [[:alnum:]]+

/*
whitespace
"β" U+2002 en space
"β" U+2003 em space
"β" U+2004 three-per-em space
"β" U+2005 four-per-em space
"β" U+2006 six-per-em space
"β" U+2007 figure space
"β" U+2008 punctuation space
"β" U+2009 thin space
"β" U+200A hair space
"β" U+205F medium mathematical space
*/
whitespace  [ \f\r\t\v]|"β"|"β"|"β"|"β"|"β"|"β"|"β"|"β"|"β"|"β"

comment_begin "[*"
comment_end   "*]"

subscript_digit     "β"|"β"|"β"|"β"|"β"|"β"|"β"|"β"|"β"|"β"
superscript_digit   "β°"|"ΒΉ"|"Β²"|"Β³"|"β΄"|"β΅"|"βΆ"|"β·"|"βΈ"|"βΉ"

subscript_sign   "β"|"β"
superscript_sign "βΊ"|"β»"

/* UTF-8 character with valid Unicode code point. */
utf8char    [\x09\x0A\x0D\x20-\x7E]|[\xC2-\xDF][\x80-\xBF]|\xE0[\xA0-\xBF][\x80-\xBF]|[\xE1-\xEC\xEE\xEF]([\x80-\xBF]{2})|\xED[\x80-\x9F][\x80-\xBF]|\xF0[\x\90-\xBF]([\x80-\xBF]{2})|[\xF1-\xF3]([\x80-\xBF]{3})|\xF4[\x80-\x8F]([\x80-\xBF]{2})

%{
#define YY_USER_ACTION  yylloc.columns(yyleng); current_position += yyleng;
%}


%%
%{
  mli::semantic_type& yylval = *yylvalp;
  mli::location_type& yylloc = *yyllocp;

  if (directive_current_token != 0) { int tok = directive_current_token; directive_current_token = 0; return tok; }

  yylloc.step();
%}

{whitespace}+ { yylloc.step(); }
\n+           { yylloc.lines(yyleng); yylloc.step(); line_position = current_position; }


"expand_implicit_premise" { expand_implicit_premise = true; }
"unexpand_implicit_premise" { expand_implicit_premise = false; }


"count" { return mli::directive_parser::token::count_key; }
"max" { return mli::directive_parser::token::max_key; }
"level" { return mli::directive_parser::token::level_key; }
"sublevel" { return mli::directive_parser::token::sublevel_key; }


"diagnostic" { return mli::directive_parser::token::diagnostic_key; }
"ignored" { return mli::directive_parser::token::ignored_key; }
"warning" { return mli::directive_parser::token::warning_key; }
"error"   { return mli::directive_parser::token::error_key; }

"unused" { return mli::directive_parser::token::unused_key; }
"variable" { return mli::directive_parser::token::variable_key; }
"type" { return mli::directive_parser::token::type_key; }
"label" { return mli::directive_parser::token::label_key; }


"trace" { return mli::directive_parser::token::trace_key; }
"untrace" { return mli::directive_parser::token::untrace_key; }


"conditional" { return mli::directive_parser::token::conditional_key; }
"strict"      { return mli::directive_parser::token::strict_key; }


"all" { return mli::directive_parser::token::all_key; }
"none" { return mli::directive_parser::token::none_key; }
"no" { return mli::directive_parser::token::no_key; }


"null" { return mli::directive_parser::token::null_key; }
"empty" { return mli::directive_parser::token::empty_key; }
"result" { return mli::directive_parser::token::result_key; }
"proof" { return mli::directive_parser::token::proof_key; }
"solve" { return mli::directive_parser::token::solve_key; }
"prooftree" { return mli::directive_parser::token::prooftree_key; }
"unify" { return mli::directive_parser::token::unify_key; }
"split" { return mli::directive_parser::token::split_key; }
"substitute" { return mli::directive_parser::token::substitute_key; }
"statement" { return mli::directive_parser::token::statement_key; }
"database" { return mli::directive_parser::token::database_key; }
"formula" { return mli::directive_parser::token::formula_key; }
"unspecializable" { return mli::directive_parser::token::unspecializable_key; }
"structure" { return mli::directive_parser::token::structure_key; }
"thread" { return mli::directive_parser::token::thread_key; }


"include"    { get_text; return mli::directive_parser::token::include_key; }
"end"        { get_text; return mli::directive_parser::token::end_key; }


"β"   { get_text; return mli::directive_parser::token::implies_key; }
"β"   { get_text; return mli::directive_parser::token::impliedby_key; }
"β"  { get_text; return mli::directive_parser::token::equivalent_key; }

"β§"  { get_text; return mli::directive_parser::token::logical_and_key; }
"β¨"   { get_text; return mli::directive_parser::token::logical_or_key; }
"Β¬"   { get_text; return mli::directive_parser::token::logical_not_key; }

":"  { directive_declaration_context = false;
       directive_bound_variable_type = free_variable_context;
       return mli::directive_parser::token::colon_key; }
","  { return mli::directive_parser::token::comma_key; }
"."  { directive_declaration_context = false;
       directive_bound_variable_type = free_variable_context;
       return mli::directive_parser::token::period_key; }

";"  { return mli::directive_parser::token::semicolon_key; }


"<"  { get_text; return mli::directive_parser::token::less_key; }
">"  { get_text; return mli::directive_parser::token::greater_key; }
"β€"  { get_text; return mli::directive_parser::token::less_or_equal_key; }
"β₯"  { get_text; return mli::directive_parser::token::greater_or_equal_key; }

"β?"  { get_text; return mli::directive_parser::token::not_less_key; }
"β―"  { get_text; return mli::directive_parser::token::not_greater_key; }
"β°"  { get_text; return mli::directive_parser::token::not_less_or_equal_key; }
"β±"  { get_text; return mli::directive_parser::token::not_greater_or_equal_key; }

"="  { get_text; return mli::directive_parser::token::equal_key; }
"β "  { get_text; return mli::directive_parser::token::not_equal_key; }


"β¦" { get_text; return mli::directive_parser::token::mapsto_key; }

"Β°"  { get_text; return mli::directive_parser::token::degree_key; }


"("  { return mli::directive_parser::token::left_parenthesis_key; }
")"  { return mli::directive_parser::token::right_parenthesis_key; }

"β½"  { return mli::directive_parser::token::superscript_left_parenthesis_key; }
"βΎ"  { return mli::directive_parser::token::superscript_right_parenthesis_key; }

"β"  { return mli::directive_parser::token::subscript_left_parenthesis_key; }
"β"  { return mli::directive_parser::token::subscript_right_parenthesis_key; }


"["  { return mli::directive_parser::token::left_bracket_key; }
"]"  { return mli::directive_parser::token::right_bracket_key; }

"β¨"  { return mli::directive_parser::token::left_angle_bracket_key; }
"β©"  { return mli::directive_parser::token::right_angle_bracket_key; }

"{"  { return mli::directive_parser::token::left_brace_key; }
"|"  { return mli::directive_parser::token::vertical_line_key; }
"}"  { return mli::directive_parser::token::right_brace_key; }

"~"  { return mli::directive_parser::token::tilde_key; }

"β"   { get_text; return mli::directive_parser::token::mult_key; }
"+"   { get_text; return mli::directive_parser::token::plus_key; }
"-"   { get_text; return mli::directive_parser::token::minus_key; }

"if"    { return mli::directive_parser::token::if_key; }
"then"  { return mli::directive_parser::token::then_key; }
"else"  { return mli::directive_parser::token::else_key; }

"while" { return mli::directive_parser::token::while_key; }
"do"    { return mli::directive_parser::token::do_key; }
"loop"  { return mli::directive_parser::token::loop_key; }
"for"   { return mli::directive_parser::token::for_key; }

"break"     { return mli::directive_parser::token::break_key; }
"continue"  { return mli::directive_parser::token::continue_key; }

"throw"  { return mli::directive_parser::token::throw_key; }
"try"    { return mli::directive_parser::token::try_key; }
"catch"  { return mli::directive_parser::token::catch_key; }


[[:digit:]]+ {
  get_text;
  yylval.object = ref<integer>(mli::make, yytext);
  return mli::directive_parser::token::natural_number_value;
}

[+-][[:digit:]]+ {
  get_text;
  yylval.object = ref<integer>(make, yytext);
  return mli::directive_parser::token::integer_value;
}




{identifier} {
  get_text;

  directive_parser::token_type ret = directive_define_variable(yylval);

  return ret;
}


{label} { get_text; return mli::directive_parser::token::label_key; }


"β" { yylval.text.clear(); BEGIN(any_identifier); }

<any_identifier>{
  "β" { /* Closing quote - all done. Text now in yylval.text. */
    BEGIN(INITIAL);

    directive_parser::token_type ret = directive_define_variable(yylval);


    return ret;
  }

  "β"    {
    BEGIN(INITIAL);
    throw mli::directive_parser::syntax_error(yylloc,
     "String with β; an earlier string might be unterminated.");
  }
  "\\β"  { yylval.text += "β"; }
  "\\β"  { yylval.text += "β"; }

	\\[0-7]{1,3} { /* Octal escape sequence. */
	  int result;
	  std::sscanf(yytext + 1, "%o", &result);
	  if (result > 0xff) {
      BEGIN(INITIAL);
      throw mli::directive_parser::syntax_error(yylloc,
        "String octal escape " + the_text + " is out-of-bounds, must be β€ \\ 377.");
    }
	  yylval.text += (char)result;
	}

	\\x[[:xdigit:]]{1,2} { /* Hexadecimal escape sequence. */
	  int result;
	  std::sscanf(yytext + 2, "%x", &result);
	  if (result > 0xff) {
      // Can actually not get here, as scanning for max 2 hex digits!
      BEGIN(INITIAL);
      throw mli::directive_parser::syntax_error(yylloc,
        "String hexadecimal escape " + the_text + " is out-of-bounds, must be β€ \\xff.");
    }
	  yylval.text += (char)result;
	}

	\\[uU][[:xdigit:]]{1,8} { /* Hexadecimal escape sequence to give UTF-8 characters. */
    yylval.text += to_utf8(std::stoul(yytext + 2, nullptr, 16));
	}

  \\[0-9]+   {
    BEGIN(INITIAL);
    throw mli::directive_parser::syntax_error(yylloc,
      "Bad string escape sequence " + the_text);
  }

  \\{2}   { yylval.text += '\\'; }
  \\&     { ; /* Non-character, used to delimit numeric escapes */ }

  \\a     { yylval.text += '\a'; }
  \\b     { yylval.text += '\b'; }
  \\f     { yylval.text += '\f'; }
  \\n     { yylval.text += '\n'; }
  \\r     { yylval.text += '\r'; }
  \\t     { yylval.text += '\t'; }
  \\v     { yylval.text += '\v'; }

  .     { yylval.text += the_text; }
  \n    {
    BEGIN(INITIAL); yylloc.lines(yyleng); yylloc.step(); line_position = current_position;
    throw mli::directive_parser::syntax_error(yylloc, "Newline in string.");
  }
}



"β"   { BEGIN(line_comment); }

<line_comment>.*\n { BEGIN(INITIAL); yylloc.lines(1); yylloc.step(); line_position = current_position; }


"[β"  { BEGIN(block_comment); directive_comment_level = 1; }

<block_comment>{ /* Block comments. */
  "β]" { /* End of the comment. */
    if (--directive_comment_level == 0) {
      BEGIN INITIAL;
    }
  }

  "[β"        { directive_comment_level++; }
  [^\xe2[\n]+ {}
  \n+         { yylloc.lines(yyleng); yylloc.step(); line_position = current_position; }
  .           { /* Stray characters ignored, including β and [. */ }

  <<EOF>> {
    BEGIN(INITIAL);
    throw mli::directive_parser::syntax_error(yylloc,
      "Nested comments not properly closed at end of directive.");
  }
}

"β]"  {
  std::cout << "Dash" << std::endl;
  BEGIN(INITIAL);
  throw mli::directive_parser::syntax_error(yylloc, "No block comment open [β to match the close β].");
}


"\""      { yylval.text.clear(); BEGIN(C_string); }


<C_string>{
  "\""   { /* Closing quote - all done. */ BEGIN(INITIAL); return mli::directive_parser::token::plain_name; }
  \n     {
    BEGIN(INITIAL); yylloc.lines(yyleng); yylloc.step(); line_position = current_position;
    throw mli::directive_parser::syntax_error(yylloc, "Unterminated C-string.");
  }

	\\[0-7]{1,3} { /* Octal escape sequence. */
	  int result;
	  std::sscanf(yytext + 1, "%o", &result);
	  if (result > 0xff) {
      BEGIN(INITIAL);
      throw mli::directive_parser::syntax_error(yylloc,
        "String octal escape " + the_text + " is out-of-bounds, must be β€ \\377.");
    }
	  yylval.text += (char)result;
	}

	\\x[[:xdigit:]]{1,2} { /* Hexadecimal escape sequence. */
	  int result;
	  std::sscanf(yytext + 2, "%x", &result);
	  if (result > 0xff) {
      BEGIN(INITIAL);
      throw mli::directive_parser::syntax_error(yylloc,
        "String hexadecimal escape " + the_text + " is out-of-bounds, must be β€ \\xff.");
    }
	  yylval.text += (char)result;
	}

  \\[0-9]+    {
    BEGIN(INITIAL);
    throw mli::directive_parser::syntax_error(yylloc,
      "Bad string escape sequence " + the_text);
  }

  \\{2}   { yylval.text += '\\'; }
  \\&     { ; /* Non-character, used to delimit numeric escapes */ }

  \\a     { yylval.text += '\a'; }
  \\b     { yylval.text += '\b'; }
  \\f     { yylval.text += '\f'; }
  \\n     { yylval.text += '\n'; }
  \\r     { yylval.text += '\r'; }
  \\t     { yylval.text += '\t'; }
  \\v     { yylval.text += '\v'; }

  \\.     { yylval.text += yytext[1]; }
  \\(\n)  { yylval.text += yytext[1]; yylloc.lines(yyleng); yylloc.step(); line_position = current_position; }
  [^\\\n\"]+  { /* " */ yylval.text += the_text; }
}


{utf8char}   { get_text;
  throw mli::directive_parser::syntax_error(yylloc, "invalid character \"" + yylval.text + "\""); }

.     { std::stringstream ss;
        ss << std::hex << std::uppercase << (unsigned)(unsigned char)yytext[0] << "β";
        throw mli::directive_parser::syntax_error(yylloc, "invalid byte " + ss.str()); }

"β}"  { return EOF; }

<<EOF>> { return EOF; }

%%

