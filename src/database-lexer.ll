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

#include "database-parser.hh"

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

std::vector<std::string> dirs; // Directory search-paths; for included files.

bool verbose = false;

bool declaration_context = false;
bool binder_declaration_context = false;
bool meta_context = false;
bool maybe_set_declaration_context = false;
bool proofline_database_context = false;
bool statement_substitution_context = false;
int bracket_depth = 0;
mli::database_parser::token_type declared_token = mli::free_variable_context;
int declared_type = 0;

int current_token = 0;

std::istream* current_istream;

std::stack<YY_BUFFER_STATE> include_stack;
std::stack<mli::location_type> location_stack;

std::stack<std::istream::pos_type> current_position_stack;
std::istream::pos_type current_position = 0;

std::stack<std::istream::pos_type> line_position_stack;
std::istream::pos_type line_position = 0;

std::stack<std::string> filename_stack;
std::stack<std::string> filepath_stack;

int logic_prefix_count = 0;

bool old_line_comment = false;
bool old_block_comment = false;

std::string str;

mli::kleenean directive_type = false;

mli::location_type loc0, loc1;

%}

%option noyywrap
%option c++
%option yyclass="mli::database_lexer"

%option stack

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


bold-upper  "𝐀"|"𝐁"|"𝐂"|"𝐃"|"𝐄"|"𝐅"|"𝐆"|"𝐇"|"𝐈"|"𝐉"|"𝐊"|"𝐋"|"𝐌"|"𝐍"|"𝐎"|"𝐏"|"𝐐"|"𝐑"|"𝐒"|"𝐓"|"𝐔"|"𝐕"|"𝐖"|"𝐗"|"𝐘"|"𝐙"
bold-lower  "𝐚"|"𝐛"|"𝐜"|"𝐝"|"𝐞"|"𝐟"|"𝐠"|"𝐡"|"𝐢"|"𝐣"|"𝐤"|"𝐥"|"𝐦"|"𝐧"|"𝐨"|"𝐩"|"𝐪"|"𝐫"|"𝐬"|"𝐭"|"𝐮"|"𝐯"|"𝐰"|"𝐱"|"𝐲"|"𝐳"
bold-digit  "𝟎"|"𝟏"|"𝟐"|"𝟑"|"𝟒"|"𝟓"|"𝟔"|"𝟕"|"𝟖"|"𝟗"

bold    {bold-upper}|{bold-lower}


italic-upper  "𝐴"|"𝐵"|"𝐶"|"𝐷"|"𝐸"|"𝐹"|"𝐺"|"𝐻"|"𝐼"|"𝐽"|"𝐾"|"𝐿"|"𝑀"|"𝑁"|"𝑂"|"𝑃"|"𝑄"|"𝑅"|"𝑆"|"𝑇"|"𝑈"|"𝑉"|"𝑊"|"𝑋"|"𝑌"|"𝑍"
italic-lower  "𝑎"|"𝑏"|"𝑐"|"𝑑"|"𝑒"|"𝑓"|"𝑔"|"ℎ"|"𝑖"|"𝑗"|"𝑘"|"𝑙"|"𝑚"|"𝑛"|"𝑜"|"𝑝"|"𝑞"|"𝑟"|"𝑠"|"𝑡"|"𝑢"|"𝑣"|"𝑤"|"𝑥"|"𝑦"|"𝑧"

italic    {italic-upper}|{italic-lower}


bold-italic-upper   "𝑨"|"𝑩"|"𝑪"|"𝑫"|"𝑬"|"𝑭"|"𝑮"|"𝑯"|"𝑰"|"𝑱"|"𝑲"|"𝑳"|"𝑴"|"𝑵"|"𝑶"|"𝑷"|"𝑸"|"𝑹"|"𝑺"|"𝑻"|"𝑼"|"𝑽"|"𝑾"|"𝑿"|"𝒀"|"𝒁"
bold-italic-lower   "𝒂"|"𝒃"|"𝒄"|"𝒅"|"𝒆"|"𝒇"|"𝒈"|"𝒉"|"𝒊"|"𝒋"|"𝒌"|"𝒍"|"𝒎"|"𝒏"|"𝒐"|"𝒑"|"𝒒"|"𝒓"|"𝒔"|"𝒕"|"𝒖"|"𝒗"|"𝒘"|"𝒙"|"𝒚"|"𝒛"

bold-italic  {bold-italic-upper}|{bold-italic-lower}


script-upper   "𝒜"|"ℬ"|"𝒞"|"𝓓"|"ℰ"|"ℱ"|"𝒢"|"ℋ"|"ℐ"|"𝒥"|"𝒦"|"ℒ"|"ℳ"|"𝒩"|"𝒪"|"𝒫"|"𝒬"|"ℛ"|"𝒮"|"𝒯"|"𝒰"|"𝒱"|"𝒲"|"𝒳"|"𝒴"|"𝒵"
script-lower   "𝒶"|"𝒷"|"𝒸"|"𝒹"|"ℯ"|"𝒻"|"ℊ"|"𝒽"|"𝒾"|"𝒿"|"𝓀"|"𝓁"|"𝓂"|"𝓃"|"ℴ"|"𝓅"|"𝓆"|"𝓇"|"𝓈"|"𝓊"|"𝓋"|"𝓌"|"𝓍"|"𝓎"|"𝓏"

script  {script-upper}|{script-lower}


script-bold-upper   "𝓐"|"𝓑"|"𝓒"|"𝓓"|"𝓔"|"𝓕"|"𝓖"|"𝓗"|"𝓘"|"𝓙"|"𝓚"|"𝓛"|"𝓜"|"𝓝"|"𝓞"|"𝓟"|"𝓠"|"𝓡"|"𝓢"|"𝓣"|"𝓤"|"𝓥"|"𝓦"|"𝓧"|"𝓨"|"𝓩"
script-bold-lower   "𝓪"|"𝓫"|"𝓬"|"𝓭"|"𝓮"|"𝓯"|"𝓰"|"𝓱"|"𝓲"|"𝓳"|"𝓴"|"𝓵"|"𝓶"|"𝓷"|"𝓸"|"𝓹"|"𝓺"|"𝓻"|"𝓼"|"𝓽"|"𝓾"|"𝓿"|"𝔀"|"𝔁"|"𝔂"|"𝔃"

script-bold  {script-bold-upper}|{script-bold-lower}


fraktur-upper   "𝔄"|"𝔅"|"ℭ"|"𝔇"|"𝔈"|"𝔉"|"𝔊"|"ℌ"|"ℑ"|"𝔍"|"𝔎"|"𝔏"|"𝔐"|"𝔑"|"𝔒"|"𝔓"|"𝔔"|"ℜ"|"𝔖"|"𝔗"|"𝔘"|"𝔙"|"𝔚"|"𝔛"|"𝔜"|"ℨ"
fraktur-lower   "𝔞"|"𝔟"|"𝔠"|"𝔡"|"𝔢"|"𝔣"|"𝔤"|"𝔥"|"𝔦"|"𝔧"|"𝔨"|"𝔩"|"𝔪"|"𝔫"|"𝔬"|"𝔭"|"𝔮"|"𝔯"|"𝔰"|"𝔱"|"𝔲"|"𝔳"|"𝔴"|"𝔵"|"𝔶"|"𝔷"

fraktur  {fraktur-upper}|{fraktur-lower}


fraktur-bold-upper  "𝕬"|"𝕭"|"𝕮"|"𝕯"|"𝕰"|"𝕱"|"𝕲"|"𝕳"|"𝕴"|"𝕵"|"𝕶"|"𝕷"|"𝕸"|"𝕹"|"𝕺"|"𝕻"|"𝕼"|"𝕽"|"𝕾"|"𝕿"|"𝖀"|"𝖁"|"𝖂"|"𝖃"|"𝖄"|"𝖅"
fraktur-bold-lower  "𝖆"|"𝖇"|"𝖈"|"𝖉"|"𝖊"|"𝖋"|"𝖌"|"𝖍"|"𝖎"|"𝖏"|"𝖐"|"𝖑"|"𝖒"|"𝖓"|"𝖔"|"𝖕"|"𝖖"|"𝖗"|"𝖘"|"𝖙"|"𝖚"|"𝖛"|"𝖜"|"𝖝"|"𝖞"|"𝖟"

fraktur-bold  {fraktur-bold-upper}|{fraktur-bold-lower}


double-struck-upper   "𝔸"|"𝔹"|"ℂ"|"𝔻"|"𝔼"|"𝔽"|"𝔾"|"ℍ"|"𝕀"|"𝕁"|"𝕂"|"𝕃"|"𝕄"|"ℕ"|"𝕆"|"ℙ"|"ℚ"|"ℝ"|"𝕊"|"𝕋"|"𝕌"|"𝕍"|"𝕎"|"𝕏"|"𝕐"|"ℤ"
double-struck-lower   "𝕒"|"𝕓"|"𝕔"|"𝕕"|"𝕖"|"𝕗"|"𝕘"|"𝕙"|"𝕚"|"𝕛"|"𝕜"|"𝕝"|"𝕞"|"𝕟"|"𝕠"|"𝕡"|"𝕢"|"𝕣"|"𝕤"|"𝕥"|"𝕦"|"𝕧"|"𝕨"|"𝕩"|"𝕪"|"𝕫"
double-struck-digit   "𝟘"|"𝟙"|"𝟚"|"𝟛"|"𝟜"|"𝟝"|"𝟞"|"𝟟"|"𝟠"|"𝟡"

double-struck   {double-struck-upper}|{double-struck-lower}


greek-upper  "Α"|"Β"|"Γ"|"Δ"|"Ε"|"Ζ"|"Η"|"Θ"|"Ι"|"Κ"|"Λ"|"Μ"|"Ν"|"Ξ"|"Ο"|"Π"|"Ρ"|"ϴ"|"Σ"|"Τ"|"Υ"|"Φ"|"Χ"|"Ψ"|"Ω"
greek-lower  "α"|"β"|"γ"|"δ"|"ε"|"ζ"|"η"|"θ"|"ι"|"κ"|"λ"|"μ"|"ν"|"ξ"|"ο"|"π"|"ρ"|"ς"|"σ"|"τ"|"υ"|"φ"|"χ"|"ψ"|"ω"|"ϵ"|"ϑ"|"ϰ"|"ϕ"|"ϱ"|"ϖ"

greek  {greek-upper}|{greek-lower}


greek-bold-upper    "𝚨"|"𝚩"|"𝚪"|"𝚫"|"𝚬"|"𝚭"|"𝚮"|"𝚯"|"𝚰"|"𝚱"|"𝚲"|"𝚳"|"𝚴"|"𝚵"|"𝚶"|"𝚷"|"𝚸"|"𝚹"|"𝚺"|"𝚻"|"𝚼"|"𝚽"|"𝚾"|"𝚿"|"𝛀"
greek-bold-lower    "𝛂"|"𝛃"|"𝛄"|"𝛅"|"𝛆"|"𝛇"|"𝛈"|"𝛉"|"𝛊"|"𝛋"|"𝛌"|"𝛍"|"𝛎"|"𝛏"|"𝛐"|"𝛑"|"𝛒"|"𝛓"|"𝛔"|"𝛕"|"𝛖"|"𝛗"|"𝛘"|"𝛙"|"𝛚"|"𝛜"|"𝛝"|"𝛞"|"𝛟"|"𝛠"|"𝛡"

greek-bold  {greek-bold-upper}|{greek-bold-lower}


greek-italic-upper  "𝛢"|"𝛣"|"𝛤"|"𝛥"|"𝛦"|"𝛧"|"𝛨"|"𝛩"|"𝛪"|"𝛫"|"𝛬"|"𝛭"|"𝛮"|"𝛯"|"𝛰"|"𝛱"|"𝛲"|"𝛳"|"𝛴"|"𝛵"|"𝛶"|"𝛷"|"𝛸"|"𝛹"|"𝛺"
greek-italic-lower  "𝛼"|"𝛽"|"𝛾"|"𝛿"|"𝜀"|"𝜁"|"𝜂"|"𝜃"|"𝜄"|"𝜅"|"𝜆"|"𝜇"|"𝜈"|"𝜉"|"𝜊"|"𝜋"|"𝜌"|"𝜍"|"𝜎"|"𝜏"|"𝜐"|"𝜑"|"𝜒"|"𝜓"|"𝜔"|"𝜖"|"𝜗"|"𝜘"|"𝜙"|"𝜚"|"𝜛"

greek-italic  {greek-italic-upper}|{greek-italic-lower}


greek-bold-italic-upper   "𝜜"|"𝜝"|"𝜞"|"𝜟"|"𝜠"|"𝜡"|"𝜢"|"𝜣"|"𝜤"|"𝜥"|"𝜦"|"𝜧"|"𝜨"|"𝜩"|"𝜪"|"𝜫"|"𝜬"|"𝜭"|"𝜮"|"𝜯"|"𝜰"|"𝜱"|"𝜲"|"𝜳"|"𝜴"
greek-bold-italic-lower   "𝜶"|"𝜷"|"𝜸"|"𝜹"|"𝜺"|"𝜻"|"𝜼"|"𝜽"|"𝜾"|"𝜿"|"𝝀"|"𝝁"|"𝝂"|"𝝃"|"𝝄"|"𝝅"|"𝝆"|"𝝇"|"𝝈"|"𝝉"|"𝝊"|"𝝋"|"𝝌"|"𝝍"|"𝝎"|"𝝐"|"𝝑"|"𝝒"|"𝝓"|"𝝔"|"𝝕"

greek-bold-italic  {greek-bold-italic-upper}|{greek-bold-italic-lower}


identifier  ([[:alpha:]]+|{bold}+|{italic}+|{bold-italic}+|{script}+|{script-bold}+|{fraktur}+|{fraktur-bold}+|{double-struck}+|{greek}+|{greek-bold}+|{greek-italic}+|{greek-bold-italic}+)

logic_prefix_identifier  ([[:alpha:]]|{bold}|{italic}|{bold-italic}|{script}|{script-bold}|{fraktur}|{fraktur-bold}|{double-struck}|{greek}|{greek-bold}|{greek-italic}|{greek-bold-italic})

label       [[:alnum:]]+

/*
whitespace
" " U+2002 en space
" " U+2003 em space
" " U+2004 three-per-em space
" " U+2005 four-per-em space
" " U+2006 six-per-em space
" " U+2007 figure space
" " U+2008 punctuation space
" " U+2009 thin space
" " U+200A hair space
" " U+205F medium mathematical space
*/
whitespace  [ \f\r\t\v]|" "|" "|" "|" "|" "|" "|" "|" "|" "|" "

comment_begin "[*"
comment_end   "*]"

subscript_digit     "₀"|"₁"|"₂"|"₃"|"₄"|"₅"|"₆"|"₇"|"₈"|"₉"
superscript_digit   "⁰"|"¹"|"²"|"³"|"⁴"|"⁵"|"⁶"|"⁷"|"⁸"|"⁹"

subscript_sign   "₊"|"₋"
superscript_sign "⁺"|"⁻"

/* UTF-8 character with valid Unicode code point. */
utf8char    [\x09\x0A\x0D\x20-\x7E]|[\xC2-\xDF][\x80-\xBF]|\xE0[\xA0-\xBF][\x80-\xBF]|[\xE1-\xEC\xEE\xEF]([\x80-\xBF]{2})|\xED[\x80-\x9F][\x80-\xBF]|\xF0[\x\90-\xBF]([\x80-\xBF]{2})|[\xF1-\xF3]([\x80-\xBF]{3})|\xF4[\x80-\x8F]([\x80-\xBF]{2})


%{
#define YY_USER_ACTION  yylloc.columns(length_utf8(yytext)); current_position += yyleng;
%}


%%
%{
  mli::semantic_type& yylval = *yylvalp;
  mli::location_type& yylloc = *yyllocp;
  current_istream = yyin;

  if (current_token != 0) { int tok = current_token; current_token = 0; return tok; }

  yylloc.step();
%}

{whitespace}+ { yylloc.step(); }
\n+           { yylloc.lines(yyleng); yylloc.step(); line_position = current_position; }


"input"    { BEGIN(include_file); }

<include_file>[[:space:]]*      /* Eat the whitespace. */

<include_file>[[:^space:]]+|(\".+\")  { /* Get the include file name. */
  include_stack.push(YY_CURRENT_BUFFER);
  std::string str;

  if (yytext[0] == '"')
    str.append(yytext + 1, yyleng - 2);
  else
    str.append(yytext, yyleng);

  std::string path = str; // Full path of file str relative dir directory paths if needed.

  yyin = new std::ifstream(str);

  if (!*yyin) {
    delete yyin;
    yyin = nullptr;

    // Opening file str failed, so try with directory paths prepended:
    for (auto& i: dirs) {
      path = (i.back() == '/')? i : i + "/";
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
      throw mli::database_parser::syntax_error(yylloc, "File " + str + " not found.");
    }
  }

  current_istream = yyin;

  filename_stack.push(str);
  filepath_stack.push(path);

  std::cout << "Begin reading " << filename_stack.top();
  if (filename_stack.top() != filepath_stack.top())
    std::cout << " (" << filepath_stack.top() << ")";
  std::cout << std::endl;

  location_stack.push(yylloc);

  current_position_stack.push(current_position);
  current_position = 0;

  line_position_stack.push(line_position);
  line_position = 0;

  yylloc.initialize(&filepath_stack.top());

  yy_switch_to_buffer(yy_create_buffer(yyin, YY_BUF_SIZE));
  BEGIN(INITIAL);
}


"include"    { get_text; return mli::database_parser::token::include_key; }
"end"        { get_text; return mli::database_parser::token::end_key; }

"formal"[[:space:]]+"system" { get_text; return mli::database_parser::token::formal_system_key; }
"theory"     { get_text; return mli::database_parser::token::theory_key; }

"postulate"  { get_text; return mli::database_parser::token::postulate_key; }
"axiom"      { get_text; return mli::database_parser::token::axiom_key; }
"rule"       { get_text; return mli::database_parser::token::rule_key; }
"conjecture" { get_text; return mli::database_parser::token::conjecture_key; }

"definition" { get_text; return mli::database_parser::token::definition_key; }

"lemma"       { get_text; yylval.number = mli::theorem::lemma_; return mli::database_parser::token::theorem_key; }
"proposition" { get_text; yylval.number = mli::theorem::proposition_; return mli::database_parser::token::theorem_key; }
"theorem"     { get_text; yylval.number = mli::theorem::theorem_; return mli::database_parser::token::theorem_key; }
"corollary"   { get_text; yylval.number = mli::theorem::corollary_; return mli::database_parser::token::theorem_key; }

"proof"       { get_text; return mli::database_parser::token::proof_key; }
"∎"           { get_text; return mli::database_parser::token::end_of_proof_key; }

"by"         { get_text;
               proofline_database_context = true;
               bracket_depth = 0;
               statement_substitution_context = false;
               return mli::database_parser::token::by_key; }

"result"      { get_text; return mli::database_parser::token::result_key; }
"premise"     { get_text; return mli::database_parser::token::premise_key; }


"⊩"    { return mli::database_parser::token::metainfer_key; }

"or"   { return mli::database_parser::token::metaor_key; }
"and"  { return mli::database_parser::token::metaand_key; }
"not"  { get_text; return mli::database_parser::token::metanot_key; }


"⊢"   { return mli::database_parser::token::infer_key; }

"≡"   { get_text; return mli::database_parser::token::object_identical_key; }
"≢"   { get_text; return mli::database_parser::token::object_not_identical_key; }
"≣"   { get_text; return mli::database_parser::token::meta_identical_key; }
"≣̷"   { get_text; return mli::database_parser::token::meta_not_identical_key; }

"fail"    { get_text; return mli::database_parser::token::fail_key; }
"succeed" { get_text; return mli::database_parser::token::succeed_key; }

"free"[[:space:]]+"for" { get_text; meta_context = true; return mli::database_parser::token::free_for_key; }
"free"[[:space:]]+"in"  { get_text; return mli::database_parser::token::free_in_key; }

"in"     { get_text; meta_context = false; return mli::database_parser::token::metain_key; }


"use" { get_text; return mli::database_parser::token::use_key; }

"≔"        { return mli::database_parser::token::defined_by_key; }
"≕"        { return mli::database_parser::token::defines_key; }
"≝"        { return mli::database_parser::token::defined_equal_key; }

"metaformula" { declaration_context = true; declared_token = mli::database_parser::token::metaformula_variable;
#if USE_VARIABLE_META
            declared_type = mli::variable::metaformula_;
#else
            declared_type = mli::variable::formula_;
#endif
             return mli::database_parser::token::identifier_variable_key; }

"formula"[[:space:]]+"sequence" { declaration_context = true; declared_token = mli::database_parser::token::metaformula_variable;
            declared_type = mli::variable::formula_sequence_; return mli::database_parser::token::identifier_variable_key; }

"formula" { declaration_context = true; declared_token = mli::database_parser::token::object_formula_variable;
            declared_type = mli::variable::formula_; return mli::database_parser::token::identifier_variable_key; }
"predicate"[[:space:]]+"variable" {
             declaration_context = true; declared_token = mli::database_parser::token::predicate_variable;
             declared_type = mli::variable::predicate_; return mli::database_parser::token::identifier_variable_key; }
"atom"[[:space:]]+"variable" {
            declaration_context = true; declared_token = mli::database_parser::token::atom_variable;
            declared_type = mli::variable::atom_; return mli::database_parser::token::identifier_variable_key; }

"function"[[:space:]]+"variable" {
            declaration_context = true; declared_token = mli::database_parser::token::function_variable;
            declared_type = mli::variable::function_; return mli::database_parser::token::identifier_variable_key; }

"object"  { declaration_context = true; declared_token = mli::database_parser::token::object_variable;
            declared_type = mli::variable::object_; return mli::database_parser::token::identifier_variable_key; }

"code"     { declaration_context = true; declared_token = mli::database_parser::token::code_variable;
             declared_type = mli::variable::code_; return mli::database_parser::token::identifier_variable_key; }

"∀"   { bound_variable_type = database_parser::token::all_variable; symbol_table.push_level(false);
        return mli::database_parser::token::all_key; }
"∃"   { bound_variable_type = database_parser::token::exist_variable; symbol_table.push_level(false);
        return mli::database_parser::token::exist_key; }


"function" {
            declaration_context = true; declared_token = mli::database_parser::token::function_key;
            declared_type = mli::term_type_; return mli::database_parser::token::identifier_function_key; }
"predicate" {
            declaration_context = true; declared_token = mli::database_parser::token::predicate_key;
            declared_type = mli::object_formula_type_; return mli::database_parser::token::identifier_function_key; }


"metapredicate" { declaration_context = true; declared_token = mli::database_parser::token::metapredicate_constant;
               declared_type = mli::metaformula_type_; return mli::database_parser::token::identifier_constant_key; }
"predicate"[[:space:]]+"constant" {
            declaration_context = true; declared_token = mli::database_parser::token::predicate_constant;
            declared_type = mli::object_formula_type_; return mli::database_parser::token::identifier_constant_key; }
"atom"       { declaration_context = true; declared_token = mli::database_parser::token::atom_constant;
               declared_type = mli::object_formula_type_; return mli::database_parser::token::identifier_constant_key; }

"function"[[:space:]]+"constant" {
            declaration_context = true; declared_token = mli::database_parser::token::function_constant;
            declared_type = mli::term_type_; return mli::database_parser::token::identifier_constant_key; }
"constant"   { declaration_context = true; declared_token = mli::database_parser::token::term_constant;
               declared_type = mli::term_type_; return mli::database_parser::token::identifier_constant_key; }

"⇒"   { get_text; return mli::database_parser::token::implies_key; }
"⇐"   { get_text; return mli::database_parser::token::impliedby_key; }
"⇔"  { get_text; return mli::database_parser::token::equivalent_key; }

"∧"  { get_text; return mli::database_parser::token::logical_and_key; }
"∨"   { get_text; return mli::database_parser::token::logical_or_key; }
"¬"   { get_text; return mli::database_parser::token::logical_not_key; }

":"  { declaration_context = false;
       bound_variable_type = free_variable_context;
       return mli::database_parser::token::colon_key; }
","  { return mli::database_parser::token::comma_key; }
"."  { declaration_context = false;
       bound_variable_type = free_variable_context;
       return mli::database_parser::token::period_key; }

";"  { return mli::database_parser::token::semicolon_key; }


"<"  { get_text; return mli::database_parser::token::less_key; }
">"  { get_text; return mli::database_parser::token::greater_key; }
"≤"  { get_text; return mli::database_parser::token::less_or_equal_key; }
"≥"  { get_text; return mli::database_parser::token::greater_or_equal_key; }

"≮"  { get_text; return mli::database_parser::token::not_less_key; }
"≯"  { get_text; return mli::database_parser::token::not_greater_key; }
"≰"  { get_text; return mli::database_parser::token::not_less_or_equal_key; }
"≱"  { get_text; return mli::database_parser::token::not_greater_or_equal_key; }

"="  { get_text; return mli::database_parser::token::equal_key; }
"≠"  { get_text; return mli::database_parser::token::not_equal_key; }


"↦" { get_text; bound_variable_type = free_variable_context; return mli::database_parser::token::mapsto_key; }
"⤇" { get_text; return mli::database_parser::token::Mapsto_key; }

"𝛌" { get_text; bound_variable_type = database_parser::token::function_map_variable; symbol_table.push_level(false);
      return mli::database_parser::token::function_map_prefix_key; }

"°"  { get_text; return mli::database_parser::token::degree_key; }
"•"  { get_text; return mli::database_parser::token::bullet_key; }

"ₓ" { get_text; return mli::database_parser::token::subscript_x_key; }


"("  { return mli::database_parser::token::left_parenthesis_key; }
")"  { return mli::database_parser::token::right_parenthesis_key; }

"⁽"  { return mli::database_parser::token::superscript_left_parenthesis_key; }
"⁾"  { return mli::database_parser::token::superscript_right_parenthesis_key; }

"₍"  { return mli::database_parser::token::subscript_left_parenthesis_key; }
"₎"  { return mli::database_parser::token::subscript_right_parenthesis_key; }


"["  { if (proofline_database_context)
         ++bracket_depth;
       if (bracket_depth == 1)
         statement_substitution_context = true;
       return mli::database_parser::token::left_bracket_key; }
"]"  { if (proofline_database_context)
         --bracket_depth;
       return mli::database_parser::token::right_bracket_key; }

"⟨"  { return mli::database_parser::token::left_angle_bracket_key; }
"⟩"  { return mli::database_parser::token::right_angle_bracket_key; }

"{"  { maybe_set_declaration_context = true;
       BEGIN(find_set_variable);
       return mli::database_parser::token::left_brace_key; }
"|"  { return mli::database_parser::token::vertical_line_key; }
"}"  { return mli::database_parser::token::right_brace_key; }

"~"  { return mli::database_parser::token::tilde_key; }

<find_set_variable>{
  {whitespace}+ { yylloc.step(); }
  \n+           { yylloc.lines(yyleng); yylloc.step(); line_position = current_position; }
}

<find_vertical_line>{
  {whitespace}+ { yylloc.step(); }
  \n+           { yylloc.lines(yyleng); yylloc.step(); line_position = current_position; }

  "|"|"∈" {
    // The set bar | as in {𝒙|𝑨}, or ∈ as in {𝒙∈𝑆|𝑨} has been found, so 𝒙 in yylval.text
    // should be defined at a new symbol table secondary level as a bound set variable.
    // Save "|" in current_token so that it will returned on the next lexer call.
    if (std::string(yytext, yyleng) == "|")
      current_token = mli::database_parser::token::vertical_line_key;
    else
      current_token = mli::database_parser::token::in_key;
    bound_variable_type = database_parser::token::set_variable;
    maybe_set_declaration_context = false;
    BEGIN(INITIAL);

    symbol_table.push_level(false);
    database_parser::token_type ret = define_variable(yylval);
    bound_variable_type = mli::free_variable_context;
    return database_parser::token::set_variable_definition;
  }

  .   { yyless(0); BEGIN(INITIAL); maybe_set_declaration_context = false;
      database_parser::token_type ret = define_variable(yylval);
      return ret;
  }
}


"Set"  {
    bound_variable_type = database_parser::token::is_set_variable;
    get_text;
    return mli::database_parser::token::is_set_key; }
"Pow"  {
    bound_variable_type = database_parser::token::is_set_variable;
    get_text;
    return mli::database_parser::token::power_set_key; }

"∅"    { get_text; return mli::database_parser::token::empty_set_key; }
"∈"    { get_text; return mli::database_parser::token::in_key; }
"∉"    { get_text; return mli::database_parser::token::not_in_key; }

"∁"    { get_text; return mli::database_parser::token::set_complement_key; }
"∪"    { get_text; return mli::database_parser::token::set_union_key; }
"∩"    { get_text; return mli::database_parser::token::set_intersection_key; }
"∖"    { get_text; return mli::database_parser::token::set_difference_key; }
"⋃"    { get_text; return mli::database_parser::token::set_union_operator_key; }
"⋂"    { get_text; return mli::database_parser::token::set_intersection_operator_key; }
"⊆"    { get_text; return mli::database_parser::token::subset_key; }
"⊊"    { get_text; return mli::database_parser::token::proper_subset_key; }
"⊇"    { get_text; return mli::database_parser::token::superset_key; }
"⊋"    { get_text; return mli::database_parser::token::proper_superset_key; }


"/"   { get_text; return mli::database_parser::token::slash_key; }
"\\"  { get_text; return mli::database_parser::token::backslash_key; }


"!"   { get_text; return mli::database_parser::token::factorial_key; }

"⋅"   { get_text; return mli::database_parser::token::mult_key; }
"+"   { get_text; return mli::database_parser::token::plus_key; }
"-"   { get_text; return mli::database_parser::token::minus_key; }


"if"    { return mli::database_parser::token::if_key; }
"then"  { return mli::database_parser::token::then_key; }
"else"  { return mli::database_parser::token::else_key; }

"while" { return mli::database_parser::token::while_key; }
"do"    { return mli::database_parser::token::do_key; }
"loop"  { return mli::database_parser::token::loop_key; }
"for"   { return mli::database_parser::token::for_key; }

"break"     { return mli::database_parser::token::break_key; }
"continue"  { return mli::database_parser::token::continue_key; }

"throw"  { return mli::database_parser::token::throw_key; }
"try"    { return mli::database_parser::token::try_key; }
"catch"  { return mli::database_parser::token::catch_key; }


[[:digit:]]+ {
  get_text;
  yylval.object = mli::ref<mli::integer>(mli::make, yytext);
  return mli::database_parser::token::natural_number_value;
}

[+-][[:digit:]]+ {
  get_text;
  yylval.object = mli::ref<mli::integer>(mli::make, yytext);
  return mli::database_parser::token::integer_value;
}


{subscript_digit}+ {
  get_text;
  yylval.object = mli::ref<mli::integer>(mli::make, subscript_to_string(yytext));
  return mli::database_parser::token::subscript_natural_number_value;
}

("₊"|"₋"){subscript_digit}+ {
  get_text;
  yylval.object = mli::ref<mli::integer>(mli::make, subscript_to_string(yytext));
  return mli::database_parser::token::subscript_integer_value;
}


{superscript_digit}+ {
  get_text;
  yylval.object = mli::ref<mli::integer>(mli::make, superscript_to_string(yytext));
  return mli::database_parser::token::superscript_natural_number_value;
}

("⁺"|"⁻"){superscript_digit}+ {
  get_text;
  yylval.object = mli::ref<mli::integer>(mli::make, superscript_to_string(yytext));
  return mli::database_parser::token::superscript_integer_value;
}




<INITIAL,find_set_variable>{identifier} {
  get_text;

  if (maybe_set_declaration_context) {
    BEGIN(find_vertical_line);
    YY_BREAK;
  }

  database_parser::token_type ret = define_variable(yylval);

  return ret;
}


{label} { get_text; return mli::database_parser::token::label_key; }


<INITIAL,find_set_variable>"“" { yylval.text.clear(); BEGIN(any_identifier); }

<any_identifier>{
  "”" { /* Closing quote - all done. Text now in yylval.text. */
    BEGIN(INITIAL);

    database_parser::token_type ret = define_variable(yylval);

    if (maybe_set_declaration_context) {
      BEGIN(find_vertical_line);
      YY_BREAK;
    }

    return ret;
  }

  "“"    {
    BEGIN(INITIAL);
    throw mli::database_parser::syntax_error(yylloc,
     "String with “; an earlier string might be unterminated.");
  }
  "\\“"  { yylval.text += "“"; }
  "\\”"  { yylval.text += "”"; }

	\\[0-7]{1,3} { /* Octal escape sequence. */
	  int result;
	  std::sscanf(yytext + 1, "%o", &result);
	  if (result > 0xff) {
      BEGIN(INITIAL);
      throw mli::database_parser::syntax_error(yylloc,
        "String octal escape " + the_text + " is out-of-bounds, must be ≤ \\ 377.");
    }
	  yylval.text += (char)result;
	}

	\\x[[:xdigit:]]{1,2} { /* Hexadecimal escape sequence. */
	  int result;
	  std::sscanf(yytext + 2, "%x", &result);
	  if (result > 0xff) {
      // Can actually not get here, as scanning for max 2 hex digits!
      BEGIN(INITIAL);
      throw mli::database_parser::syntax_error(yylloc,
        "String hexadecimal escape " + the_text + " is out-of-bounds, must be ≤ \\xff.");
    }
	  yylval.text += (char)result;
	}

	\\[uU][[:xdigit:]]{1,8} { /* Hexadecimal escape sequence to give UTF-8 characters. */
    yylval.text += to_utf8(std::stoul(yytext + 2, nullptr, 16));
	}

  \\[0-9]+   {
    BEGIN(INITIAL);
    throw mli::database_parser::syntax_error(yylloc,
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
    throw mli::database_parser::syntax_error(yylloc, "Newline in string.");
  }
}


<find_set_variable>{
  .   { yyless(0); BEGIN(INITIAL); maybe_set_declaration_context = false; }
}


"Ł"   { logic_prefix_count = 1; BEGIN(logic_prefix); }

<logic_prefix>{
  [[:space:]]+  {}    /* Eat the whitespace. */
  "N"|"¬"   { return mli::database_parser::token::prefix_not_key; }
  "A"|"∨"   { get_text; ++logic_prefix_count; return mli::database_parser::token::prefix_or_key; }
  "K"|"∧"   { get_text; ++logic_prefix_count; return mli::database_parser::token::prefix_and_key; }
  "C"|"⇒"   { get_text; ++logic_prefix_count; return mli::database_parser::token::prefix_implies_key; }
  "E"|"⇔"   { get_text; ++logic_prefix_count; return mli::database_parser::token::prefix_equivalent_key; }
  {logic_prefix_identifier}   {
    get_text;
    --logic_prefix_count;
    if (logic_prefix_count < 1) BEGIN(INITIAL);

    auto x = mli::symbol_table.find(yylval.text);

    if (!x) {
      BEGIN(INITIAL);
      throw mli::database_parser::syntax_error(yylloc,
        "Logic prefix variable " + yylval.text + " is not declared.");
    }

    mli::variable* vp = mli::ref_cast<mli::variable*>(x->second);

    // Check if it is a variable which is declared without definition, in which case make
    // a copy with right proof depth, insert it in the symbol table, and change x->second
    // so subsequently the new copy is used instead of the original lookup value.
    if (vp != nullptr && vp->depth_ == -1) {
      mli::ref<mli::variable> v(make, *vp);
      v->depth_ = proof_depth;
      symbol_table.insert_or_assign(yylval.text, {x->first, v});

      x->second = v;
    }

    if (x->first != mli::database_parser::token::object_formula_variable) {
      BEGIN(INITIAL);
      throw mli::database_parser::syntax_error(yylloc,
        "Logic prefix variable " + yylval.text + " is not of type formula.");
    }
    yylval.object = x->second;
    yylval.number = x->first;
    return mli::database_parser::token::prefix_formula_variable;
  }
  .   {
    BEGIN(INITIAL);
    throw mli::database_parser::syntax_error(yylloc,
      "Logic prefix expression is inconsistent.");
  }
}


"\""      { yylval.text.clear(); BEGIN(C_string); }


"—"   { yy_push_state(line_comment); }

<line_comment>.*\n { yy_pop_state(); yylloc.lines(1); yylloc.step(); line_position = current_position; }


"[—"  { yy_push_state(block_comment); }

<block_comment>{ /* Block comments. */
  "—]"  { yy_pop_state(); /* End of the comment. */ }

  "[—"  { yy_push_state(block_comment); }

  [^\xe2[\n]+ {}
  \n+         { yylloc.lines(yyleng); yylloc.step(); line_position = current_position; }
  .           { /* Stray characters ignored, including — and [. */ }

  <<EOF>> {
    BEGIN(INITIAL);
    throw mli::database_parser::syntax_error(yylloc,
      "Nested comments not properly closed at end of file.");
  }
}

"—]"  {
  BEGIN(INITIAL);
  throw mli::database_parser::syntax_error(yylloc,
    "No block comment open [— earlier to match the close —] at this location.");
}


"{—"  { yylloc.step();
    int r = directive_read(*yyin, yylloc);

    if (r != 0) {
      BEGIN(INITIAL);
      throw mli::database_parser::syntax_error(yylloc, "Directive syntax error.");
    }
}


"—}"  {
  BEGIN(INITIAL);
  throw mli::database_parser::syntax_error(yylloc, "No directive open {— to match the close —}.");
}


<C_string>{
  "\""   { /* Closing quote - all done. */ BEGIN(INITIAL); return mli::database_parser::token::plain_name; }
  \n     {
    BEGIN(INITIAL); yylloc.lines(yyleng); yylloc.step(); line_position = current_position;
    throw mli::database_parser::syntax_error(yylloc, "Unterminated C-string.");
  }

	\\[0-7]{1,3} { /* Octal escape sequence. */
	  int result;
	  std::sscanf(yytext + 1, "%o", &result);
	  if (result > 0xff) {
      BEGIN(INITIAL);
      throw mli::database_parser::syntax_error(yylloc,
        "String octal escape " + the_text + " is out-of-bounds, must be ≤ \\377.");
    }
	  yylval.text += (char)result;
	}

	\\x[[:xdigit:]]{1,2} { /* Hexadecimal escape sequence. */
	  int result;
	  std::sscanf(yytext + 2, "%x", &result);
	  if (result > 0xff) {
      BEGIN(INITIAL);
      throw mli::database_parser::syntax_error(yylloc,
        "String hexadecimal escape " + the_text + " is out-of-bounds, must be ≤ \\xff.");
    }
	  yylval.text += (char)result;
	}

  \\[0-9]+    {
    BEGIN(INITIAL);
    throw mli::database_parser::syntax_error(yylloc,
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
  throw mli::database_parser::syntax_error(yylloc, "invalid character \"" + yylval.text + "\""); }

.     { std::stringstream ss;
        ss << std::hex << std::uppercase << (unsigned)(unsigned char)yytext[0] << "ₓ";
        throw mli::database_parser::syntax_error(yylloc, "invalid byte " + ss.str()); }

<<EOF>> {
  if (include_stack.empty())
    return EOF;

  delete yyin; // yyin is not deleted by yy_delete_buffer.
  yyin = nullptr;

  yy_delete_buffer(YY_CURRENT_BUFFER);
  yy_switch_to_buffer(include_stack.top());
  include_stack.pop();
  current_istream = yyin;

  yylloc = location_stack.top();
  location_stack.pop();

  current_position = current_position_stack.top();
  current_position_stack.pop();

  line_position = line_position_stack.top();
  line_position_stack.pop();

  yylloc.step();

  std::cout << "End reading " << filename_stack.top();
  if (filename_stack.top() != filepath_stack.top())
    std::cout << " (" << filepath_stack.top() << ")";
  std::cout << std::endl;

  filename_stack.pop();
  filepath_stack.pop();

  std::cout << "Continue reading " << yylloc << std::endl;
}

%%

