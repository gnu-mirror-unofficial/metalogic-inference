// A Bison parser, made by GNU Bison 3.0.4.

// Skeleton implementation for Bison LALR(1) parsers in C++

// Copyright (C) 2002-2015 Free Software Foundation, Inc.

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

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

// Take the name prefix into account.
#define yylex   mlilex

// First part of user declarations.

#line 39 "parser.cc" // lalr1.cc:404

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

#include "parser.hh"

// User implementation prologue.

#line 53 "parser.cc" // lalr1.cc:412
// Unqualified %code blocks.
#line 74 "parser.yy" // lalr1.cc:413


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


#line 138 "parser.cc" // lalr1.cc:413


#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> // FIXME: INFRINGES ON USER NAME SPACE.
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif



// Suppress unused-variable warnings by "using" E.
#define YYUSE(E) ((void) (E))

// Enable debugging if requested.
#if YYDEBUG

// A pseudo ostream that takes yydebug_ into account.
# define YYCDEBUG if (yydebug_) (*yycdebug_)

# define YY_SYMBOL_PRINT(Title, Symbol)         \
  do {                                          \
    if (yydebug_)                               \
    {                                           \
      *yycdebug_ << Title << ' ';               \
      yy_print_ (*yycdebug_, Symbol);           \
      *yycdebug_ << std::endl;                  \
    }                                           \
  } while (false)

# define YY_REDUCE_PRINT(Rule)          \
  do {                                  \
    if (yydebug_)                       \
      yy_reduce_print_ (Rule);          \
  } while (false)

# define YY_STACK_PRINT()               \
  do {                                  \
    if (yydebug_)                       \
      yystack_print_ ();                \
  } while (false)

#else // !YYDEBUG

# define YYCDEBUG if (false) std::cerr
# define YY_SYMBOL_PRINT(Title, Symbol)  YYUSE(Symbol)
# define YY_REDUCE_PRINT(Rule)           static_cast<void>(0)
# define YY_STACK_PRINT()                static_cast<void>(0)

#endif // !YYDEBUG

#define yyerrok         (yyerrstatus_ = 0)
#define yyclearin       (yyla.clear ())

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab
#define YYRECOVERING()  (!!yyerrstatus_)

#line 22 "parser.yy" // lalr1.cc:479
namespace mli {
#line 205 "parser.cc" // lalr1.cc:479

  /// Build a parser object.
  mli_parser::mli_parser (parse_type& yypval_yyarg, mlilex_f& mlilex_yyarg, std::istream& isp_yyarg)
    :
#if YYDEBUG
      yydebug_ (false),
      yycdebug_ (&std::cerr),
#endif
      yypval (yypval_yyarg),
      mlilex (mlilex_yyarg),
      isp (isp_yyarg)
  {}

  mli_parser::~mli_parser ()
  {}


  /*---------------.
  | Symbol types.  |
  `---------------*/

  inline
  mli_parser::syntax_error::syntax_error (const std::string& m)
    : std::runtime_error (m)
  {}

  // basic_symbol.
  template <typename Base>
  inline
  mli_parser::basic_symbol<Base>::basic_symbol ()
    : value ()
  {}

  template <typename Base>
  inline
  mli_parser::basic_symbol<Base>::basic_symbol (const basic_symbol& other)
    : Base (other)
    , value ()
  {
    value = other.value;
  }


  template <typename Base>
  inline
  mli_parser::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const semantic_type& v)
    : Base (t)
    , value (v)
  {}


  /// Constructor for valueless symbols.
  template <typename Base>
  inline
  mli_parser::basic_symbol<Base>::basic_symbol (typename Base::kind_type t)
    : Base (t)
    , value ()
  {}

  template <typename Base>
  inline
  mli_parser::basic_symbol<Base>::~basic_symbol ()
  {
    clear ();
  }

  template <typename Base>
  inline
  void
  mli_parser::basic_symbol<Base>::clear ()
  {
    Base::clear ();
  }

  template <typename Base>
  inline
  bool
  mli_parser::basic_symbol<Base>::empty () const
  {
    return Base::type_get () == empty_symbol;
  }

  template <typename Base>
  inline
  void
  mli_parser::basic_symbol<Base>::move (basic_symbol& s)
  {
    super_type::move(s);
    value = s.value;
  }

  // by_type.
  inline
  mli_parser::by_type::by_type ()
    : type (empty_symbol)
  {}

  inline
  mli_parser::by_type::by_type (const by_type& other)
    : type (other.type)
  {}

  inline
  mli_parser::by_type::by_type (token_type t)
    : type (yytranslate_ (t))
  {}

  inline
  void
  mli_parser::by_type::clear ()
  {
    type = empty_symbol;
  }

  inline
  void
  mli_parser::by_type::move (by_type& that)
  {
    type = that.type;
    that.clear ();
  }

  inline
  int
  mli_parser::by_type::type_get () const
  {
    return type;
  }


  // by_state.
  inline
  mli_parser::by_state::by_state ()
    : state (empty_state)
  {}

  inline
  mli_parser::by_state::by_state (const by_state& other)
    : state (other.state)
  {}

  inline
  void
  mli_parser::by_state::clear ()
  {
    state = empty_state;
  }

  inline
  void
  mli_parser::by_state::move (by_state& that)
  {
    state = that.state;
    that.clear ();
  }

  inline
  mli_parser::by_state::by_state (state_type s)
    : state (s)
  {}

  inline
  mli_parser::symbol_number_type
  mli_parser::by_state::type_get () const
  {
    if (state == empty_state)
      return empty_symbol;
    else
      return yystos_[state];
  }

  inline
  mli_parser::stack_symbol_type::stack_symbol_type ()
  {}


  inline
  mli_parser::stack_symbol_type::stack_symbol_type (state_type s, symbol_type& that)
    : super_type (s)
  {
    value = that.value;
    // that is emptied.
    that.type = empty_symbol;
  }

  inline
  mli_parser::stack_symbol_type&
  mli_parser::stack_symbol_type::operator= (const stack_symbol_type& that)
  {
    state = that.state;
    value = that.value;
    return *this;
  }


  template <typename Base>
  inline
  void
  mli_parser::yy_destroy_ (const char* yymsg, basic_symbol<Base>& yysym) const
  {
    if (yymsg)
      YY_SYMBOL_PRINT (yymsg, yysym);

    // User destructor.
    YYUSE (yysym.type_get ());
  }

#if YYDEBUG
  template <typename Base>
  void
  mli_parser::yy_print_ (std::ostream& yyo,
                                     const basic_symbol<Base>& yysym) const
  {
    std::ostream& yyoutput = yyo;
    YYUSE (yyoutput);
    symbol_number_type yytype = yysym.type_get ();
    // Avoid a (spurious) G++ 4.8 warning about "array subscript is
    // below array bounds".
    if (yysym.empty ())
      std::abort ();
    yyo << (yytype < yyntokens_ ? "token" : "nterm")
        << ' ' << yytname_[yytype] << " (";
    YYUSE (yytype);
    yyo << ')';
  }
#endif

  inline
  void
  mli_parser::yypush_ (const char* m, state_type s, symbol_type& sym)
  {
    stack_symbol_type t (s, sym);
    yypush_ (m, t);
  }

  inline
  void
  mli_parser::yypush_ (const char* m, stack_symbol_type& s)
  {
    if (m)
      YY_SYMBOL_PRINT (m, s);
    yystack_.push (s);
  }

  inline
  void
  mli_parser::yypop_ (unsigned int n)
  {
    yystack_.pop (n);
  }

#if YYDEBUG
  std::ostream&
  mli_parser::debug_stream () const
  {
    return *yycdebug_;
  }

  void
  mli_parser::set_debug_stream (std::ostream& o)
  {
    yycdebug_ = &o;
  }


  mli_parser::debug_level_type
  mli_parser::debug_level () const
  {
    return yydebug_;
  }

  void
  mli_parser::set_debug_level (debug_level_type l)
  {
    yydebug_ = l;
  }
#endif // YYDEBUG

  inline mli_parser::state_type
  mli_parser::yy_lr_goto_state_ (state_type yystate, int yysym)
  {
    int yyr = yypgoto_[yysym - yyntokens_] + yystate;
    if (0 <= yyr && yyr <= yylast_ && yycheck_[yyr] == yystate)
      return yytable_[yyr];
    else
      return yydefgoto_[yysym - yyntokens_];
  }

  inline bool
  mli_parser::yy_pact_value_is_default_ (int yyvalue)
  {
    return yyvalue == yypact_ninf_;
  }

  inline bool
  mli_parser::yy_table_value_is_error_ (int yyvalue)
  {
    return yyvalue == yytable_ninf_;
  }

  int
  mli_parser::parse ()
  {
    // State.
    int yyn;
    /// Length of the RHS of the rule being reduced.
    int yylen = 0;

    // Error handling.
    int yynerrs_ = 0;
    int yyerrstatus_ = 0;

    /// The lookahead symbol.
    symbol_type yyla;

    /// The return value of parse ().
    int yyresult;

    // FIXME: This shoud be completely indented.  It is not yet to
    // avoid gratuitous conflicts when merging into the master branch.
    try
      {
    YYCDEBUG << "Starting parse" << std::endl;


    /* Initialize the stack.  The initial state will be set in
       yynewstate, since the latter expects the semantical and the
       location values to have been already stored, initialize these
       stacks with a primary value.  */
    yystack_.clear ();
    yypush_ (YY_NULLPTR, 0, yyla);

    // A new symbol was pushed on the stack.
  yynewstate:
    YYCDEBUG << "Entering state " << yystack_[0].state << std::endl;

    // Accept?
    if (yystack_[0].state == yyfinal_)
      goto yyacceptlab;

    goto yybackup;

    // Backup.
  yybackup:

    // Try to take a decision without lookahead.
    yyn = yypact_[yystack_[0].state];
    if (yy_pact_value_is_default_ (yyn))
      goto yydefault;

    // Read a lookahead token.
    if (yyla.empty ())
      {
        YYCDEBUG << "Reading a token: ";
        try
          {
            yyla.type = yytranslate_ (yylex (&yyla.value));
          }
        catch (const syntax_error& yyexc)
          {
            error (yyexc);
            goto yyerrlab1;
          }
      }
    YY_SYMBOL_PRINT ("Next token is", yyla);

    /* If the proper action on seeing token YYLA.TYPE is to reduce or
       to detect an error, take that action.  */
    yyn += yyla.type_get ();
    if (yyn < 0 || yylast_ < yyn || yycheck_[yyn] != yyla.type_get ())
      goto yydefault;

    // Reduce or error.
    yyn = yytable_[yyn];
    if (yyn <= 0)
      {
        if (yy_table_value_is_error_ (yyn))
          goto yyerrlab;
        yyn = -yyn;
        goto yyreduce;
      }

    // Count tokens shifted since error; after three, turn off error status.
    if (yyerrstatus_)
      --yyerrstatus_;

    // Shift the lookahead token.
    yypush_ ("Shifting", yyn, yyla);
    goto yynewstate;

  /*-----------------------------------------------------------.
  | yydefault -- do the default action for the current state.  |
  `-----------------------------------------------------------*/
  yydefault:
    yyn = yydefact_[yystack_[0].state];
    if (yyn == 0)
      goto yyerrlab;
    goto yyreduce;

  /*-----------------------------.
  | yyreduce -- Do a reduction.  |
  `-----------------------------*/
  yyreduce:
    yylen = yyr2_[yyn];
    {
      stack_symbol_type yylhs;
      yylhs.state = yy_lr_goto_state_(yystack_[yylen].state, yyr1_[yyn]);
      /* If YYLEN is nonzero, implement the default value of the
         action: '$$ = $1'.  Otherwise, use the top of the stack.

         Otherwise, the following line sets YYLHS.VALUE to garbage.
         This behavior is undocumented and Bison users should not rely
         upon it.  */
      if (yylen)
        yylhs.value = yystack_[yylen - 1].value;
      else
        yylhs.value = yystack_[0].value;


      // Perform the reduction.
      YY_REDUCE_PRINT (yyn);
      try
        {
          switch (yyn)
            {
  case 2:
#line 371 "parser.yy" // lalr1.cc:859
    {}
#line 634 "parser.cc" // lalr1.cc:859
    break;

  case 3:
#line 372 "parser.yy" // lalr1.cc:859
    {}
#line 640 "parser.cc" // lalr1.cc:859
    break;

  case 4:
#line 373 "parser.yy" // lalr1.cc:859
    {
      declaration_context = false;
      binder_declaration_context = false;
      YYABORT;
    }
#line 650 "parser.cc" // lalr1.cc:859
    break;

  case 5:
#line 381 "parser.yy" // lalr1.cc:859
    {}
#line 656 "parser.cc" // lalr1.cc:859
    break;

  case 6:
#line 382 "parser.yy" // lalr1.cc:859
    {}
#line 662 "parser.cc" // lalr1.cc:859
    break;

  case 7:
#line 386 "parser.yy" // lalr1.cc:859
    {
      level_max = cast_reference<integer>((yystack_[1].value).object_).get_ui();
    }
#line 670 "parser.cc" // lalr1.cc:859
    break;

  case 8:
#line 389 "parser.yy" // lalr1.cc:859
    {
      sublevel_max = cast_reference<integer>((yystack_[1].value).object_).get_ui();
    }
#line 678 "parser.cc" // lalr1.cc:859
    break;

  case 9:
#line 392 "parser.yy" // lalr1.cc:859
    {
      unify_count_max = cast_reference<integer>((yystack_[1].value).object_).get_ui();
    }
#line 686 "parser.cc" // lalr1.cc:859
    break;

  case 10:
#line 395 "parser.yy" // lalr1.cc:859
    { mli_table_stack_.clear(); }
#line 692 "parser.cc" // lalr1.cc:859
    break;

  case 11:
#line 395 "parser.yy" // lalr1.cc:859
    {}
#line 698 "parser.cc" // lalr1.cc:859
    break;

  case 12:
#line 399 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = ref<object>(ref<formula>((yystack_[0].value).object_)->set_bind()); }
#line 704 "parser.cc" // lalr1.cc:859
    break;

  case 13:
#line 400 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = ref<object>(ref<formula>((yystack_[0].value).object_)->set_bind());
    }
#line 712 "parser.cc" // lalr1.cc:859
    break;

  case 14:
#line 406 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 718 "parser.cc" // lalr1.cc:859
    break;

  case 15:
#line 407 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = ref<object>(ref<substitution>((yystack_[0].value).object_) + ref<substitution>((yystack_[1].value).object_));
    }
#line 726 "parser.cc" // lalr1.cc:859
    break;

  case 16:
#line 413 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 732 "parser.cc" // lalr1.cc:859
    break;

  case 17:
#line 414 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 738 "parser.cc" // lalr1.cc:859
    break;

  case 18:
#line 415 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 744 "parser.cc" // lalr1.cc:859
    break;

  case 19:
#line 420 "parser.yy" // lalr1.cc:859
    {
      ref<variable> v((yystack_[3].value).object_);
      ref<formula> f((yystack_[1].value).object_);
      (yylhs.value).object_ = ref<object>(explicit_free_occurrences_substitution(v, f));
    }
#line 754 "parser.cc" // lalr1.cc:859
    break;

  case 20:
#line 428 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 760 "parser.cc" // lalr1.cc:859
    break;

  case 21:
#line 429 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = ref<object>(ref<substitution>((yystack_[0].value).object_) + ref<substitution>((yystack_[1].value).object_));
    }
#line 768 "parser.cc" // lalr1.cc:859
    break;

  case 22:
#line 435 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 774 "parser.cc" // lalr1.cc:859
    break;

  case 23:
#line 436 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 780 "parser.cc" // lalr1.cc:859
    break;

  case 24:
#line 440 "parser.yy" // lalr1.cc:859
    {
      ref<variable> v((yystack_[3].value).object_);
      ref<formula> f((yystack_[1].value).object_);
      (yylhs.value).object_ = ref<object>(explicit_free_occurrences_substitution(v, f));
    }
#line 790 "parser.cc" // lalr1.cc:859
    break;

  case 25:
#line 445 "parser.yy" // lalr1.cc:859
    {
      ref<variable> v((yystack_[3].value).object_);
      ref<formula> f((yystack_[1].value).object_);
      (yylhs.value).object_ = ref<object>(explicit_free_occurrences_substitution(v, f));
    }
#line 800 "parser.cc" // lalr1.cc:859
    break;

  case 26:
#line 450 "parser.yy" // lalr1.cc:859
    {
      ref<variable> v((yystack_[3].value).object_);
      ref<formula> f((yystack_[1].value).object_);
      (yylhs.value).object_ = ref<object>(explicit_free_occurrences_substitution(v, f));
    }
#line 810 "parser.cc" // lalr1.cc:859
    break;

  case 27:
#line 458 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 816 "parser.cc" // lalr1.cc:859
    break;

  case 28:
#line 459 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = ref<object>(ref<substitution>((yystack_[0].value).object_) + ref<substitution>((yystack_[1].value).object_));
    }
#line 824 "parser.cc" // lalr1.cc:859
    break;

  case 29:
#line 465 "parser.yy" // lalr1.cc:859
    {
      ref<variable> v((yystack_[3].value).object_);
      ref<formula> f((yystack_[1].value).object_);
      (yylhs.value).object_ = ref<object>(explicit_free_occurrences_substitution(v, f));
    }
#line 834 "parser.cc" // lalr1.cc:859
    break;

  case 30:
#line 474 "parser.yy" // lalr1.cc:859
    { theory_ = new theory((yystack_[1].value).text_);
          yypval.insert(theory_);
          mli_table_stack_.push_level(); }
#line 842 "parser.cc" // lalr1.cc:859
    break;

  case 31:
#line 479 "parser.yy" // lalr1.cc:859
    {
      if ((yystack_[8].value).text_ != (yystack_[1].value).text_) {
        std::cerr << "Name mismatch, theory " << (yystack_[8].value).text_
          << ", end theory " << (yystack_[1].value).text_ << "." << std::endl;
        YYERROR;
      }
      mli_table_stack_.pop_level(); }
#line 854 "parser.cc" // lalr1.cc:859
    break;

  case 32:
#line 489 "parser.yy" // lalr1.cc:859
    {}
#line 860 "parser.cc" // lalr1.cc:859
    break;

  case 33:
#line 490 "parser.yy" // lalr1.cc:859
    {}
#line 866 "parser.cc" // lalr1.cc:859
    break;

  case 34:
#line 494 "parser.yy" // lalr1.cc:859
    {
      maybe<ref<theory> > th = yypval.find((yystack_[0].value).text_);
      if (!th) {
        mli::mli_parser::error("Include theory " + (yystack_[0].value).text_ + " not found.");
        YYERROR;
      }
      theory_->insert(*th);
    }
#line 879 "parser.cc" // lalr1.cc:859
    break;

  case 35:
#line 505 "parser.yy" // lalr1.cc:859
    {}
#line 885 "parser.cc" // lalr1.cc:859
    break;

  case 36:
#line 506 "parser.yy" // lalr1.cc:859
    {}
#line 891 "parser.cc" // lalr1.cc:859
    break;

  case 37:
#line 511 "parser.yy" // lalr1.cc:859
    { mli_table_stack_.push_level(); }
#line 897 "parser.cc" // lalr1.cc:859
    break;

  case 38:
#line 513 "parser.yy" // lalr1.cc:859
    { mli_table_stack_.pop_level(); }
#line 903 "parser.cc" // lalr1.cc:859
    break;

  case 39:
#line 517 "parser.yy" // lalr1.cc:859
    {}
#line 909 "parser.cc" // lalr1.cc:859
    break;

  case 40:
#line 518 "parser.yy" // lalr1.cc:859
    {}
#line 915 "parser.cc" // lalr1.cc:859
    break;

  case 41:
#line 522 "parser.yy" // lalr1.cc:859
    {}
#line 921 "parser.cc" // lalr1.cc:859
    break;

  case 42:
#line 523 "parser.yy" // lalr1.cc:859
    { theory_->insert(ref<labelstatement>((yystack_[0].value).object_)); }
#line 927 "parser.cc" // lalr1.cc:859
    break;

  case 43:
#line 524 "parser.yy" // lalr1.cc:859
    { theory_->insert(ref<labelstatement>((yystack_[0].value).object_)); }
#line 933 "parser.cc" // lalr1.cc:859
    break;

  case 44:
#line 528 "parser.yy" // lalr1.cc:859
    {}
#line 939 "parser.cc" // lalr1.cc:859
    break;

  case 45:
#line 529 "parser.yy" // lalr1.cc:859
    {}
#line 945 "parser.cc" // lalr1.cc:859
    break;

  case 46:
#line 538 "parser.yy" // lalr1.cc:859
    { theory_->insert(ref<labelstatement>((yystack_[0].value).object_)); }
#line 951 "parser.cc" // lalr1.cc:859
    break;

  case 47:
#line 539 "parser.yy" // lalr1.cc:859
    {}
#line 957 "parser.cc" // lalr1.cc:859
    break;

  case 48:
#line 540 "parser.yy" // lalr1.cc:859
    { theory_->insert(ref<labelstatement>((yystack_[0].value).object_)); }
#line 963 "parser.cc" // lalr1.cc:859
    break;

  case 49:
#line 545 "parser.yy" // lalr1.cc:859
    { mli_table_stack_.push_level(); }
#line 969 "parser.cc" // lalr1.cc:859
    break;

  case 50:
#line 546 "parser.yy" // lalr1.cc:859
    {
      mli_table_stack_.pop_level();
      inference& cl = cast_reference<inference>((yystack_[1].value).object_);
      (yylhs.value).object_ = new supposition(supposition::postulate_, (yystack_[4].value).text_, cl, true);
    }
#line 979 "parser.cc" // lalr1.cc:859
    break;

  case 51:
#line 552 "parser.yy" // lalr1.cc:859
    { mli_table_stack_.push_level(); }
#line 985 "parser.cc" // lalr1.cc:859
    break;

  case 52:
#line 553 "parser.yy" // lalr1.cc:859
    {
      mli_table_stack_.pop_level();
      inference& cl = cast_reference<inference>((yystack_[1].value).object_);
      if (!cl.body_.is_null()) {
        mli::mli_parser::error("Axiom with non-empty body.");
        YYERROR;
      }
      (yylhs.value).object_ = new supposition(supposition::postulate_, (yystack_[4].value).text_, cl);
    }
#line 999 "parser.cc" // lalr1.cc:859
    break;

  case 53:
#line 563 "parser.yy" // lalr1.cc:859
    { mli_table_stack_.push_level(); }
#line 1005 "parser.cc" // lalr1.cc:859
    break;

  case 54:
#line 564 "parser.yy" // lalr1.cc:859
    {
      mli_table_stack_.pop_level();
      inference& cl = cast_reference<inference>((yystack_[1].value).object_);
      if (cl.body_.is_null()) {
        mli::mli_parser::error("Rule with empty body.");
        YYERROR;
      }
      (yylhs.value).object_ = new supposition(supposition::postulate_, (yystack_[4].value).text_, cl);
    }
#line 1019 "parser.cc" // lalr1.cc:859
    break;

  case 55:
#line 577 "parser.yy" // lalr1.cc:859
    { mli_table_stack_.push_level(); }
#line 1025 "parser.cc" // lalr1.cc:859
    break;

  case 56:
#line 578 "parser.yy" // lalr1.cc:859
    {
      mli_table_stack_.pop_level();
      definition& d = cast_reference<definition>((yystack_[1].value).object_);
      (yylhs.value).object_ = new named_definition((yystack_[4].value).text_, d);
    }
#line 1035 "parser.cc" // lalr1.cc:859
    break;

  case 57:
#line 586 "parser.yy" // lalr1.cc:859
    { (yylhs.value).text_ = (yystack_[0].value).text_; }
#line 1041 "parser.cc" // lalr1.cc:859
    break;

  case 58:
#line 587 "parser.yy" // lalr1.cc:859
    { (yylhs.value).text_ = (yystack_[0].value).text_; }
#line 1047 "parser.cc" // lalr1.cc:859
    break;

  case 59:
#line 588 "parser.yy" // lalr1.cc:859
    { (yylhs.value).text_ = (yystack_[0].value).text_; }
#line 1053 "parser.cc" // lalr1.cc:859
    break;

  case 60:
#line 592 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = ref<object>(labelstatement_stack_.top());
      ref<labelstatement> t((yylhs.value).object_); // The theorem.
      t->prove();     // Attempt to prove the theorem.
      mli_table_stack_.pop_level();
      labelstatement_stack_.pop();
    }
#line 1065 "parser.cc" // lalr1.cc:859
    break;

  case 61:
#line 602 "parser.yy" // lalr1.cc:859
    {
      inference& inf = cast_reference<inference>((yystack_[1].value).object_);
      std::map<std::string, std::pair<int, ref<object> > >& top = mli_table_stack_.top();
      theorem* tp = new theorem(
        theorem::type((yystack_[2].value).number_), (yystack_[2].value).text_, inf, theory_, proof_depth);
      labelstatement_stack_.top() = tp;
      theorem_theory_ = tp->get_theory();
    }
#line 1078 "parser.cc" // lalr1.cc:859
    break;

  case 62:
#line 613 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).text_ = (yystack_[1].value).text_;
      (yylhs.value).number_ = (yystack_[2].value).number_;
      mli_table_stack_.push_level();
      labelstatement_stack_.push(ref<labelstatement>());
    }
#line 1089 "parser.cc" // lalr1.cc:859
    break;

  case 63:
#line 622 "parser.yy" // lalr1.cc:859
    {
      --proof_depth;
      mli_table_stack_.pop_level();
      proofline_stack_.pop_level();
      has_labelstatement_stack_.pop(); }
#line 1099 "parser.cc" // lalr1.cc:859
    break;

  case 64:
#line 630 "parser.yy" // lalr1.cc:859
    {
      ++proof_depth;
      mli_table_stack_.push_level();
      proofline_stack_.push_level();
      has_labelstatement_stack_.push(false);
    }
#line 1110 "parser.cc" // lalr1.cc:859
    break;

  case 65:
#line 639 "parser.yy" // lalr1.cc:859
    {}
#line 1116 "parser.cc" // lalr1.cc:859
    break;

  case 66:
#line 640 "parser.yy" // lalr1.cc:859
    {}
#line 1122 "parser.cc" // lalr1.cc:859
    break;

  case 67:
#line 644 "parser.yy" // lalr1.cc:859
    {
      proofline_database_context = false;
      theorem& t = cast_reference<theorem>(labelstatement_stack_.top());
      if (ref<formula>(t.head()) == ref<formula>((yystack_[3].value).object_)) {
        if (has_labelstatement_stack_.top()) {
          mli::mli_parser::error("Duplicate proof statement line.");
          YYERROR;
        } else  has_labelstatement_stack_.top() = true;
      }
      if (!has_labelstatement_stack_.top() && (yystack_[4].value).text_ == "conclusion") {
        mli::mli_parser::error("Proof line name `conclusion' used when not the theorem conclusion.");
        YYERROR;
      }
      std::map<std::string, std::pair<int, ref<object> > >& top = mli_table_stack_.top();
      ref<labelstatement> proof_line =
        t.push_back(
          (yystack_[4].value).text_, ref<formula>((yystack_[3].value).object_), ref<database>((yystack_[1].value).object_),
          has_labelstatement_stack_.top(), proof_depth);
      mli_table_stack_.pop_level();
      if (!proofline_stack_.insert((yystack_[4].value).text_, proof_line)) {
        if ((yystack_[4].value).text_.empty())
          mli::mli_parser::error("Proof line name `' used.");
        else
          mli::mli_parser::error("Proof line name " + (yystack_[4].value).text_  + " already given to a proof line.");
        YYERROR;
      }
    }
#line 1154 "parser.cc" // lalr1.cc:859
    break;

  case 68:
#line 671 "parser.yy" // lalr1.cc:859
    {
      theorem& t = cast_reference<theorem>(labelstatement_stack_.top());
      ref<labelstatement> proof_line = t.push_back(ref<labelstatement>((yystack_[0].value).object_));
      if (!proofline_stack_.insert((yystack_[0].value).text_, proof_line)) {
        if ((yystack_[0].value).text_.empty())
          mli::mli_parser::error("Proof line name `' used.");
        else
          mli::mli_parser::error("Proof line name " + (yystack_[0].value).text_  + " already given to a proof line.");
        YYERROR;
      }
    }
#line 1170 "parser.cc" // lalr1.cc:859
    break;

  case 69:
#line 682 "parser.yy" // lalr1.cc:859
    {}
#line 1176 "parser.cc" // lalr1.cc:859
    break;

  case 70:
#line 683 "parser.yy" // lalr1.cc:859
    {
      theorem& t = cast_reference<theorem>(labelstatement_stack_.top());
      ref<labelstatement> proof_line = t.push_back(ref<labelstatement>((yystack_[0].value).object_));
      if (!proofline_stack_.insert((yystack_[0].value).text_, proof_line)) {
        if ((yystack_[0].value).text_.empty())
          mli::mli_parser::error("Proof line name `' used.");
        else
          mli::mli_parser::error("Proof line name " + (yystack_[0].value).text_  + " already given to a proof line.");
        YYERROR;
      }
    }
#line 1192 "parser.cc" // lalr1.cc:859
    break;

  case 71:
#line 697 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).text_ = (yystack_[2].value).text_;
      (yylhs.value).object_ = ref<object>(labelstatement_stack_.top());
      mli_table_stack_.pop_level();
      labelstatement_stack_.pop();
    }
#line 1203 "parser.cc" // lalr1.cc:859
    break;

  case 72:
#line 706 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).text_ = (yystack_[1].value).text_;
      inference& inf = cast_reference<inference>((yystack_[0].value).object_);
      std::map<std::string, std::pair<int, ref<object> > >& top = mli_table_stack_.top();
      theorem* tp = new theorem(theorem::claim_, (yystack_[1].value).text_, inf, theory_, proof_depth);
      labelstatement_stack_.top() = tp;
    }
#line 1215 "parser.cc" // lalr1.cc:859
    break;

  case 73:
#line 716 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).text_ = (yystack_[1].value).text_;
      (yylhs.value).number_ = (yystack_[2].value).number_;
      mli_table_stack_.push_level();
      labelstatement_stack_.push(ref<labelstatement>());
    }
#line 1226 "parser.cc" // lalr1.cc:859
    break;

  case 74:
#line 725 "parser.yy" // lalr1.cc:859
    {
    (yylhs.value).text_ = (yystack_[1].value).text_;
    mli_table_stack_.push_level();
  }
#line 1235 "parser.cc" // lalr1.cc:859
    break;

  case 75:
#line 732 "parser.yy" // lalr1.cc:859
    {
      proofline_database_context = false;
      if (has_labelstatement_stack_.top()) {
        mli::mli_parser::error("Duplicate proof conclusion line.");
        YYERROR;
      }
      theorem& t = cast_reference<theorem>(labelstatement_stack_.top());
      ref<labelstatement> proof_line =
        t.push_back((yystack_[3].value).text_, t.head(), ref<database>((yystack_[1].value).object_), true, proof_depth);
      if (!proofline_stack_.insert((yystack_[3].value).text_, proof_line)) {
        mli::mli_parser::error("Proof conclusion line not inserted as the name `conclusion' already given to a proof line.");
        YYERROR;
      }
    }
#line 1254 "parser.cc" // lalr1.cc:859
    break;

  case 76:
#line 749 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1260 "parser.cc" // lalr1.cc:859
    break;

  case 77:
#line 750 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = 
        new leveled_database(ref<database>((yystack_[2].value).object_), ref<database>((yystack_[0].value).object_));
    }
#line 1269 "parser.cc" // lalr1.cc:859
    break;

  case 78:
#line 757 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1276 "parser.cc" // lalr1.cc:859
    break;

  case 79:
#line 759 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = ref<object>(ref<database>((yystack_[2].value).object_) + ref<database>((yystack_[0].value).object_));
    }
#line 1284 "parser.cc" // lalr1.cc:859
    break;

  case 80:
#line 765 "parser.yy" // lalr1.cc:859
    {
      ref<database> d(new sequential_database());
      d->insert(ref<labelstatement>((yystack_[0].value).object_));
      (yylhs.value).object_ = ref<object>(d);
    }
#line 1294 "parser.cc" // lalr1.cc:859
    break;

  case 81:
#line 770 "parser.yy" // lalr1.cc:859
    {
      database* dp = new sequential_database();
      ref<database> d(dp);
      dp->insert(new premise(labelstatement_stack_.top()));
      (yylhs.value).object_ = ref<object>(d);
    }
#line 1305 "parser.cc" // lalr1.cc:859
    break;

  case 82:
#line 779 "parser.yy" // lalr1.cc:859
    {
      // Accept also non-proved statements (as actual proving will come later):
      maybe<ref<labelstatement> > st;
      st = proofline_stack_.find((yystack_[0].value).text_);
      if (!st)  st = theorem_theory_->find((yystack_[0].value).text_, 0, false);
      if (!st) {
        mli::mli_parser::error("statement name " + (yystack_[0].value).text_
          + " not found earlier in proof, in premises or theory.");
        YYERROR;
      }
      (yylhs.value).object_ = ref<object>(*st);
    }
#line 1322 "parser.cc" // lalr1.cc:859
    break;

  case 83:
#line 791 "parser.yy" // lalr1.cc:859
    {
      // Accept also non-proved statements (as actual proving will come later):
      maybe<ref<labelstatement> > st;
      st = proofline_stack_.find((yystack_[0].value).text_);
      if (!st)  st = theorem_theory_->find((yystack_[0].value).text_, 0, false);
      if (!st) {
        mli::mli_parser::error("statement name " + (yystack_[0].value).text_
          + " not found earlier in proof, in premises or theory.");
        YYERROR;
      }
      (yylhs.value).object_ = ref<object>(*st);
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
#line 1353 "parser.cc" // lalr1.cc:859
    break;

  case 84:
#line 817 "parser.yy" // lalr1.cc:859
    {
      // The try-catch checks whether the labelstatement-substitution is legal:
      ref<labelstatement> p((yystack_[1].value).object_);
      ref<substitution> s((yystack_[0].value).object_);
      try {
        (yylhs.value).object_ = new labelstatement_substitution(p, s);
      } catch (substitute_error&) {
        mli::mli_parser::error("Proposition substitute error.");
        p->write(std::cerr,
          write_style(write_name | write_type | write_statement));
        std::cerr << "\n  " << s << std::endl;
        YYERROR;        
      }
      mli_table_stack_.pop_level();
    }
#line 1373 "parser.cc" // lalr1.cc:859
    break;

  case 85:
#line 835 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = ref<object>(ref<formula>((yystack_[0].value).object_)->set_bind()); }
#line 1379 "parser.cc" // lalr1.cc:859
    break;

  case 86:
#line 836 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = ref<object>(ref<formula>((yystack_[0].value).object_)->set_bind());
    }
#line 1387 "parser.cc" // lalr1.cc:859
    break;

  case 87:
#line 842 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = ref<object>(ref<formula>((yystack_[0].value).object_)->set_bind()); }
#line 1393 "parser.cc" // lalr1.cc:859
    break;

  case 88:
#line 843 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = ref<object>(ref<formula>((yystack_[0].value).object_)->set_bind());
    }
#line 1401 "parser.cc" // lalr1.cc:859
    break;

  case 89:
#line 849 "parser.yy" // lalr1.cc:859
    {}
#line 1407 "parser.cc" // lalr1.cc:859
    break;

  case 90:
#line 853 "parser.yy" // lalr1.cc:859
    {}
#line 1413 "parser.cc" // lalr1.cc:859
    break;

  case 91:
#line 854 "parser.yy" // lalr1.cc:859
    {}
#line 1419 "parser.cc" // lalr1.cc:859
    break;

  case 92:
#line 858 "parser.yy" // lalr1.cc:859
    {}
#line 1425 "parser.cc" // lalr1.cc:859
    break;

  case 93:
#line 859 "parser.yy" // lalr1.cc:859
    {}
#line 1431 "parser.cc" // lalr1.cc:859
    break;

  case 94:
#line 863 "parser.yy" // lalr1.cc:859
    {
      table_stack_insert_below((yystack_[0].value).text_, declared_token,
        new constant((yystack_[0].value).text_, formula_type(declared_type))); }
#line 1439 "parser.cc" // lalr1.cc:859
    break;

  case 95:
#line 866 "parser.yy" // lalr1.cc:859
    {
      table_stack_insert_below((yystack_[0].value).text_, declared_token, 
        new constant((yystack_[0].value).text_, formula_type(declared_type))); }
#line 1447 "parser.cc" // lalr1.cc:859
    break;

  case 96:
#line 872 "parser.yy" // lalr1.cc:859
    {
       table_stack_insert((yystack_[0].value).text_, declared_token, 
         new variable((yystack_[0].value).text_, variable::type(declared_type), proof_depth)); }
#line 1455 "parser.cc" // lalr1.cc:859
    break;

  case 97:
#line 876 "parser.yy" // lalr1.cc:859
    { table_stack_insert((yystack_[0].value).text_, declared_token,
          new variable((yystack_[0].value).text_, variable::type(declared_type), proof_depth)); }
#line 1462 "parser.cc" // lalr1.cc:859
    break;

  case 98:
#line 881 "parser.yy" // lalr1.cc:859
    {
      inference* ip = cast_pointer<inference>((yystack_[0].value).object_);
      if (ip != 0)
        (yylhs.value).object_ = (yystack_[0].value).object_;
      else
        (yylhs.value).object_ = new inference(ref<formula>((yystack_[0].value).object_));
    }
#line 1474 "parser.cc" // lalr1.cc:859
    break;

  case 99:
#line 891 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1480 "parser.cc" // lalr1.cc:859
    break;

  case 100:
#line 892 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1486 "parser.cc" // lalr1.cc:859
    break;

  case 101:
#line 893 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1492 "parser.cc" // lalr1.cc:859
    break;

  case 102:
#line 897 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new definition(ref<formula>((yystack_[2].value).object_), ref<formula>((yystack_[0].value).object_), ref<formula>(),
        object_formula_type_, formula_definition_oprec); }
#line 1500 "parser.cc" // lalr1.cc:859
    break;

  case 103:
#line 900 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new definition(ref<formula>((yystack_[0].value).object_), ref<formula>((yystack_[2].value).object_), ref<formula>(),
        object_formula_type_, formula_definition_oprec); }
#line 1508 "parser.cc" // lalr1.cc:859
    break;

  case 104:
#line 911 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new definition(ref<formula>((yystack_[2].value).object_), ref<formula>((yystack_[0].value).object_), ref<formula>(),
        object_formula_type_, formula_definition_oprec); }
#line 1516 "parser.cc" // lalr1.cc:859
    break;

  case 105:
#line 914 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new definition(ref<formula>((yystack_[0].value).object_), ref<formula>((yystack_[2].value).object_), ref<formula>(),
        object_formula_type_, formula_definition_oprec); }
#line 1524 "parser.cc" // lalr1.cc:859
    break;

  case 106:
#line 925 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new definition(ref<formula>((yystack_[2].value).object_), ref<formula>((yystack_[0].value).object_), ref<formula>(),
        term_type_, term_definition_oprec); }
#line 1532 "parser.cc" // lalr1.cc:859
    break;

  case 107:
#line 928 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new definition(ref<formula>((yystack_[2].value).object_), ref<formula>((yystack_[0].value).object_), ref<formula>((yystack_[4].value).object_),
        term_type_, term_definition_oprec); }
#line 1540 "parser.cc" // lalr1.cc:859
    break;

  case 108:
#line 931 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new definition(ref<formula>((yystack_[0].value).object_), ref<formula>((yystack_[2].value).object_), ref<formula>(),
        term_type_, term_definition_oprec); }
#line 1548 "parser.cc" // lalr1.cc:859
    break;

  case 109:
#line 937 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1554 "parser.cc" // lalr1.cc:859
    break;

  case 110:
#line 938 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1560 "parser.cc" // lalr1.cc:859
    break;

  case 111:
#line 942 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1566 "parser.cc" // lalr1.cc:859
    break;

  case 112:
#line 943 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1572 "parser.cc" // lalr1.cc:859
    break;

  case 113:
#line 944 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = ref<object>(new metanot(ref<formula>((yystack_[0].value).object_)));
    }
#line 1580 "parser.cc" // lalr1.cc:859
    break;

  case 114:
#line 947 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = ref<object>(
        mli::concatenate(ref<formula>((yystack_[2].value).object_), ref<formula>((yystack_[0].value).object_), metaand_));
    }
#line 1589 "parser.cc" // lalr1.cc:859
    break;

  case 115:
#line 951 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = ref<object>(
        mli::concatenate(ref<formula>((yystack_[2].value).object_), ref<formula>((yystack_[0].value).object_), metaor_));
    }
#line 1598 "parser.cc" // lalr1.cc:859
    break;

  case 116:
#line 955 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ =
        new inference(ref<formula>((yystack_[0].value).object_), ref<formula>((yystack_[2].value).object_), inference::infer_);
    }
#line 1607 "parser.cc" // lalr1.cc:859
    break;

  case 117:
#line 959 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ =
        new inference(ref<formula>((yystack_[2].value).object_), ref<formula>((yystack_[0].value).object_), inference::infered_by_);
    }
#line 1616 "parser.cc" // lalr1.cc:859
    break;

  case 118:
#line 963 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = new inference(ref<formula>((yystack_[0].value).object_)); }
#line 1622 "parser.cc" // lalr1.cc:859
    break;

  case 119:
#line 964 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = new inference(ref<formula>((yystack_[1].value).object_)); }
#line 1628 "parser.cc" // lalr1.cc:859
    break;

  case 120:
#line 965 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[1].value).object_; }
#line 1634 "parser.cc" // lalr1.cc:859
    break;

  case 121:
#line 966 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new substitution_formula(ref<substitution>((yystack_[0].value).object_), ref<formula>((yystack_[1].value).object_)); }
#line 1641 "parser.cc" // lalr1.cc:859
    break;

  case 122:
#line 971 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1647 "parser.cc" // lalr1.cc:859
    break;

  case 123:
#line 972 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[1].value).object_; }
#line 1653 "parser.cc" // lalr1.cc:859
    break;

  case 124:
#line 976 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1659 "parser.cc" // lalr1.cc:859
    break;

  case 125:
#line 977 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1665 "parser.cc" // lalr1.cc:859
    break;

  case 126:
#line 981 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = new succeed_fail(false); }
#line 1671 "parser.cc" // lalr1.cc:859
    break;

  case 127:
#line 982 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = new succeed_fail(true); }
#line 1677 "parser.cc" // lalr1.cc:859
    break;

  case 128:
#line 983 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new objectidentical(ref<variable>((yystack_[2].value).object_), ref<variable>((yystack_[0].value).object_), true);
    }
#line 1685 "parser.cc" // lalr1.cc:859
    break;

  case 129:
#line 986 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new objectidentical(ref<variable>((yystack_[2].value).object_), ref<variable>((yystack_[0].value).object_), false);
    }
#line 1693 "parser.cc" // lalr1.cc:859
    break;

  case 130:
#line 989 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new free_in_object(ref<variable>((yystack_[2].value).object_), ref<formula>((yystack_[0].value).object_), true);
    }
#line 1701 "parser.cc" // lalr1.cc:859
    break;

  case 131:
#line 992 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new free_in_object(ref<variable>((yystack_[2].value).object_), ref<formula>((yystack_[0].value).object_), true);
    }
#line 1709 "parser.cc" // lalr1.cc:859
    break;

  case 132:
#line 995 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new free_in_object(ref<variable>((yystack_[3].value).object_), ref<formula>((yystack_[0].value).object_), false);
    }
#line 1717 "parser.cc" // lalr1.cc:859
    break;

  case 133:
#line 998 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new free_in_object(ref<variable>((yystack_[3].value).object_), ref<formula>((yystack_[0].value).object_), false);
    }
#line 1725 "parser.cc" // lalr1.cc:859
    break;

  case 134:
#line 1001 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new free_for_object(
        ref<formula>((yystack_[4].value).object_), ref<variable>((yystack_[2].value).object_), ref<formula>((yystack_[0].value).object_), true);
    }
#line 1734 "parser.cc" // lalr1.cc:859
    break;

  case 135:
#line 1005 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new free_for_object(
        ref<formula>((yystack_[4].value).object_), ref<variable>((yystack_[2].value).object_), ref<formula>((yystack_[0].value).object_), true);
    }
#line 1743 "parser.cc" // lalr1.cc:859
    break;

  case 136:
#line 1012 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1749 "parser.cc" // lalr1.cc:859
    break;

  case 137:
#line 1013 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1755 "parser.cc" // lalr1.cc:859
    break;

  case 138:
#line 1017 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1761 "parser.cc" // lalr1.cc:859
    break;

  case 139:
#line 1018 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new identical(ref<formula>((yystack_[2].value).object_), ref<formula>((yystack_[0].value).object_), true);
    }
#line 1769 "parser.cc" // lalr1.cc:859
    break;

  case 140:
#line 1021 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new identical(ref<formula>((yystack_[2].value).object_), ref<formula>((yystack_[0].value).object_), false);
    }
#line 1777 "parser.cc" // lalr1.cc:859
    break;

  case 141:
#line 1024 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new identical(ref<formula>((yystack_[2].value).object_), ref<formula>((yystack_[0].value).object_), true);
    }
#line 1785 "parser.cc" // lalr1.cc:859
    break;

  case 142:
#line 1027 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new identical(ref<formula>((yystack_[2].value).object_), ref<formula>((yystack_[0].value).object_), false);
    }
#line 1793 "parser.cc" // lalr1.cc:859
    break;

  case 143:
#line 1033 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new structure(ref<formula>((yystack_[1].value).object_), ref<formula>((yystack_[0].value).object_),
        structure::metapredicate, structure::postargument, operator_precedence()); }
#line 1801 "parser.cc" // lalr1.cc:859
    break;

  case 144:
#line 1036 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new structure(ref<formula>((yystack_[1].value).object_), ref<formula>((yystack_[0].value).object_),
        structure::metapredicate, structure::postargument, operator_precedence()); }
#line 1809 "parser.cc" // lalr1.cc:859
    break;

  case 145:
#line 1042 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[1].value).object_; }
#line 1815 "parser.cc" // lalr1.cc:859
    break;

  case 146:
#line 1046 "parser.yy" // lalr1.cc:859
    {
      sequence* vp
        = new sequence(metapredicate_argument_);
      (yylhs.value).object_ = vp;
      vp->push_back(ref<formula>((yystack_[0].value).object_)); }
#line 1825 "parser.cc" // lalr1.cc:859
    break;

  case 147:
#line 1051 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = (yystack_[2].value).object_;
      sequence& vp = cast_reference<sequence>((yylhs.value).object_);
      vp.push_back(ref<formula>((yystack_[0].value).object_)); }
#line 1834 "parser.cc" // lalr1.cc:859
    break;

  case 148:
#line 1058 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1840 "parser.cc" // lalr1.cc:859
    break;

  case 149:
#line 1059 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new substitution_formula(ref<substitution>((yystack_[0].value).object_), ref<formula>((yystack_[1].value).object_));
    }
#line 1848 "parser.cc" // lalr1.cc:859
    break;

  case 150:
#line 1062 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1854 "parser.cc" // lalr1.cc:859
    break;

  case 151:
#line 1063 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[1].value).object_; }
#line 1860 "parser.cc" // lalr1.cc:859
    break;

  case 152:
#line 1064 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1866 "parser.cc" // lalr1.cc:859
    break;

  case 153:
#line 1068 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1872 "parser.cc" // lalr1.cc:859
    break;

  case 154:
#line 1069 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1878 "parser.cc" // lalr1.cc:859
    break;

  case 155:
#line 1070 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[1].value).object_; }
#line 1884 "parser.cc" // lalr1.cc:859
    break;

  case 156:
#line 1074 "parser.yy" // lalr1.cc:859
    {
      mli_table_stack_.pop_level();
      variable_list* vsp = cast_pointer<variable_list>((yystack_[1].value).object_);
      (yylhs.value).object_ = new bound_formula(*vsp, ref<formula>((yystack_[0].value).object_));
    }
#line 1894 "parser.cc" // lalr1.cc:859
    break;

  case 157:
#line 1079 "parser.yy" // lalr1.cc:859
    {
      mli_table_stack_.pop_level();
      variable_list* vsp = cast_pointer<variable_list>((yystack_[2].value).object_);
      (yylhs.value).object_ = new bound_formula(*vsp, ref<formula>((yystack_[0].value).object_));
    }
#line 1904 "parser.cc" // lalr1.cc:859
    break;

  case 158:
#line 1087 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1910 "parser.cc" // lalr1.cc:859
    break;

  case 159:
#line 1088 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1916 "parser.cc" // lalr1.cc:859
    break;

  case 160:
#line 1089 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1922 "parser.cc" // lalr1.cc:859
    break;

  case 161:
#line 1090 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[1].value).object_; }
#line 1928 "parser.cc" // lalr1.cc:859
    break;

  case 162:
#line 1091 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1934 "parser.cc" // lalr1.cc:859
    break;

  case 163:
#line 1095 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1940 "parser.cc" // lalr1.cc:859
    break;

  case 164:
#line 1096 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[1].value).object_; }
#line 1946 "parser.cc" // lalr1.cc:859
    break;

  case 165:
#line 1100 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1952 "parser.cc" // lalr1.cc:859
    break;

  case 166:
#line 1101 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1958 "parser.cc" // lalr1.cc:859
    break;

  case 167:
#line 1102 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1964 "parser.cc" // lalr1.cc:859
    break;

  case 168:
#line 1103 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1970 "parser.cc" // lalr1.cc:859
    break;

  case 169:
#line 1108 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 1976 "parser.cc" // lalr1.cc:859
    break;

  case 170:
#line 1109 "parser.yy" // lalr1.cc:859
    {
      structure* cp = new structure((yystack_[1].value).text_, structure::predicate);
      (yylhs.value).object_ = cp;
      cp->push_back(ref<formula>((yystack_[2].value).object_));
      cp->push_back(ref<formula>((yystack_[0].value).object_));
      cp->set(structure::infix);  /* Binary infix predicate. */
      cp->set(equal_oprec); }
#line 1988 "parser.cc" // lalr1.cc:859
    break;

  case 171:
#line 1116 "parser.yy" // lalr1.cc:859
    {
      structure* cp = new structure((yystack_[1].value).text_, structure::predicate);
      (yylhs.value).object_ = cp;
      cp->push_back(ref<formula>((yystack_[2].value).object_));
      cp->push_back(ref<formula>((yystack_[0].value).object_));
      cp->set(structure::infix);  /* Binary infix predicate. */
      cp->set(equal_oprec); }
#line 2000 "parser.cc" // lalr1.cc:859
    break;

  case 172:
#line 1123 "parser.yy" // lalr1.cc:859
    {
      structure* cp = new structure((yystack_[1].value).text_, structure::predicate);
      (yylhs.value).object_ = cp;
      cp->push_back(ref<formula>((yystack_[2].value).object_));
      cp->push_back(ref<formula>((yystack_[0].value).object_));
      cp->set(structure::infix);  /* Binary infix predicate. */
      cp->set(in_oprec); }
#line 2012 "parser.cc" // lalr1.cc:859
    break;

  case 173:
#line 1130 "parser.yy" // lalr1.cc:859
    {
      structure* cp = new structure((yystack_[1].value).text_, structure::predicate);
      (yylhs.value).object_ = cp;
      cp->push_back(ref<formula>((yystack_[2].value).object_));
      cp->push_back(ref<formula>((yystack_[0].value).object_));
      cp->set(structure::infix);  /* Binary infix predicate. */
      cp->set(subset_oprec); }
#line 2024 "parser.cc" // lalr1.cc:859
    break;

  case 174:
#line 1137 "parser.yy" // lalr1.cc:859
    {
      structure* cp = new structure((yystack_[1].value).text_, structure::predicate);
      (yylhs.value).object_ = cp;
      cp->push_back(ref<formula>((yystack_[2].value).object_));
      cp->push_back(ref<formula>((yystack_[0].value).object_));
      cp->set(structure::infix);  /* Binary infix predicate. */
      cp->set(psubset_oprec); }
#line 2036 "parser.cc" // lalr1.cc:859
    break;

  case 175:
#line 1144 "parser.yy" // lalr1.cc:859
    { mli_table_stack_.push_level(); }
#line 2042 "parser.cc" // lalr1.cc:859
    break;

  case 176:
#line 1145 "parser.yy" // lalr1.cc:859
    {
      mli_table_stack_.pop_level();
      (yylhs.value).object_ = new bound_formula(
        ref<variable>((yystack_[1].value).object_), ref<formula>((yystack_[0].value).object_), bound_formula::is_set_);
    }
#line 2052 "parser.cc" // lalr1.cc:859
    break;

  case 177:
#line 1153 "parser.yy" // lalr1.cc:859
    {
      binder_declaration_context = false;
      (yylhs.value).object_ = new variable((yystack_[0].value).text_, variable::object_, 0);
      table_stack_insert((yystack_[0].value).text_, token::is_set_variable, (yylhs.value).object_);
    }
#line 2062 "parser.cc" // lalr1.cc:859
    break;

  case 178:
#line 1158 "parser.yy" // lalr1.cc:859
    {
      binder_declaration_context = false;
      (yylhs.value).object_ = (yystack_[0].value).object_;
      table_stack_insert((yystack_[0].value).text_, token::metaobjectvariable, (yystack_[0].value).object_);
    }
#line 2072 "parser.cc" // lalr1.cc:859
    break;

  case 179:
#line 1166 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new structure(ref<formula>((yystack_[1].value).object_), ref<formula>((yystack_[0].value).object_),
        structure::predicate, structure::postargument, operator_precedence()); }
#line 2080 "parser.cc" // lalr1.cc:859
    break;

  case 180:
#line 1169 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new structure(ref<formula>((yystack_[1].value).object_), ref<formula>((yystack_[0].value).object_),
        structure::predicate, structure::postargument, operator_precedence()); }
#line 2088 "parser.cc" // lalr1.cc:859
    break;

  case 181:
#line 1176 "parser.yy" // lalr1.cc:859
    {
      structure* cp = new structure((yystack_[1].value).text_, structure::logic);
      (yylhs.value).object_ = cp;
      cp->push_back(ref<formula>((yystack_[0].value).object_));
      cp->set(structure::prefix);
      cp->set(not_oprec); }
#line 2099 "parser.cc" // lalr1.cc:859
    break;

  case 182:
#line 1182 "parser.yy" // lalr1.cc:859
    {
      structure* cp = new structure((yystack_[1].value).text_, structure::logic);
      (yylhs.value).object_ = cp;
      cp->push_back(ref<formula>((yystack_[2].value).object_));
      cp->push_back(ref<formula>((yystack_[0].value).object_));
      cp->set(structure::infix);
      cp->set(or_oprec); }
#line 2111 "parser.cc" // lalr1.cc:859
    break;

  case 183:
#line 1189 "parser.yy" // lalr1.cc:859
    {
      structure* cp = new structure((yystack_[1].value).text_, structure::logic);
      (yylhs.value).object_ = cp;
      cp->push_back(ref<formula>((yystack_[2].value).object_));
      cp->push_back(ref<formula>((yystack_[0].value).object_));
      cp->set(structure::infix);
      cp->set(and_oprec); }
#line 2123 "parser.cc" // lalr1.cc:859
    break;

  case 184:
#line 1196 "parser.yy" // lalr1.cc:859
    {
      structure* cp = new structure((yystack_[1].value).text_, structure::logic);
      (yylhs.value).object_ = cp;
      cp->push_back(ref<formula>((yystack_[2].value).object_));
      cp->push_back(ref<formula>((yystack_[0].value).object_));
      cp->set(structure::infix);
      cp->set(implies_oprec); }
#line 2135 "parser.cc" // lalr1.cc:859
    break;

  case 185:
#line 1203 "parser.yy" // lalr1.cc:859
    {
      structure* cp = new structure((yystack_[1].value).text_, structure::logic);
      (yylhs.value).object_ = cp;
      cp->push_back(ref<formula>((yystack_[2].value).object_));
      cp->push_back(ref<formula>((yystack_[0].value).object_));
      cp->set(structure::infix);
      cp->set(impliedby_oprec); }
#line 2147 "parser.cc" // lalr1.cc:859
    break;

  case 186:
#line 1210 "parser.yy" // lalr1.cc:859
    {
      structure* cp = new structure((yystack_[1].value).text_, structure::logic);
      (yylhs.value).object_ = cp;
      cp->push_back(ref<formula>((yystack_[2].value).object_));
      cp->push_back(ref<formula>((yystack_[0].value).object_));
      cp->set(structure::infix);
      cp->set(equivalent_oprec); }
#line 2159 "parser.cc" // lalr1.cc:859
    break;

  case 187:
#line 1220 "parser.yy" // lalr1.cc:859
    { mli_table_stack_.push_level(); }
#line 2165 "parser.cc" // lalr1.cc:859
    break;

  case 188:
#line 1221 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2171 "parser.cc" // lalr1.cc:859
    break;

  case 189:
#line 1225 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2177 "parser.cc" // lalr1.cc:859
    break;

  case 190:
#line 1226 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2183 "parser.cc" // lalr1.cc:859
    break;

  case 191:
#line 1227 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = (yystack_[1].value).object_;
      variable_list* vsp = cast_pointer<variable_list>((yylhs.value).object_);
      variable_list* vsp2 = cast_pointer<variable_list>((yystack_[0].value).object_);
      vsp->push_back(*vsp2);
    }
#line 2194 "parser.cc" // lalr1.cc:859
    break;

  case 192:
#line 1233 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = (yystack_[1].value).object_;
      variable_list* vsp = cast_pointer<variable_list>((yylhs.value).object_);
      variable_list* vsp2 = cast_pointer<variable_list>((yystack_[0].value).object_);
      vsp->push_back(*vsp2);
    }
#line 2205 "parser.cc" // lalr1.cc:859
    break;

  case 193:
#line 1242 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2211 "parser.cc" // lalr1.cc:859
    break;

  case 194:
#line 1243 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[1].value).object_; /* Add $3. */ }
#line 2217 "parser.cc" // lalr1.cc:859
    break;

  case 195:
#line 1247 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2223 "parser.cc" // lalr1.cc:859
    break;

  case 196:
#line 1248 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[1].value).object_; /* Add $3. */ }
#line 2229 "parser.cc" // lalr1.cc:859
    break;

  case 197:
#line 1252 "parser.yy" // lalr1.cc:859
    {
      binder_declaration_context = false;
      (yylhs.value).object_ = new variable_list(ref<variable>((yystack_[0].value).object_), bound_formula::all_);
    }
#line 2238 "parser.cc" // lalr1.cc:859
    break;

  case 198:
#line 1256 "parser.yy" // lalr1.cc:859
    { binder_declaration_context = true; }
#line 2244 "parser.cc" // lalr1.cc:859
    break;

  case 199:
#line 1257 "parser.yy" // lalr1.cc:859
    {
      binder_declaration_context = false;
      (yylhs.value).object_ = (yystack_[3].value).object_;
      cast_pointer<variable_list>((yylhs.value).object_)
        ->push_back(ref<variable>((yystack_[0].value).object_), bound_formula::all_);
    }
#line 2255 "parser.cc" // lalr1.cc:859
    break;

  case 200:
#line 1266 "parser.yy" // lalr1.cc:859
    {
      ref<object> v = new variable((yystack_[0].value).text_, variable::object_, 0);
      table_stack_insert((yystack_[0].value).text_, token::all_variable, v);
      (yylhs.value).object_ = v;
    }
#line 2265 "parser.cc" // lalr1.cc:859
    break;

  case 201:
#line 1271 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = (yystack_[0].value).object_;
      table_stack_insert((yystack_[0].value).text_, token::metaobjectvariable, (yystack_[0].value).object_);
    }
#line 2274 "parser.cc" // lalr1.cc:859
    break;

  case 202:
#line 1278 "parser.yy" // lalr1.cc:859
    {
      binder_declaration_context = false;
      (yylhs.value).object_ = new variable_list(ref<variable>((yystack_[0].value).object_), bound_formula::exist_);
    }
#line 2283 "parser.cc" // lalr1.cc:859
    break;

  case 203:
#line 1282 "parser.yy" // lalr1.cc:859
    { binder_declaration_context = true; }
#line 2289 "parser.cc" // lalr1.cc:859
    break;

  case 204:
#line 1283 "parser.yy" // lalr1.cc:859
    {
      binder_declaration_context = false;
      (yylhs.value).object_ = (yystack_[3].value).object_;
      cast_pointer<variable_list>((yylhs.value).object_)
        ->push_back(ref<variable>((yystack_[0].value).object_), bound_formula::exist_);
    }
#line 2300 "parser.cc" // lalr1.cc:859
    break;

  case 205:
#line 1292 "parser.yy" // lalr1.cc:859
    {
      ref<object> v = new variable((yystack_[0].value).text_, variable::object_, 0);
      table_stack_insert((yystack_[0].value).text_, token::exist_variable, v);
      (yylhs.value).object_ = v;
    }
#line 2310 "parser.cc" // lalr1.cc:859
    break;

  case 206:
#line 1297 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = (yystack_[0].value).object_;
      table_stack_insert((yystack_[0].value).text_, token::metaobjectvariable, (yystack_[0].value).object_);
    }
#line 2319 "parser.cc" // lalr1.cc:859
    break;

  case 207:
#line 1304 "parser.yy" // lalr1.cc:859
    {
#if 0
      std::set<std::string>::iterator i = clp_parser_variables.begin(), i1 = clp_parser_variables.end();
      for (; i != i1; ++i) {
        (yystack_[1].value).termlist.push_back(new variable(*i, variable::free_), 0));
        (yylhs.value).termlist.push_back(
          new structure((yystack_[0].value).object_, (yystack_[1].value).termlist));
        (yystack_[1].value).termlist.clear();
      }
#endif
    }
#line 2335 "parser.cc" // lalr1.cc:859
    break;

  case 208:
#line 1318 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2341 "parser.cc" // lalr1.cc:859
    break;

  case 209:
#line 1319 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2347 "parser.cc" // lalr1.cc:859
    break;

  case 210:
#line 1324 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[1].value).object_; }
#line 2353 "parser.cc" // lalr1.cc:859
    break;

  case 211:
#line 1328 "parser.yy" // lalr1.cc:859
    {
      sequence* vp = new sequence(predicate_argument_);
      (yylhs.value).object_ = vp;
      vp->push_back(ref<formula>((yystack_[0].value).object_)); }
#line 2362 "parser.cc" // lalr1.cc:859
    break;

  case 212:
#line 1332 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = (yystack_[2].value).object_;
      sequence& vp = cast_reference<sequence>((yylhs.value).object_);
      vp.push_back(ref<formula>((yystack_[0].value).object_)); }
#line 2371 "parser.cc" // lalr1.cc:859
    break;

  case 213:
#line 1339 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[1].value).object_; }
#line 2377 "parser.cc" // lalr1.cc:859
    break;

  case 214:
#line 1343 "parser.yy" // lalr1.cc:859
    {
      sequence* vp = new sequence(function_argument_);
      (yylhs.value).object_ = vp;
      vp->push_back(ref<formula>((yystack_[0].value).object_)); }
#line 2386 "parser.cc" // lalr1.cc:859
    break;

  case 215:
#line 1347 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = (yystack_[2].value).object_;
      sequence& vp = cast_reference<sequence>((yylhs.value).object_);
      vp.push_back(ref<formula>((yystack_[0].value).object_)); }
#line 2395 "parser.cc" // lalr1.cc:859
    break;

  case 216:
#line 1354 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2401 "parser.cc" // lalr1.cc:859
    break;

  case 217:
#line 1355 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2407 "parser.cc" // lalr1.cc:859
    break;

  case 218:
#line 1356 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new substitution_formula(ref<substitution>((yystack_[0].value).object_), ref<formula>((yystack_[1].value).object_));
    }
#line 2415 "parser.cc" // lalr1.cc:859
    break;

  case 219:
#line 1362 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2421 "parser.cc" // lalr1.cc:859
    break;

  case 220:
#line 1363 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2427 "parser.cc" // lalr1.cc:859
    break;

  case 221:
#line 1364 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2433 "parser.cc" // lalr1.cc:859
    break;

  case 222:
#line 1365 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2439 "parser.cc" // lalr1.cc:859
    break;

  case 223:
#line 1366 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[1].value).object_; }
#line 2445 "parser.cc" // lalr1.cc:859
    break;

  case 224:
#line 1371 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2451 "parser.cc" // lalr1.cc:859
    break;

  case 225:
#line 1372 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2457 "parser.cc" // lalr1.cc:859
    break;

  case 226:
#line 1373 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2463 "parser.cc" // lalr1.cc:859
    break;

  case 227:
#line 1374 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2469 "parser.cc" // lalr1.cc:859
    break;

  case 228:
#line 1375 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2475 "parser.cc" // lalr1.cc:859
    break;

  case 229:
#line 1377 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2481 "parser.cc" // lalr1.cc:859
    break;

  case 230:
#line 1378 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2487 "parser.cc" // lalr1.cc:859
    break;

  case 231:
#line 1379 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2493 "parser.cc" // lalr1.cc:859
    break;

  case 232:
#line 1380 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2499 "parser.cc" // lalr1.cc:859
    break;

  case 233:
#line 1381 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2505 "parser.cc" // lalr1.cc:859
    break;

  case 234:
#line 1385 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = new structure(ref<formula>((yystack_[1].value).object_), ref<formula>((yystack_[0].value).object_),
        structure::function, structure::postargument, operator_precedence()); }
#line 2513 "parser.cc" // lalr1.cc:859
    break;

  case 235:
#line 1389 "parser.yy" // lalr1.cc:859
    { // $$.object_ = new integer_addition(ref<formula>($1.object_), ref<formula>($3.object_));
      structure* cp = new structure((yystack_[1].value).text_, structure::function);
      (yylhs.value).object_ = cp;
      cp->push_back(ref<formula>((yystack_[2].value).object_));
      cp->push_back(ref<formula>((yystack_[0].value).object_));
      cp->set(structure::infix);
      cp->set(plus_oprec); }
#line 2525 "parser.cc" // lalr1.cc:859
    break;

  case 236:
#line 1396 "parser.yy" // lalr1.cc:859
    { // $$.object_ = new integer_addition(ref<formula>($1.object_), new integer_negative(ref<formula>($3.object_)));
      structure* cp = new structure((yystack_[1].value).text_, structure::function);
      (yylhs.value).object_ = cp;
      cp->push_back(ref<formula>((yystack_[2].value).object_));
      cp->push_back(ref<formula>((yystack_[0].value).object_));
      cp->set(structure::infix);
      cp->set(minus_oprec); }
#line 2537 "parser.cc" // lalr1.cc:859
    break;

  case 237:
#line 1403 "parser.yy" // lalr1.cc:859
    { // $$.object_ = new integer_negative(ref<formula>($2.object_)); }
      structure* cp = new structure((yystack_[0].value).text_, structure::function);
      (yylhs.value).object_ = cp;
      cp->push_back(ref<formula>((yystack_[0].value).object_));
      cp->set(structure::prefix);
      cp->set(unary_minus_oprec); }
#line 2548 "parser.cc" // lalr1.cc:859
    break;

  case 238:
#line 1409 "parser.yy" // lalr1.cc:859
    {
      structure* cp = new structure((yystack_[1].value).text_, structure::function);
      (yylhs.value).object_ = cp;
      cp->push_back(ref<formula>((yystack_[2].value).object_));
      cp->push_back(ref<formula>((yystack_[0].value).object_));
      cp->set(structure::infix);
      cp->set(mult_oprec); }
#line 2560 "parser.cc" // lalr1.cc:859
    break;

  case 239:
#line 1416 "parser.yy" // lalr1.cc:859
    {
      structure* cp = new structure((yystack_[1].value).text_, structure::function);
      (yylhs.value).object_ = cp;
      cp->push_back(ref<formula>((yystack_[2].value).object_));
      cp->push_back(ref<formula>((yystack_[0].value).object_));
      cp->set(structure::infix);
      cp->set(divide_oprec); }
#line 2572 "parser.cc" // lalr1.cc:859
    break;

  case 240:
#line 1423 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2578 "parser.cc" // lalr1.cc:859
    break;

  case 241:
#line 1427 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = new sequence(member_list_set_); }
#line 2584 "parser.cc" // lalr1.cc:859
    break;

  case 242:
#line 1428 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[1].value).object_; }
#line 2590 "parser.cc" // lalr1.cc:859
    break;

  case 243:
#line 1429 "parser.yy" // lalr1.cc:859
    {
      mli_table_stack_.pop_level();
      (yylhs.value).object_ = new bound_formula(
        ref<variable>((yystack_[3].value).object_), ref<formula>((yystack_[1].value).object_), bound_formula::set_);
    }
#line 2600 "parser.cc" // lalr1.cc:859
    break;

  case 244:
#line 1434 "parser.yy" // lalr1.cc:859
    { mli_table_stack_.push_level(); }
#line 2606 "parser.cc" // lalr1.cc:859
    break;

  case 245:
#line 1435 "parser.yy" // lalr1.cc:859
    {
      mli_table_stack_.pop_level();
      variable_list* vsp = cast_pointer<variable_list>((yystack_[4].value).object_);
      sequence* sp =
        new sequence(ref<formula>((yystack_[3].value).object_), implicit_set_);
      sp->push_back(ref<formula>((yystack_[1].value).object_));
      (yylhs.value).object_ =
        new bound_formula(*vsp, ref<formula>(sp));
    }
#line 2620 "parser.cc" // lalr1.cc:859
    break;

  case 246:
#line 1447 "parser.yy" // lalr1.cc:859
    {
      mli_table_stack_.push_level();
      (yylhs.value).object_ = new variable((yystack_[0].value).text_, variable::object_, 0);
      table_stack_insert((yystack_[0].value).text_, token::set_variable, (yylhs.value).object_);
    }
#line 2630 "parser.cc" // lalr1.cc:859
    break;

  case 247:
#line 1452 "parser.yy" // lalr1.cc:859
    {
      mli_table_stack_.push_level();
      (yylhs.value).object_ = (yystack_[0].value).object_;
      table_stack_insert((yystack_[0].value).text_, token::metaobjectvariable, (yystack_[0].value).object_);
    }
#line 2640 "parser.cc" // lalr1.cc:859
    break;

  case 248:
#line 1460 "parser.yy" // lalr1.cc:859
    {
      binder_declaration_context = false;
      (yylhs.value).object_ = new variable_list(ref<variable>((yystack_[0].value).object_), bound_formula::implicit_set_);
    }
#line 2649 "parser.cc" // lalr1.cc:859
    break;

  case 249:
#line 1464 "parser.yy" // lalr1.cc:859
    { binder_declaration_context = true; }
#line 2655 "parser.cc" // lalr1.cc:859
    break;

  case 250:
#line 1465 "parser.yy" // lalr1.cc:859
    {
      binder_declaration_context = false;
      (yylhs.value).object_ = (yystack_[3].value).object_;
      cast_pointer<variable_list>((yylhs.value).object_)->push_back(ref<variable>((yystack_[0].value).object_), bound_formula::implicit_set_);
    }
#line 2665 "parser.cc" // lalr1.cc:859
    break;

  case 251:
#line 1473 "parser.yy" // lalr1.cc:859
    {
      ref<object> v = new variable((yystack_[0].value).text_, variable::object_, 0);
      table_stack_insert((yystack_[0].value).text_, token::implicit_set_variable, v);
      (yylhs.value).object_ = v;
    }
#line 2675 "parser.cc" // lalr1.cc:859
    break;

  case 252:
#line 1478 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = (yystack_[0].value).object_;
      table_stack_insert((yystack_[0].value).text_, token::metaobjectvariable, (yystack_[0].value).object_);
    }
#line 2684 "parser.cc" // lalr1.cc:859
    break;

  case 253:
#line 1485 "parser.yy" // lalr1.cc:859
    {
      sequence* vp = new sequence(member_list_set_);
      (yylhs.value).object_ = vp;
      vp->push_back(ref<formula>((yystack_[0].value).object_)); }
#line 2693 "parser.cc" // lalr1.cc:859
    break;

  case 254:
#line 1489 "parser.yy" // lalr1.cc:859
    {
      (yylhs.value).object_ = (yystack_[2].value).object_;
      sequence& vp = cast_reference<sequence>((yylhs.value).object_);
      vp.push_back(ref<formula>((yystack_[0].value).object_));
    }
#line 2703 "parser.cc" // lalr1.cc:859
    break;

  case 255:
#line 1497 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2709 "parser.cc" // lalr1.cc:859
    break;

  case 256:
#line 1498 "parser.yy" // lalr1.cc:859
    { (yylhs.value).object_ = (yystack_[0].value).object_; }
#line 2715 "parser.cc" // lalr1.cc:859
    break;


#line 2719 "parser.cc" // lalr1.cc:859
            default:
              break;
            }
        }
      catch (const syntax_error& yyexc)
        {
          error (yyexc);
          YYERROR;
        }
      YY_SYMBOL_PRINT ("-> $$ =", yylhs);
      yypop_ (yylen);
      yylen = 0;
      YY_STACK_PRINT ();

      // Shift the result of the reduction.
      yypush_ (YY_NULLPTR, yylhs);
    }
    goto yynewstate;

  /*--------------------------------------.
  | yyerrlab -- here on detecting error.  |
  `--------------------------------------*/
  yyerrlab:
    // If not already recovering from an error, report this error.
    if (!yyerrstatus_)
      {
        ++yynerrs_;
        error (yysyntax_error_ (yystack_[0].state, yyla));
      }


    if (yyerrstatus_ == 3)
      {
        /* If just tried and failed to reuse lookahead token after an
           error, discard it.  */

        // Return failure if at end of input.
        if (yyla.type_get () == yyeof_)
          YYABORT;
        else if (!yyla.empty ())
          {
            yy_destroy_ ("Error: discarding", yyla);
            yyla.clear ();
          }
      }

    // Else will try to reuse lookahead token after shifting the error token.
    goto yyerrlab1;


  /*---------------------------------------------------.
  | yyerrorlab -- error raised explicitly by YYERROR.  |
  `---------------------------------------------------*/
  yyerrorlab:

    /* Pacify compilers like GCC when the user code never invokes
       YYERROR and the label yyerrorlab therefore never appears in user
       code.  */
    if (false)
      goto yyerrorlab;
    /* Do not reclaim the symbols of the rule whose action triggered
       this YYERROR.  */
    yypop_ (yylen);
    yylen = 0;
    goto yyerrlab1;

  /*-------------------------------------------------------------.
  | yyerrlab1 -- common code for both syntax error and YYERROR.  |
  `-------------------------------------------------------------*/
  yyerrlab1:
    yyerrstatus_ = 3;   // Each real token shifted decrements this.
    {
      stack_symbol_type error_token;
      for (;;)
        {
          yyn = yypact_[yystack_[0].state];
          if (!yy_pact_value_is_default_ (yyn))
            {
              yyn += yyterror_;
              if (0 <= yyn && yyn <= yylast_ && yycheck_[yyn] == yyterror_)
                {
                  yyn = yytable_[yyn];
                  if (0 < yyn)
                    break;
                }
            }

          // Pop the current state because it cannot handle the error token.
          if (yystack_.size () == 1)
            YYABORT;

          yy_destroy_ ("Error: popping", yystack_[0]);
          yypop_ ();
          YY_STACK_PRINT ();
        }


      // Shift the error token.
      error_token.state = yyn;
      yypush_ ("Shifting", error_token);
    }
    goto yynewstate;

    // Accept.
  yyacceptlab:
    yyresult = 0;
    goto yyreturn;

    // Abort.
  yyabortlab:
    yyresult = 1;
    goto yyreturn;

  yyreturn:
    if (!yyla.empty ())
      yy_destroy_ ("Cleanup: discarding lookahead", yyla);

    /* Do not reclaim the symbols of the rule whose action triggered
       this YYABORT or YYACCEPT.  */
    yypop_ (yylen);
    while (1 < yystack_.size ())
      {
        yy_destroy_ ("Cleanup: popping", yystack_[0]);
        yypop_ ();
      }

    return yyresult;
  }
    catch (...)
      {
        YYCDEBUG << "Exception caught: cleaning lookahead and stack"
                 << std::endl;
        // Do not try to display the values of the reclaimed symbols,
        // as their printer might throw an exception.
        if (!yyla.empty ())
          yy_destroy_ (YY_NULLPTR, yyla);

        while (1 < yystack_.size ())
          {
            yy_destroy_ (YY_NULLPTR, yystack_[0]);
            yypop_ ();
          }
        throw;
      }
  }

  void
  mli_parser::error (const syntax_error& yyexc)
  {
    error (yyexc.what());
  }

  // Generate an error message.
  std::string
  mli_parser::yysyntax_error_ (state_type, const symbol_type&) const
  {
    return YY_("syntax error");
  }


  const short int mli_parser::yypact_ninf_ = -364;

  const short int mli_parser::yytable_ninf_ = -257;

  const short int
  mli_parser::yypact_[] =
  {
     596,  -364,   -58,   -32,   -28,    75,   355,  -364,    77,    11,
      66,    83,  -364,  -364,   -15,  -364,  -364,  -364,  -364,  -364,
    -364,  -364,    92,  -364,   113,   183,   154,   167,   127,   206,
    -364,    36,  -364,   136,  -364,   226,    36,   -15,   -15,   194,
     202,  -364,  -364,  -364,   229,   363,  -364,    -9,  -364,  -364,
    -364,   -15,   157,   165,  -364,   176,  -364,   177,   166,  -364,
    -364,   477,  -364,  -364,   198,   204,  -364,  -364,  -364,   -66,
     174,   204,   179,  -364,   369,   205,  -364,   422,  -364,  -364,
    -364,  -364,  -364,   580,  -364,  -364,   718,  -364,   477,   525,
     477,   209,   477,  -364,   -24,  -364,   212,  -364,  -364,   426,
    -364,  -364,    89,   216,  -364,  -364,  -364,  -364,  -364,   628,
      46,   286,   217,  -364,  -364,  -364,   224,  -364,  -364,   125,
     238,  -364,  -364,   228,   275,  -364,    30,   -14,   580,  -364,
     718,  -364,  -364,  -364,  -364,  -364,   580,  -364,   408,   718,
    -364,   294,   -24,   245,   -12,   156,  -364,   248,  -364,   182,
     330,   279,   -65,  -364,  -364,  -364,   477,   420,   477,   477,
     642,   212,  -364,  -364,  -364,  -364,     7,     7,   580,   348,
     580,   580,   580,   580,   580,   580,   580,   686,   216,  -364,
    -364,  -364,  -364,  -364,   580,   580,  -364,  -364,    12,    28,
      46,  -364,  -364,   718,   718,     7,   718,   718,   718,   718,
     718,   718,   718,   718,   718,   728,   217,  -364,   718,  -364,
     375,   -15,   -15,   -15,  -364,  -364,  -364,  -364,  -364,   363,
    -364,  -364,   -15,   371,  -364,   306,  -364,  -364,   307,   363,
     363,   376,  -364,    86,   288,   124,   182,   273,   298,   460,
      56,   308,   310,  -364,   131,   580,   718,  -364,   -14,   -14,
    -364,   311,   315,   338,   339,   341,  -364,   347,  -364,  -364,
    -364,  -364,  -364,   288,   408,   580,   288,   288,  -364,   370,
     181,   181,   444,  -364,   288,   364,  -364,  -364,    24,  -364,
    -364,  -364,    97,  -364,  -364,  -364,   182,   182,   407,   182,
     182,  -364,   -69,   -69,   182,   182,   182,  -364,  -364,   141,
     182,   354,   368,   372,   401,   405,   477,  -364,  -364,  -364,
    -364,   -10,   185,   250,   143,   406,     1,  -364,   229,  -364,
     433,   477,   -24,  -364,   580,  -364,   718,  -364,  -364,  -364,
      74,  -364,  -364,   718,  -364,   232,   182,   477,   580,   673,
     453,   718,   288,   408,  -364,    39,   412,  -364,   415,  -364,
     580,   718,  -364,  -364,  -364,  -364,  -364,  -364,  -364,   477,
     477,   477,   580,   580,   718,   718,  -364,  -364,   417,   102,
     416,  -364,  -364,  -364,     1,   -24,   288,   182,  -364,  -364,
     580,  -364,  -364,  -364,   178,   419,  -364,   -26,    59,   424,
     425,    41,  -364,  -364,  -364,    12,    28,   288,   408,   182,
     363,   363,   363,   254,   455,   461,   288,   288,   182,   182,
     212,     1,  -364,     1,   119,   478,   580,   131,  -364,  -364,
    -364,  -364,  -364,  -364,  -364,   463,   466,   467,   718,   212,
    -364,  -364,  -364,  -364,   255,  -364,  -364,  -364,  -364,   182,
    -364
  };

  const unsigned char
  mli_parser::yydefact_[] =
  {
       0,     4,     0,     0,     0,     0,     2,     6,     0,     0,
       0,     0,     1,     5,     0,    11,     7,     8,     9,    57,
      58,    59,     0,    30,    32,     0,    44,     0,     0,     0,
      44,    35,    34,     0,    37,     0,    36,     0,     0,     0,
       0,    45,    48,    46,     0,   187,    47,     0,    90,    33,
      39,     0,     0,     0,    94,    92,    96,    93,     0,    60,
      65,   187,   126,   127,     0,     0,   165,   255,   219,   124,
     166,     0,   167,   224,   228,   226,   227,   225,   229,   230,
     231,   232,   233,   187,   220,   221,     0,   175,   187,   244,
     187,     0,   187,    85,    98,   109,     0,   111,   112,     0,
     125,   138,   110,     0,   152,   148,   168,   169,   150,     0,
       0,     0,   216,   222,   217,   240,     0,    89,    91,     0,
       0,    55,    62,     0,     0,    64,     0,   118,   187,   143,
       0,   179,   144,   180,   228,   225,   187,   181,     0,     0,
     237,     0,     0,   109,   110,     0,   246,   228,   241,   253,
       0,     0,     0,   113,    61,    86,   187,   119,   187,   187,
       0,   121,    14,    16,    17,    18,     0,     0,   187,     0,
     187,   187,   187,   187,   187,   187,   187,     0,   149,    20,
      22,    23,   166,   167,   187,   187,   156,   163,     0,     0,
     188,   189,   190,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   218,    27,     0,   234,
       0,     0,     0,     0,    40,    42,    43,    41,    31,   187,
      95,    97,     0,     0,    70,     0,    66,    68,     0,   187,
     187,     0,    69,     0,   146,     0,   211,     0,     0,     0,
       0,   120,   151,   223,     0,   187,     0,   242,   116,   117,
     114,   115,     0,     0,     0,     0,   226,     0,    15,   136,
     137,   128,   129,   130,   131,   187,   139,   140,   183,   182,
     184,   185,   186,    21,   157,     0,   200,   201,   193,   197,
     205,   206,   195,   202,   191,   192,   141,   142,     0,   170,
     171,   238,   235,   236,   172,   173,   174,   239,    28,     0,
     214,     0,     0,     0,     0,     0,   187,    87,    99,   100,
     101,     0,   109,   110,     0,     0,     0,    74,     0,    72,
       0,   187,    12,    63,   187,   145,     0,   210,   177,   178,
     187,   251,   252,   249,   248,     0,   254,   187,   187,     0,
       0,     0,   132,   133,   164,     0,     0,   194,     0,   196,
     187,     0,   213,    38,    49,    51,    53,    56,    88,   187,
     187,   187,   187,   187,     0,     0,    73,    81,    82,     0,
      76,    78,    80,    71,     0,    13,   147,   212,   158,   159,
     187,   162,   176,   160,     0,     0,   243,     0,     0,     0,
       0,     0,   208,   209,   207,     0,     0,   134,   135,   215,
     187,   187,   187,     0,   109,   109,   104,   105,   106,   108,
       0,     0,    75,     0,     0,     0,   187,     0,    19,    24,
      25,    26,    29,   199,   204,     0,     0,     0,     0,    84,
      77,    79,    67,   161,     0,   250,    50,    52,    54,   107,
     245
  };

  const short int
  mli_parser::yypgoto_[] =
  {
    -364,  -364,  -364,   518,  -364,  -364,   160,  -160,  -364,  -364,
     373,   -94,  -364,  -100,  -364,  -364,  -364,  -364,  -364,  -364,
    -364,  -364,  -364,   536,  -364,  -364,  -364,  -364,  -364,   -80,
    -364,     0,  -364,  -364,  -364,   253,  -364,  -364,  -364,  -364,
    -364,  -364,  -364,  -364,  -363,  -364,   159,  -364,  -364,  -225,
    -364,   -16,  -364,   526,  -364,  -364,   483,   271,  -364,  -364,
    -364,   -59,   -78,  -364,  -364,  -364,  -141,  -364,  -364,   510,
    -364,    34,  -364,   268,  -364,  -364,   474,   260,  -364,  -364,
     274,  -364,  -364,  -364,  -364,   394,   413,  -364,  -364,   210,
    -364,  -364,   211,   324,  -364,   537,  -364,  -364,  -364,   -45,
    -364,  -147,  -364,  -364,  -364,  -364,  -364,  -364,   192,  -364,
    -364
  };

  const short int
  mli_parser::yydefgoto_[] =
  {
      -1,     5,     6,     7,     8,   320,   161,   162,   163,   178,
     179,   164,   206,   165,    15,    24,    26,    33,    29,    30,
      50,   119,   214,    31,    41,   215,   400,   401,   402,    42,
     219,   368,    43,    44,    45,    59,    60,   126,   226,   227,
     228,   229,   230,   231,   369,   370,   371,   372,   410,    91,
     305,    92,    47,    48,    55,    57,    93,   307,   308,   309,
     310,    94,    95,    96,    97,    98,    99,   100,   101,   129,
     233,   102,   103,   104,   382,   186,   105,   106,   141,   330,
     107,   108,   109,   110,   190,   191,   192,   278,   346,   279,
     282,   348,   283,   347,   394,   131,   235,   209,   299,   138,
     112,   113,   114,   115,   150,   151,   333,   385,   334,   152,
     116
  };

  const short int
  mli_parser::yytable_[] =
  {
     111,   258,   127,   181,   319,   156,   157,   156,   157,   180,
     143,   414,   207,   257,    22,    46,   111,  -257,  -257,   198,
      46,   359,   157,   170,   171,   261,   262,     9,   367,   142,
     257,   153,   246,   128,    19,  -122,    20,    52,    53,   216,
     204,   140,   247,   145,   149,   111,   224,   111,   430,    37,
      19,   120,    20,    10,   288,    37,   222,    11,   257,   223,
      38,   276,    39,    40,   172,   173,   174,   175,   176,   259,
      21,   158,   260,   158,   277,    12,   418,   280,   181,    19,
     159,    20,   159,   158,   180,   236,    21,   158,   242,   117,
     281,   238,   159,    14,   239,   392,   159,   248,   249,   250,
     251,    39,    40,   217,   393,   328,   298,    39,    40,    16,
     232,   111,   111,   111,   111,    21,   345,   137,   329,   188,
     189,  -198,   144,   264,   170,   171,   225,    65,    25,   198,
     199,   200,   378,    71,   379,   172,   173,   174,   175,   176,
     238,   312,   210,   422,    37,   211,   212,   213,   286,   287,
     204,   289,   290,   291,   292,   293,   294,   295,   296,   297,
     311,   419,   234,   300,    17,   172,   173,   174,   175,   176,
     237,   322,    28,   380,   314,   425,   426,   427,   193,   194,
     331,    18,   195,   324,   111,   111,   325,   364,   365,   345,
      23,   193,   194,   332,  -203,   195,    39,    40,   411,    27,
     412,   336,   263,   306,   266,   267,   268,   269,   270,   271,
     272,   302,   303,   304,   321,   411,    32,   432,   274,   275,
     343,   326,   315,    35,   327,    34,   196,   197,   312,   360,
     361,   198,   199,   200,    49,   201,   202,   203,   351,   196,
     197,   352,    51,    54,   198,   199,   200,   311,   201,   202,
     203,    56,   204,   313,    58,   121,   243,   172,   173,  -257,
    -257,   314,   375,   122,   125,   204,   198,   199,   200,   258,
     198,   199,   200,   123,   124,  -153,   111,   220,   387,   335,
    -154,   377,   404,   405,   416,   170,   171,   204,   384,   193,
     194,   204,   111,   195,   362,   363,   391,   128,   428,   342,
     248,   142,   142,   130,  -256,   398,   399,   154,   172,   173,
     174,   175,   176,   160,   403,   111,   111,   177,   205,   408,
     409,   193,   194,   208,   221,   195,   172,   173,   174,   175,
     176,   172,   173,   174,   175,   176,   218,   196,   197,   386,
     313,   240,   198,   199,   200,   241,   201,   202,   203,   172,
     173,   174,   175,   176,  -247,   111,   111,   111,   376,     2,
       3,     4,   440,   204,   172,   173,   174,   175,   176,   196,
     197,   -10,   388,   242,   198,   199,   200,   244,   201,   202,
     203,   196,   197,   439,   397,   245,   198,   199,   200,   265,
     201,   202,   203,   301,    61,   204,   406,   407,   243,   316,
      62,    63,  -136,  -136,   317,   318,   323,   204,   158,  -123,
    -136,  -155,  -136,   337,   415,    64,    65,    66,    67,    68,
      69,    70,    71,    72,    73,    74,    75,    76,    77,    78,
      79,    80,    81,    82,    39,    40,   338,   339,    83,   340,
     172,   173,   174,   175,   176,   341,   172,   350,    84,    85,
     434,  -257,   353,    86,    87,  -137,  -137,    62,    63,   166,
     167,   374,    88,  -137,   344,  -137,   354,   168,    89,   169,
     355,    90,    64,    65,    66,    67,    68,    69,    70,    71,
      72,    73,    74,    75,    76,    77,    78,    79,    80,    81,
      82,   196,   197,  -187,  -187,    83,   198,   199,   200,   356,
     201,   202,   203,   357,   366,    84,    85,   390,    61,   395,
      86,    87,   396,   413,    62,    63,   417,   204,   -83,    88,
     172,   173,   174,   175,    13,    89,   420,   421,    90,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      75,    76,    77,    78,    79,    80,    81,    82,   198,   199,
     200,   273,    83,  -102,   172,   173,   174,   175,   176,  -103,
     243,   436,    84,    85,   437,   438,    36,    86,    87,   204,
     429,   373,   431,   118,   146,   155,    88,   358,   433,   132,
      67,    68,    89,   187,   284,    90,    73,   147,    75,    76,
     135,    78,    79,    80,    81,    82,    -3,     1,   381,   389,
       2,     3,     4,   285,   383,   423,   349,   424,   133,   435,
      84,    85,   -10,     0,     0,    86,     0,     0,     0,     0,
       0,     0,     0,     0,   139,     0,     0,     0,     0,     0,
      89,     0,   148,    65,    66,    67,    68,     0,    70,    71,
      72,    73,   134,    75,    76,   135,    78,    79,    80,    81,
      82,     0,     0,     0,     0,    83,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    84,    85,     0,     0,     0,
      86,    87,     0,     0,     0,     0,     0,     0,     0,   136,
       0,    65,    66,    67,    68,    89,   182,    71,   183,    73,
     134,    75,    76,   135,    78,    79,    80,    81,    82,   252,
     253,   254,   255,    73,   134,   256,    76,   135,    78,    79,
      80,    81,    82,    84,    85,     0,     0,     0,    86,    87,
       0,     0,     0,   184,     0,     0,    65,   185,    67,    68,
       0,     0,    71,    89,    73,   134,    75,    76,   135,    78,
      79,    80,    81,    82,   253,   254,   255,    73,   134,   256,
      76,   135,    78,    79,    80,    81,    82,     0,    84,    85,
       0,     0,     0,    86,    87,     0,     0,     0,     0,     0,
       0,     0,   139,    67,    68,     0,     0,     0,    89,    73,
     134,    75,    76,   135,    78,    79,    80,    81,    82,    73,
     134,   256,    76,   135,    78,    79,    80,    81,    82,     0,
       0,     0,     0,    84,    85,     0,     0,     0,    86,     0,
       0,     0,     0,     0,     0,     0,     0,   139,     0,     0,
       0,     0,     0,    89
  };

  const short int
  mli_parser::yycheck_[] =
  {
      45,   161,    61,   103,   229,    31,    32,    31,    32,   103,
      88,   374,   112,   160,    14,    31,    61,    31,    32,    88,
      36,    31,    32,    35,    36,   166,   167,    85,    27,    88,
     177,    90,    97,    99,    49,   101,    51,    37,    38,   119,
     109,    86,   107,    88,    89,    90,   126,    92,   411,    19,
      49,    51,    51,    85,   195,    19,    26,    85,   205,    29,
      24,    49,    71,    72,    76,    77,    78,    79,    80,    62,
      85,    97,    65,    97,    62,     0,   102,    49,   178,    49,
     106,    51,   106,    97,   178,   130,    85,    97,   100,    98,
      62,   136,   106,    16,   139,    56,   106,   156,   157,   158,
     159,    71,    72,   119,    65,    49,   206,    71,    72,    98,
     126,   156,   157,   158,   159,    85,    92,    83,    62,    73,
      74,    97,    88,   168,    35,    36,   126,    53,    15,    88,
      89,    90,    58,    59,    60,    76,    77,    78,    79,    80,
     185,   219,    17,   102,    19,    20,    21,    22,   193,   194,
     109,   196,   197,   198,   199,   200,   201,   202,   203,   204,
     219,   102,   128,   208,    98,    76,    77,    78,    79,    80,
     136,   230,    18,    99,   219,   400,   401,   402,    35,    36,
      49,    98,    39,    97,   229,   230,   100,    44,    45,    92,
      98,    35,    36,    62,    97,    39,    71,    72,    96,    16,
      98,   246,   168,   219,   170,   171,   172,   173,   174,   175,
     176,   211,   212,   213,   230,    96,    49,    98,   184,   185,
     265,    97,   222,    17,   100,    98,    83,    84,   306,    44,
      45,    88,    89,    90,    98,    92,    93,    94,    97,    83,
      84,   100,    16,    49,    88,    89,    90,   306,    92,    93,
      94,    49,   109,   219,    25,    98,   100,    76,    77,    78,
      79,   306,   321,    98,    98,   109,    88,    89,    90,   429,
      88,    89,    90,    97,    97,   101,   321,    49,   337,   245,
     101,   326,   360,   361,   106,    35,    36,   109,   333,    35,
      36,   109,   337,    39,    44,    45,   341,    99,    44,   265,
     359,   360,   361,    99,    99,   350,   351,    98,    76,    77,
      78,    79,    80,   101,   359,   360,   361,   101,   101,   364,
     365,    35,    36,    99,    49,    39,    76,    77,    78,    79,
      80,    76,    77,    78,    79,    80,    98,    83,    84,   107,
     306,    47,    88,    89,    90,   100,    92,    93,    94,    76,
      77,    78,    79,    80,   106,   400,   401,   402,   324,     4,
       5,     6,   107,   109,    76,    77,    78,    79,    80,    83,
      84,    16,   338,   100,    88,    89,    90,    47,    92,    93,
      94,    83,    84,   428,   350,   106,    88,    89,    90,    41,
      92,    93,    94,    18,    31,   109,   362,   363,   100,    28,
      37,    38,    33,    34,    98,    98,    30,   109,    97,   101,
      41,   101,    43,    98,   380,    52,    53,    54,    55,    56,
      57,    58,    59,    60,    61,    62,    63,    64,    65,    66,
      67,    68,    69,    70,    71,    72,    98,    98,    75,    98,
      76,    77,    78,    79,    80,    98,    76,    40,    85,    86,
     416,    31,    98,    90,    91,    33,    34,    37,    38,    33,
      34,    28,    99,    41,   100,    43,    98,    41,   105,    43,
      98,   108,    52,    53,    54,    55,    56,    57,    58,    59,
      60,    61,    62,    63,    64,    65,    66,    67,    68,    69,
      70,    83,    84,    73,    74,    75,    88,    89,    90,    98,
      92,    93,    94,    98,    98,    85,    86,    54,    31,    97,
      90,    91,    97,    97,    37,    38,    97,   109,   101,    99,
      76,    77,    78,    79,     6,   105,   102,   102,   108,    52,
      53,    54,    55,    56,    57,    58,    59,    60,    61,    62,
      63,    64,    65,    66,    67,    68,    69,    70,    88,    89,
      90,   178,    75,    98,    76,    77,    78,    79,    80,    98,
     100,    98,    85,    86,    98,    98,    30,    90,    91,   109,
     410,   318,   413,    47,    49,    92,    99,   306,   100,    69,
      55,    56,   105,   109,   190,   108,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,     0,     1,   330,   339,
       4,     5,     6,   190,   330,   395,   282,   396,    71,   417,
      85,    86,    16,    -1,    -1,    90,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    99,    -1,    -1,    -1,    -1,    -1,
     105,    -1,   107,    53,    54,    55,    56,    -1,    58,    59,
      60,    61,    62,    63,    64,    65,    66,    67,    68,    69,
      70,    -1,    -1,    -1,    -1,    75,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    85,    86,    -1,    -1,    -1,
      90,    91,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    99,
      -1,    53,    54,    55,    56,   105,    58,    59,    60,    61,
      62,    63,    64,    65,    66,    67,    68,    69,    70,    57,
      58,    59,    60,    61,    62,    63,    64,    65,    66,    67,
      68,    69,    70,    85,    86,    -1,    -1,    -1,    90,    91,
      -1,    -1,    -1,    95,    -1,    -1,    53,    99,    55,    56,
      -1,    -1,    59,   105,    61,    62,    63,    64,    65,    66,
      67,    68,    69,    70,    58,    59,    60,    61,    62,    63,
      64,    65,    66,    67,    68,    69,    70,    -1,    85,    86,
      -1,    -1,    -1,    90,    91,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    99,    55,    56,    -1,    -1,    -1,   105,    61,
      62,    63,    64,    65,    66,    67,    68,    69,    70,    61,
      62,    63,    64,    65,    66,    67,    68,    69,    70,    -1,
      -1,    -1,    -1,    85,    86,    -1,    -1,    -1,    90,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    99,    -1,    -1,
      -1,    -1,    -1,   105
  };

  const unsigned char
  mli_parser::yystos_[] =
  {
       0,     1,     4,     5,     6,   114,   115,   116,   117,    85,
      85,    85,     0,   116,    16,   127,    98,    98,    98,    49,
      51,    85,   144,    98,   128,    15,   129,    16,    18,   131,
     132,   136,    49,   130,    98,    17,   136,    19,    24,    71,
      72,   137,   142,   145,   146,   147,   164,   165,   166,    98,
     133,    16,   144,   144,    49,   167,    49,   168,    25,   148,
     149,    31,    37,    38,    52,    53,    54,    55,    56,    57,
      58,    59,    60,    61,    62,    63,    64,    65,    66,    67,
      68,    69,    70,    75,    85,    86,    90,    91,    99,   105,
     108,   162,   164,   169,   174,   175,   176,   177,   178,   179,
     180,   181,   184,   185,   186,   189,   190,   193,   194,   195,
     196,   212,   213,   214,   215,   216,   223,    98,   166,   134,
     144,    98,    98,    97,    97,    98,   150,   174,    99,   182,
      99,   208,   182,   208,    62,    65,    99,   184,   212,    99,
     212,   191,   174,   175,   184,   212,    49,    62,   107,   212,
     217,   218,   222,   174,    98,   169,    31,    32,    97,   106,
     101,   119,   120,   121,   124,   126,    33,    34,    41,    43,
      35,    36,    76,    77,    78,    79,    80,   101,   122,   123,
     124,   126,    58,    60,    95,    99,   188,   189,    73,    74,
     197,   198,   199,    35,    36,    39,    83,    84,    88,    89,
      90,    92,    93,    94,   109,   101,   125,   126,    99,   210,
      17,    20,    21,    22,   135,   138,   142,   164,    98,   143,
      49,    49,    26,    29,   142,   144,   151,   152,   153,   154,
     155,   156,   164,   183,   184,   209,   212,   184,   212,   212,
      47,   100,   100,   100,    47,   106,    97,   107,   174,   174,
     174,   174,    57,    58,    59,    60,    63,   214,   120,    62,
      65,   179,   179,   184,   212,    41,   184,   184,   184,   184,
     184,   184,   184,   123,   184,   184,    49,    62,   200,   202,
      49,    62,   203,   205,   198,   199,   212,   212,   179,   212,
     212,   212,   212,   212,   212,   212,   212,   212,   126,   211,
     212,    18,   144,   144,   144,   163,   164,   170,   171,   172,
     173,   174,   175,   184,   212,   144,    28,    98,    98,   162,
     118,   164,   174,    30,    97,   100,    97,   100,    49,    62,
     192,    49,    62,   219,   221,   184,   212,    98,    98,    98,
      98,    98,   184,   212,   100,    92,   201,   206,   204,   206,
      40,    97,   100,    98,    98,    98,    98,    98,   170,    31,
      44,    45,    44,    45,    44,    45,    98,    27,   144,   157,
     158,   159,   160,   148,    28,   174,   184,   212,    58,    60,
      99,   186,   187,   193,   212,   220,   107,   174,   184,   190,
      54,   212,    56,    65,   207,    97,    97,   184,   212,   212,
     139,   140,   141,   212,   175,   175,   184,   184,   212,   212,
     161,    96,    98,    97,   157,   184,   106,    97,   102,   102,
     102,   102,   102,   202,   205,   162,   162,   162,    44,   119,
     157,   159,    98,   100,   184,   221,    98,    98,    98,   212,
     107
  };

  const unsigned char
  mli_parser::yyr1_[] =
  {
       0,   113,   114,   114,   114,   115,   115,   116,   116,   116,
     117,   116,   118,   118,   119,   119,   120,   120,   120,   121,
     122,   122,   123,   123,   124,   124,   124,   125,   125,   126,
     128,   127,   129,   129,   130,   131,   131,   133,   132,   134,
     134,   135,   135,   135,   136,   136,   137,   137,   137,   139,
     138,   140,   138,   141,   138,   143,   142,   144,   144,   144,
     145,   146,   147,   148,   149,   150,   150,   151,   151,   151,
     151,   152,   153,   154,   155,   156,   157,   157,   158,   158,
     159,   159,   160,   161,   160,   162,   162,   163,   163,   164,
     165,   165,   166,   166,   167,   167,   168,   168,   169,   170,
     170,   170,   171,   171,   172,   172,   173,   173,   173,   174,
     174,   175,   175,   175,   175,   175,   175,   175,   175,   175,
     175,   175,   176,   176,   177,   177,   178,   178,   178,   178,
     178,   178,   178,   178,   178,   178,   179,   179,   180,   180,
     180,   180,   180,   181,   181,   182,   183,   183,   184,   184,
     184,   184,   184,   185,   185,   185,   186,   186,   187,   187,
     187,   187,   187,   188,   188,   189,   189,   189,   189,   190,
     190,   190,   190,   190,   190,   191,   190,   192,   192,   193,
     193,   194,   194,   194,   194,   194,   194,   196,   195,   197,
     197,   197,   197,   198,   198,   199,   199,   200,   201,   200,
     202,   202,   203,   204,   203,   205,   205,   206,   207,   207,
     208,   209,   209,   210,   211,   211,   212,   212,   212,   213,
     213,   213,   213,   213,   214,   214,   214,   214,   214,   214,
     214,   214,   214,   214,   215,   215,   215,   215,   215,   215,
     215,   216,   216,   216,   217,   216,   218,   218,   219,   220,
     219,   221,   221,   222,   222,   223,   223
  };

  const unsigned char
  mli_parser::yyr2_[] =
  {
       0,     2,     1,     0,     1,     2,     1,     3,     3,     3,
       0,     2,     1,     2,     1,     2,     1,     1,     1,     5,
       1,     2,     1,     1,     5,     5,     5,     1,     2,     5,
       0,    10,     0,     4,     1,     1,     2,     0,     7,     0,
       2,     1,     1,     1,     0,     2,     1,     1,     1,     0,
       6,     0,     6,     0,     6,     0,     6,     1,     1,     1,
       2,     3,     3,     4,     2,     0,     2,     5,     1,     1,
       1,     3,     2,     3,     2,     4,     1,     3,     1,     3,
       1,     1,     1,     0,     3,     1,     2,     1,     2,     2,
       1,     2,     2,     2,     1,     3,     1,     3,     1,     1,
       1,     1,     3,     3,     3,     3,     3,     5,     3,     1,
       1,     1,     1,     2,     3,     3,     3,     3,     2,     2,
       3,     2,     1,     3,     1,     1,     1,     1,     3,     3,
       3,     3,     4,     4,     5,     5,     1,     1,     1,     3,
       3,     3,     3,     2,     2,     3,     1,     3,     1,     2,
       1,     3,     1,     1,     1,     3,     2,     3,     1,     1,
       1,     3,     1,     1,     3,     1,     1,     1,     1,     1,
       3,     3,     3,     3,     3,     0,     5,     1,     1,     2,
       2,     2,     3,     3,     3,     3,     3,     0,     2,     1,
       1,     2,     2,     2,     3,     2,     3,     1,     0,     4,
       1,     1,     1,     0,     4,     1,     1,     2,     1,     1,
       3,     1,     3,     3,     1,     3,     1,     1,     2,     1,
       1,     1,     1,     3,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     2,     3,     3,     2,     3,     3,
       1,     2,     3,     5,     0,     8,     1,     1,     1,     0,
       4,     1,     1,     1,     3,     1,     1
  };


#if YYDEBUG
  // YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
  // First, the terminals, then, starting at \a yyntokens_, nonterminals.
  const char*
  const mli_parser::yytname_[] =
  {
  "$end", "error", "$undefined", "\"token error\"", "\"level_max\"",
  "\"sublevel_max\"", "\"unify_count_max\"", "\"goal\"", "\"unification\"",
  "\"substitution\"", "\"type\"", "\":-\"", "\"!\"", "\"solve\"",
  "\"verify\"", "\"include\"", "\"theory\"", "\"end\"",
  "\"formal system\"", "\"definition\"", "\"postulate\"", "\"axiom\"",
  "\"rule\"", "\"conjecture\"", "\"theorem\"", "\"proof\"", "\"claim\"",
  "\"premise\"", "\"by\"", "\"conclusion\"", "\"∎\"", "\"⊢\"",
  "\"⊣\"", "\"≡\"", "\"≢\"", "\"≣\"", "\"≣̷\"", "\"fail\"",
  "\"succeed\"", "\"free for\"", "\"in\"", "\"free in\"", "\"use\"",
  "\"not\"", "\"≔\"", "\"≕\"", "\"≝\"", "\"↓\"", "\"↑\"",
  "\"name\"", "\"name or object\"", "\"label\"",
  "\"metapredicate constant\"", "\"predicate constant\"",
  "\"atom constant\"", "\"function constant\"", "\"term constant\"",
  "\"metaformula variable\"", "\"object formula variable\"",
  "\"predicate variable\"", "\"atom variable\"", "\"term variable\"",
  "\"metaobjectvariable\"", "\"function variable\"",
  "\"constant variable\"", "\"object variable\"", "\"all variable\"",
  "\"exist variable\"", "\"Set variable\"", "\"set variable\"",
  "\"implicit set variable\"", "\"identifier constant\"",
  "\"identifier variable\"", "\"∀\"", "\"∃\"", "\"¬\"", "\"∧\"",
  "\"∨\"", "\"⇒\"", "\"⇐\"", "\"⇔\"", "\"~[\"", "\"~]\"", "\"=\"",
  "\"≠\"", "unsigned_integer_value", "signed_integer_value", "\"++\"",
  "\"*\"", "\"+\"", "\"-\"", "\"Set\"", "\"∈\"", "\"⊂\"", "\"⊊\"",
  "\":\"", "\";\"", "\",\"", "\".\"", "\"(\"", "\")\"", "\"[\"", "\"]\"",
  "\"⟨\"", "\"⟩\"", "\"{\"", "\"|\"", "\"}\"", "\"~\"", "\"/\"",
  "\"\\\\\"", "unary_quantifier", "unary_minus", "$accept", "file",
  "file_contents", "command", "$@1", "declared_formula",
  "metaformula_substitution_sequence", "substitution_for_metaformula",
  "metaformula_substitution", "formula_substitution_sequence",
  "substitution_for_formula", "formula_substitution",
  "term_substitution_sequence", "term_substitution", "theory", "$@2",
  "include_theory", "theory_name", "theory_body", "formal_system", "$@3",
  "formal_system_body", "formal_system_body_item", "theory_body_list",
  "theory_body_item", "postulate", "$@4", "$@5", "$@6",
  "definition_labelstatement", "$@7", "statement_name", "theorem",
  "theorem_statement", "theorem_head", "proof", "proof_head",
  "proof_lines", "proof_line", "subproof", "subproof_statement",
  "subproof_head", "proof_line_head", "proof_of_conclusion",
  "find_statement", "find_statement_list", "find_statement_item",
  "find_statement_name", "@8", "statement", "definition_statement",
  "identifier_declaration", "declarator_list",
  "declarator_identifier_list", "identifier_constant_list",
  "identifier_variable_list", "statement_body", "definition",
  "metaformula_definition", "object_formula_definition", "term_definition",
  "metaformula", "pure_metaformula", "simple_metaformula",
  "atomic_metaformula", "special_metaformula", "meta_object_free",
  "metapredicate", "metapredicate_function", "metapredicate_argument",
  "metapredicate_argument_body", "object_formula", "very_simple_formula",
  "quantized_formula", "simple_formula", "quantized_body",
  "atomic_formula", "predicate", "$@9", "is_set_identifier",
  "predicate_function", "logic_formula", "quantizer_declaration", "$@10",
  "quantized_variable_list", "all_variable_list", "exist_variable_list",
  "all_identifier_list", "$@11", "all_identifier", "exist_identifier_list",
  "$@12", "exist_identifier", "in_set", "set_identifier",
  "predicate_argument", "predicate_argument_body", "function_argument",
  "function_argument_body", "term", "simple_term", "term_identifier",
  "function_term", "set_term", "$@13", "set_single_identifier_variable",
  "implicit_set_identifier_list", "$@14", "implicit_set_identifier",
  "set_member_list", "function_term_identifier", YY_NULLPTR
  };


  const unsigned short int
  mli_parser::yyrline_[] =
  {
       0,   371,   371,   372,   373,   381,   382,   386,   389,   392,
     395,   395,   399,   400,   406,   407,   413,   414,   415,   420,
     428,   429,   435,   436,   440,   445,   450,   458,   459,   465,
     474,   473,   489,   490,   494,   505,   506,   511,   510,   517,
     518,   522,   523,   524,   528,   529,   538,   539,   540,   545,
     544,   552,   551,   563,   562,   577,   576,   586,   587,   588,
     592,   602,   613,   622,   630,   639,   640,   644,   671,   682,
     683,   697,   706,   716,   725,   732,   749,   750,   757,   759,
     765,   770,   779,   791,   791,   835,   836,   842,   843,   849,
     853,   854,   858,   859,   863,   866,   872,   875,   881,   891,
     892,   893,   897,   900,   911,   914,   925,   928,   931,   937,
     938,   942,   943,   944,   947,   951,   955,   959,   963,   964,
     965,   966,   971,   972,   976,   977,   981,   982,   983,   986,
     989,   992,   995,   998,  1001,  1005,  1012,  1013,  1017,  1018,
    1021,  1024,  1027,  1033,  1036,  1042,  1046,  1051,  1058,  1059,
    1062,  1063,  1064,  1068,  1069,  1070,  1074,  1079,  1087,  1088,
    1089,  1090,  1091,  1095,  1096,  1100,  1101,  1102,  1103,  1108,
    1109,  1116,  1123,  1130,  1137,  1144,  1144,  1153,  1158,  1166,
    1169,  1176,  1182,  1189,  1196,  1203,  1210,  1220,  1220,  1225,
    1226,  1227,  1233,  1242,  1243,  1247,  1248,  1252,  1256,  1256,
    1266,  1271,  1278,  1282,  1282,  1292,  1297,  1304,  1318,  1319,
    1324,  1328,  1332,  1339,  1343,  1347,  1354,  1355,  1356,  1362,
    1363,  1364,  1365,  1366,  1371,  1372,  1373,  1374,  1375,  1377,
    1378,  1379,  1380,  1381,  1385,  1389,  1396,  1403,  1409,  1416,
    1423,  1427,  1428,  1429,  1434,  1434,  1447,  1452,  1460,  1464,
    1464,  1473,  1478,  1485,  1489,  1497,  1498
  };

  // Print the state stack on the debug stream.
  void
  mli_parser::yystack_print_ ()
  {
    *yycdebug_ << "Stack now";
    for (stack_type::const_iterator
           i = yystack_.begin (),
           i_end = yystack_.end ();
         i != i_end; ++i)
      *yycdebug_ << ' ' << i->state;
    *yycdebug_ << std::endl;
  }

  // Report on the debug stream that the rule \a yyrule is going to be reduced.
  void
  mli_parser::yy_reduce_print_ (int yyrule)
  {
    unsigned int yylno = yyrline_[yyrule];
    int yynrhs = yyr2_[yyrule];
    // Print the symbols being reduced, and their result.
    *yycdebug_ << "Reducing stack by rule " << yyrule - 1
               << " (line " << yylno << "):" << std::endl;
    // The symbols being reduced.
    for (int yyi = 0; yyi < yynrhs; yyi++)
      YY_SYMBOL_PRINT ("   $" << yyi + 1 << " =",
                       yystack_[(yynrhs) - (yyi + 1)]);
  }
#endif // YYDEBUG

  // Symbol number corresponding to token number t.
  inline
  mli_parser::token_number_type
  mli_parser::yytranslate_ (int t)
  {
    static
    const token_number_type
    translate_table[] =
    {
     0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      75,    76,    77,    78,    79,    80,    81,    82,    83,    84,
      85,    86,    87,    88,    89,    90,    91,    92,    93,    94,
      95,    96,    97,    98,    99,   100,   101,   102,   103,   104,
     105,   106,   107,   108,   109,   110,   111,   112
    };
    const unsigned int user_token_number_max_ = 367;
    const token_number_type undef_token_ = 2;

    if (static_cast<int>(t) <= yyeof_)
      return yyeof_;
    else if (static_cast<unsigned int> (t) <= user_token_number_max_)
      return translate_table[t];
    else
      return undef_token_;
  }

#line 22 "parser.yy" // lalr1.cc:1167
} // mli
#line 3495 "parser.cc" // lalr1.cc:1167
#line 1501 "parser.yy" // lalr1.cc:1168


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

