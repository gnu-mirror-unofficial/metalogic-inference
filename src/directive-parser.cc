// A Bison parser, made by GNU Bison 3.8.1.

// Skeleton implementation for Bison LALR(1) parsers in C++

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

// DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
// especially those whose name start with YY_ or yy_.  They are
// private implementation details that can be changed or removed.


// Take the name prefix into account.
#define yylex   mlilex



#include "directive-parser.hh"


// Unqualified %code blocks.
#line 117 "../../mli-root/src/directive-parser.yy"


  // #define YYDEBUG 1


    /* MetaLogic Inference Database Parser. */

  #include <algorithm>
  #include <fstream>
  #include <iostream>
  #include <iterator>
  #include <sstream>
  #include <stack>
  #include <vector>
  #include <utility>

  #include "database.hh"
  #include "definition.hh"
  #include "proposition.hh"
  #include "substitution.hh"
  #include "metacondition.hh"

  #include "precedence.hh"

  extern std::string infile_name;

  extern bool declaration_context;
  extern bool maybe_set_declaration_context;
  extern bool proofline_database_context;
  extern bool statement_substitution_context;
  extern int bracket_depth;

  extern mli::directive_parser::token_type declared_token;
  extern int declared_type;
  extern int current_token;


  namespace mli {

    kleenean the_directive_type = false;

    bool set_trace = false;
    trace_type trace_flag = trace_none;


    symbol_table_t directive_symbol_table;



    mli::directive_parser::token_type directive_to_token(variable::type t) {
      switch (t) {
#if USE_VARIABLE_META
        case variable::metaformula_:   return mli::directive_parser::token::metaformula_variable;
#endif
        case variable::formula_:       return mli::directive_parser::token::object_formula_variable;
        case variable::predicate_:     return mli::directive_parser::token::predicate_variable;
        case variable::atom_:          return mli::directive_parser::token::atom_variable;
        case variable::function_:      return mli::directive_parser::token::function_variable;
        case variable::object_:        return mli::directive_parser::token::object_variable;
        default:                       return mli::directive_parser::token::token_error;
      }
    }


    // For bound variable definitions, set to the token type that
    // should be inserted in the symbol table:
    directive_parser::token_type directive_bound_variable_type = directive_parser::token_type(0);



    directive_parser::token_type directive_define_variable(semantic_type& yylval) {
      if (statement_substitution_context) {
        statement_substitution_context = false;
        std::optional<std::pair<directive_parser::token_type, mli::ref<mli::unit>>> x = mli::directive_symbol_table.find_top(yylval.text);
        if (!x)  return mli::directive_parser::token::plain_name;
        yylval.object = x->second;
        yylval.number = x->first;
        return x->first;
      }

      if (declaration_context)
        return mli::directive_parser::token::plain_name;

      std::optional<std::pair<mli::directive_parser::token_type, mli::ref<mli::unit>>> x = mli::directive_symbol_table.find(yylval.text);


      if (!x) {
        // Not a bound variable case:
        if (directive_bound_variable_type == mli::free_variable_context)
          return mli::directive_parser::token::plain_name;

        // Bound variable case: Create a limited variable og bind 1, insert at the secondary
        // (bound variable) stack level.
        ref<variable> v;
        v->bind_ = 1;
        directive_symbol_table.insert(yylval.text, {directive_bound_variable_type, v});

        yylval.object = v;
        yylval.number = directive_bound_variable_type;

        return directive_bound_variable_type;
      }


      mli::variable* vp = mli::ref_cast<mli::variable*>(x->second);

      if (vp != nullptr
        && (vp->depth_ == -1 || directive_bound_variable_type != mli::free_variable_context)) {

        if (directive_bound_variable_type == mli::free_variable_context) {
          // Case definition of a free variable:

          // Check if it is a variable which is declared without definition, in which case make
          // a copy with right proof depth, insert it in the symbol table, and change x->second
          // so subsequently the new copy is used instead of the original lookup value.
          mli::ref<mli::variable> v(make, *vp);

          directive_symbol_table.insert_or_assign(yylval.text, {x->first, v});

          x->second = v;
        }
        else {
          // Case definition of a bound variable:

          // If ordinary (not limited), create a limited variable of bind 1, insert at
          // the secondary (bound variable) stack level.
          // If limited:
          //   If not defined, create a limited variable of bind 1, and insert at the
          //   primary (free variable) stack level.
          //   If defined, return it (do nothing, as x is already set to it).

          if (!vp->is_limited()) {
            mli::ref<mli::variable> v(make, *vp);
            v->metatype_ = variable::limited_;
            v->bind_ = 1;

            directive_symbol_table.insert(yylval.text, {x->first, v});

            x->second = v;
          }
          else if (vp->depth_ == -1) {
            mli::ref<mli::variable> v(make, *vp);

            directive_symbol_table.insert_or_assign(yylval.text, {x->first, v});

            x->second = v;
          }

          yylval.object = x->second;
          yylval.number = x->first;

          return directive_bound_variable_type;
        }
      }

      yylval.object = x->second;
      yylval.number = x->first;

      return x->first;
    }

  } // namespace mli



#line 214 "../../mli-root/src/directive-parser.cc"


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


// Whether we are compiled with exception support.
#ifndef YY_EXCEPTIONS
# if defined __GNUC__ && !defined __EXCEPTIONS
#  define YY_EXCEPTIONS 0
# else
#  define YY_EXCEPTIONS 1
# endif
#endif

#define YYRHSLOC(Rhs, K) ((Rhs)[K].location)
/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

# ifndef YYLLOC_DEFAULT
#  define YYLLOC_DEFAULT(Current, Rhs, N)                               \
    do                                                                  \
      if (N)                                                            \
        {                                                               \
          (Current).begin  = YYRHSLOC (Rhs, 1).begin;                   \
          (Current).end    = YYRHSLOC (Rhs, N).end;                     \
        }                                                               \
      else                                                              \
        {                                                               \
          (Current).begin = (Current).end = YYRHSLOC (Rhs, 0).end;      \
        }                                                               \
    while (false)
# endif


// Enable debugging if requested.
#if MLIDEBUG

// A pseudo ostream that takes yydebug_ into account.
# define YYCDEBUG if (yydebug_) (*yycdebug_)

# define YY_SYMBOL_PRINT(Title, Symbol)         \
  do {                                          \
    if (yydebug_)                               \
    {                                           \
      *yycdebug_ << Title << ' ';               \
      yy_print_ (*yycdebug_, Symbol);           \
      *yycdebug_ << '\n';                       \
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
      yy_stack_print_ ();                \
  } while (false)

#else // !MLIDEBUG

# define YYCDEBUG if (false) std::cerr
# define YY_SYMBOL_PRINT(Title, Symbol)  YY_USE (Symbol)
# define YY_REDUCE_PRINT(Rule)           static_cast<void> (0)
# define YY_STACK_PRINT()                static_cast<void> (0)

#endif // !MLIDEBUG

#define yyerrok         (yyerrstatus_ = 0)
#define yyclearin       (yyla.clear ())

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab
#define YYRECOVERING()  (!!yyerrstatus_)

#line 22 "../../mli-root/src/directive-parser.yy"
namespace mli {
#line 307 "../../mli-root/src/directive-parser.cc"

  /// Build a parser object.
  directive_parser::directive_parser (mli::directive_lexer& mlilex_yyarg, mli::location_type& loc_yyarg)
#if MLIDEBUG
    : yydebug_ (false),
      yycdebug_ (&std::cerr),
#else
    :
#endif
      mlilex (mlilex_yyarg),
      loc (loc_yyarg)
  {}

  directive_parser::~directive_parser ()
  {}

  directive_parser::syntax_error::~syntax_error () YY_NOEXCEPT YY_NOTHROW
  {}

  /*---------------.
  | symbol kinds.  |
  `---------------*/

  // basic_symbol.
  template <typename Base>
  directive_parser::basic_symbol<Base>::basic_symbol (const basic_symbol& that)
    : Base (that)
    , value (that.value)
    , location (that.location)
  {}


  /// Constructor for valueless symbols.
  template <typename Base>
  directive_parser::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, YY_MOVE_REF (location_type) l)
    : Base (t)
    , value ()
    , location (l)
  {}

  template <typename Base>
  directive_parser::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, YY_RVREF (value_type) v, YY_RVREF (location_type) l)
    : Base (t)
    , value (YY_MOVE (v))
    , location (YY_MOVE (l))
  {}

  template <typename Base>
  directive_parser::symbol_kind_type
  directive_parser::basic_symbol<Base>::type_get () const YY_NOEXCEPT
  {
    return this->kind ();
  }

  template <typename Base>
  bool
  directive_parser::basic_symbol<Base>::empty () const YY_NOEXCEPT
  {
    return this->kind () == symbol_kind::S_YYEMPTY;
  }

  template <typename Base>
  void
  directive_parser::basic_symbol<Base>::move (basic_symbol& s)
  {
    super_type::move (s);
    value = YY_MOVE (s.value);
    location = YY_MOVE (s.location);
  }

  // by_kind.
  directive_parser::by_kind::by_kind ()
    : kind_ (symbol_kind::S_YYEMPTY)
  {}

#if 201103L <= YY_CPLUSPLUS
  directive_parser::by_kind::by_kind (by_kind&& that)
    : kind_ (that.kind_)
  {
    that.clear ();
  }
#endif

  directive_parser::by_kind::by_kind (const by_kind& that)
    : kind_ (that.kind_)
  {}

  directive_parser::by_kind::by_kind (token_kind_type t)
    : kind_ (yytranslate_ (t))
  {}

  void
  directive_parser::by_kind::clear () YY_NOEXCEPT
  {
    kind_ = symbol_kind::S_YYEMPTY;
  }

  void
  directive_parser::by_kind::move (by_kind& that)
  {
    kind_ = that.kind_;
    that.clear ();
  }

  directive_parser::symbol_kind_type
  directive_parser::by_kind::kind () const YY_NOEXCEPT
  {
    return kind_;
  }

  directive_parser::symbol_kind_type
  directive_parser::by_kind::type_get () const YY_NOEXCEPT
  {
    return this->kind ();
  }


  // by_state.
  directive_parser::by_state::by_state () YY_NOEXCEPT
    : state (empty_state)
  {}

  directive_parser::by_state::by_state (const by_state& that) YY_NOEXCEPT
    : state (that.state)
  {}

  void
  directive_parser::by_state::clear () YY_NOEXCEPT
  {
    state = empty_state;
  }

  void
  directive_parser::by_state::move (by_state& that)
  {
    state = that.state;
    that.clear ();
  }

  directive_parser::by_state::by_state (state_type s) YY_NOEXCEPT
    : state (s)
  {}

  directive_parser::symbol_kind_type
  directive_parser::by_state::kind () const YY_NOEXCEPT
  {
    if (state == empty_state)
      return symbol_kind::S_YYEMPTY;
    else
      return YY_CAST (symbol_kind_type, yystos_[+state]);
  }

  directive_parser::stack_symbol_type::stack_symbol_type ()
  {}

  directive_parser::stack_symbol_type::stack_symbol_type (YY_RVREF (stack_symbol_type) that)
    : super_type (YY_MOVE (that.state), YY_MOVE (that.value), YY_MOVE (that.location))
  {
#if 201103L <= YY_CPLUSPLUS
    // that is emptied.
    that.state = empty_state;
#endif
  }

  directive_parser::stack_symbol_type::stack_symbol_type (state_type s, YY_MOVE_REF (symbol_type) that)
    : super_type (s, YY_MOVE (that.value), YY_MOVE (that.location))
  {
    // that is emptied.
    that.kind_ = symbol_kind::S_YYEMPTY;
  }

#if YY_CPLUSPLUS < 201103L
  directive_parser::stack_symbol_type&
  directive_parser::stack_symbol_type::operator= (const stack_symbol_type& that)
  {
    state = that.state;
    value = that.value;
    location = that.location;
    return *this;
  }

  directive_parser::stack_symbol_type&
  directive_parser::stack_symbol_type::operator= (stack_symbol_type& that)
  {
    state = that.state;
    value = that.value;
    location = that.location;
    // that is emptied.
    that.state = empty_state;
    return *this;
  }
#endif

  template <typename Base>
  void
  directive_parser::yy_destroy_ (const char* yymsg, basic_symbol<Base>& yysym) const
  {
    if (yymsg)
      YY_SYMBOL_PRINT (yymsg, yysym);

    // User destructor.
    YY_USE (yysym.kind ());
  }

#if MLIDEBUG
  template <typename Base>
  void
  directive_parser::yy_print_ (std::ostream& yyo, const basic_symbol<Base>& yysym) const
  {
    std::ostream& yyoutput = yyo;
    YY_USE (yyoutput);
    if (yysym.empty ())
      yyo << "empty symbol";
    else
      {
        symbol_kind_type yykind = yysym.kind ();
        yyo << (yykind < YYNTOKENS ? "token" : "nterm")
            << ' ' << yysym.name () << " ("
            << yysym.location << ": ";
        YY_USE (yykind);
        yyo << ')';
      }
  }
#endif

  void
  directive_parser::yypush_ (const char* m, YY_MOVE_REF (stack_symbol_type) sym)
  {
    if (m)
      YY_SYMBOL_PRINT (m, sym);
    yystack_.push (YY_MOVE (sym));
  }

  void
  directive_parser::yypush_ (const char* m, state_type s, YY_MOVE_REF (symbol_type) sym)
  {
#if 201103L <= YY_CPLUSPLUS
    yypush_ (m, stack_symbol_type (s, std::move (sym)));
#else
    stack_symbol_type ss (s, sym);
    yypush_ (m, ss);
#endif
  }

  void
  directive_parser::yypop_ (int n)
  {
    yystack_.pop (n);
  }

#if MLIDEBUG
  std::ostream&
  directive_parser::debug_stream () const
  {
    return *yycdebug_;
  }

  void
  directive_parser::set_debug_stream (std::ostream& o)
  {
    yycdebug_ = &o;
  }


  directive_parser::debug_level_type
  directive_parser::debug_level () const
  {
    return yydebug_;
  }

  void
  directive_parser::set_debug_level (debug_level_type l)
  {
    yydebug_ = l;
  }
#endif // MLIDEBUG

  directive_parser::state_type
  directive_parser::yy_lr_goto_state_ (state_type yystate, int yysym)
  {
    int yyr = yypgoto_[yysym - YYNTOKENS] + yystate;
    if (0 <= yyr && yyr <= yylast_ && yycheck_[yyr] == yystate)
      return yytable_[yyr];
    else
      return yydefgoto_[yysym - YYNTOKENS];
  }

  bool
  directive_parser::yy_pact_value_is_default_ (int yyvalue)
  {
    return yyvalue == yypact_ninf_;
  }

  bool
  directive_parser::yy_table_value_is_error_ (int yyvalue)
  {
    return yyvalue == yytable_ninf_;
  }

  int
  directive_parser::operator() ()
  {
    return parse ();
  }

  int
  directive_parser::parse ()
  {
    int yyn;
    /// Length of the RHS of the rule being reduced.
    int yylen = 0;

    // Error handling.
    int yynerrs_ = 0;
    int yyerrstatus_ = 0;

    /// The lookahead symbol.
    symbol_type yyla;

    /// The locations where the error started and ended.
    stack_symbol_type yyerror_range[3];

    /// The return value of parse ().
    int yyresult;

#if YY_EXCEPTIONS
    try
#endif // YY_EXCEPTIONS
      {
    YYCDEBUG << "Starting parse\n";


    // User initialization code.
#line 32 "../../mli-root/src/directive-parser.yy"
{
  yyla.location = loc; // Initialize the initial location.
}

#line 646 "../../mli-root/src/directive-parser.cc"


    /* Initialize the stack.  The initial state will be set in
       yynewstate, since the latter expects the semantical and the
       location values to have been already stored, initialize these
       stacks with a primary value.  */
    yystack_.clear ();
    yypush_ (YY_NULLPTR, 0, YY_MOVE (yyla));

  /*-----------------------------------------------.
  | yynewstate -- push a new symbol on the stack.  |
  `-----------------------------------------------*/
  yynewstate:
    YYCDEBUG << "Entering state " << int (yystack_[0].state) << '\n';
    YY_STACK_PRINT ();

    // Accept?
    if (yystack_[0].state == yyfinal_)
      YYACCEPT;

    goto yybackup;


  /*-----------.
  | yybackup.  |
  `-----------*/
  yybackup:
    // Try to take a decision without lookahead.
    yyn = yypact_[+yystack_[0].state];
    if (yy_pact_value_is_default_ (yyn))
      goto yydefault;

    // Read a lookahead token.
    if (yyla.empty ())
      {
        YYCDEBUG << "Reading a token\n";
#if YY_EXCEPTIONS
        try
#endif // YY_EXCEPTIONS
          {
            yyla.kind_ = yytranslate_ (yylex (&yyla.value, &yyla.location));
          }
#if YY_EXCEPTIONS
        catch (const syntax_error& yyexc)
          {
            YYCDEBUG << "Caught exception: " << yyexc.what() << '\n';
            error (yyexc);
            goto yyerrlab1;
          }
#endif // YY_EXCEPTIONS
      }
    YY_SYMBOL_PRINT ("Next token is", yyla);

    if (yyla.kind () == symbol_kind::S_YYerror)
    {
      // The scanner already issued an error message, process directly
      // to error recovery.  But do not keep the error token as
      // lookahead, it is too special and may lead us to an endless
      // loop in error recovery. */
      yyla.kind_ = symbol_kind::S_YYUNDEF;
      goto yyerrlab1;
    }

    /* If the proper action on seeing token YYLA.TYPE is to reduce or
       to detect an error, take that action.  */
    yyn += yyla.kind ();
    if (yyn < 0 || yylast_ < yyn || yycheck_[yyn] != yyla.kind ())
      {
        goto yydefault;
      }

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
    yypush_ ("Shifting", state_type (yyn), YY_MOVE (yyla));
    goto yynewstate;


  /*-----------------------------------------------------------.
  | yydefault -- do the default action for the current state.  |
  `-----------------------------------------------------------*/
  yydefault:
    yyn = yydefact_[+yystack_[0].state];
    if (yyn == 0)
      goto yyerrlab;
    goto yyreduce;


  /*-----------------------------.
  | yyreduce -- do a reduction.  |
  `-----------------------------*/
  yyreduce:
    yylen = yyr2_[yyn];
    {
      stack_symbol_type yylhs;
      yylhs.state = yy_lr_goto_state_ (yystack_[yylen].state, yyr1_[yyn]);
      /* If YYLEN is nonzero, implement the default value of the
         action: '$$ = $1'.  Otherwise, use the top of the stack.

         Otherwise, the following line sets YYLHS.VALUE to garbage.
         This behavior is undocumented and Bison users should not rely
         upon it.  */
      if (yylen)
        yylhs.value = yystack_[yylen - 1].value;
      else
        yylhs.value = yystack_[0].value;

      // Default location.
      {
        stack_type::slice range (yystack_, yylen);
        YYLLOC_DEFAULT (yylhs.location, range, yylen);
        yyerror_range[1].location = yylhs.location;
      }

      // Perform the reduction.
      YY_REDUCE_PRINT (yyn);
#if YY_EXCEPTIONS
      try
#endif // YY_EXCEPTIONS
        {
          switch (yyn)
            {
  case 3: // file: file_contents
#line 604 "../../mli-root/src/directive-parser.yy"
                  {}
#line 784 "../../mli-root/src/directive-parser.cc"
    break;

  case 4: // file: error
#line 605 "../../mli-root/src/directive-parser.yy"
          {
      declaration_context = false;
      directive_bound_variable_type = free_variable_context;
      YYABORT;
    }
#line 794 "../../mli-root/src/directive-parser.cc"
    break;

  case 5: // file_contents: file_contents command
#line 614 "../../mli-root/src/directive-parser.yy"
                          {}
#line 800 "../../mli-root/src/directive-parser.cc"
    break;

  case 6: // file_contents: command
#line 615 "../../mli-root/src/directive-parser.yy"
                          {}
#line 806 "../../mli-root/src/directive-parser.cc"
    break;

  case 7: // command: diagnostic_statement
#line 620 "../../mli-root/src/directive-parser.yy"
                         {}
#line 812 "../../mli-root/src/directive-parser.cc"
    break;

  case 8: // command: trace_statement
#line 621 "../../mli-root/src/directive-parser.yy"
                    {}
#line 818 "../../mli-root/src/directive-parser.cc"
    break;

  case 9: // command: proof_strictness
#line 622 "../../mli-root/src/directive-parser.yy"
                     {}
#line 824 "../../mli-root/src/directive-parser.cc"
    break;

  case 10: // command: limits
#line 623 "../../mli-root/src/directive-parser.yy"
           {}
#line 830 "../../mli-root/src/directive-parser.cc"
    break;

  case 11: // diagnostic_statement: "diagnostic" diagnostic_type diagnostic
#line 628 "../../mli-root/src/directive-parser.yy"
                                            { unused_variable = the_directive_type; }
#line 836 "../../mli-root/src/directive-parser.cc"
    break;

  case 12: // diagnostic_type: "ignored"
#line 633 "../../mli-root/src/directive-parser.yy"
              { the_directive_type = false; }
#line 842 "../../mli-root/src/directive-parser.cc"
    break;

  case 13: // diagnostic_type: "warning"
#line 634 "../../mli-root/src/directive-parser.yy"
              { the_directive_type = undefined; }
#line 848 "../../mli-root/src/directive-parser.cc"
    break;

  case 14: // diagnostic_type: "error"
#line 635 "../../mli-root/src/directive-parser.yy"
              { the_directive_type = true; }
#line 854 "../../mli-root/src/directive-parser.cc"
    break;

  case 16: // trace_statement: trace_qualifier trace_type
#line 645 "../../mli-root/src/directive-parser.yy"
                             {
    if (set_trace)
      trace_value |= trace_flag;
    else
      trace_value &= ~trace_flag;
  }
#line 865 "../../mli-root/src/directive-parser.cc"
    break;

  case 17: // trace_qualifier: "trace"
#line 655 "../../mli-root/src/directive-parser.yy"
            { set_trace = true; }
#line 871 "../../mli-root/src/directive-parser.cc"
    break;

  case 18: // trace_qualifier: "untrace"
#line 656 "../../mli-root/src/directive-parser.yy"
              { set_trace = false; }
#line 877 "../../mli-root/src/directive-parser.cc"
    break;

  case 19: // trace_type: "all"
#line 661 "../../mli-root/src/directive-parser.yy"
          { trace_flag = trace_all; }
#line 883 "../../mli-root/src/directive-parser.cc"
    break;

  case 20: // trace_type: "null"
#line 662 "../../mli-root/src/directive-parser.yy"
           { trace_flag = trace_null; }
#line 889 "../../mli-root/src/directive-parser.cc"
    break;

  case 21: // trace_type: "empty"
#line 663 "../../mli-root/src/directive-parser.yy"
            { trace_flag = trace_empty; }
#line 895 "../../mli-root/src/directive-parser.cc"
    break;

  case 22: // trace_type: "result"
#line 664 "../../mli-root/src/directive-parser.yy"
             { trace_flag = trace_result; }
#line 901 "../../mli-root/src/directive-parser.cc"
    break;

  case 23: // trace_type: "proof"
#line 665 "../../mli-root/src/directive-parser.yy"
            { trace_flag = trace_proof; }
#line 907 "../../mli-root/src/directive-parser.cc"
    break;

  case 24: // trace_type: "solve"
#line 666 "../../mli-root/src/directive-parser.yy"
            { trace_flag = trace_solve; }
#line 913 "../../mli-root/src/directive-parser.cc"
    break;

  case 25: // trace_type: "prooftree"
#line 667 "../../mli-root/src/directive-parser.yy"
                { trace_flag = trace_prooftree; }
#line 919 "../../mli-root/src/directive-parser.cc"
    break;

  case 26: // trace_type: "unify"
#line 668 "../../mli-root/src/directive-parser.yy"
            { trace_flag = trace_unify; }
#line 925 "../../mli-root/src/directive-parser.cc"
    break;

  case 27: // trace_type: "split"
#line 669 "../../mli-root/src/directive-parser.yy"
            { trace_flag = trace_split; }
#line 931 "../../mli-root/src/directive-parser.cc"
    break;

  case 28: // trace_type: "substitute"
#line 670 "../../mli-root/src/directive-parser.yy"
                 { trace_flag = trace_substitute; }
#line 937 "../../mli-root/src/directive-parser.cc"
    break;

  case 29: // trace_type: "statement"
#line 671 "../../mli-root/src/directive-parser.yy"
                { trace_flag = trace_statement; }
#line 943 "../../mli-root/src/directive-parser.cc"
    break;

  case 30: // trace_type: "database"
#line 672 "../../mli-root/src/directive-parser.yy"
               { trace_flag = trace_database; }
#line 949 "../../mli-root/src/directive-parser.cc"
    break;

  case 31: // trace_type: "formula" "type"
#line 673 "../../mli-root/src/directive-parser.yy"
                     { trace_flag = trace_formula_type; }
#line 955 "../../mli-root/src/directive-parser.cc"
    break;

  case 32: // trace_type: "unspecializable"
#line 674 "../../mli-root/src/directive-parser.yy"
                      { trace_flag = trace_unspecializable; }
#line 961 "../../mli-root/src/directive-parser.cc"
    break;

  case 33: // trace_type: "variable" "type"
#line 675 "../../mli-root/src/directive-parser.yy"
                      { trace_flag = trace_variable_type; }
#line 967 "../../mli-root/src/directive-parser.cc"
    break;

  case 34: // trace_type: "variable" "label"
#line 676 "../../mli-root/src/directive-parser.yy"
                       { trace_flag = trace_variable_label; }
#line 973 "../../mli-root/src/directive-parser.cc"
    break;

  case 35: // trace_type: "structure" "type"
#line 677 "../../mli-root/src/directive-parser.yy"
                       { trace_flag = trace_structure_type; }
#line 979 "../../mli-root/src/directive-parser.cc"
    break;

  case 36: // trace_type: "thread"
#line 678 "../../mli-root/src/directive-parser.yy"
             { trace_flag = trace_thread; }
#line 985 "../../mli-root/src/directive-parser.cc"
    break;

  case 37: // trace_type: "level"
#line 679 "../../mli-root/src/directive-parser.yy"
            { trace_flag = trace_level; }
#line 991 "../../mli-root/src/directive-parser.cc"
    break;

  case 38: // proof_strictness: "strict" "proof"
#line 684 "../../mli-root/src/directive-parser.yy"
                          { mli::strict_proof = true; }
#line 997 "../../mli-root/src/directive-parser.cc"
    break;

  case 39: // proof_strictness: "conditional" "proof"
#line 685 "../../mli-root/src/directive-parser.yy"
                          { mli::strict_proof = false; }
#line 1003 "../../mli-root/src/directive-parser.cc"
    break;

  case 40: // limits: "thread" "count" integer
#line 690 "../../mli-root/src/directive-parser.yy"
                                { thread_count = (difference_type)ref_cast<integer&>(yystack_[0].value.object); }
#line 1009 "../../mli-root/src/directive-parser.cc"
    break;

  case 41: // limits: "level" "max" "natural number value"
#line 691 "../../mli-root/src/directive-parser.yy"
                                          { level_max = (size_type)ref_cast<integer&>(yystack_[0].value.object); }
#line 1015 "../../mli-root/src/directive-parser.cc"
    break;

  case 42: // limits: "sublevel" "max" "natural number value"
#line 692 "../../mli-root/src/directive-parser.yy"
                                             { sublevel_max = (size_type)ref_cast<integer&>(yystack_[0].value.object); }
#line 1021 "../../mli-root/src/directive-parser.cc"
    break;

  case 43: // limits: "proof" "count" "natural number value"
#line 693 "../../mli-root/src/directive-parser.yy"
                                            { proof_count = (size_type)ref_cast<integer&>(yystack_[0].value.object); }
#line 1027 "../../mli-root/src/directive-parser.cc"
    break;

  case 44: // limits: "unify" "count" "max" "natural number value"
#line 694 "../../mli-root/src/directive-parser.yy"
                                                  { unify_count_max = (size_type)ref_cast<integer&>(yystack_[0].value.object); }
#line 1033 "../../mli-root/src/directive-parser.cc"
    break;


#line 1037 "../../mli-root/src/directive-parser.cc"

            default:
              break;
            }
        }
#if YY_EXCEPTIONS
      catch (const syntax_error& yyexc)
        {
          YYCDEBUG << "Caught exception: " << yyexc.what() << '\n';
          error (yyexc);
          YYERROR;
        }
#endif // YY_EXCEPTIONS
      YY_SYMBOL_PRINT ("-> $$ =", yylhs);
      yypop_ (yylen);
      yylen = 0;

      // Shift the result of the reduction.
      yypush_ (YY_NULLPTR, YY_MOVE (yylhs));
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
        context yyctx (*this, yyla);
        std::string msg = yysyntax_error_ (yyctx);
        error (yyla.location, YY_MOVE (msg));
      }


    yyerror_range[1].location = yyla.location;
    if (yyerrstatus_ == 3)
      {
        /* If just tried and failed to reuse lookahead token after an
           error, discard it.  */

        // Return failure if at end of input.
        if (yyla.kind () == symbol_kind::S_YYEOF)
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
    /* Pacify compilers when the user code never invokes YYERROR and
       the label yyerrorlab therefore never appears in user code.  */
    if (false)
      YYERROR;

    /* Do not reclaim the symbols of the rule whose action triggered
       this YYERROR.  */
    yypop_ (yylen);
    yylen = 0;
    YY_STACK_PRINT ();
    goto yyerrlab1;


  /*-------------------------------------------------------------.
  | yyerrlab1 -- common code for both syntax error and YYERROR.  |
  `-------------------------------------------------------------*/
  yyerrlab1:
    yyerrstatus_ = 3;   // Each real token shifted decrements this.
    // Pop stack until we find a state that shifts the error token.
    for (;;)
      {
        yyn = yypact_[+yystack_[0].state];
        if (!yy_pact_value_is_default_ (yyn))
          {
            yyn += symbol_kind::S_YYerror;
            if (0 <= yyn && yyn <= yylast_
                && yycheck_[yyn] == symbol_kind::S_YYerror)
              {
                yyn = yytable_[yyn];
                if (0 < yyn)
                  break;
              }
          }

        // Pop the current state because it cannot handle the error token.
        if (yystack_.size () == 1)
          YYABORT;

        yyerror_range[1].location = yystack_[0].location;
        yy_destroy_ ("Error: popping", yystack_[0]);
        yypop_ ();
        YY_STACK_PRINT ();
      }
    {
      stack_symbol_type error_token;

      yyerror_range[2].location = yyla.location;
      YYLLOC_DEFAULT (error_token.location, yyerror_range, 2);

      // Shift the error token.
      error_token.state = state_type (yyn);
      yypush_ ("Shifting", YY_MOVE (error_token));
    }
    goto yynewstate;


  /*-------------------------------------.
  | yyacceptlab -- YYACCEPT comes here.  |
  `-------------------------------------*/
  yyacceptlab:
    yyresult = 0;
    goto yyreturn;


  /*-----------------------------------.
  | yyabortlab -- YYABORT comes here.  |
  `-----------------------------------*/
  yyabortlab:
    yyresult = 1;
    goto yyreturn;


  /*-----------------------------------------------------.
  | yyreturn -- parsing is finished, return the result.  |
  `-----------------------------------------------------*/
  yyreturn:
    if (!yyla.empty ())
      yy_destroy_ ("Cleanup: discarding lookahead", yyla);

    /* Do not reclaim the symbols of the rule whose action triggered
       this YYABORT or YYACCEPT.  */
    yypop_ (yylen);
    YY_STACK_PRINT ();
    while (1 < yystack_.size ())
      {
        yy_destroy_ ("Cleanup: popping", yystack_[0]);
        yypop_ ();
      }

    return yyresult;
  }
#if YY_EXCEPTIONS
    catch (...)
      {
        YYCDEBUG << "Exception caught: cleaning lookahead and stack\n";
        // Do not try to display the values of the reclaimed symbols,
        // as their printers might throw an exception.
        if (!yyla.empty ())
          yy_destroy_ (YY_NULLPTR, yyla);

        while (1 < yystack_.size ())
          {
            yy_destroy_ (YY_NULLPTR, yystack_[0]);
            yypop_ ();
          }
        throw;
      }
#endif // YY_EXCEPTIONS
  }

  void
  directive_parser::error (const syntax_error& yyexc)
  {
    error (yyexc.location, yyexc.what ());
  }

  /* Return YYSTR after stripping away unnecessary quotes and
     backslashes, so that it's suitable for yyerror.  The heuristic is
     that double-quoting is unnecessary unless the string contains an
     apostrophe, a comma, or backslash (other than backslash-backslash).
     YYSTR is taken from yytname.  */
  std::string
  directive_parser::yytnamerr_ (const char *yystr)
  {
    if (*yystr == '"')
      {
        std::string yyr;
        char const *yyp = yystr;

        for (;;)
          switch (*++yyp)
            {
            case '\'':
            case ',':
              goto do_not_strip_quotes;

            case '\\':
              if (*++yyp != '\\')
                goto do_not_strip_quotes;
              else
                goto append;

            append:
            default:
              yyr += *yyp;
              break;

            case '"':
              return yyr;
            }
      do_not_strip_quotes: ;
      }

    return yystr;
  }

  std::string
  directive_parser::symbol_name (symbol_kind_type yysymbol)
  {
    return yytnamerr_ (yytname_[yysymbol]);
  }



  // directive_parser::context.
  directive_parser::context::context (const directive_parser& yyparser, const symbol_type& yyla)
    : yyparser_ (yyparser)
    , yyla_ (yyla)
  {}

  int
  directive_parser::context::expected_tokens (symbol_kind_type yyarg[], int yyargn) const
  {
    // Actual number of expected tokens
    int yycount = 0;

    const int yyn = yypact_[+yyparser_.yystack_[0].state];
    if (!yy_pact_value_is_default_ (yyn))
      {
        /* Start YYX at -YYN if negative to avoid negative indexes in
           YYCHECK.  In other words, skip the first -YYN actions for
           this state because they are default actions.  */
        const int yyxbegin = yyn < 0 ? -yyn : 0;
        // Stay within bounds of both yycheck and yytname.
        const int yychecklim = yylast_ - yyn + 1;
        const int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
        for (int yyx = yyxbegin; yyx < yyxend; ++yyx)
          if (yycheck_[yyx + yyn] == yyx && yyx != symbol_kind::S_YYerror
              && !yy_table_value_is_error_ (yytable_[yyx + yyn]))
            {
              if (!yyarg)
                ++yycount;
              else if (yycount == yyargn)
                return 0;
              else
                yyarg[yycount++] = YY_CAST (symbol_kind_type, yyx);
            }
      }

    if (yyarg && yycount == 0 && 0 < yyargn)
      yyarg[0] = symbol_kind::S_YYEMPTY;
    return yycount;
  }






  int
  directive_parser::yy_syntax_error_arguments_ (const context& yyctx,
                                                 symbol_kind_type yyarg[], int yyargn) const
  {
    /* There are many possibilities here to consider:
       - If this state is a consistent state with a default action, then
         the only way this function was invoked is if the default action
         is an error action.  In that case, don't check for expected
         tokens because there are none.
       - The only way there can be no lookahead present (in yyla) is
         if this state is a consistent state with a default action.
         Thus, detecting the absence of a lookahead is sufficient to
         determine that there is no unexpected or expected token to
         report.  In that case, just report a simple "syntax error".
       - Don't assume there isn't a lookahead just because this state is
         a consistent state with a default action.  There might have
         been a previous inconsistent state, consistent state with a
         non-default action, or user semantic action that manipulated
         yyla.  (However, yyla is currently not documented for users.)
       - Of course, the expected token list depends on states to have
         correct lookahead information, and it depends on the parser not
         to perform extra reductions after fetching a lookahead from the
         scanner and before detecting a syntax error.  Thus, state merging
         (from LALR or IELR) and default reductions corrupt the expected
         token list.  However, the list is correct for canonical LR with
         one exception: it will still contain any token that will not be
         accepted due to an error action in a later state.
    */

    if (!yyctx.lookahead ().empty ())
      {
        if (yyarg)
          yyarg[0] = yyctx.token ();
        int yyn = yyctx.expected_tokens (yyarg ? yyarg + 1 : yyarg, yyargn - 1);
        return yyn + 1;
      }
    return 0;
  }

  // Generate an error message.
  std::string
  directive_parser::yysyntax_error_ (const context& yyctx) const
  {
    // Its maximum.
    enum { YYARGS_MAX = 5 };
    // Arguments of yyformat.
    symbol_kind_type yyarg[YYARGS_MAX];
    int yycount = yy_syntax_error_arguments_ (yyctx, yyarg, YYARGS_MAX);

    char const* yyformat = YY_NULLPTR;
    switch (yycount)
      {
#define YYCASE_(N, S)                         \
        case N:                               \
          yyformat = S;                       \
        break
      default: // Avoid compiler warnings.
        YYCASE_ (0, YY_("syntax error"));
        YYCASE_ (1, YY_("syntax error, unexpected %s"));
        YYCASE_ (2, YY_("syntax error, unexpected %s, expecting %s"));
        YYCASE_ (3, YY_("syntax error, unexpected %s, expecting %s or %s"));
        YYCASE_ (4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
        YYCASE_ (5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
#undef YYCASE_
      }

    std::string yyres;
    // Argument number.
    std::ptrdiff_t yyi = 0;
    for (char const* yyp = yyformat; *yyp; ++yyp)
      if (yyp[0] == '%' && yyp[1] == 's' && yyi < yycount)
        {
          yyres += symbol_name (yyarg[yyi++]);
          ++yyp;
        }
      else
        yyres += *yyp;
    return yyres;
  }


  const signed char directive_parser::yypact_ninf_ = -38;

  const signed char directive_parser::yytable_ninf_ = -3;

  const signed char
  directive_parser::yypact_[] =
  {
       0,   -38,     1,   -12,    -6,    -4,    -7,    -5,   -38,   -38,
       9,    10,    14,    13,   -38,   -38,   -38,    29,   -38,   -38,
     -38,   -38,   -38,     7,   -11,   -10,     2,   -38,   -38,    23,
     -37,   -38,   -38,    -2,   -38,   -38,   -38,   -38,   -38,   -38,
     -38,   -38,   -38,   -38,   -38,   -38,   -38,    16,   -38,    33,
     -38,   -38,    35,   -38,   -38,   -38,   -38,    11,   -38,   -38,
     -38,   -38,   -38,   -38,   -38,   -38,   -38
  };

  const signed char
  directive_parser::yydefact_[] =
  {
       0,     4,     0,     0,     0,     0,     0,     0,    17,    18,
       0,     0,     0,     3,     6,     7,     8,     0,     9,    10,
      12,    13,    14,     0,     0,     0,     0,    39,    38,     0,
       0,     1,     5,     0,    19,    37,    23,    20,    21,    22,
      24,    25,    26,    27,    28,    29,    30,     0,    32,     0,
      36,    16,     0,    11,    41,    42,    43,     0,    45,    46,
      40,    33,    34,    31,    35,    15,    44
  };

  const signed char
  directive_parser::yypgoto_[] =
  {
     -38,   -38,   -38,    39,   -38,   -38,   -38,   -38,   -38,   -38,
     -38,   -38,   -38
  };

  const signed char
  directive_parser::yydefgoto_[] =
  {
       0,    12,    13,    14,    15,    23,    53,    16,    17,    51,
      18,    19,    60
  };

  const signed char
  directive_parser::yytable_[] =
  {
      -2,     1,    58,    59,     2,    24,    20,    21,    22,    61,
      62,    25,    26,    27,    31,    28,    52,     2,     3,     4,
       5,     6,     7,     8,     9,    29,    30,    63,    54,    55,
      10,     3,     4,     5,     6,     7,     8,     9,    11,    33,
      57,    56,    34,    10,    64,    65,     0,    35,     0,    36,
      66,    11,    32,     0,    37,    38,    39,    40,    41,    42,
      43,    44,    45,    46,    47,    48,    49,    50
  };

  const signed char
  directive_parser::yycheck_[] =
  {
       0,     1,    39,    40,     4,    17,     5,     6,     7,    11,
      12,    17,    16,    20,     0,    20,     9,     4,    18,    19,
      20,    21,    22,    23,    24,    16,    16,    11,    39,    39,
      30,    18,    19,    20,    21,    22,    23,    24,    38,    10,
      17,    39,    13,    30,    11,    10,    -1,    18,    -1,    20,
      39,    38,    13,    -1,    25,    26,    27,    28,    29,    30,
      31,    32,    33,    34,    35,    36,    37,    38
  };

  const unsigned char
  directive_parser::yystos_[] =
  {
       0,     1,     4,    18,    19,    20,    21,    22,    23,    24,
      30,    38,   158,   159,   160,   161,   164,   165,   167,   168,
       5,     6,     7,   162,    17,    17,    16,    20,    20,    16,
      16,     0,   160,    10,    13,    18,    20,    25,    26,    27,
      28,    29,    30,    31,    32,    33,    34,    35,    36,    37,
      38,   166,     9,   163,    39,    39,    39,    17,    39,    40,
     169,    11,    12,    11,    11,    10,    39
  };

  const unsigned char
  directive_parser::yyr1_[] =
  {
       0,   157,   158,   158,   158,   159,   159,   160,   160,   160,
     160,   161,   162,   162,   162,   163,   164,   165,   165,   166,
     166,   166,   166,   166,   166,   166,   166,   166,   166,   166,
     166,   166,   166,   166,   166,   166,   166,   166,   167,   167,
     168,   168,   168,   168,   168,   169,   169
  };

  const signed char
  directive_parser::yyr2_[] =
  {
       0,     2,     0,     1,     1,     2,     1,     1,     1,     1,
       1,     3,     1,     1,     1,     2,     2,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     2,     1,     2,     2,     2,     1,     1,     2,     2,
       3,     3,     3,     3,     4,     1,     1
  };


#if MLIDEBUG || 1
  // YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
  // First, the terminals, then, starting at \a YYNTOKENS, nonterminals.
  const char*
  const directive_parser::yytname_[] =
  {
  "\"end of file\"", "error", "\"invalid token\"", "\"token error\"",
  "\"diagnostic\"", "\"ignored\"", "\"warning\"", "\"error\"",
  "\"unused variable\"", "\"unused\"", "\"variable\"", "\"type\"",
  "\"label\"", "\"all\"", "\"none\"", "\"no\"", "\"count\"", "\"max\"",
  "\"level\"", "\"sublevel\"", "\"proof\"", "\"conditional\"",
  "\"strict\"", "\"trace\"", "\"untrace\"", "\"null\"", "\"empty\"",
  "\"result\"", "\"solve\"", "\"prooftree\"", "\"unify\"", "\"split\"",
  "\"substitute\"", "\"statement\"", "\"database\"", "\"formula\"",
  "\"unspecializable\"", "\"structure\"", "\"thread\"",
  "\"natural number value\"", "\"integer value\"", "\"include\"",
  "\"end\"", "\"name\"", "\"metapredicate constant\"",
  "\"predicate constant\"", "\"atom constant\"", "\"function constant\"",
  "\"term constant\"", "\"metaformula variable\"",
  "\"object formula variable\"", "\"predicate variable\"",
  "\"atom variable\"", "\"prefix formula variable\"",
  "\"function variable\"", "\"constant variable\"", "\"object variable\"",
  "\"code variable\"", "\"all variable\"", "\"exist variable\"",
  "\"Set variable\"", "\"set variable\"", "\"set variable definition\"",
  "\"implicit set variable\"", "\"identifier constant\"",
  "\"identifier variable\"", "\"∃\"", "\"¬\"", "\"∧\"", "\"∨\"", "\"⇒\"",
  "\"⇐\"", "\"⇔\"", "prefix_not_key", "prefix_and_key", "prefix_or_key",
  "prefix_implies_key", "prefix_equivalent_key", "\"<\"", "\">\"", "\"≤\"",
  "\"≥\"", "\"≮\"", "\"≯\"", "\"≰\"", "\"≱\"", "\"=\"", "\"≠\"", "\"↦\"",
  "\"°\"", "\"!\"", "\"⋅\"", "\"+\"", "\"-\"", "\"Set\"", "\"Pow\"",
  "\"∅\"", "\"∈\"", "\"∉\"", "\"∁\"", "\"∪\"", "\"∩\"", "\"∖\"", "\"⋃\"",
  "\"⋂\"", "\"⊆\"", "\"⊊\"", "\"⊇\"", "\"⊋\"", "\":\"", "\";\"", "\",\"",
  "\".\"", "\"(\"", "\")\"", "\"[\"", "\"]\"", "\"⟨\"", "\"⟩\"", "\"⁽\"",
  "\"⁾\"", "\"₍\"", "\"₎\"", "\"{\"", "\"|\"", "\"}\"", "\"~\"", "\"/\"",
  "\"\\\\\"", "\"if\"", "\"then\"", "\"else\"", "\"while\"", "\"do\"",
  "\"loop\"", "\"for\"", "\"break\"", "\"continue\"", "\"throw\"",
  "\"try\"", "\"catch\"", "\"⊩\"", "\"⊣\"", "\"⊢\"", "\"free in\"",
  "\"free for\"", "\"in\"", "\"not\"", "\"≔\"", "\"≕\"", "\"≝\"", "\"≡\"",
  "\"≢\"", "\"≣\"", "\"≣̷\"", "superscript_unsigned_integer_value",
  "unary_minus", "$accept", "file", "file_contents", "command",
  "diagnostic_statement", "diagnostic_type", "diagnostic",
  "trace_statement", "trace_qualifier", "trace_type", "proof_strictness",
  "limits", "integer", YY_NULLPTR
  };
#endif


#if MLIDEBUG
  const short
  directive_parser::yyrline_[] =
  {
       0,   603,   603,   604,   605,   614,   615,   620,   621,   622,
     623,   628,   633,   634,   635,   640,   645,   655,   656,   661,
     662,   663,   664,   665,   666,   667,   668,   669,   670,   671,
     672,   673,   674,   675,   676,   677,   678,   679,   684,   685,
     690,   691,   692,   693,   694,   699,   700
  };

  void
  directive_parser::yy_stack_print_ () const
  {
    *yycdebug_ << "Stack now";
    for (stack_type::const_iterator
           i = yystack_.begin (),
           i_end = yystack_.end ();
         i != i_end; ++i)
      *yycdebug_ << ' ' << int (i->state);
    *yycdebug_ << '\n';
  }

  void
  directive_parser::yy_reduce_print_ (int yyrule) const
  {
    int yylno = yyrline_[yyrule];
    int yynrhs = yyr2_[yyrule];
    // Print the symbols being reduced, and their result.
    *yycdebug_ << "Reducing stack by rule " << yyrule - 1
               << " (line " << yylno << "):\n";
    // The symbols being reduced.
    for (int yyi = 0; yyi < yynrhs; yyi++)
      YY_SYMBOL_PRINT ("   $" << yyi + 1 << " =",
                       yystack_[(yynrhs) - (yyi + 1)]);
  }
#endif // MLIDEBUG

  directive_parser::symbol_kind_type
  directive_parser::yytranslate_ (int t)
  {
    // YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to
    // TOKEN-NUM as returned by yylex.
    static
    const unsigned char
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
     105,   106,   107,   108,   109,   110,   111,   112,   113,   114,
     115,   116,   117,   118,   119,   120,   121,   122,   123,   124,
     125,   126,   127,   128,   129,   130,   131,   132,   133,   134,
     135,   136,   137,   138,   139,   140,   141,   142,   143,   144,
     145,   146,   147,   148,   149,   150,   151,   152,   153,   154,
     155,   156
    };
    // Last valid token kind.
    const int code_max = 411;

    if (t <= 0)
      return symbol_kind::S_YYEOF;
    else if (t <= code_max)
      return static_cast <symbol_kind_type> (translate_table[t]);
    else
      return symbol_kind::S_YYUNDEF;
  }

#line 22 "../../mli-root/src/directive-parser.yy"
} // mli
#line 1638 "../../mli-root/src/directive-parser.cc"

#line 705 "../../mli-root/src/directive-parser.yy"


#include <sstream>

  extern std::istream* current_istream;
  extern std::istream::pos_type line_position;

namespace mli {

  void directive_parser::error(const location_type& loc, const std::string& errstr) {
    diagnostic(loc, errstr, mlilex.in(), line_position);
  }


  int directive_read(std::istream& is, mli::location_type& loc) {
    mli::directive_lexer lex(is, std::cout);

    mli::directive_parser p(lex, loc);

    int r = p.parse();

    if (r != 0)
      is.setstate(std::ios::failbit);
    else
      is.clear(is.rdstate() & ~(std::ios::failbit | std::ios::badbit));

    return r;
  }

  int directive_read(const std::string& str, mli::location_type& loc) {
    std::stringstream iss(str);

    return directive_read(iss, loc);
  }

} // namespace mli

