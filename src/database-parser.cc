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



#include "database-parser.hh"


// Unqualified %code blocks.
#line 123 "../../mli-root/src/database-parser.yy"


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

  #include "function.hh"

  #include "precedence.hh"


  std::string infile_name;

  extern bool declaration_context;
  extern bool maybe_set_declaration_context;
  extern bool proofline_database_context;
  extern bool statement_substitution_context;
  extern int bracket_depth;

  extern mli::database_parser::token_type declared_token;   // Lookahead token
  mli::database_parser::token_type current_declared_token;  // May be set in mid action to avoid using the lookahe token.
  extern int declared_type;
  extern int current_token;
  extern std::string current_line;

  extern std::set<std::string> clp_parser_variables;



  namespace mli {

    kleenean unused_variable = false;


    symbol_table_t symbol_table;

    std::set<ref<variable>> statement_variables_;

    ref<theory> theory_;  // Theory to enter propositions into.
    ref<database> theorem_theory_;  // Theory used for a theorem proof.

    // Stacks to handle nested statements and their proofs:
    std::vector<ref<statement>> statement_stack_; // Pushed & popped at statement boundaries.


    // Pushed & popped at proof boundaries:
    mli::table_stack<std::string, ref<statement>> proofline_stack_; // Proof line table.

    // The proofe depth is used for nested proof variable renumbering.
    // Incremented at the beginning of a theorem or subtheorem, and decremented at the proof end.
    depth proof_depth = 0, proof_depth0 = 0;


    mli::database_parser::token_type to_token(variable::type t) {
      switch (t) {
#if USE_VARIABLE_META
        case variable::metaformula_:   return mli::database_parser::token::metaformula_variable;
#endif
        case variable::formula_:       return mli::database_parser::token::object_formula_variable;
        case variable::predicate_:     return mli::database_parser::token::predicate_variable;
        case variable::atom_:          return mli::database_parser::token::atom_variable;
        case variable::function_:      return mli::database_parser::token::function_variable;
        case variable::object_:        return mli::database_parser::token::object_variable;
        default:                       return mli::database_parser::token::token_error;
      }
    }


    // For bound variable definitions, set to the token type that
    // should be inserted in the symbol table:
    database_parser::token_type bound_variable_type = database_parser::token_type(0);

    ref<formula> head(const statement& x) {
      auto xp = ref_cast<inference*>(x.statement_);
      if (xp != nullptr)
        return xp->head_;
      return x.statement_;
    }


    database_parser::token_type define_variable(semantic_type& yylval) {
      if (statement_substitution_context) {
        statement_substitution_context = false;
        std::optional<std::pair<database_parser::token_type, mli::ref<mli::unit>>> x = mli::symbol_table.find_top(yylval.text);
        if (!x)  return mli::database_parser::token::plain_name;
        yylval.object = x->second;
        yylval.number = x->first;
        return x->first;
      }

      if (declaration_context)
        return mli::database_parser::token::plain_name;

      std::optional<std::pair<mli::database_parser::token_type, mli::ref<mli::unit>>> x = mli::symbol_table.find(yylval.text);


      if (!x) {
        // Not a bound variable case:
        if (bound_variable_type == mli::free_variable_context)
          return mli::database_parser::token::plain_name;

        // Bound variable case: Create a limited variable of bind 1, insert at the secondary
        // (bound variable) stack level.
        ref<variable> v = ref<variable>(make, yylval.text, variable::limited_, variable::object_, proof_depth);

        v->bind_ = 1;
        symbol_table.insert(yylval.text, {bound_variable_type, v});

        yylval.object = v;
        yylval.number = bound_variable_type;

        return bound_variable_type;
      }


      mli::variable* vp = mli::ref_cast<mli::variable*>(x->second);

      if (vp != nullptr
        && (vp->depth_ == -1 || bound_variable_type != mli::free_variable_context)) {

        if (bound_variable_type == mli::free_variable_context) {
          // Case definition of a free variable:

          // Check if it is a variable which is declared without definition, in which case make
          // a copy with right proof depth, insert it in the symbol table, and change x->second
          // so subsequently the new copy is used instead of the original lookup value.
          mli::ref<mli::variable> v(make, *vp);
          v->depth_ = proof_depth;

          symbol_table.insert_or_assign(yylval.text, {x->first, v});

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
            v->depth_ = proof_depth;
            v->metatype_ = variable::limited_;
            v->bind_ = 1;

            symbol_table.insert(yylval.text, {x->first, v});

            x->second = v;
          }
          else if (vp->depth_ == -1) {
            mli::ref<mli::variable> v(make, *vp);
            v->depth_ = proof_depth;

            symbol_table.insert_or_assign(yylval.text, {x->first, v});

            x->second = v;
          }

          yylval.object = x->second;
          yylval.number = x->first;

          return bound_variable_type;
        }
      }

      yylval.object = x->second;
      yylval.number = x->first;

      return x->first;
    }

  } // namespace mli



#line 244 "../../mli-root/src/database-parser.cc"


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

#line 22 "../../mli-root/src/database-parser.yy"
namespace mli {
#line 337 "../../mli-root/src/database-parser.cc"

  /// Build a parser object.
  database_parser::database_parser (mli::theory_database& yypval_yyarg, mli::database_lexer& mlilex_yyarg)
#if MLIDEBUG
    : yydebug_ (false),
      yycdebug_ (&std::cerr),
#else
    :
#endif
      yy_lac_established_ (false),
      yypval (yypval_yyarg),
      mlilex (mlilex_yyarg)
  {}

  database_parser::~database_parser ()
  {}

  database_parser::syntax_error::~syntax_error () YY_NOEXCEPT YY_NOTHROW
  {}

  /*---------------.
  | symbol kinds.  |
  `---------------*/

  // basic_symbol.
  template <typename Base>
  database_parser::basic_symbol<Base>::basic_symbol (const basic_symbol& that)
    : Base (that)
    , value (that.value)
    , location (that.location)
  {}


  /// Constructor for valueless symbols.
  template <typename Base>
  database_parser::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, YY_MOVE_REF (location_type) l)
    : Base (t)
    , value ()
    , location (l)
  {}

  template <typename Base>
  database_parser::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, YY_RVREF (value_type) v, YY_RVREF (location_type) l)
    : Base (t)
    , value (YY_MOVE (v))
    , location (YY_MOVE (l))
  {}

  template <typename Base>
  database_parser::symbol_kind_type
  database_parser::basic_symbol<Base>::type_get () const YY_NOEXCEPT
  {
    return this->kind ();
  }

  template <typename Base>
  bool
  database_parser::basic_symbol<Base>::empty () const YY_NOEXCEPT
  {
    return this->kind () == symbol_kind::S_YYEMPTY;
  }

  template <typename Base>
  void
  database_parser::basic_symbol<Base>::move (basic_symbol& s)
  {
    super_type::move (s);
    value = YY_MOVE (s.value);
    location = YY_MOVE (s.location);
  }

  // by_kind.
  database_parser::by_kind::by_kind ()
    : kind_ (symbol_kind::S_YYEMPTY)
  {}

#if 201103L <= YY_CPLUSPLUS
  database_parser::by_kind::by_kind (by_kind&& that)
    : kind_ (that.kind_)
  {
    that.clear ();
  }
#endif

  database_parser::by_kind::by_kind (const by_kind& that)
    : kind_ (that.kind_)
  {}

  database_parser::by_kind::by_kind (token_kind_type t)
    : kind_ (yytranslate_ (t))
  {}

  void
  database_parser::by_kind::clear () YY_NOEXCEPT
  {
    kind_ = symbol_kind::S_YYEMPTY;
  }

  void
  database_parser::by_kind::move (by_kind& that)
  {
    kind_ = that.kind_;
    that.clear ();
  }

  database_parser::symbol_kind_type
  database_parser::by_kind::kind () const YY_NOEXCEPT
  {
    return kind_;
  }

  database_parser::symbol_kind_type
  database_parser::by_kind::type_get () const YY_NOEXCEPT
  {
    return this->kind ();
  }


  // by_state.
  database_parser::by_state::by_state () YY_NOEXCEPT
    : state (empty_state)
  {}

  database_parser::by_state::by_state (const by_state& that) YY_NOEXCEPT
    : state (that.state)
  {}

  void
  database_parser::by_state::clear () YY_NOEXCEPT
  {
    state = empty_state;
  }

  void
  database_parser::by_state::move (by_state& that)
  {
    state = that.state;
    that.clear ();
  }

  database_parser::by_state::by_state (state_type s) YY_NOEXCEPT
    : state (s)
  {}

  database_parser::symbol_kind_type
  database_parser::by_state::kind () const YY_NOEXCEPT
  {
    if (state == empty_state)
      return symbol_kind::S_YYEMPTY;
    else
      return YY_CAST (symbol_kind_type, yystos_[+state]);
  }

  database_parser::stack_symbol_type::stack_symbol_type ()
  {}

  database_parser::stack_symbol_type::stack_symbol_type (YY_RVREF (stack_symbol_type) that)
    : super_type (YY_MOVE (that.state), YY_MOVE (that.value), YY_MOVE (that.location))
  {
#if 201103L <= YY_CPLUSPLUS
    // that is emptied.
    that.state = empty_state;
#endif
  }

  database_parser::stack_symbol_type::stack_symbol_type (state_type s, YY_MOVE_REF (symbol_type) that)
    : super_type (s, YY_MOVE (that.value), YY_MOVE (that.location))
  {
    // that is emptied.
    that.kind_ = symbol_kind::S_YYEMPTY;
  }

#if YY_CPLUSPLUS < 201103L
  database_parser::stack_symbol_type&
  database_parser::stack_symbol_type::operator= (const stack_symbol_type& that)
  {
    state = that.state;
    value = that.value;
    location = that.location;
    return *this;
  }

  database_parser::stack_symbol_type&
  database_parser::stack_symbol_type::operator= (stack_symbol_type& that)
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
  database_parser::yy_destroy_ (const char* yymsg, basic_symbol<Base>& yysym) const
  {
    if (yymsg)
      YY_SYMBOL_PRINT (yymsg, yysym);

    // User destructor.
    YY_USE (yysym.kind ());
  }

#if MLIDEBUG
  template <typename Base>
  void
  database_parser::yy_print_ (std::ostream& yyo, const basic_symbol<Base>& yysym) const
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
  database_parser::yypush_ (const char* m, YY_MOVE_REF (stack_symbol_type) sym)
  {
    if (m)
      YY_SYMBOL_PRINT (m, sym);
    yystack_.push (YY_MOVE (sym));
  }

  void
  database_parser::yypush_ (const char* m, state_type s, YY_MOVE_REF (symbol_type) sym)
  {
#if 201103L <= YY_CPLUSPLUS
    yypush_ (m, stack_symbol_type (s, std::move (sym)));
#else
    stack_symbol_type ss (s, sym);
    yypush_ (m, ss);
#endif
  }

  void
  database_parser::yypop_ (int n)
  {
    yystack_.pop (n);
  }

#if MLIDEBUG
  std::ostream&
  database_parser::debug_stream () const
  {
    return *yycdebug_;
  }

  void
  database_parser::set_debug_stream (std::ostream& o)
  {
    yycdebug_ = &o;
  }


  database_parser::debug_level_type
  database_parser::debug_level () const
  {
    return yydebug_;
  }

  void
  database_parser::set_debug_level (debug_level_type l)
  {
    yydebug_ = l;
  }
#endif // MLIDEBUG

  database_parser::state_type
  database_parser::yy_lr_goto_state_ (state_type yystate, int yysym)
  {
    int yyr = yypgoto_[yysym - YYNTOKENS] + yystate;
    if (0 <= yyr && yyr <= yylast_ && yycheck_[yyr] == yystate)
      return yytable_[yyr];
    else
      return yydefgoto_[yysym - YYNTOKENS];
  }

  bool
  database_parser::yy_pact_value_is_default_ (int yyvalue)
  {
    return yyvalue == yypact_ninf_;
  }

  bool
  database_parser::yy_table_value_is_error_ (int yyvalue)
  {
    return yyvalue == yytable_ninf_;
  }

  int
  database_parser::operator() ()
  {
    return parse ();
  }

  int
  database_parser::parse ()
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

    // Discard the LAC context in case there still is one left from a
    // previous invocation.
    yy_lac_discard_ ("init");

#if YY_EXCEPTIONS
    try
#endif // YY_EXCEPTIONS
      {
    YYCDEBUG << "Starting parse\n";


    // User initialization code.
#line 33 "../../mli-root/src/database-parser.yy"
{
  yyla.location.initialize(&infile_name); // Initialize the initial location.
}

#line 681 "../../mli-root/src/database-parser.cc"


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
        if (!yy_lac_establish_ (yyla.kind ()))
          goto yyerrlab;
        goto yydefault;
      }

    // Reduce or error.
    yyn = yytable_[yyn];
    if (yyn <= 0)
      {
        if (yy_table_value_is_error_ (yyn))
          goto yyerrlab;
        if (!yy_lac_establish_ (yyla.kind ()))
          goto yyerrlab;

        yyn = -yyn;
        goto yyreduce;
      }

    // Count tokens shifted since error; after three, turn off error status.
    if (yyerrstatus_)
      --yyerrstatus_;

    // Shift the lookahead token.
    yypush_ ("Shifting", state_type (yyn), YY_MOVE (yyla));
    yy_lac_discard_ ("shift");
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
#line 646 "../../mli-root/src/database-parser.yy"
                  {}
#line 825 "../../mli-root/src/database-parser.cc"
    break;

  case 4: // file: error
#line 647 "../../mli-root/src/database-parser.yy"
          {
      declaration_context = false;
      bound_variable_type = free_variable_context;
      YYABORT;
    }
#line 835 "../../mli-root/src/database-parser.cc"
    break;

  case 5: // file_contents: file_contents command
#line 656 "../../mli-root/src/database-parser.yy"
                          {}
#line 841 "../../mli-root/src/database-parser.cc"
    break;

  case 6: // file_contents: command
#line 657 "../../mli-root/src/database-parser.yy"
                          {}
#line 847 "../../mli-root/src/database-parser.cc"
    break;

  case 7: // $@1: %empty
#line 662 "../../mli-root/src/database-parser.yy"
    { symbol_table.clear(); }
#line 853 "../../mli-root/src/database-parser.cc"
    break;

  case 8: // command: $@1 theory
#line 662 "../../mli-root/src/database-parser.yy"
                                     {}
#line 859 "../../mli-root/src/database-parser.cc"
    break;

  case 9: // metaformula_substitution_sequence: substitution_for_metaformula
#line 667 "../../mli-root/src/database-parser.yy"
                                    { yylhs.value.object = yystack_[0].value.object; }
#line 865 "../../mli-root/src/database-parser.cc"
    break;

  case 10: // metaformula_substitution_sequence: metaformula_substitution_sequence substitution_for_metaformula
#line 668 "../../mli-root/src/database-parser.yy"
                                                                         {
      yylhs.value.object =  ref<substitution>(yystack_[1].value.object) * ref<substitution>(yystack_[0].value.object);
    }
#line 873 "../../mli-root/src/database-parser.cc"
    break;

  case 11: // substitution_for_metaformula: metaformula_substitution
#line 675 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.object = yystack_[0].value.object; }
#line 879 "../../mli-root/src/database-parser.cc"
    break;

  case 12: // substitution_for_metaformula: formula_substitution
#line 676 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.object = yystack_[0].value.object; }
#line 885 "../../mli-root/src/database-parser.cc"
    break;

  case 13: // substitution_for_metaformula: term_substitution
#line 677 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.object = yystack_[0].value.object; }
#line 891 "../../mli-root/src/database-parser.cc"
    break;

  case 14: // metaformula_substitution: "[" "metaformula variable" "⤇" metaformula "]"
#line 682 "../../mli-root/src/database-parser.yy"
                                                       {
      ref<variable> v(yystack_[3].value.object);
      ref<formula> f(yystack_[1].value.object);
      yylhs.value.object = ref<explicit_substitution>(make, v, f);
    }
#line 901 "../../mli-root/src/database-parser.cc"
    break;

  case 15: // formula_substitution_sequence: substitution_for_formula
#line 691 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.object = yystack_[0].value.object; }
#line 907 "../../mli-root/src/database-parser.cc"
    break;

  case 16: // formula_substitution_sequence: formula_substitution_sequence substitution_for_formula
#line 692 "../../mli-root/src/database-parser.yy"
                                                                 {
      yylhs.value.object = ref<substitution>(yystack_[1].value.object) * ref<substitution>(yystack_[0].value.object);
    }
#line 915 "../../mli-root/src/database-parser.cc"
    break;

  case 17: // substitution_for_formula: formula_substitution
#line 699 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.object = yystack_[0].value.object; }
#line 921 "../../mli-root/src/database-parser.cc"
    break;

  case 18: // substitution_for_formula: term_substitution
#line 700 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.object = yystack_[0].value.object; }
#line 927 "../../mli-root/src/database-parser.cc"
    break;

  case 19: // formula_substitution: "[" "object formula variable" "⤇" object_formula "]"
#line 705 "../../mli-root/src/database-parser.yy"
                                                             {
      ref<variable> v(yystack_[3].value.object);
      ref<formula> f(yystack_[1].value.object);
      yylhs.value.object = ref<explicit_substitution>(make, v, f);
    }
#line 937 "../../mli-root/src/database-parser.cc"
    break;

  case 20: // formula_substitution: "[" "predicate variable" "⤇" predicate "]"
#line 710 "../../mli-root/src/database-parser.yy"
                                                   {
      ref<variable> v(yystack_[3].value.object);
      ref<formula> f(yystack_[1].value.object);
      yylhs.value.object = ref<explicit_substitution>(make, v, f);
    }
#line 947 "../../mli-root/src/database-parser.cc"
    break;

  case 21: // formula_substitution: "[" "atom variable" "⤇" "atom constant" "]"
#line 715 "../../mli-root/src/database-parser.yy"
                                                  {
      ref<variable> v(yystack_[3].value.object);
      ref<formula> f(yystack_[1].value.object);
      yylhs.value.object = ref<explicit_substitution>(make, v, f);
    }
#line 957 "../../mli-root/src/database-parser.cc"
    break;

  case 22: // term_substitution_sequence: term_substitution
#line 724 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.object = yystack_[0].value.object; }
#line 963 "../../mli-root/src/database-parser.cc"
    break;

  case 23: // term_substitution_sequence: term_substitution_sequence term_substitution
#line 725 "../../mli-root/src/database-parser.yy"
                                                       {
      yylhs.value.object = ref<substitution>(yystack_[1].value.object) * ref<substitution>(yystack_[0].value.object);
    }
#line 971 "../../mli-root/src/database-parser.cc"
    break;

  case 24: // term_substitution: "[" term_identifier "⤇" term "]"
#line 732 "../../mli-root/src/database-parser.yy"
                                           {
      ref<variable> v(yystack_[3].value.object);
      ref<formula> f(yystack_[1].value.object);
      yylhs.value.object = ref<explicit_substitution>(make, v, f);
    }
#line 981 "../../mli-root/src/database-parser.cc"
    break;

  case 25: // predicate_function_application: "(" "object variable" "↦" object_formula ")" tuple
#line 741 "../../mli-root/src/database-parser.yy"
                                                              {
      yylhs.value.object = ref<function_application>(make, ref<function_map>(make, yystack_[4].value.object, yystack_[2].value.object), yystack_[0].value.object);
    }
#line 989 "../../mli-root/src/database-parser.cc"
    break;

  case 26: // $@2: %empty
#line 744 "../../mli-root/src/database-parser.yy"
                                                           { symbol_table.pop_level(); }
#line 995 "../../mli-root/src/database-parser.cc"
    break;

  case 27: // predicate_function_application: "(" "𝛌" "function map variable" "↦" object_formula $@2 ")" tuple
#line 744 "../../mli-root/src/database-parser.yy"
                                                                                                      {
      yylhs.value.object = ref<function_application>(make, ref<function_map>(make, yystack_[5].value.object, yystack_[3].value.object), yystack_[0].value.object);
    }
#line 1003 "../../mli-root/src/database-parser.cc"
    break;

  case 28: // predicate_function_application: "predicate" tuple
#line 747 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.object = ref<function_application>(make, yystack_[1].value.object, yystack_[0].value.object); }
#line 1009 "../../mli-root/src/database-parser.cc"
    break;

  case 29: // term_function_application: "(" "object variable" "↦" term ")" tuple
#line 752 "../../mli-root/src/database-parser.yy"
                                                    {
      yylhs.value.object = ref<function_application>(make, ref<function_map>(make, yystack_[4].value.object, yystack_[2].value.object), yystack_[0].value.object);
    }
#line 1017 "../../mli-root/src/database-parser.cc"
    break;

  case 30: // $@3: %empty
#line 755 "../../mli-root/src/database-parser.yy"
                                                 { symbol_table.pop_level(); }
#line 1023 "../../mli-root/src/database-parser.cc"
    break;

  case 31: // term_function_application: "(" "𝛌" "function map variable" "↦" term $@3 ")" tuple
#line 755 "../../mli-root/src/database-parser.yy"
                                                                                            {
      yylhs.value.object = ref<function_application>(make, ref<function_map>(make, yystack_[5].value.object, yystack_[3].value.object), yystack_[0].value.object);
    }
#line 1031 "../../mli-root/src/database-parser.cc"
    break;

  case 32: // term_function_application: "function" tuple
#line 758 "../../mli-root/src/database-parser.yy"
                             { yylhs.value.object = ref<function_application>(make, yystack_[1].value.object, yystack_[0].value.object); }
#line 1037 "../../mli-root/src/database-parser.cc"
    break;

  case 33: // $@4: %empty
#line 764 "../../mli-root/src/database-parser.yy"
        { theory_ = ref<theory>(make, yystack_[1].value.text);
          yypval.insert(theory_);
          symbol_table.push_level();
    }
#line 1046 "../../mli-root/src/database-parser.cc"
    break;

  case 34: // theory: "theory" statement_name "." $@4 include_theories theory_body "end" "theory" end_theory_name "."
#line 770 "../../mli-root/src/database-parser.yy"
                                          {
      if (yystack_[1].value.number != 0 && yystack_[8].value.text != yystack_[1].value.text) {
        mli::database_parser::error(yystack_[1].location, "warning: Name mismatch, theory " + yystack_[8].value.text
          + ", end theory " + yystack_[1].value.text + ".");
      }

      symbol_table.pop_level();
    }
#line 1059 "../../mli-root/src/database-parser.cc"
    break;

  case 35: // end_theory_name: %empty
#line 782 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.number = 0; }
#line 1065 "../../mli-root/src/database-parser.cc"
    break;

  case 36: // end_theory_name: statement_name
#line 783 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.text = yystack_[0].value.text; yylhs.value.number = 1; }
#line 1071 "../../mli-root/src/database-parser.cc"
    break;

  case 38: // include_theories: include_theories include_theory
#line 789 "../../mli-root/src/database-parser.yy"
                                    {}
#line 1077 "../../mli-root/src/database-parser.cc"
    break;

  case 39: // include_theory: "include" "theory" theory_name "."
#line 793 "../../mli-root/src/database-parser.yy"
                                         {
      std::optional<ref<theory>> th = yypval.find(yystack_[1].value.text);

      if (!th)
        throw syntax_error(yystack_[1].location, "Include theory " + yystack_[1].value.text + " not found.");

      theory_->insert(*th);
    }
#line 1090 "../../mli-root/src/database-parser.cc"
    break;

  case 40: // theory_name: "name"
#line 805 "../../mli-root/src/database-parser.yy"
                { yylhs.value = yystack_[0].value; }
#line 1096 "../../mli-root/src/database-parser.cc"
    break;

  case 41: // theory_name: "label"
#line 806 "../../mli-root/src/database-parser.yy"
                { yylhs.value = yystack_[0].value; }
#line 1102 "../../mli-root/src/database-parser.cc"
    break;

  case 42: // theory_body: theory_body_list
#line 811 "../../mli-root/src/database-parser.yy"
                     {}
#line 1108 "../../mli-root/src/database-parser.cc"
    break;

  case 43: // theory_body: formal_system theory_body_list
#line 812 "../../mli-root/src/database-parser.yy"
                                   {}
#line 1114 "../../mli-root/src/database-parser.cc"
    break;

  case 44: // $@5: %empty
#line 818 "../../mli-root/src/database-parser.yy"
    { symbol_table.push_level(); }
#line 1120 "../../mli-root/src/database-parser.cc"
    break;

  case 45: // formal_system: "formal system" "." $@5 formal_system_body "end" "formal system" "."
#line 820 "../../mli-root/src/database-parser.yy"
                              { symbol_table.pop_level(); }
#line 1126 "../../mli-root/src/database-parser.cc"
    break;

  case 47: // formal_system_body: formal_system_body formal_system_body_item
#line 826 "../../mli-root/src/database-parser.yy"
                                               {}
#line 1132 "../../mli-root/src/database-parser.cc"
    break;

  case 48: // formal_system_body_item: identifier_declaration
#line 831 "../../mli-root/src/database-parser.yy"
                           {}
#line 1138 "../../mli-root/src/database-parser.cc"
    break;

  case 49: // formal_system_body_item: postulate
#line 832 "../../mli-root/src/database-parser.yy"
                 { theory_->insert(ref<statement>(yystack_[0].value.object)); }
#line 1144 "../../mli-root/src/database-parser.cc"
    break;

  case 50: // formal_system_body_item: definition_labelstatement
#line 833 "../../mli-root/src/database-parser.yy"
                                 { theory_->insert(ref<statement>(yystack_[0].value.object)); }
#line 1150 "../../mli-root/src/database-parser.cc"
    break;

  case 52: // theory_body_list: theory_body_list theory_body_item
#line 839 "../../mli-root/src/database-parser.yy"
                                      {}
#line 1156 "../../mli-root/src/database-parser.cc"
    break;

  case 53: // theory_body_item: theorem
#line 849 "../../mli-root/src/database-parser.yy"
               { theory_->insert(ref<statement>(yystack_[0].value.object)); }
#line 1162 "../../mli-root/src/database-parser.cc"
    break;

  case 54: // theory_body_item: identifier_declaration
#line 850 "../../mli-root/src/database-parser.yy"
                           {}
#line 1168 "../../mli-root/src/database-parser.cc"
    break;

  case 55: // theory_body_item: conjecture
#line 851 "../../mli-root/src/database-parser.yy"
                  { theory_->insert(ref<statement>(yystack_[0].value.object)); }
#line 1174 "../../mli-root/src/database-parser.cc"
    break;

  case 56: // theory_body_item: definition_labelstatement
#line 853 "../../mli-root/src/database-parser.yy"
                                 { theory_->insert(ref<statement>(yystack_[0].value.object)); }
#line 1180 "../../mli-root/src/database-parser.cc"
    break;

  case 57: // $@6: %empty
#line 859 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 1186 "../../mli-root/src/database-parser.cc"
    break;

  case 58: // postulate: "postulate" statement_name "." $@6 statement "."
#line 860 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();
      yylhs.value.object = ref<supposition>(make, supposition::postulate_, yystack_[4].value.text, yystack_[1].value.object, true);
    }
#line 1195 "../../mli-root/src/database-parser.cc"
    break;

  case 60: // $@7: %empty
#line 866 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 1201 "../../mli-root/src/database-parser.cc"
    break;

  case 61: // postulate: "axiom" statement_name "." $@7 statement "."
#line 867 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();

      ref<formula> f(yystack_[1].value.object);

      if (!f->is_axiom())
        throw syntax_error(yystack_[1].location, "Axiom statement not an object formula.");

      yylhs.value.object = ref<supposition>(make, supposition::postulate_, yystack_[4].value.text, f);
    }
#line 1216 "../../mli-root/src/database-parser.cc"
    break;

  case 62: // $@8: %empty
#line 878 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 1222 "../../mli-root/src/database-parser.cc"
    break;

  case 63: // postulate: "rule" statement_name "." $@8 statement "."
#line 879 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();

      ref<formula> f(yystack_[1].value.object);

      if (!f->is_rule())
        throw syntax_error(yystack_[1].location, "Rule statement not an inference.");

      yylhs.value.object = ref<supposition>(make, supposition::postulate_, yystack_[4].value.text, f);
    }
#line 1237 "../../mli-root/src/database-parser.cc"
    break;

  case 64: // $@9: %empty
#line 894 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 1243 "../../mli-root/src/database-parser.cc"
    break;

  case 65: // conjecture: "conjecture" statement_name "." $@9 statement "."
#line 895 "../../mli-root/src/database-parser.yy"
                     {
      symbol_table.pop_level();
      yylhs.value.object = ref<supposition>(make, supposition::conjecture_, yystack_[4].value.text, yystack_[1].value.object, true);
    }
#line 1252 "../../mli-root/src/database-parser.cc"
    break;

  case 66: // $@10: %empty
#line 903 "../../mli-root/src/database-parser.yy"
        { symbol_table.push_level(); }
#line 1258 "../../mli-root/src/database-parser.cc"
    break;

  case 67: // definition_labelstatement: "definition" statement_name "." $@10 definition_statement "."
#line 904 "../../mli-root/src/database-parser.yy"
                                {
      symbol_table.pop_level();
      yylhs.value.text = yystack_[4].value.text;
      yylhs.value.object = ref<definition>(make, yystack_[4].value.text, yystack_[1].value.object);
    }
#line 1268 "../../mli-root/src/database-parser.cc"
    break;

  case 68: // statement_name: "name"
#line 913 "../../mli-root/src/database-parser.yy"
              { yylhs.value.text = yystack_[0].value.text; }
#line 1274 "../../mli-root/src/database-parser.cc"
    break;

  case 69: // statement_name: "label"
#line 914 "../../mli-root/src/database-parser.yy"
               { yylhs.value.text = yystack_[0].value.text; }
#line 1280 "../../mli-root/src/database-parser.cc"
    break;

  case 70: // statement_name: "natural number value"
#line 915 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.text = yystack_[0].value.text; }
#line 1286 "../../mli-root/src/database-parser.cc"
    break;

  case 71: // theorem: theorem_statement proof
#line 920 "../../mli-root/src/database-parser.yy"
                            {
      yylhs.value.object = statement_stack_.back();
      ref<statement> t(yylhs.value.object); // The theorem.
      t->prove(proof_count);     // Attempt to prove the theorem.
      symbol_table.pop_level();
      statement_stack_.pop_back();
    }
#line 1298 "../../mli-root/src/database-parser.cc"
    break;

  case 72: // theorem_statement: theorem_head statement
#line 931 "../../mli-root/src/database-parser.yy"
                                 {
      symbol_table_t::table& top = symbol_table.top();
      ref<theorem> tr(make,
        theorem::type(yystack_[1].value.number), yystack_[1].value.text, yystack_[0].value.object, theory_, proof_depth);
      statement_stack_.back() = tr;
      theorem_theory_ = tr->get_theory();
    }
#line 1310 "../../mli-root/src/database-parser.cc"
    break;

  case 73: // theorem_head: "theorem" statement_name "."
#line 942 "../../mli-root/src/database-parser.yy"
                                       {
      yylhs.value.text = yystack_[1].value.text;
      yylhs.value.number = yystack_[2].value.number;
      symbol_table.push_level();
      statement_stack_.push_back(ref<statement>());
    }
#line 1321 "../../mli-root/src/database-parser.cc"
    break;

  case 75: // $@11: %empty
#line 953 "../../mli-root/src/database-parser.yy"
    {
      ++proof_depth;
      symbol_table.push_level();
      proofline_stack_.push_level();
    }
#line 1331 "../../mli-root/src/database-parser.cc"
    break;

  case 76: // proof: $@11 proof_of_conclusion
#line 958 "../../mli-root/src/database-parser.yy"
                        {
      --proof_depth;
      symbol_table.pop_level();
      proofline_stack_.pop_level();
    }
#line 1341 "../../mli-root/src/database-parser.cc"
    break;

  case 77: // compound-proof: proof_head proof_lines "∎"
#line 967 "../../mli-root/src/database-parser.yy"
                               {
      --proof_depth;
      symbol_table.pop_level();
      proofline_stack_.pop_level();
    }
#line 1351 "../../mli-root/src/database-parser.cc"
    break;

  case 79: // proof_head: "proof"
#line 977 "../../mli-root/src/database-parser.yy"
            {
      ++proof_depth;
      symbol_table.push_level();
      proofline_stack_.push_level();
    }
#line 1361 "../../mli-root/src/database-parser.cc"
    break;

  case 81: // proof_lines: proof_lines proof_line
#line 987 "../../mli-root/src/database-parser.yy"
                           {}
#line 1367 "../../mli-root/src/database-parser.cc"
    break;

  case 82: // statement_label: statement_name "."
#line 992 "../../mli-root/src/database-parser.yy"
                          {
      yylhs.value.text = yystack_[1].value.text;
      symbol_table.push_level();
    }
#line 1376 "../../mli-root/src/database-parser.cc"
    break;

  case 83: // proof_line: statement_label statement "by" find_statement "."
#line 1000 "../../mli-root/src/database-parser.yy"
                                                               {
      // Handles explicit find_statement substitutions A[x⤇e].
      proofline_database_context = false;

      theorem& t = ref_cast<theorem&>(statement_stack_.back());

      bool concluding = false;

      if (t.get_formula() == yystack_[3].value.object || head(t) == yystack_[3].value.object)
        concluding = true;

      if (!concluding && yystack_[4].value.text == "conclusion")
        throw syntax_error(yystack_[4].location, "Proof line name “conclusion” used when not the theorem conclusion.");

      if (!concluding && yystack_[4].value.text == "result")
        throw syntax_error(yystack_[4].location, "Proof line name “result” used when not the theorem result.");

      symbol_table_t::table& top = symbol_table.top();

      ref<statement> proof_line =
        t.push_back(
          yystack_[4].value.text, ref<formula>(yystack_[3].value.object), ref<database>(yystack_[1].value.object), concluding, proof_depth);

      symbol_table.pop_level();

      if (!proofline_stack_.insert(yystack_[4].value.text, proof_line)) {
        if (yystack_[4].value.text.empty())
          throw syntax_error(yystack_[4].location, "Proof line empty name “” used.");
        else
          throw syntax_error(yystack_[4].location, "Proof line name " + yystack_[4].value.text  + " already given to a proof line.");
      }
    }
#line 1413 "../../mli-root/src/database-parser.cc"
    break;

  case 84: // proof_line: subproof
#line 1032 "../../mli-root/src/database-parser.yy"
                {
      theorem& t = ref_cast<theorem&>(statement_stack_.back());
      ref<statement> proof_line = t.push_back(ref<statement>(yystack_[0].value.object));
      if (!proofline_stack_.insert(yystack_[0].value.text, proof_line)) {
        if (yystack_[0].value.text.empty())
          throw syntax_error(yystack_[0].location, "Proof line empty name “” used.");
        else
          throw syntax_error(yystack_[0].location, "Proof line name " + yystack_[0].value.text  + " already given to a proof line.");
      }
    }
#line 1428 "../../mli-root/src/database-parser.cc"
    break;

  case 85: // $@12: %empty
#line 1042 "../../mli-root/src/database-parser.yy"
    {}
#line 1434 "../../mli-root/src/database-parser.cc"
    break;

  case 86: // proof_line: $@12 identifier_declaration
#line 1042 "../../mli-root/src/database-parser.yy"
                              {}
#line 1440 "../../mli-root/src/database-parser.cc"
    break;

  case 87: // proof_line: definition_labelstatement
#line 1046 "../../mli-root/src/database-parser.yy"
                                 {
      theorem& t = ref_cast<theorem&>(statement_stack_.back());
      ref<statement> proof_line = t.push_back(ref<statement>(yystack_[0].value.object));

      if (!proofline_stack_.insert(yystack_[0].value.text, proof_line)) {
        if (yystack_[0].value.text.empty())
          throw syntax_error(yystack_[0].location, "Proof line name “” used.");
        else
          throw syntax_error(yystack_[0].location, "Proof line name " + yystack_[0].value.text  + " already given to a proof line.");
      }
    }
#line 1456 "../../mli-root/src/database-parser.cc"
    break;

  case 88: // proof_line: proof_of_conclusion
#line 1057 "../../mli-root/src/database-parser.yy"
                        {}
#line 1462 "../../mli-root/src/database-parser.cc"
    break;

  case 89: // subproof: subproof_statement compound-proof
#line 1062 "../../mli-root/src/database-parser.yy"
                                         {
      yylhs.value.text = yystack_[1].value.text;
      yylhs.value.object = statement_stack_.back();
      symbol_table.pop_level();
      statement_stack_.pop_back();
    }
#line 1473 "../../mli-root/src/database-parser.cc"
    break;

  case 90: // subproof_statement: statement_label statement
#line 1072 "../../mli-root/src/database-parser.yy"
                                    {
      yylhs.value.text = yystack_[1].value.text;
      symbol_table_t::table& top = symbol_table.top();
      ref<theorem> tp(make, theorem::claim_, yystack_[1].value.text, yystack_[0].value.object, theory_, proof_depth);
      statement_stack_.push_back(tp);
    }
#line 1484 "../../mli-root/src/database-parser.cc"
    break;

  case 91: // proof_of_conclusion: optional-result "by" find_statement "."
#line 1082 "../../mli-root/src/database-parser.yy"
                                                  {
      proofline_database_context = false;

      theorem& t = ref_cast<theorem&>(statement_stack_.back());
      ref<statement> proof_line =
        t.push_back(yystack_[3].value.text, t.get_formula(), ref<database>(yystack_[1].value.object), true, proof_depth);
    }
#line 1496 "../../mli-root/src/database-parser.cc"
    break;

  case 92: // optional-result: %empty
#line 1093 "../../mli-root/src/database-parser.yy"
                  { yylhs.value.text = "result"; }
#line 1502 "../../mli-root/src/database-parser.cc"
    break;

  case 93: // optional-result: "result"
#line 1094 "../../mli-root/src/database-parser.yy"
                  { yylhs.value = yystack_[0].value; }
#line 1508 "../../mli-root/src/database-parser.cc"
    break;

  case 94: // find_statement: find_statement_list
#line 1099 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<level_database>(make, ref<database>(yystack_[0].value.object)); }
#line 1514 "../../mli-root/src/database-parser.cc"
    break;

  case 95: // find_statement: find_statement ":" find_statement_list
#line 1100 "../../mli-root/src/database-parser.yy"
                                                 {
      ref<level_database>(yystack_[2].value.object)->push_back(ref<database>(yystack_[0].value.object));
      yylhs.value.object = yystack_[2].value.object;
    }
#line 1523 "../../mli-root/src/database-parser.cc"
    break;

  case 96: // find_statement_list: find_statement_sequence
#line 1108 "../../mli-root/src/database-parser.yy"
                               {
      yylhs.value.object = ref<sublevel_database>(make, ref<sequence_database>(yystack_[0].value.object));
    }
#line 1531 "../../mli-root/src/database-parser.cc"
    break;

  case 97: // find_statement_list: find_statement_list ";" find_statement_sequence
#line 1111 "../../mli-root/src/database-parser.yy"
                                                          {
      ref<sublevel_database>(yystack_[2].value.object)->push_back(ref<database>(yystack_[0].value.object));
      yylhs.value.object = yystack_[2].value.object;
    }
#line 1540 "../../mli-root/src/database-parser.cc"
    break;

  case 98: // find_statement_sequence: %empty
#line 1119 "../../mli-root/src/database-parser.yy"
                  { yylhs.value.object = ref<sequence_database>(make); }
#line 1546 "../../mli-root/src/database-parser.cc"
    break;

  case 99: // find_statement_sequence: find_statement_item
#line 1120 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.object = ref<sequence_database>(make, ref<statement>(yystack_[0].value.object)); }
#line 1553 "../../mli-root/src/database-parser.cc"
    break;

  case 100: // find_statement_sequence: find_statement_item "₍" find_definition_sequence "₎"
#line 1122 "../../mli-root/src/database-parser.yy"
                                                               {
      yylhs.value.object = ref<sequence_database>(make, ref<statement>(yystack_[3].value.object));
      ref<sequence_database>(yylhs.value.object)->insert(ref<sequence_database>(yystack_[1].value.object));
    }
#line 1562 "../../mli-root/src/database-parser.cc"
    break;

  case 101: // find_statement_sequence: find_statement_sequence "," find_statement_item
#line 1126 "../../mli-root/src/database-parser.yy"
                                                          {
      ref<sequence_database>(yystack_[2].value.object)->insert(ref<statement>(yystack_[0].value.object));
      yylhs.value.object = yystack_[2].value.object;
    }
#line 1571 "../../mli-root/src/database-parser.cc"
    break;

  case 102: // find_statement_sequence: find_statement_sequence "," find_statement_item "₍" find_definition_sequence "₎"
#line 1130 "../../mli-root/src/database-parser.yy"
                                                                                              {
      yylhs.value.object = yystack_[5].value.object;
      ref<sequence_database>(yylhs.value.object)->insert(ref<statement>(yystack_[3].value.object));
      ref<sequence_database>(yylhs.value.object)->insert(ref<sequence_database>(yystack_[1].value.object));
    }
#line 1581 "../../mli-root/src/database-parser.cc"
    break;

  case 103: // find_definition_sequence: find_statement_item
#line 1139 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.object = ref<sequence_database>(make, ref<statement>(yystack_[0].value.object)); }
#line 1588 "../../mli-root/src/database-parser.cc"
    break;

  case 104: // find_definition_sequence: find_definition_sequence "," find_statement_item
#line 1141 "../../mli-root/src/database-parser.yy"
                                                           {
      ref<sequence_database>(yystack_[2].value.object)->insert(ref<statement>(yystack_[0].value.object));
      yylhs.value.object = yystack_[2].value.object;
    }
#line 1597 "../../mli-root/src/database-parser.cc"
    break;

  case 105: // find_statement_item: find_statement_name
#line 1149 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.object = yystack_[0].value.object;
    }
#line 1605 "../../mli-root/src/database-parser.cc"
    break;

  case 106: // find_statement_item: "premise"
#line 1152 "../../mli-root/src/database-parser.yy"
              {
      yylhs.value.object = ref<premise>(make, statement_stack_.back());
    }
#line 1613 "../../mli-root/src/database-parser.cc"
    break;

  case 107: // find_statement_item: "premise" statement_name
#line 1155 "../../mli-root/src/database-parser.yy"
                                {
      auto i = statement_stack_.rbegin();

      // Search stack from top for statement name:
      for (; i != statement_stack_.rend(); ++i)
        if ((*i)->name() == yystack_[0].value.text) {
          yylhs.value.object = ref<premise>(make, *i);
          break;
        }

      if (i == statement_stack_.rend())
        throw syntax_error(yystack_[0].location, "Proof line premise " + yystack_[0].value.text  + " not found.");
    }
#line 1631 "../../mli-root/src/database-parser.cc"
    break;

  case 108: // find_statement_item: "premise" statement_name "subscript natural number value"
#line 1168 "../../mli-root/src/database-parser.yy"
                                                                  {
      auto i = statement_stack_.rbegin();

      // Search stack from top for statement name:
      for (; i != statement_stack_.rend(); ++i)
        if ((*i)->name() == yystack_[1].value.text) {
          size_type k = (size_type)ref_cast<integer&>(yystack_[0].value.object);
          yylhs.value.object = ref<premise>(make, *i, k);
          break;
        }

      if (i == statement_stack_.rend())
        throw syntax_error(yystack_[1].location, "Proof line premise " + yystack_[1].value.text  + " not found.");
    }
#line 1650 "../../mli-root/src/database-parser.cc"
    break;

  case 109: // find_statement_item: "premise" "⊢"
#line 1182 "../../mli-root/src/database-parser.yy"
                  {
      // As the implicit premise is automatically resolved in inference::unify, any
      // formula that does not produce illegal alternatives will suffice:
      yylhs.value.object = ref<premise>(make);
    }
#line 1660 "../../mli-root/src/database-parser.cc"
    break;

  case 110: // find_statement_item: "premise" "⊢" "subscript natural number value"
#line 1187 "../../mli-root/src/database-parser.yy"
                                                    {
      // As the implicit premise is automatically resolved in inference::unify, any
      // formula that does not produce illegal alternatives will suffice:
      size_type k = (size_type)ref_cast<integer&>(yystack_[0].value.object);
      yylhs.value.object = ref<premise>(make, k);
    }
#line 1671 "../../mli-root/src/database-parser.cc"
    break;

  case 111: // find_statement_name: statement_name
#line 1197 "../../mli-root/src/database-parser.yy"
                      {
      // Accept also non-proved statements (as actual proving will come later):
      std::optional<ref<statement>> st;
      st = proofline_stack_.find(yystack_[0].value.text);

      if (!st)
        st = theorem_theory_->find(yystack_[0].value.text, 0);

      if (!st)
        throw syntax_error(yystack_[0].location,
          "statement name " + yystack_[0].value.text + " not found earlier in proof, in premises or theory.");

      yylhs.value.object = *st;
    }
#line 1690 "../../mli-root/src/database-parser.cc"
    break;

  case 112: // @13: %empty
#line 1211 "../../mli-root/src/database-parser.yy"
                      {
      // Accept also non-proved statements (as actual proving will come later):
      std::optional<ref<statement>> st;
      st = proofline_stack_.find(yystack_[0].value.text);
      if (!st)
        st = theorem_theory_->find(yystack_[0].value.text, 0);

      if (!st)
        throw syntax_error(yystack_[0].location,
          "statement name " + yystack_[0].value.text + " not found earlier in proof, in premises or theory.");

      yylhs.value.object = *st;
      // Find the variables of *st and record them for use in the substitution domain checks:
      ref<statement> pr = *st;
      statement_variables_.clear();
      pr->declared(statement_variables_);
      // Then push the declared *st variables & constants onto symbol_table
      // making them usable in substitution codomains:
      symbol_table.push_level();
      for (auto& i: statement_variables_)
        symbol_table.insert(i->name, {to_token(i->type_), i});
    }
#line 1717 "../../mli-root/src/database-parser.cc"
    break;

  case 113: // find_statement_name: statement_name @13 metaformula_substitution_sequence
#line 1234 "../../mli-root/src/database-parser.yy"
                                         {
      // The try-catch checks whether the statement-substitution is legal:
      ref<statement> p(yystack_[1].value.object);
      ref<substitution> s(yystack_[0].value.object);
      try {
        yylhs.value.object = ref<statement_substitution>(make, p, s);
      } catch (illegal_substitution&) {
        mli::database_parser::error(yystack_[0].location, "Proposition substitute error.");
        p->write(std::cerr,
          write_style(write_name | write_type | write_statement));
        std::cerr << "\n  " << s << std::endl;
        YYERROR;        
      }
      symbol_table.pop_level();
    }
#line 1737 "../../mli-root/src/database-parser.cc"
    break;

  case 114: // statement: metaformula
#line 1253 "../../mli-root/src/database-parser.yy"
                   { yylhs.value.object = ref<formula>(yystack_[0].value.object)->set_bind(); }
#line 1743 "../../mli-root/src/database-parser.cc"
    break;

  case 115: // statement: identifier_declaration metaformula
#line 1254 "../../mli-root/src/database-parser.yy"
                                          {
      ref<formula> f(yystack_[0].value.object);
      yylhs.value.object = f->set_bind();

      if (unused_variable != false) {
        std::set<ref<variable>> vs;
        f->contains(vs, occurrence::declared);

        std::set<ref<variable>> vr;  // Redundant variables.

        for (auto& i: symbol_table.top()) {
          try {
            ref<variable> v(i.second.second);
            if (vs.find(v) == vs.end())
              vr.insert(v);
          }
          catch (std::bad_cast&) {}
        }

        if (!vr.empty()) {
          std::string err;
          if (vr.size() > 1) err += "s";
          err += " ";
          bool it0 = true;

          for (auto& i: vr) {
            if (it0) it0 = false;
            else err += ", ";
            err += i->name;
          }

        std::string ds = "Declared variable" + err + " not used in statement.";

        if (unused_variable != true)
          mli::database_parser::error(yystack_[0].location, "warning: " + ds);
        else
          throw syntax_error(yystack_[0].location, ds);
        }
      }
    }
#line 1788 "../../mli-root/src/database-parser.cc"
    break;

  case 116: // definition_statement: definition
#line 1298 "../../mli-root/src/database-parser.yy"
                  { yylhs.value.object = ref<formula>(yystack_[0].value.object)->set_bind(); }
#line 1794 "../../mli-root/src/database-parser.cc"
    break;

  case 117: // definition_statement: identifier_declaration definition
#line 1299 "../../mli-root/src/database-parser.yy"
                                         {
      yylhs.value.object = ref<formula>(yystack_[0].value.object)->set_bind();
    }
#line 1802 "../../mli-root/src/database-parser.cc"
    break;

  case 118: // identifier_declaration: declarator_list "."
#line 1306 "../../mli-root/src/database-parser.yy"
                        {}
#line 1808 "../../mli-root/src/database-parser.cc"
    break;

  case 119: // declarator_list: declarator_identifier_list
#line 1311 "../../mli-root/src/database-parser.yy"
                               {}
#line 1814 "../../mli-root/src/database-parser.cc"
    break;

  case 120: // declarator_list: declarator_list declarator_identifier_list
#line 1312 "../../mli-root/src/database-parser.yy"
                                               {}
#line 1820 "../../mli-root/src/database-parser.cc"
    break;

  case 121: // declarator_identifier_list: "identifier constant" identifier_constant_list
#line 1317 "../../mli-root/src/database-parser.yy"
                                                     {}
#line 1826 "../../mli-root/src/database-parser.cc"
    break;

  case 122: // declarator_identifier_list: "identifier variable" identifier_variable_list
#line 1318 "../../mli-root/src/database-parser.yy"
                                                     {}
#line 1832 "../../mli-root/src/database-parser.cc"
    break;

  case 123: // declarator_identifier_list: "identifier function" identifier_function_list
#line 1319 "../../mli-root/src/database-parser.yy"
                                                     {}
#line 1838 "../../mli-root/src/database-parser.cc"
    break;

  case 124: // identifier_function_list: identifier_function_name
#line 1324 "../../mli-root/src/database-parser.yy"
                             {}
#line 1844 "../../mli-root/src/database-parser.cc"
    break;

  case 125: // identifier_function_list: identifier_function_list "," identifier_function_name
#line 1325 "../../mli-root/src/database-parser.yy"
                                                          {}
#line 1850 "../../mli-root/src/database-parser.cc"
    break;

  case 126: // $@14: %empty
#line 1336 "../../mli-root/src/database-parser.yy"
              { current_declared_token = declared_token; }
#line 1856 "../../mli-root/src/database-parser.cc"
    break;

  case 127: // $@15: %empty
#line 1337 "../../mli-root/src/database-parser.yy"
        { bound_variable_type = database_parser::token::function_map_variable; }
#line 1862 "../../mli-root/src/database-parser.cc"
    break;

  case 128: // identifier_function_name: "name" $@14 ":" $@15 "function map variable" "↦" object_formula
#line 1338 "../../mli-root/src/database-parser.yy"
                                                   {
      // Check if name already has top level definition:
      std::optional<std::pair<int, mli::ref<mli::unit>>> x0 = mli::symbol_table.find_top(yystack_[6].value.text);
      if (x0) {
        throw syntax_error(yystack_[6].location, "Name " + yystack_[6].value.text + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert(yystack_[6].value.text, {current_declared_token,
        ref<function_map>(make, yystack_[2].value.object, yystack_[0].value.object)});
    }
#line 1878 "../../mli-root/src/database-parser.cc"
    break;

  case 129: // identifier_constant_list: identifier_constant_name
#line 1371 "../../mli-root/src/database-parser.yy"
                             {}
#line 1884 "../../mli-root/src/database-parser.cc"
    break;

  case 130: // identifier_constant_list: identifier_constant_list "," identifier_constant_name
#line 1372 "../../mli-root/src/database-parser.yy"
                                                          {}
#line 1890 "../../mli-root/src/database-parser.cc"
    break;

  case 131: // identifier_constant_name: "name"
#line 1377 "../../mli-root/src/database-parser.yy"
              {
      // Check if name already has top level definition:
      std::optional<std::pair<int, mli::ref<mli::unit>>> x0 = mli::symbol_table.find_top(yystack_[0].value.text);
      if (x0) {
        throw syntax_error(yystack_[0].location, "Name " + yystack_[0].value.text + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert(yystack_[0].value.text, {declared_token,
        ref<constant>(make, yystack_[0].value.text, formula_type(declared_type))});
    }
#line 1906 "../../mli-root/src/database-parser.cc"
    break;

  case 132: // identifier_variable_list: identifier_variable_name
#line 1392 "../../mli-root/src/database-parser.yy"
                             {}
#line 1912 "../../mli-root/src/database-parser.cc"
    break;

  case 133: // identifier_variable_list: identifier_variable_list "," identifier_variable_name
#line 1393 "../../mli-root/src/database-parser.yy"
                                                          {}
#line 1918 "../../mli-root/src/database-parser.cc"
    break;

  case 134: // identifier_variable_name: "name"
#line 1398 "../../mli-root/src/database-parser.yy"
              {
      // Check if name already has top level definition:
      std::optional<std::pair<int, mli::ref<mli::unit>>> x0 = mli::symbol_table.find_top(yystack_[0].value.text);
      if (x0) {
        throw syntax_error(yystack_[0].location, "Name " + yystack_[0].value.text + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

       symbol_table.insert(yystack_[0].value.text, {declared_token,
         ref<variable>(make, yystack_[0].value.text, variable::type(declared_type), -1)});
    }
#line 1934 "../../mli-root/src/database-parser.cc"
    break;

  case 135: // identifier_variable_name: "°" "name"
#line 1409 "../../mli-root/src/database-parser.yy"
                  {
      // Check if name already has top level definition:
      std::optional<std::pair<int, mli::ref<mli::unit>>> x0 = mli::symbol_table.find_top(yystack_[0].value.text);
      if (x0) {
        throw syntax_error(yystack_[0].location, "Name " + yystack_[0].value.text + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert(yystack_[0].value.text, {declared_token,
        ref<variable>(make, yystack_[0].value.text, variable::limited_, variable::type(declared_type), -1)});
    }
#line 1950 "../../mli-root/src/database-parser.cc"
    break;

  case 136: // identifier_variable_name: "•" "name"
#line 1420 "../../mli-root/src/database-parser.yy"
                  {
      // Check if name already has top level definition:
      std::optional<std::pair<int, mli::ref<mli::unit>>> x0 = mli::symbol_table.find_top(yystack_[0].value.text);
      if (x0) {
        throw syntax_error(yystack_[0].location, "Name " + yystack_[0].value.text + " already defined in this scope as "
          + symbol_name((symbol_kind_type)x0->first) + ".");
      }

      symbol_table.insert(yystack_[0].value.text, {declared_token,
        ref<variable>(make, yystack_[0].value.text, variable::term_, variable::type(declared_type), -1)});
    }
#line 1966 "../../mli-root/src/database-parser.cc"
    break;

  case 137: // definition: metaformula_definition
#line 1435 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.object = yystack_[0].value.object; }
#line 1972 "../../mli-root/src/database-parser.cc"
    break;

  case 138: // definition: object_formula_definition
#line 1436 "../../mli-root/src/database-parser.yy"
                                 { yylhs.value.object = yystack_[0].value.object; }
#line 1978 "../../mli-root/src/database-parser.cc"
    break;

  case 139: // definition: term_definition
#line 1437 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.object = yystack_[0].value.object; }
#line 1984 "../../mli-root/src/database-parser.cc"
    break;

  case 140: // metaformula_definition: pure_metaformula "≔" pure_metaformula
#line 1442 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.object = ref<abbreviation>(make, ref<formula>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), ref<formula>(),
        object_formula_type_, formula_definition_oprec); }
#line 1992 "../../mli-root/src/database-parser.cc"
    break;

  case 141: // metaformula_definition: pure_metaformula "≕" pure_metaformula
#line 1445 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.object = ref<abbreviation>(make, ref<formula>(yystack_[0].value.object), ref<formula>(yystack_[2].value.object), ref<formula>(),
        object_formula_type_, formula_definition_oprec); }
#line 2000 "../../mli-root/src/database-parser.cc"
    break;

  case 142: // object_formula_definition: object_formula "≔" object_formula
#line 1457 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.object = ref<abbreviation>(make, ref<formula>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), ref<formula>(),
        object_formula_type_, formula_definition_oprec); }
#line 2008 "../../mli-root/src/database-parser.cc"
    break;

  case 143: // object_formula_definition: object_formula "≕" object_formula
#line 1460 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.object = ref<abbreviation>(make, ref<formula>(yystack_[0].value.object), ref<formula>(yystack_[2].value.object), ref<formula>(),
        object_formula_type_, formula_definition_oprec); }
#line 2016 "../../mli-root/src/database-parser.cc"
    break;

  case 144: // term_definition: term "≔" term
#line 1472 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.object = ref<abbreviation>(make, ref<formula>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), ref<formula>(),
        term_type_, term_definition_oprec); }
#line 2024 "../../mli-root/src/database-parser.cc"
    break;

  case 145: // term_definition: term "≕" term
#line 1481 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.object = ref<abbreviation>(make, ref<formula>(yystack_[0].value.object), ref<formula>(yystack_[2].value.object), ref<formula>(),
        term_type_, term_definition_oprec); }
#line 2032 "../../mli-root/src/database-parser.cc"
    break;

  case 146: // metaformula: pure_metaformula
#line 1488 "../../mli-root/src/database-parser.yy"
                        { yylhs.value.object = yystack_[0].value.object; }
#line 2038 "../../mli-root/src/database-parser.cc"
    break;

  case 147: // metaformula: object_formula
#line 1489 "../../mli-root/src/database-parser.yy"
                      { yylhs.value.object = yystack_[0].value.object; }
#line 2044 "../../mli-root/src/database-parser.cc"
    break;

  case 148: // pure_metaformula: atomic_metaformula
#line 1494 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 2050 "../../mli-root/src/database-parser.cc"
    break;

  case 149: // pure_metaformula: special_metaformula
#line 1495 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = yystack_[0].value.object; }
#line 2056 "../../mli-root/src/database-parser.cc"
    break;

  case 150: // pure_metaformula: "~" metaformula
#line 1496 "../../mli-root/src/database-parser.yy"
                       {
      yylhs.value.object = ref<metanot>(make, ref<formula>(yystack_[0].value.object));
    }
#line 2064 "../../mli-root/src/database-parser.cc"
    break;

  case 151: // pure_metaformula: metaformula ";" metaformula
#line 1499 "../../mli-root/src/database-parser.yy"
                                      {
      yylhs.value.object = mli::concatenate(ref<formula>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object));
    }
#line 2072 "../../mli-root/src/database-parser.cc"
    break;

  case 152: // pure_metaformula: metaformula "," metaformula
#line 1502 "../../mli-root/src/database-parser.yy"
                                      {
      yylhs.value.object = mli::concatenate(ref<formula>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object));
    }
#line 2080 "../../mli-root/src/database-parser.cc"
    break;

  case 153: // pure_metaformula: metaformula "⊩" optional_superscript_natural_number_value optional_varied_variable_matrix optional_varied_in_reduction_variable_matrix metaformula
#line 1507 "../../mli-root/src/database-parser.yy"
                     {
      size_type k = (size_type)ref_cast<integer&>(yystack_[3].value.object);

      if (k < 1)
        k = 2;
      else
        k += 2;

      ref<inference> i(make, ref<formula>(yystack_[0].value.object), ref<formula>(yystack_[5].value.object), metalevel_t(k));

      inference* mp = ref_cast<inference*>(yystack_[2].value.object);
      if (mp != nullptr)
        i->varied_ = mp->varied_;

      inference* mrp = ref_cast<inference*>(yystack_[1].value.object);
      if (mrp != nullptr)
        i->varied_in_reduction_ = mrp->varied_in_reduction_;


      // Check that varied and invariable indices given do not exceed
      // exceed the conclusion (head) and premise (body) sizes:

      formula_sequence* hp = ref_cast<formula_sequence*>(i->head_);
      size_type n_head = (hp == nullptr)? 1 : hp->formulas_.size();

      formula_sequence* bp = ref_cast<formula_sequence*>(i->body_);
      size_type n_body = (bp == nullptr)? 1 : bp->formulas_.size();


      if (!i->varied_.empty()) {
        // Max values of varied conclusion and premise indices.

        // As the conclusions are sorted by index, the max value is the last one:
        size_type vc_max = i->varied_.rbegin()->first;

        size_type vp_max = 0;
        for (auto& i: i->varied_) {
          size_type n = i.second.rbegin()->first;
          if (n > vp_max) vp_max = n;
        }

        if (vc_max >= n_head)
          throw syntax_error(yystack_[2].location,
            "inference varied variable conclusion index " + std::to_string(vc_max)
            + " must be less than the number of conclusions " + std::to_string(n_head) + ".");

        if (vp_max >= n_body)
          throw syntax_error(yystack_[2].location,
            "inference varied variable premise index " + std::to_string(vp_max)
            + " must be less than the number of premises " + std::to_string(n_body) + ".");
      }

      yylhs.value.object = i;
    }
#line 2139 "../../mli-root/src/database-parser.cc"
    break;

  case 154: // pure_metaformula: metaformula "⊢" optional_superscript_natural_number_value optional_varied_variable_matrix optional_varied_in_reduction_variable_matrix metaformula
#line 1575 "../../mli-root/src/database-parser.yy"
                     {
      size_type k = (size_type)ref_cast<integer&>(yystack_[3].value.object);

      if (k < 1)
        k = 1;

      ref<inference> i(make, ref<formula>(yystack_[0].value.object), ref<formula>(yystack_[5].value.object), metalevel_t(k));

      inference* mp = ref_cast<inference*>(yystack_[2].value.object);
      if (mp != nullptr)
        i->varied_ = mp->varied_;

      inference* mrp = ref_cast<inference*>(yystack_[1].value.object);
      if (mrp != nullptr)
        i->varied_in_reduction_ = mrp->varied_in_reduction_;


      // Check that varied and invariable indices given do not exceed
      // exceed the conclusion (head) and premise (body) sizes:

      formula_sequence* hp = ref_cast<formula_sequence*>(i->head_);
      size_type n_head = (hp == nullptr)? 1 : hp->formulas_.size();

      formula_sequence* bp = ref_cast<formula_sequence*>(i->body_);
      size_type n_body = (bp == nullptr)? 1 : bp->formulas_.size();


      if (!i->varied_.empty()) {
        // Max values of varied conclusion and premise indices.

        // As the conclusions are sorted by index, the max value is the last one:
        size_type vc_max = i->varied_.rbegin()->first;

        size_type vp_max = 0;
        for (auto& i: i->varied_) {
          size_type n = i.second.rbegin()->first;
          if (n > vp_max) vp_max = n;
        }

        if (vc_max >= n_head)
          throw syntax_error(yystack_[2].location,
            "inference varied variable conclusion index " + std::to_string(vc_max)
            + " must be less than the number of conclusions " + std::to_string(n_head) + ".");

        if (vp_max >= n_body)
          throw syntax_error(yystack_[2].location,
            "inference varied variable premise index " + std::to_string(vp_max)
            + " must be less than the number of premises " + std::to_string(n_body) + ".");
      }

      yylhs.value.object = i;
    }
#line 2196 "../../mli-root/src/database-parser.cc"
    break;

  case 155: // pure_metaformula: "⊢" metaformula
#line 1634 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.object = ref<inference>(make, ref<formula>(yystack_[0].value.object)); }
#line 2202 "../../mli-root/src/database-parser.cc"
    break;

  case 156: // pure_metaformula: "(" pure_metaformula ")"
#line 1636 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.object = yystack_[1].value.object; }
#line 2208 "../../mli-root/src/database-parser.cc"
    break;

  case 157: // pure_metaformula: simple_metaformula metaformula_substitution_sequence
#line 1637 "../../mli-root/src/database-parser.yy"
                                                               {
      yylhs.value.object = ref<substitution_formula>(make, ref<substitution>(yystack_[0].value.object), ref<formula>(yystack_[1].value.object)); }
#line 2215 "../../mli-root/src/database-parser.cc"
    break;

  case 159: // optional_varied_variable_matrix: "⁽" varied_variable_conclusions "⁾"
#line 1644 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.object = yystack_[1].value.object; }
#line 2221 "../../mli-root/src/database-parser.cc"
    break;

  case 160: // optional_varied_variable_matrix: "⁽" varied_variable_premises "⁾"
#line 1645 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.object = yystack_[1].value.object; }
#line 2227 "../../mli-root/src/database-parser.cc"
    break;

  case 161: // optional_varied_variable_matrix: "⁽" varied_variable_set "⁾"
#line 1646 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.object = yystack_[1].value.object; }
#line 2233 "../../mli-root/src/database-parser.cc"
    break;

  case 163: // varied_variable_conclusions: varied_variable_conclusions ";" varied_variable_conclusion
#line 1651 "../../mli-root/src/database-parser.yy"
                                                                      {
      inference& xs = ref_cast<inference&>(yystack_[2].value.object);
      inference& x = ref_cast<inference&>(yystack_[0].value.object);

      for (auto& i: x.varied_)
        for (auto& j: i.second)
          xs.varied_[i.first][j.first].insert(j.second.begin(), j.second.end());

      yylhs.value.object = yystack_[2].value.object;
    }
#line 2248 "../../mli-root/src/database-parser.cc"
    break;

  case 164: // varied_variable_conclusion: "superscript natural number value" varied_variable_premises
#line 1664 "../../mli-root/src/database-parser.yy"
                                                                     {
      ref<inference> i(make);
      inference& xs = ref_cast<inference&>(yystack_[0].value.object);
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      i->varied_[k].insert(xs.varied_[0].begin(), xs.varied_[0].end());
      yylhs.value.object = i;

    }
#line 2262 "../../mli-root/src/database-parser.cc"
    break;

  case 166: // varied_variable_premises: varied_variable_premises "," varied_variable_premise
#line 1677 "../../mli-root/src/database-parser.yy"
                                                                {
      inference& xs = ref_cast<inference&>(yystack_[2].value.object);
      inference& x = ref_cast<inference&>(yystack_[0].value.object);

      for (auto& j: x.varied_[0])
        xs.varied_[0][j.first].insert(j.second.begin(), j.second.end());

      yylhs.value.object = yystack_[2].value.object;
    }
#line 2276 "../../mli-root/src/database-parser.cc"
    break;

  case 167: // varied_variable_premise: "superscript natural number value" varied_variable_set
#line 1689 "../../mli-root/src/database-parser.yy"
                                                                {
      ref<inference> i(make);
      inference& xs = ref_cast<inference&>(yystack_[0].value.object);
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      i->varied_[0][k].insert(xs.varied_[0][0].begin(), xs.varied_[0][0].end());

      yylhs.value.object = i;
    }
#line 2290 "../../mli-root/src/database-parser.cc"
    break;

  case 169: // varied_variable_set: varied_variable_set varied_variable
#line 1702 "../../mli-root/src/database-parser.yy"
                                               {
      inference& xs = ref_cast<inference&>(yystack_[1].value.object);
      inference& x = ref_cast<inference&>(yystack_[0].value.object);

      xs.varied_[0][0].insert(x.varied_[0][0].begin(), x.varied_[0][0].end());

      yylhs.value.object = yystack_[1].value.object;
    }
#line 2303 "../../mli-root/src/database-parser.cc"
    break;

  case 170: // varied_variable: "object variable"
#line 1713 "../../mli-root/src/database-parser.yy"
                       {
      ref<inference> i(make);
      i->varied_[0][0].insert(yystack_[0].value.object);
      yylhs.value.object = i;
    }
#line 2313 "../../mli-root/src/database-parser.cc"
    break;

  case 171: // varied_variable: "metaformula variable"
#line 1718 "../../mli-root/src/database-parser.yy"
                            {
      ref<inference> i(make);
      i->varied_[0][0].insert(yystack_[0].value.object);
      yylhs.value.object = i;
    }
#line 2323 "../../mli-root/src/database-parser.cc"
    break;

  case 173: // optional_varied_in_reduction_variable_matrix: "₍" varied_in_reduction_variable_conclusions "₎"
#line 1729 "../../mli-root/src/database-parser.yy"
                                                         { yylhs.value.object = yystack_[1].value.object; }
#line 2329 "../../mli-root/src/database-parser.cc"
    break;

  case 174: // optional_varied_in_reduction_variable_matrix: "₍" varied_in_reduction_variable_premises "₎"
#line 1730 "../../mli-root/src/database-parser.yy"
                                                         { yylhs.value.object = yystack_[1].value.object; }
#line 2335 "../../mli-root/src/database-parser.cc"
    break;

  case 175: // optional_varied_in_reduction_variable_matrix: "₍" varied_in_reduction_variable_set "₎"
#line 1731 "../../mli-root/src/database-parser.yy"
                                                         { yylhs.value.object = yystack_[1].value.object; }
#line 2341 "../../mli-root/src/database-parser.cc"
    break;

  case 177: // varied_in_reduction_variable_conclusions: varied_in_reduction_variable_conclusions ";" varied_in_reduction_variable_conclusion
#line 1736 "../../mli-root/src/database-parser.yy"
                                                                                                {
      inference& xs = ref_cast<inference&>(yystack_[2].value.object);
      inference& x = ref_cast<inference&>(yystack_[0].value.object);

      for (auto& i: x.varied_in_reduction_)
        for (auto& j: i.second)
          xs.varied_in_reduction_[i.first][j.first].insert(j.second.begin(), j.second.end());

      yylhs.value.object = yystack_[2].value.object;
    }
#line 2356 "../../mli-root/src/database-parser.cc"
    break;

  case 178: // varied_in_reduction_variable_conclusion: "subscript natural number value" varied_in_reduction_variable_premises
#line 1749 "../../mli-root/src/database-parser.yy"
                                                                                {
      ref<inference> i(make);
      inference& xs = ref_cast<inference&>(yystack_[0].value.object);
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      i->varied_in_reduction_[k].insert(xs.varied_in_reduction_[0].begin(), xs.varied_in_reduction_[0].end());
      yylhs.value.object = i;

    }
#line 2370 "../../mli-root/src/database-parser.cc"
    break;

  case 180: // varied_in_reduction_variable_premises: varied_in_reduction_variable_premises "," varied_in_reduction_variable_premise
#line 1762 "../../mli-root/src/database-parser.yy"
                                                                                          {
      inference& xs = ref_cast<inference&>(yystack_[2].value.object);
      inference& x = ref_cast<inference&>(yystack_[0].value.object);

      for (auto& j: x.varied_in_reduction_[0])
        xs.varied_in_reduction_[0][j.first].insert(j.second.begin(), j.second.end());

      yylhs.value.object = yystack_[2].value.object;
    }
#line 2384 "../../mli-root/src/database-parser.cc"
    break;

  case 181: // varied_in_reduction_variable_premise: "subscript natural number value" varied_in_reduction_variable_set
#line 1774 "../../mli-root/src/database-parser.yy"
                                                                           {
      ref<inference> i(make);
      inference& xs = ref_cast<inference&>(yystack_[0].value.object);
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      i->varied_in_reduction_[0][k].insert(xs.varied_in_reduction_[0][0].begin(), xs.varied_in_reduction_[0][0].end());

      yylhs.value.object = i;
    }
#line 2398 "../../mli-root/src/database-parser.cc"
    break;

  case 183: // varied_in_reduction_variable_set: varied_in_reduction_variable_set varied_in_reduction_variable
#line 1787 "../../mli-root/src/database-parser.yy"
                                                                         {
      inference& xs = ref_cast<inference&>(yystack_[1].value.object);
      inference& x = ref_cast<inference&>(yystack_[0].value.object);

      xs.varied_in_reduction_[0][0].insert(x.varied_in_reduction_[0][0].begin(), x.varied_in_reduction_[0][0].end());

      yylhs.value.object = yystack_[1].value.object;
    }
#line 2411 "../../mli-root/src/database-parser.cc"
    break;

  case 184: // varied_in_reduction_variable: "object variable"
#line 1798 "../../mli-root/src/database-parser.yy"
                       {
      ref<inference> i(make);
      i->varied_in_reduction_[0][0].insert(yystack_[0].value.object);
      yylhs.value.object = i;
    }
#line 2421 "../../mli-root/src/database-parser.cc"
    break;

  case 185: // varied_in_reduction_variable: "metaformula variable"
#line 1803 "../../mli-root/src/database-parser.yy"
                            {
      ref<inference> i(make);
      i->varied_in_reduction_[0][0].insert(yystack_[0].value.object);
      yylhs.value.object = i;
    }
#line 2431 "../../mli-root/src/database-parser.cc"
    break;

  case 186: // simple_metaformula: "metaformula variable"
#line 1871 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.object = yystack_[0].value.object; }
#line 2437 "../../mli-root/src/database-parser.cc"
    break;

  case 187: // simple_metaformula: "(" pure_metaformula ")"
#line 1872 "../../mli-root/src/database-parser.yy"
                                { yylhs.value.object = yystack_[1].value.object; }
#line 2443 "../../mli-root/src/database-parser.cc"
    break;

  case 188: // atomic_metaformula: "metaformula variable"
#line 1877 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.object = yystack_[0].value.object; }
#line 2449 "../../mli-root/src/database-parser.cc"
    break;

  case 189: // atomic_metaformula: metapredicate
#line 1878 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.object = yystack_[0].value.object; }
#line 2455 "../../mli-root/src/database-parser.cc"
    break;

  case 190: // special_metaformula: meta_object_free "≢" meta_object_free
#line 1890 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.object = ref<objectidentical>(make, ref<variable>(yystack_[2].value.object), ref<variable>(yystack_[0].value.object), false);
    }
#line 2463 "../../mli-root/src/database-parser.cc"
    break;

  case 191: // special_metaformula: meta_object_free "free in" object_formula
#line 1893 "../../mli-root/src/database-parser.yy"
                                                    {
      yylhs.value.object = ref<free_in_object>(make, ref<variable>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), true);
    }
#line 2471 "../../mli-root/src/database-parser.cc"
    break;

  case 192: // special_metaformula: meta_object_free "free in" term
#line 1896 "../../mli-root/src/database-parser.yy"
                                          {
      yylhs.value.object = ref<free_in_object>(make, ref<variable>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), true);
    }
#line 2479 "../../mli-root/src/database-parser.cc"
    break;

  case 193: // special_metaformula: meta_object_free "not" "free in" object_formula
#line 1899 "../../mli-root/src/database-parser.yy"
                                                          {
      yylhs.value.object = ref<free_in_object>(make, ref<variable>(yystack_[3].value.object), ref<formula>(yystack_[0].value.object), false);
    }
#line 2487 "../../mli-root/src/database-parser.cc"
    break;

  case 194: // special_metaformula: meta_object_free "not" "free in" term
#line 1902 "../../mli-root/src/database-parser.yy"
                                                {
      yylhs.value.object = ref<free_in_object>(make, ref<variable>(yystack_[3].value.object), ref<formula>(yystack_[0].value.object), false);
    }
#line 2495 "../../mli-root/src/database-parser.cc"
    break;

  case 195: // special_metaformula: term "free for" meta_object_free "in" object_formula
#line 1905 "../../mli-root/src/database-parser.yy"
                                                                  {
      yylhs.value.object = ref<free_for_object>(make, 
        ref<formula>(yystack_[4].value.object), ref<variable>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), true);
    }
#line 2504 "../../mli-root/src/database-parser.cc"
    break;

  case 196: // special_metaformula: term "free for" meta_object_free "in" term
#line 1909 "../../mli-root/src/database-parser.yy"
                                                        {
      yylhs.value.object = ref<free_for_object>(make, 
        ref<formula>(yystack_[4].value.object), ref<variable>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), true);
    }
#line 2513 "../../mli-root/src/database-parser.cc"
    break;

  case 197: // meta_object_free: "object variable"
#line 1917 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.object = yystack_[0].value.object; }
#line 2519 "../../mli-root/src/database-parser.cc"
    break;

  case 198: // metapredicate: metapredicate_function
#line 1922 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.object = yystack_[0].value.object; }
#line 2525 "../../mli-root/src/database-parser.cc"
    break;

  case 199: // metapredicate: object_formula "≣" object_formula
#line 1923 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.object = ref<identical>(make, ref<formula>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), true);
    }
#line 2533 "../../mli-root/src/database-parser.cc"
    break;

  case 200: // metapredicate: object_formula "≣̷" object_formula
#line 1926 "../../mli-root/src/database-parser.yy"
                                            {
      yylhs.value.object = ref<identical>(make, ref<formula>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), false);
    }
#line 2541 "../../mli-root/src/database-parser.cc"
    break;

  case 201: // metapredicate: term "≣" term
#line 1929 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.object = ref<identical>(make, ref<formula>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), true);
    }
#line 2549 "../../mli-root/src/database-parser.cc"
    break;

  case 202: // metapredicate: term "≣̷" term
#line 1932 "../../mli-root/src/database-parser.yy"
                        {
      yylhs.value.object = ref<identical>(make, ref<formula>(yystack_[2].value.object), ref<formula>(yystack_[0].value.object), false);
    }
#line 2557 "../../mli-root/src/database-parser.cc"
    break;

  case 203: // metapredicate_function: "metapredicate constant" metapredicate_argument
#line 1939 "../../mli-root/src/database-parser.yy"
                                                        {
      yylhs.value.object = ref<structure>(make, ref<formula>(yystack_[1].value.object), ref<formula>(yystack_[0].value.object),
        structure::predicate, 1_ml, structure::postargument, precedence_t());
    }
#line 2566 "../../mli-root/src/database-parser.cc"
    break;

  case 204: // metapredicate_function: "metaformula variable" metapredicate_argument
#line 1943 "../../mli-root/src/database-parser.yy"
                                                      {
      yylhs.value.object = ref<structure>(make, ref<formula>(yystack_[1].value.object), ref<formula>(yystack_[0].value.object),
        structure::predicate, 1_ml, structure::postargument, precedence_t());
    }
#line 2575 "../../mli-root/src/database-parser.cc"
    break;

  case 205: // metapredicate_argument: "(" metapredicate_argument_body ")"
#line 1951 "../../mli-root/src/database-parser.yy"
                                           { yylhs.value.object = yystack_[1].value.object; }
#line 2581 "../../mli-root/src/database-parser.cc"
    break;

  case 206: // metapredicate_argument_body: object_formula
#line 1956 "../../mli-root/src/database-parser.yy"
                      {
      ref<sequence> vr(make, sequence::tuple);
      yylhs.value.object = vr;
      vr->push_back(ref<formula>(yystack_[0].value.object)); }
#line 2590 "../../mli-root/src/database-parser.cc"
    break;

  case 207: // metapredicate_argument_body: metapredicate_argument_body "," object_formula
#line 1960 "../../mli-root/src/database-parser.yy"
                                                         {
      yylhs.value.object = yystack_[2].value.object;
      sequence& vr = ref_cast<sequence&>(yylhs.value.object);
      vr.push_back(ref<formula>(yystack_[0].value.object)); }
#line 2599 "../../mli-root/src/database-parser.cc"
    break;

  case 208: // object_formula: atomic_formula
#line 1968 "../../mli-root/src/database-parser.yy"
                      { yylhs.value.object = yystack_[0].value.object; }
#line 2605 "../../mli-root/src/database-parser.cc"
    break;

  case 209: // object_formula: very_simple_formula formula_substitution_sequence
#line 1969 "../../mli-root/src/database-parser.yy"
                                                            {
      yylhs.value.object = ref<substitution_formula>(make, ref<substitution>(yystack_[0].value.object), ref<formula>(yystack_[1].value.object));
    }
#line 2613 "../../mli-root/src/database-parser.cc"
    break;

  case 210: // object_formula: predicate_function_application
#line 1972 "../../mli-root/src/database-parser.yy"
                                      { yylhs.value.object = yystack_[0].value.object; }
#line 2619 "../../mli-root/src/database-parser.cc"
    break;

  case 211: // object_formula: logic_formula
#line 1973 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.object = yystack_[0].value.object; }
#line 2625 "../../mli-root/src/database-parser.cc"
    break;

  case 212: // object_formula: "(" object_formula ")"
#line 1974 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.object = yystack_[1].value.object; }
#line 2631 "../../mli-root/src/database-parser.cc"
    break;

  case 213: // object_formula: quantized_formula
#line 1975 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.object = yystack_[0].value.object; }
#line 2637 "../../mli-root/src/database-parser.cc"
    break;

  case 214: // object_formula: hoare_triple
#line 1976 "../../mli-root/src/database-parser.yy"
                 {}
#line 2643 "../../mli-root/src/database-parser.cc"
    break;

  case 215: // hoare_triple: "{" object_formula "}" code_sequence "{" object_formula "}"
#line 1981 "../../mli-root/src/database-parser.yy"
                                                              { yylhs.value.object = ref<formula>(); }
#line 2649 "../../mli-root/src/database-parser.cc"
    break;

  case 216: // code_statement: code_term
#line 1992 "../../mli-root/src/database-parser.yy"
              {}
#line 2655 "../../mli-root/src/database-parser.cc"
    break;

  case 218: // code_sequence: %empty
#line 1998 "../../mli-root/src/database-parser.yy"
           {}
#line 2661 "../../mli-root/src/database-parser.cc"
    break;

  case 219: // code_sequence: code_term
#line 1999 "../../mli-root/src/database-parser.yy"
              {}
#line 2667 "../../mli-root/src/database-parser.cc"
    break;

  case 220: // code_sequence: code_sequence ";" code_term
#line 2000 "../../mli-root/src/database-parser.yy"
                                {}
#line 2673 "../../mli-root/src/database-parser.cc"
    break;

  case 221: // code_term: "code variable"
#line 2005 "../../mli-root/src/database-parser.yy"
                 {}
#line 2679 "../../mli-root/src/database-parser.cc"
    break;

  case 222: // code_term: "∅"
#line 2006 "../../mli-root/src/database-parser.yy"
       {}
#line 2685 "../../mli-root/src/database-parser.cc"
    break;

  case 223: // code_term: "object variable" "≔" term
#line 2007 "../../mli-root/src/database-parser.yy"
                            {}
#line 2691 "../../mli-root/src/database-parser.cc"
    break;

  case 224: // code_term: "if" object_formula "then" code_statement "else" code_statement
#line 2008 "../../mli-root/src/database-parser.yy"
                                                                   {}
#line 2697 "../../mli-root/src/database-parser.cc"
    break;

  case 225: // code_term: "while" object_formula "do" code_statement
#line 2009 "../../mli-root/src/database-parser.yy"
                                              {}
#line 2703 "../../mli-root/src/database-parser.cc"
    break;

  case 226: // very_simple_formula: "object formula variable"
#line 2014 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.object = yystack_[0].value.object; }
#line 2709 "../../mli-root/src/database-parser.cc"
    break;

  case 227: // very_simple_formula: "atom variable"
#line 2015 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.object = yystack_[0].value.object; }
#line 2715 "../../mli-root/src/database-parser.cc"
    break;

  case 228: // very_simple_formula: "(" object_formula ")"
#line 2016 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.object = yystack_[1].value.object; }
#line 2721 "../../mli-root/src/database-parser.cc"
    break;

  case 229: // quantized_formula: quantizer_declaration quantized_body
#line 2021 "../../mli-root/src/database-parser.yy"
                                               {
      symbol_table.pop_level();
      variable_list& vsr = ref_cast<variable_list&>(yystack_[1].value.object);
      yylhs.value.object = ref<bound_formula>(make, vsr, ref<formula>(yystack_[0].value.object));
    }
#line 2731 "../../mli-root/src/database-parser.cc"
    break;

  case 230: // quantized_formula: quantizer_declaration optional_in_term ":" object_formula
#line 2026 "../../mli-root/src/database-parser.yy"
                                                                       {
      symbol_table.pop_level();
      variable_list& vsr = ref_cast<variable_list&>(yystack_[3].value.object);
      yylhs.value.object = ref<bound_formula>(make, vsr, yystack_[2].value.object, ref<formula>(yystack_[0].value.object));
    }
#line 2741 "../../mli-root/src/database-parser.cc"
    break;

  case 231: // quantized_formula: quantizer_declaration optional_in_term quantized_formula
#line 2031 "../../mli-root/src/database-parser.yy"
                                                                      {
      symbol_table.pop_level();
      variable_list& vsr = ref_cast<variable_list&>(yystack_[2].value.object);
      yylhs.value.object = ref<bound_formula>(make, vsr, yystack_[1].value.object, ref<formula>(yystack_[0].value.object));
    }
#line 2751 "../../mli-root/src/database-parser.cc"
    break;

  case 232: // simple_formula: "object formula variable"
#line 2040 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.object = yystack_[0].value.object; }
#line 2757 "../../mli-root/src/database-parser.cc"
    break;

  case 233: // simple_formula: "atom variable"
#line 2041 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.object = yystack_[0].value.object; }
#line 2763 "../../mli-root/src/database-parser.cc"
    break;

  case 234: // simple_formula: predicate_expression
#line 2042 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.object = yystack_[0].value.object; }
#line 2769 "../../mli-root/src/database-parser.cc"
    break;

  case 235: // simple_formula: "(" object_formula ")"
#line 2043 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.object = yystack_[1].value.object; }
#line 2775 "../../mli-root/src/database-parser.cc"
    break;

  case 236: // simple_formula: quantized_formula
#line 2044 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.object = yystack_[0].value.object; }
#line 2781 "../../mli-root/src/database-parser.cc"
    break;

  case 237: // quantized_body: atomic_formula
#line 2050 "../../mli-root/src/database-parser.yy"
                      { yylhs.value.object = yystack_[0].value.object; }
#line 2787 "../../mli-root/src/database-parser.cc"
    break;

  case 238: // quantized_body: "(" object_formula ")"
#line 2051 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.object = yystack_[1].value.object; }
#line 2793 "../../mli-root/src/database-parser.cc"
    break;

  case 239: // atomic_formula: "atom constant"
#line 2055 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.object = yystack_[0].value.object; }
#line 2799 "../../mli-root/src/database-parser.cc"
    break;

  case 240: // atomic_formula: "object formula variable"
#line 2056 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.object = yystack_[0].value.object; }
#line 2805 "../../mli-root/src/database-parser.cc"
    break;

  case 241: // atomic_formula: "atom variable"
#line 2057 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.object = yystack_[0].value.object; }
#line 2811 "../../mli-root/src/database-parser.cc"
    break;

  case 242: // atomic_formula: predicate
#line 2058 "../../mli-root/src/database-parser.yy"
                 { yylhs.value.object = yystack_[0].value.object; }
#line 2817 "../../mli-root/src/database-parser.cc"
    break;

  case 243: // predicate: predicate_expression
#line 2064 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.object = yystack_[0].value.object; }
#line 2823 "../../mli-root/src/database-parser.cc"
    break;

  case 244: // predicate: term "=" term
#line 2065 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, equal_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2829 "../../mli-root/src/database-parser.cc"
    break;

  case 245: // predicate: term "≠" term
#line 2066 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, not_equal_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2835 "../../mli-root/src/database-parser.cc"
    break;

  case 246: // predicate: term "<" term
#line 2068 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, less_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2841 "../../mli-root/src/database-parser.cc"
    break;

  case 247: // predicate: term ">" term
#line 2069 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, greater_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2847 "../../mli-root/src/database-parser.cc"
    break;

  case 248: // predicate: term "≤" term
#line 2070 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, less_or_equal_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2853 "../../mli-root/src/database-parser.cc"
    break;

  case 249: // predicate: term "≥" term
#line 2071 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, greater_or_equal_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2859 "../../mli-root/src/database-parser.cc"
    break;

  case 250: // predicate: term "≮" term
#line 2072 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, not_less_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2865 "../../mli-root/src/database-parser.cc"
    break;

  case 251: // predicate: term "≯" term
#line 2073 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, not_greater_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2871 "../../mli-root/src/database-parser.cc"
    break;

  case 252: // predicate: term "≰" term
#line 2074 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, not_less_or_equal_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2877 "../../mli-root/src/database-parser.cc"
    break;

  case 253: // predicate: term "≱" term
#line 2075 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, not_greater_or_equal_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2883 "../../mli-root/src/database-parser.cc"
    break;

  case 254: // predicate: term "∈" term
#line 2077 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, in_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2889 "../../mli-root/src/database-parser.cc"
    break;

  case 255: // predicate: term "∉" term
#line 2078 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, not_in_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2895 "../../mli-root/src/database-parser.cc"
    break;

  case 256: // predicate: term "⊆" term
#line 2079 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, subset_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2901 "../../mli-root/src/database-parser.cc"
    break;

  case 257: // predicate: term "⊊" term
#line 2080 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, proper_subset_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2907 "../../mli-root/src/database-parser.cc"
    break;

  case 258: // predicate: term "⊇" term
#line 2081 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, superset_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2913 "../../mli-root/src/database-parser.cc"
    break;

  case 259: // predicate: term "⊋" term
#line 2082 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::predicate, 0_ml, structure::infix, proper_superset_oprec, yystack_[2].value.object, yystack_[0].value.object); }
#line 2919 "../../mli-root/src/database-parser.cc"
    break;

  case 260: // $@16: %empty
#line 2083 "../../mli-root/src/database-parser.yy"
          { symbol_table.push_level(false); bound_variable_type = database_parser::token::is_set_variable; }
#line 2925 "../../mli-root/src/database-parser.cc"
    break;

  case 261: // $@17: %empty
#line 2084 "../../mli-root/src/database-parser.yy"
                               { bound_variable_type = free_variable_context; }
#line 2931 "../../mli-root/src/database-parser.cc"
    break;

  case 262: // predicate: "Set" $@16 "₍" "Set variable" "₎" $@17 simple_formula
#line 2085 "../../mli-root/src/database-parser.yy"
                       {
      symbol_table.pop_level();
      yylhs.value.object = ref<bound_formula>(make,
        ref<variable>(yystack_[3].value.object), ref<formula>(yystack_[0].value.object), bound_formula::is_set_);
    }
#line 2941 "../../mli-root/src/database-parser.cc"
    break;

  case 263: // predicate_expression: predicate_identifier tuple
#line 2094 "../../mli-root/src/database-parser.yy"
                                     {
      yylhs.value.object = ref<structure>(make, ref<formula>(yystack_[1].value.object), ref<formula>(yystack_[0].value.object),
        structure::predicate, 0_ml, structure::postargument, precedence_t());
    }
#line 2950 "../../mli-root/src/database-parser.cc"
    break;

  case 264: // predicate_identifier: "predicate constant"
#line 2102 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object;  }
#line 2956 "../../mli-root/src/database-parser.cc"
    break;

  case 265: // predicate_identifier: "predicate variable"
#line 2103 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object;  }
#line 2962 "../../mli-root/src/database-parser.cc"
    break;

  case 266: // optional_superscript_natural_number_value: %empty
#line 2108 "../../mli-root/src/database-parser.yy"
           { yylhs.value.object = ref<mli::integer>(make); yylhs.value.text = ""; }
#line 2968 "../../mli-root/src/database-parser.cc"
    break;

  case 268: // logic_formula: "¬" optional_superscript_natural_number_value object_formula
#line 2121 "../../mli-root/src/database-parser.yy"
                                                                          {
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      yylhs.value.object = ref<structure>(make, yystack_[2].value.text, structure::logic, metalevel_t(k),
        structure::prefix, logical_not_oprec, yystack_[0].value.object);
    }
#line 2979 "../../mli-root/src/database-parser.cc"
    break;

  case 269: // logic_formula: object_formula "∨" optional_superscript_natural_number_value object_formula
#line 2127 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      yylhs.value.object = ref<structure>(make, yystack_[2].value.text, structure::logic, metalevel_t(k),
        structure::infix, logical_or_oprec, yystack_[3].value.object, yystack_[0].value.object);
    }
#line 2990 "../../mli-root/src/database-parser.cc"
    break;

  case 270: // logic_formula: object_formula "∧" optional_superscript_natural_number_value object_formula
#line 2133 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      yylhs.value.object = ref<structure>(make, yystack_[2].value.text, structure::logic, metalevel_t(k),
        structure::infix, logical_and_oprec, yystack_[3].value.object, yystack_[0].value.object);
    }
#line 3001 "../../mli-root/src/database-parser.cc"
    break;

  case 271: // logic_formula: object_formula "⇒" optional_superscript_natural_number_value object_formula
#line 2139 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      yylhs.value.object = ref<structure>(make, yystack_[2].value.text, structure::logic, metalevel_t(k),
        structure::infix, implies_oprec, yystack_[3].value.object, yystack_[0].value.object);
    }
#line 3012 "../../mli-root/src/database-parser.cc"
    break;

  case 272: // logic_formula: object_formula "⇐" optional_superscript_natural_number_value object_formula
#line 2145 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      yylhs.value.object = ref<structure>(make, yystack_[2].value.text, structure::logic, metalevel_t(k),
        structure::infix, impliedby_oprec, yystack_[3].value.object, yystack_[0].value.object);
    }
#line 3023 "../../mli-root/src/database-parser.cc"
    break;

  case 273: // logic_formula: object_formula "⇔" optional_superscript_natural_number_value object_formula
#line 2151 "../../mli-root/src/database-parser.yy"
                                                                                            {
      size_type k = (size_type)ref_cast<integer&>(yystack_[1].value.object);

      yylhs.value.object = ref<structure>(make, yystack_[2].value.text, structure::logic, metalevel_t(k),
        structure::infix, equivalent_oprec, yystack_[3].value.object, yystack_[0].value.object);
    }
#line 3034 "../../mli-root/src/database-parser.cc"
    break;

  case 274: // logic_formula: prefix_logic_formula
#line 2157 "../../mli-root/src/database-parser.yy"
                            { yylhs.value.object = yystack_[0].value.object;  }
#line 3040 "../../mli-root/src/database-parser.cc"
    break;

  case 275: // prefix_logic_formula: "prefix formula variable"
#line 2162 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.object = yystack_[0].value.object; }
#line 3046 "../../mli-root/src/database-parser.cc"
    break;

  case 276: // prefix_logic_formula: prefix_not_key prefix_logic_formula
#line 2163 "../../mli-root/src/database-parser.yy"
                                              {
      yylhs.value.object = ref<structure>(make, "¬", structure::logic, 0_ml,
        structure::prefix, logical_not_oprec, yystack_[0].value.object);
    }
#line 3055 "../../mli-root/src/database-parser.cc"
    break;

  case 277: // prefix_logic_formula: prefix_or_key prefix_logic_formula prefix_logic_formula
#line 2167 "../../mli-root/src/database-parser.yy"
                                                                     {
      yylhs.value.object = ref<structure>(make, "∨", structure::logic, 0_ml,
        structure::infix, logical_or_oprec, yystack_[1].value.object, yystack_[0].value.object);
    }
#line 3064 "../../mli-root/src/database-parser.cc"
    break;

  case 278: // prefix_logic_formula: prefix_and_key prefix_logic_formula prefix_logic_formula
#line 2171 "../../mli-root/src/database-parser.yy"
                                                                      {
      yylhs.value.object = ref<structure>(make, "∧", structure::logic, 0_ml,
        structure::infix, logical_and_oprec, yystack_[1].value.object, yystack_[0].value.object);
    }
#line 3073 "../../mli-root/src/database-parser.cc"
    break;

  case 279: // prefix_logic_formula: prefix_implies_key prefix_logic_formula prefix_logic_formula
#line 2175 "../../mli-root/src/database-parser.yy"
                                                                          {
      yylhs.value.object = ref<structure>(make, "⇒", structure::logic, 0_ml,
        structure::infix, implies_oprec, yystack_[1].value.object, yystack_[0].value.object);
    }
#line 3082 "../../mli-root/src/database-parser.cc"
    break;

  case 280: // prefix_logic_formula: prefix_equivalent_key prefix_logic_formula prefix_logic_formula
#line 2179 "../../mli-root/src/database-parser.yy"
                                                                             {
      yylhs.value.object = ref<structure>(make, "⇔", structure::logic, 0_ml,
        structure::infix, equivalent_oprec, yystack_[1].value.object, yystack_[0].value.object);
 }
#line 3091 "../../mli-root/src/database-parser.cc"
    break;

  case 281: // quantizer_declaration: quantized_variable_list
#line 2187 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.object = yystack_[0].value.object; }
#line 3097 "../../mli-root/src/database-parser.cc"
    break;

  case 282: // quantized_variable_list: all_variable_list
#line 2191 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.object = yystack_[0].value.object; }
#line 3103 "../../mli-root/src/database-parser.cc"
    break;

  case 283: // quantized_variable_list: exist_variable_list
#line 2192 "../../mli-root/src/database-parser.yy"
                           { yylhs.value.object = yystack_[0].value.object; }
#line 3109 "../../mli-root/src/database-parser.cc"
    break;

  case 284: // all_variable_list: "∀" all_identifier_list
#line 2197 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.object = yystack_[0].value.object; }
#line 3115 "../../mli-root/src/database-parser.cc"
    break;

  case 285: // exist_variable_list: "∃" exist_identifier_list
#line 2202 "../../mli-root/src/database-parser.yy"
                                 { yylhs.value.object = yystack_[0].value.object; }
#line 3121 "../../mli-root/src/database-parser.cc"
    break;

  case 286: // all_identifier_list: "all variable"
#line 2207 "../../mli-root/src/database-parser.yy"
                    {
      bound_variable_type = free_variable_context;
      yylhs.value.object = ref<variable_list>(make, ref<variable>(yystack_[0].value.object), bound_formula::all_);
    }
#line 3130 "../../mli-root/src/database-parser.cc"
    break;

  case 287: // $@18: %empty
#line 2211 "../../mli-root/src/database-parser.yy"
                           { bound_variable_type = token::all_variable; }
#line 3136 "../../mli-root/src/database-parser.cc"
    break;

  case 288: // all_identifier_list: all_identifier_list $@18 "," "all variable"
#line 2212 "../../mli-root/src/database-parser.yy"
                          {
      bound_variable_type = free_variable_context;
      yylhs.value.object = yystack_[3].value.object;
      ref_cast<variable_list&>(yylhs.value.object).push_back(ref<variable>(yystack_[0].value.object), bound_formula::all_);
    }
#line 3146 "../../mli-root/src/database-parser.cc"
    break;

  case 289: // exist_identifier_list: "exist variable"
#line 2221 "../../mli-root/src/database-parser.yy"
                      {
      bound_variable_type = free_variable_context;
      yylhs.value.object = ref<variable_list>(make, ref<variable>(yystack_[0].value.object), bound_formula::exist_);
    }
#line 3155 "../../mli-root/src/database-parser.cc"
    break;

  case 290: // $@19: %empty
#line 2225 "../../mli-root/src/database-parser.yy"
                             { bound_variable_type = database_parser::token::exist_variable; }
#line 3161 "../../mli-root/src/database-parser.cc"
    break;

  case 291: // exist_identifier_list: exist_identifier_list $@19 "," "exist variable"
#line 2226 "../../mli-root/src/database-parser.yy"
                            {
      bound_variable_type = free_variable_context;
      yylhs.value.object = yystack_[3].value.object;
      ref_cast<variable_list&>(yylhs.value.object).push_back(ref<variable>(yystack_[0].value.object), bound_formula::exist_);
    }
#line 3171 "../../mli-root/src/database-parser.cc"
    break;

  case 292: // optional_in_term: %empty
#line 2236 "../../mli-root/src/database-parser.yy"
           { yylhs.value.object = ref<formula>(make); }
#line 3177 "../../mli-root/src/database-parser.cc"
    break;

  case 293: // optional_in_term: "∈" term
#line 2237 "../../mli-root/src/database-parser.yy"
                { yylhs.value.object = yystack_[0].value.object; }
#line 3183 "../../mli-root/src/database-parser.cc"
    break;

  case 294: // tuple: "(" tuple_body ")"
#line 2244 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[1].value.object; }
#line 3189 "../../mli-root/src/database-parser.cc"
    break;

  case 295: // tuple_body: term
#line 2249 "../../mli-root/src/database-parser.yy"
            {
      ref<sequence> vr(make, sequence::tuple);
      yylhs.value.object = vr;
      vr->push_back(ref<formula>(yystack_[0].value.object));
    }
#line 3199 "../../mli-root/src/database-parser.cc"
    break;

  case 296: // tuple_body: tuple_body "," term
#line 2254 "../../mli-root/src/database-parser.yy"
                              {
      yylhs.value.object = yystack_[2].value.object;
      sequence& vr = ref_cast<sequence&>(yylhs.value.object);
      vr.push_back(ref<formula>(yystack_[0].value.object));
    }
#line 3209 "../../mli-root/src/database-parser.cc"
    break;

  case 297: // term: simple_term
#line 2263 "../../mli-root/src/database-parser.yy"
                   { yylhs.value.object = yystack_[0].value.object; }
#line 3215 "../../mli-root/src/database-parser.cc"
    break;

  case 298: // term: function_term
#line 2264 "../../mli-root/src/database-parser.yy"
                     { yylhs.value.object = yystack_[0].value.object; }
#line 3221 "../../mli-root/src/database-parser.cc"
    break;

  case 299: // term: simple_term term_substitution_sequence
#line 2265 "../../mli-root/src/database-parser.yy"
                                                 {
      yylhs.value.object = ref<substitution_formula>(make, ref<substitution>(yystack_[0].value.object), ref<formula>(yystack_[1].value.object));
    }
#line 3229 "../../mli-root/src/database-parser.cc"
    break;

  case 300: // term: set_term
#line 2268 "../../mli-root/src/database-parser.yy"
                { yylhs.value.object = yystack_[0].value.object; }
#line 3235 "../../mli-root/src/database-parser.cc"
    break;

  case 301: // simple_term: "term constant"
#line 2273 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.object = yystack_[0].value.object; }
#line 3241 "../../mli-root/src/database-parser.cc"
    break;

  case 302: // simple_term: "natural number value"
#line 2274 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.object = yystack_[0].value.object; }
#line 3247 "../../mli-root/src/database-parser.cc"
    break;

  case 303: // simple_term: "integer value"
#line 2275 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.object = yystack_[0].value.object; }
#line 3253 "../../mli-root/src/database-parser.cc"
    break;

  case 304: // simple_term: term_identifier
#line 2276 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.object = yystack_[0].value.object; }
#line 3259 "../../mli-root/src/database-parser.cc"
    break;

  case 305: // simple_term: "(" term ")"
#line 2277 "../../mli-root/src/database-parser.yy"
                       { yylhs.value.object = yystack_[1].value.object; }
#line 3265 "../../mli-root/src/database-parser.cc"
    break;

  case 306: // term_identifier: "object variable" variable_exclusion_set
#line 2282 "../../mli-root/src/database-parser.yy"
                                                    {
      ref<variable> xr = yystack_[1].value.object;
      ref<variable> vr = yystack_[0].value.object;
      xr->excluded_.insert(vr->excluded_.begin(), vr->excluded_.end());
      yylhs.value.object = yystack_[1].value.object;
    }
#line 3276 "../../mli-root/src/database-parser.cc"
    break;

  case 307: // term_identifier: "function variable"
#line 2288 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 3282 "../../mli-root/src/database-parser.cc"
    break;

  case 308: // term_identifier: "function map variable"
#line 2289 "../../mli-root/src/database-parser.yy"
                              { yylhs.value.object = yystack_[0].value.object; }
#line 3288 "../../mli-root/src/database-parser.cc"
    break;

  case 309: // term_identifier: "all variable"
#line 2290 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 3294 "../../mli-root/src/database-parser.cc"
    break;

  case 310: // term_identifier: "exist variable"
#line 2291 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 3300 "../../mli-root/src/database-parser.cc"
    break;

  case 311: // term_identifier: "Set variable"
#line 2292 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 3306 "../../mli-root/src/database-parser.cc"
    break;

  case 312: // term_identifier: "set variable"
#line 2293 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 3312 "../../mli-root/src/database-parser.cc"
    break;

  case 313: // term_identifier: "implicit set variable"
#line 2294 "../../mli-root/src/database-parser.yy"
                             { yylhs.value.object = yystack_[0].value.object; }
#line 3318 "../../mli-root/src/database-parser.cc"
    break;

  case 314: // variable_exclusion_set: %empty
#line 2299 "../../mli-root/src/database-parser.yy"
           { yylhs.value.object = ref<variable>(make);  }
#line 3324 "../../mli-root/src/database-parser.cc"
    break;

  case 315: // variable_exclusion_set: "ₓ" "₍" variable_exclusion_list "₎"
#line 2300 "../../mli-root/src/database-parser.yy"
                                            { yylhs.value.object = yystack_[1].value.object; }
#line 3330 "../../mli-root/src/database-parser.cc"
    break;

  case 316: // variable_exclusion_list: bound_variable
#line 2305 "../../mli-root/src/database-parser.yy"
                      { ref<variable> vr(make); vr->excluded_.insert(yystack_[0].value.object); yylhs.value.object = vr; }
#line 3336 "../../mli-root/src/database-parser.cc"
    break;

  case 317: // variable_exclusion_list: variable_exclusion_list bound_variable
#line 2306 "../../mli-root/src/database-parser.yy"
                                                   {
      ref<variable> vr = yystack_[1].value.object;
      vr->excluded_.insert(yystack_[0].value.object);
      yylhs.value.object = vr;
    }
#line 3346 "../../mli-root/src/database-parser.cc"
    break;

  case 318: // bound_variable: "all variable"
#line 2315 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 3352 "../../mli-root/src/database-parser.cc"
    break;

  case 319: // bound_variable: "exist variable"
#line 2316 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 3358 "../../mli-root/src/database-parser.cc"
    break;

  case 320: // bound_variable: "Set variable"
#line 2317 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 3364 "../../mli-root/src/database-parser.cc"
    break;

  case 321: // bound_variable: "set variable"
#line 2318 "../../mli-root/src/database-parser.yy"
                          { yylhs.value.object = yystack_[0].value.object; }
#line 3370 "../../mli-root/src/database-parser.cc"
    break;

  case 322: // bound_variable: "implicit set variable"
#line 2319 "../../mli-root/src/database-parser.yy"
                             { yylhs.value.object = yystack_[0].value.object; }
#line 3376 "../../mli-root/src/database-parser.cc"
    break;

  case 323: // function_term: function_term_identifier tuple
#line 2324 "../../mli-root/src/database-parser.yy"
                                         {
      yylhs.value.object = ref<structure>(make, ref<formula>(yystack_[1].value.object), ref<formula>(yystack_[0].value.object),
        structure::function, 0_ml, structure::postargument, precedence_t()); }
#line 3384 "../../mli-root/src/database-parser.cc"
    break;

  case 324: // function_term: term_function_application
#line 2327 "../../mli-root/src/database-parser.yy"
                                 { yylhs.value.object = yystack_[0].value.object; }
#line 3390 "../../mli-root/src/database-parser.cc"
    break;

  case 325: // function_term: term "!"
#line 2328 "../../mli-root/src/database-parser.yy"
                   {
      yylhs.value.object = ref<structure>(make, yystack_[0].value.text, structure::function, 0_ml,
        structure::postfix, factorial_oprec, yystack_[1].value.object);
    }
#line 3399 "../../mli-root/src/database-parser.cc"
    break;

  case 326: // function_term: term "+" term
#line 2332 "../../mli-root/src/database-parser.yy"
                           { // $$.object = ref<integer_addition>(make, ref<formula>($x.object), ref<formula>($y.object));
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::infix, plus_oprec, yystack_[2].value.object, yystack_[0].value.object);
    }
#line 3408 "../../mli-root/src/database-parser.cc"
    break;

  case 327: // function_term: term "-" term
#line 2336 "../../mli-root/src/database-parser.yy"
                           { // $$.object = ref<integer_addition>(make, ref<formula>($x.object), ref<integer_negative>(make, ref<formula>($y.object)));
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::infix, minus_oprec, yystack_[2].value.object, yystack_[0].value.object);
    }
#line 3417 "../../mli-root/src/database-parser.cc"
    break;

  case 328: // function_term: "-" term
#line 2340 "../../mli-root/src/database-parser.yy"
                                      { // $$.object = ref<integer_negative>(make, ref<formula>($x.object)); }
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::prefix, unary_minus_oprec, yystack_[0].value.object);
    }
#line 3426 "../../mli-root/src/database-parser.cc"
    break;

  case 329: // function_term: term "⋅" term
#line 2344 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::infix, mult_oprec, yystack_[2].value.object, yystack_[0].value.object);
    }
#line 3435 "../../mli-root/src/database-parser.cc"
    break;

  case 330: // function_term: term "/" term
#line 2348 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::infix, divide_oprec, yystack_[2].value.object, yystack_[0].value.object);
    }
#line 3444 "../../mli-root/src/database-parser.cc"
    break;

  case 331: // set_term: "{" "}"
#line 2356 "../../mli-root/src/database-parser.yy"
            { yylhs.value.object = ref<sequence>(make, sequence::member_list_set); }
#line 3450 "../../mli-root/src/database-parser.cc"
    break;

  case 332: // set_term: "∅"
#line 2357 "../../mli-root/src/database-parser.yy"
        { yylhs.value.object = ref<constant>(make, "∅", formula_type(database_parser::token::term_constant)); }
#line 3456 "../../mli-root/src/database-parser.cc"
    break;

  case 333: // set_term: "{" set_member_list "}"
#line 2358 "../../mli-root/src/database-parser.yy"
                               { yylhs.value.object = yystack_[1].value.object; }
#line 3462 "../../mli-root/src/database-parser.cc"
    break;

  case 334: // set_term: "{" "set variable definition" optional_in_term "|" object_formula "}"
#line 2359 "../../mli-root/src/database-parser.yy"
                                                                                 {
      symbol_table.pop_level();
      yylhs.value.object = ref<bound_formula>(make, yystack_[4].value.object, yystack_[3].value.object, yystack_[1].value.object, bound_formula::set_);
    }
#line 3471 "../../mli-root/src/database-parser.cc"
    break;

  case 335: // set_term: "{" "₍" implicit_set_identifier_list optional_in_term "₎" term "|" object_formula "}"
#line 2363 "../../mli-root/src/database-parser.yy"
                                                                                                      {
      symbol_table.pop_level();
      variable_list& vs = ref_cast<variable_list&>(yystack_[6].value.object);
      ref<sequence> sp(make, ref<formula>(yystack_[3].value.object), sequence::implicit_set);
      sp->push_back(ref<formula>(yystack_[1].value.object));
      yylhs.value.object =
        ref<bound_formula>(make, vs, yystack_[5].value.object, ref<formula>(sp));
    }
#line 3484 "../../mli-root/src/database-parser.cc"
    break;

  case 336: // set_term: term "∪" term
#line 2371 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::infix, set_union_oprec, yystack_[2].value.object, yystack_[0].value.object);
    }
#line 3493 "../../mli-root/src/database-parser.cc"
    break;

  case 337: // set_term: term "∩" term
#line 2375 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::infix, set_intersection_oprec, yystack_[2].value.object, yystack_[0].value.object);
    }
#line 3502 "../../mli-root/src/database-parser.cc"
    break;

  case 338: // set_term: term "∖" term
#line 2379 "../../mli-root/src/database-parser.yy"
                           {
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::infix, set_difference_oprec, yystack_[2].value.object, yystack_[0].value.object);
    }
#line 3511 "../../mli-root/src/database-parser.cc"
    break;

  case 339: // set_term: "∁" term
#line 2383 "../../mli-root/src/database-parser.yy"
                   {
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::prefix, set_complement_oprec, yystack_[0].value.object);
    }
#line 3520 "../../mli-root/src/database-parser.cc"
    break;

  case 340: // set_term: "⋃" term
#line 2387 "../../mli-root/src/database-parser.yy"
                   { /* prefix union operator  */
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::prefix, set_union_operator_oprec, yystack_[0].value.object);
    }
#line 3529 "../../mli-root/src/database-parser.cc"
    break;

  case 341: // set_term: "∩" term
#line 2391 "../../mli-root/src/database-parser.yy"
                   { /* prefix intersection operator  */
      yylhs.value.object = ref<structure>(make, yystack_[1].value.text, structure::function, 0_ml,
        structure::prefix, set_intersection_operator_oprec, yystack_[0].value.object);
    }
#line 3538 "../../mli-root/src/database-parser.cc"
    break;

  case 342: // $@20: %empty
#line 2399 "../../mli-root/src/database-parser.yy"
    { symbol_table.push_level(false); bound_variable_type = database_parser::token::is_set_variable; }
#line 3544 "../../mli-root/src/database-parser.cc"
    break;

  case 343: // implicit_set_identifier_list: $@20 "Set variable"
#line 2400 "../../mli-root/src/database-parser.yy"
                       {
      bound_variable_type = free_variable_context;
      yylhs.value.object = ref<variable_list>(make, ref<variable>(yystack_[0].value.object), bound_formula::implicit_set);
    }
#line 3553 "../../mli-root/src/database-parser.cc"
    break;

  case 344: // $@21: %empty
#line 2404 "../../mli-root/src/database-parser.yy"
                                    { bound_variable_type = database_parser::token::is_set_variable; }
#line 3559 "../../mli-root/src/database-parser.cc"
    break;

  case 345: // implicit_set_identifier_list: implicit_set_identifier_list $@21 "," "Set variable"
#line 2405 "../../mli-root/src/database-parser.yy"
                             {
      bound_variable_type = free_variable_context;
      yylhs.value.object = yystack_[3].value.object;
      ref_cast<variable_list&>(yylhs.value.object).push_back(ref<variable>(yystack_[0].value.object), bound_formula::implicit_set);
    }
#line 3569 "../../mli-root/src/database-parser.cc"
    break;

  case 346: // set_member_list: term
#line 2414 "../../mli-root/src/database-parser.yy"
            {
      ref<sequence> vr(make, sequence::member_list_set);
      yylhs.value.object = vr;
      vr->push_back(ref<formula>(yystack_[0].value.object)); }
#line 3578 "../../mli-root/src/database-parser.cc"
    break;

  case 347: // set_member_list: set_member_list "," term
#line 2418 "../../mli-root/src/database-parser.yy"
                                   {
      yylhs.value.object = yystack_[2].value.object;
      sequence& vr = ref_cast<sequence&>(yylhs.value.object);
      vr.push_back(ref<formula>(yystack_[0].value.object));
    }
#line 3588 "../../mli-root/src/database-parser.cc"
    break;

  case 348: // function_term_identifier: "function constant"
#line 2427 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.object = yystack_[0].value.object; }
#line 3594 "../../mli-root/src/database-parser.cc"
    break;

  case 349: // function_term_identifier: "function variable"
#line 2428 "../../mli-root/src/database-parser.yy"
                         { yylhs.value.object = yystack_[0].value.object; }
#line 3600 "../../mli-root/src/database-parser.cc"
    break;


#line 3604 "../../mli-root/src/database-parser.cc"

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
      yy_lac_discard_ ("error recovery");
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
  database_parser::error (const syntax_error& yyexc)
  {
    error (yyexc.location, yyexc.what ());
  }

  /* Return YYSTR after stripping away unnecessary quotes and
     backslashes, so that it's suitable for yyerror.  The heuristic is
     that double-quoting is unnecessary unless the string contains an
     apostrophe, a comma, or backslash (other than backslash-backslash).
     YYSTR is taken from yytname.  */
  std::string
  database_parser::yytnamerr_ (const char *yystr)
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
  database_parser::symbol_name (symbol_kind_type yysymbol)
  {
    return yytnamerr_ (yytname_[yysymbol]);
  }



  // database_parser::context.
  database_parser::context::context (const database_parser& yyparser, const symbol_type& yyla)
    : yyparser_ (yyparser)
    , yyla_ (yyla)
  {}

  int
  database_parser::context::expected_tokens (symbol_kind_type yyarg[], int yyargn) const
  {
    // Actual number of expected tokens
    int yycount = 0;

#if MLIDEBUG
    // Execute LAC once. We don't care if it is successful, we
    // only do it for the sake of debugging output.
    if (!yyparser_.yy_lac_established_)
      yyparser_.yy_lac_check_ (yyla_.kind ());
#endif

    for (int yyx = 0; yyx < YYNTOKENS; ++yyx)
      {
        symbol_kind_type yysym = YY_CAST (symbol_kind_type, yyx);
        if (yysym != symbol_kind::S_YYerror
            && yysym != symbol_kind::S_YYUNDEF
            && yyparser_.yy_lac_check_ (yysym))
          {
            if (!yyarg)
              ++yycount;
            else if (yycount == yyargn)
              return 0;
            else
              yyarg[yycount++] = yysym;
          }
      }
    if (yyarg && yycount == 0 && 0 < yyargn)
      yyarg[0] = symbol_kind::S_YYEMPTY;
    return yycount;
  }




  bool
  database_parser::yy_lac_check_ (symbol_kind_type yytoken) const
  {
    // Logically, the yylac_stack's lifetime is confined to this function.
    // Clear it, to get rid of potential left-overs from previous call.
    yylac_stack_.clear ();
    // Reduce until we encounter a shift and thereby accept the token.
#if MLIDEBUG
    YYCDEBUG << "LAC: checking lookahead " << symbol_name (yytoken) << ':';
#endif
    std::ptrdiff_t lac_top = 0;
    while (true)
      {
        state_type top_state = (yylac_stack_.empty ()
                                ? yystack_[lac_top].state
                                : yylac_stack_.back ());
        int yyrule = yypact_[+top_state];
        if (yy_pact_value_is_default_ (yyrule)
            || (yyrule += yytoken) < 0 || yylast_ < yyrule
            || yycheck_[yyrule] != yytoken)
          {
            // Use the default action.
            yyrule = yydefact_[+top_state];
            if (yyrule == 0)
              {
                YYCDEBUG << " Err\n";
                return false;
              }
          }
        else
          {
            // Use the action from yytable.
            yyrule = yytable_[yyrule];
            if (yy_table_value_is_error_ (yyrule))
              {
                YYCDEBUG << " Err\n";
                return false;
              }
            if (0 < yyrule)
              {
                YYCDEBUG << " S" << yyrule << '\n';
                return true;
              }
            yyrule = -yyrule;
          }
        // By now we know we have to simulate a reduce.
        YYCDEBUG << " R" << yyrule - 1;
        // Pop the corresponding number of values from the stack.
        {
          std::ptrdiff_t yylen = yyr2_[yyrule];
          // First pop from the LAC stack as many tokens as possible.
          std::ptrdiff_t lac_size = std::ptrdiff_t (yylac_stack_.size ());
          if (yylen < lac_size)
            {
              yylac_stack_.resize (std::size_t (lac_size - yylen));
              yylen = 0;
            }
          else if (lac_size)
            {
              yylac_stack_.clear ();
              yylen -= lac_size;
            }
          // Only afterwards look at the main stack.
          // We simulate popping elements by incrementing lac_top.
          lac_top += yylen;
        }
        // Keep top_state in sync with the updated stack.
        top_state = (yylac_stack_.empty ()
                     ? yystack_[lac_top].state
                     : yylac_stack_.back ());
        // Push the resulting state of the reduction.
        state_type state = yy_lr_goto_state_ (top_state, yyr1_[yyrule]);
        YYCDEBUG << " G" << int (state);
        yylac_stack_.push_back (state);
      }
  }

  // Establish the initial context if no initial context currently exists.
  bool
  database_parser::yy_lac_establish_ (symbol_kind_type yytoken)
  {
    /* Establish the initial context for the current lookahead if no initial
       context is currently established.

       We define a context as a snapshot of the parser stacks.  We define
       the initial context for a lookahead as the context in which the
       parser initially examines that lookahead in order to select a
       syntactic action.  Thus, if the lookahead eventually proves
       syntactically unacceptable (possibly in a later context reached via a
       series of reductions), the initial context can be used to determine
       the exact set of tokens that would be syntactically acceptable in the
       lookahead's place.  Moreover, it is the context after which any
       further semantic actions would be erroneous because they would be
       determined by a syntactically unacceptable token.

       yy_lac_establish_ should be invoked when a reduction is about to be
       performed in an inconsistent state (which, for the purposes of LAC,
       includes consistent states that don't know they're consistent because
       their default reductions have been disabled).

       For parse.lac=full, the implementation of yy_lac_establish_ is as
       follows.  If no initial context is currently established for the
       current lookahead, then check if that lookahead can eventually be
       shifted if syntactic actions continue from the current context.  */
    if (yy_lac_established_)
      return true;
    else
      {
#if MLIDEBUG
        YYCDEBUG << "LAC: initial context established for "
                 << symbol_name (yytoken) << '\n';
#endif
        yy_lac_established_ = true;
        return yy_lac_check_ (yytoken);
      }
  }

  // Discard any previous initial lookahead context.
  void
  database_parser::yy_lac_discard_ (const char* event)
  {
   /* Discard any previous initial lookahead context because of Event,
      which may be a lookahead change or an invalidation of the currently
      established initial context for the current lookahead.

      The most common example of a lookahead change is a shift.  An example
      of both cases is syntax error recovery.  That is, a syntax error
      occurs when the lookahead is syntactically erroneous for the
      currently established initial context, so error recovery manipulates
      the parser stacks to try to find a new initial context in which the
      current lookahead is syntactically acceptable.  If it fails to find
      such a context, it discards the lookahead.  */
    if (yy_lac_established_)
      {
        YYCDEBUG << "LAC: initial context discarded due to "
                 << event << '\n';
        yy_lac_established_ = false;
      }
  }


  int
  database_parser::yy_syntax_error_arguments_ (const context& yyctx,
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
         In the first two cases, it might appear that the current syntax
         error should have been detected in the previous state when
         yy_lac_check was invoked.  However, at that time, there might
         have been a different syntax error that discarded a different
         initial context during error recovery, leaving behind the
         current lookahead.
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
  database_parser::yysyntax_error_ (const context& yyctx) const
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


  const short database_parser::yypact_ninf_ = -517;

  const short database_parser::yytable_ninf_ = -350;

  const short
  database_parser::yypact_[] =
  {
     386,  -517,    61,    80,  -517,   136,  -517,  -517,   -26,  -517,
    -517,  -517,  -517,    40,  -517,  -517,   300,   194,    98,  -517,
     240,  -517,   322,   295,  -517,   263,   322,   -26,   -26,   -26,
     285,   131,   320,  -517,  -517,  -517,  -517,   358,    32,  -517,
     -11,  -517,  -517,  -517,   161,  -517,   -26,   243,   261,   279,
    -517,   287,  -517,  -517,   355,   380,   309,  -517,  -517,   312,
    -517,  -517,  -517,  -517,   425,  -517,  -517,   675,   348,   351,
     351,  -517,  -517,  -517,  -517,   379,   333,  -517,   340,  -517,
     357,   144,  -517,  -517,  -517,  -517,  -517,  -517,   426,   428,
     405,   450,   450,   450,   450,   450,  -517,  -517,  1455,  -517,
    -517,  1455,  1455,  1455,   492,   922,   675,  -517,  -517,  -517,
     675,    10,  -517,   381,  -517,  -517,   176,  -517,  -517,   442,
    -517,   382,  -517,  -517,  -517,  -517,   351,  -517,  -517,  1344,
    -517,  -517,  -517,   839,   383,  -517,  -517,  -517,   351,  -517,
    -517,  -517,   359,   393,  -517,  -517,  -517,  -517,   285,  -517,
    -517,   131,   399,   320,  -517,  -517,   504,   165,   408,  1258,
    -517,  1455,  -517,  -517,  -517,   397,  -517,  -517,   431,  -517,
     433,  -517,  1258,  -517,   450,   450,   450,   450,   462,  1434,
     991,  -517,   444,   278,   278,   278,   244,   499,    10,   440,
      88,   778,   469,  1086,  -517,  -517,   -31,  1605,   139,  -517,
      10,   405,   405,   675,   675,   851,   381,  -517,  -517,  -517,
    -517,   544,   525,  1258,  1258,  1258,   405,   405,   405,   405,
     405,   952,   382,  -517,  -517,  -517,  -517,  -517,  -517,  1455,
    1172,  -517,  -517,   107,  1605,  1455,  1455,   525,  1455,  1455,
    1455,  1455,  1455,  1455,  1455,  1455,  1455,  1455,  -517,  1455,
    1455,  1455,  1455,  1455,  1455,  1455,  1455,  1455,  1455,  1455,
    1455,  1455,   738,   383,  -517,  -517,   573,   -26,   -26,   -26,
    -517,  -517,  -517,  -517,  -517,  -517,    32,    32,  -517,  -517,
    -517,  -517,   167,  -517,  -517,   458,    32,  -517,   365,  -517,
     358,  -517,   103,   392,   235,   565,   294,   464,   472,  -517,
    -517,  -517,  -517,  -517,    78,   526,   385,   565,   536,  1258,
     516,   481,   489,  -517,   482,   188,   335,  1511,   -58,   559,
      86,  1455,  -517,   493,   493,     4,  -517,   534,   535,   537,
     538,  -517,   540,  -517,  1258,  -517,  -517,   392,  1605,   392,
     392,  1258,  1258,  1258,  1258,  1258,  -517,   565,   342,  1258,
    -517,   565,   565,   598,   565,   565,   565,   565,   565,   565,
     565,   565,   565,   565,  -517,   -72,   -72,   565,   565,   643,
     278,   278,   565,   565,   565,   565,  -517,  -517,   510,   511,
     514,   515,   517,   675,  -517,  -517,  -517,  -517,   361,   572,
     736,   523,   574,   234,   522,   245,   529,   530,   519,  -517,
    -517,   635,  -517,  -517,  1258,  -517,  1455,  -517,  -517,  -517,
    -517,  -517,  -517,   160,  -517,   599,   597,  1455,   569,   542,
     407,  1558,  1258,  1258,   546,   548,  -517,   623,  -517,  -517,
    1258,  1258,  -100,  -517,   565,   140,   539,   539,   675,  1258,
    1365,   636,  1455,   392,  1605,  -517,   613,   430,   430,   271,
    -517,   392,  1258,  -517,  -517,  -517,  -517,  -517,  -517,   675,
     675,  1258,  1258,  1455,  1455,  -517,   594,   587,   588,   381,
     167,  -517,   167,   167,   167,   167,   392,   565,  -517,  -517,
    -517,  -517,   460,  1455,  -517,   351,   351,   392,  1605,   219,
    1455,   627,  1455,   185,   -24,    86,  1258,  -517,  -517,   164,
     155,  -517,   -71,  -517,    14,  -517,   199,   675,   675,    -3,
     276,   563,   564,   509,   392,  1605,    32,    32,    32,   570,
     571,   392,   392,   565,   565,  1258,  -517,  -517,   381,   529,
     530,   556,    69,  -517,   272,   565,   148,  -517,  -517,   567,
     576,  -517,   561,  -517,   565,    47,    47,  -517,   242,   192,
     575,   192,   596,  -517,   603,  -517,  -517,  -517,  -517,  -517,
     231,   -78,  -517,   172,  -517,    75,  -517,    12,   408,  -517,
    -517,  -517,  -517,  -517,   583,   584,   585,   392,   167,   167,
    -517,  -517,  -517,  -517,  1258,  -517,  -517,  -517,   351,   351,
    1258,    86,   568,  -517,  -517,  -517,   603,  -517,  -517,   273,
     589,   273,   601,  -517,   612,  -517,  -517,  -517,  -517,  -517,
    -517,   175,  -517,   422,  -517,  -517,   247,    41,    47,   612,
    -517,  -517,  -517,  -517,  -517,  -517,  -517
  };

  const short
  database_parser::yydefact_[] =
  {
       0,     4,     0,     3,     6,     0,     1,     5,     0,     8,
      68,    69,    70,     0,    33,    37,    51,     0,     0,    38,
       0,    51,    42,     0,    44,     0,    43,     0,     0,     0,
       0,     0,     0,    52,    55,    56,    53,    75,     0,    54,
       0,   119,    40,    41,     0,    46,    35,     0,     0,     0,
     131,   121,   129,   134,     0,     0,   122,   132,   126,   123,
     124,    79,    78,    71,    92,    74,    80,     0,     0,     0,
       0,   264,   239,   348,   301,   188,   240,   265,   241,   275,
     307,   314,   309,   310,   308,   311,   312,   313,     0,     0,
     266,     0,     0,     0,     0,     0,   302,   303,     0,   260,
     332,     0,     0,     0,     0,     0,     0,   210,   324,    72,
       0,   114,   146,     0,   148,   149,     0,   189,   198,   147,
     214,     0,   213,   208,   242,   243,     0,   211,   274,   292,
     281,   282,   283,     0,   297,   304,   298,   300,     0,   118,
     120,    39,     0,     0,    36,    66,    64,    73,     0,   135,
     136,     0,     0,     0,    93,    76,     0,    85,   155,     0,
     203,     0,    32,    28,   204,     0,   306,   286,   284,   289,
     285,   267,     0,   276,     0,     0,     0,     0,   314,     0,
       0,   328,     0,   339,   341,   340,   314,     0,     0,   146,
     147,     0,   292,     0,   342,   331,     0,   346,     0,   150,
     115,   266,   266,     0,     0,     0,   157,     9,    11,    12,
      13,     0,     0,     0,     0,     0,   266,   266,   266,   266,
     266,     0,   209,    15,    17,    18,   263,   240,   241,     0,
       0,   229,   237,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   325,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   299,    22,   323,     0,     0,     0,     0,
      47,    49,    59,    50,    48,    34,     0,     0,   130,   133,
     127,   125,    98,    77,    87,     0,     0,    81,     0,    84,
       0,    88,     0,   206,     0,   295,     0,     0,     0,   268,
     278,   277,   279,   280,   314,     0,     0,   346,     0,     0,
       0,   156,   212,   305,     0,   314,     0,     0,   292,     0,
     218,     0,   333,   158,   158,   151,   152,     0,     0,     0,
       0,   307,     0,    10,     0,   197,   190,   191,   192,   199,
     200,     0,     0,     0,     0,     0,    16,   293,     0,     0,
     231,   201,   202,     0,   246,   247,   248,   249,   250,   251,
     252,   253,   244,   245,   329,   326,   327,   254,   255,   336,
     337,   338,   256,   257,   258,   259,   330,    23,     0,     0,
       0,     0,     0,     0,   116,   137,   138,   139,   146,   147,
       0,     0,     0,   106,   111,     0,    94,    96,    99,   105,
      82,    90,    86,    89,     0,   205,     0,   294,   318,   319,
     320,   321,   322,     0,   316,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   343,     0,   221,   222,
       0,     0,     0,   219,   347,     0,   172,   172,     0,     0,
       0,     0,     0,   193,   194,   270,   269,   271,   272,   273,
     238,   230,     0,    45,    57,    60,    62,    67,   117,     0,
       0,     0,     0,     0,     0,    65,     0,   109,   107,     0,
      98,    91,    98,     0,     0,    98,   207,   296,   315,   317,
     288,   291,     0,     0,   261,     0,     0,    26,    30,     0,
       0,     0,     0,     0,     0,     0,     0,   171,   170,     0,
       0,   162,     0,   165,     0,   168,     0,     0,     0,     0,
       0,     0,     0,     0,   195,   196,     0,     0,     0,   146,
     146,   142,   143,   144,   145,     0,   110,   108,   113,    95,
      97,   101,     0,   103,     0,    30,     0,    25,    29,     0,
       0,   334,     0,   345,   223,     0,     0,   220,     0,     0,
     164,   167,     0,   159,     0,   160,   161,   169,   185,   184,
       0,     0,   176,     0,   179,     0,   182,   153,   154,    14,
      19,    20,    21,    24,     0,     0,     0,   128,     0,     0,
     100,    83,   232,   233,     0,   236,   262,   234,     0,     0,
       0,   218,     0,   216,   225,   215,     0,   163,   166,     0,
     178,   181,     0,   173,     0,   174,   175,   183,    58,    61,
      63,     0,   104,     0,    27,    31,     0,     0,     0,     0,
     177,   180,   102,   235,   335,   217,   224
  };

  const short
  database_parser::yypgoto_[] =
  {
    -517,  -517,  -517,   707,  -517,   259,  -205,  -517,  -517,   512,
     -99,  -517,  -113,  -517,  -517,  -517,  -517,  -517,  -517,  -517,
    -517,  -517,  -517,  -517,  -517,  -517,  -517,  -517,   715,  -517,
    -517,  -517,  -517,  -517,   595,  -517,    52,  -517,    -4,  -517,
    -517,  -517,  -517,  -517,   448,  -517,  -517,  -517,  -517,  -517,
    -517,  -517,   600,  -517,   277,   286,   274,   177,  -459,  -517,
    -517,  -268,  -517,    -9,  -517,   718,  -517,   606,  -517,  -517,
    -517,   616,  -517,   609,   378,  -517,  -517,  -517,   -41,   -98,
     441,  -517,   215,   337,   220,   338,  -450,   339,  -517,   173,
     275,   178,   280,  -414,  -517,  -517,  -517,  -178,  -517,  -517,
     709,  -517,  -102,  -517,  -516,   197,  -313,  -517,  -228,  -517,
    -517,   662,   360,  -517,  -517,   265,  -517,   371,  -517,    54,
    -517,  -517,  -517,  -517,  -517,  -517,  -517,  -517,  -182,   -70,
    -517,   195,  -517,   -28,  -517,  -517,   389,  -517,  -517,  -517,
    -517,  -517,  -517,  -517
  };

  const short
  database_parser::yydefgoto_[] =
  {
       0,     2,     3,     4,     5,   206,   207,   208,   222,   223,
     209,   263,   210,   107,   539,   108,   540,     9,    15,   143,
      16,    19,    44,    20,    21,    45,   142,   270,    22,    33,
     271,   516,   517,   518,    34,   277,    35,   276,   394,    36,
      37,    38,    63,    64,    65,    66,   157,   286,   287,   288,
     289,   290,   155,   156,   395,   396,   397,   532,   398,   399,
     469,   109,   382,   110,    40,    41,    59,    60,   152,   392,
      51,    52,    56,    57,   384,   385,   386,   387,   111,   112,
     436,   500,   501,   550,   503,   551,   505,   507,   561,   562,
     600,   564,   601,   566,   113,   114,   115,   116,   117,   118,
     160,   292,   119,   120,   592,   432,   593,   121,   122,   586,
     231,   123,   124,   182,   536,   125,   126,   172,   127,   128,
     129,   130,   131,   132,   168,   297,   170,   298,   233,   162,
     294,   234,   134,   135,   166,   413,   414,   136,   137,   318,
     319,   425,   198,   138
  };

  const short
  database_parser::yytable_[] =
  {
     163,   333,   190,   196,    13,   350,   189,   433,   225,   391,
     314,    10,    11,    39,   531,   533,   201,    39,   401,   495,
     202,   264,   224,    47,    48,    49,   158,   202,   249,   201,
     594,  -350,   496,   202,   336,   202,   216,   217,   218,   219,
     220,   602,   144,   216,   217,   218,   219,   220,   229,   554,
      30,    31,    32,   603,   557,    67,   226,   293,   555,   353,
     497,     6,  -344,   188,   261,   199,   498,    12,   265,   200,
     299,    68,    69,    70,    71,    72,    73,    74,    75,    76,
      77,    78,    79,    80,    81,    -7,    82,    83,    84,    85,
      86,   316,    87,    30,    31,    32,    88,    89,    90,   427,
     428,   557,   626,   320,    91,    92,    93,    94,    95,   225,
     139,   337,   339,   340,   214,   215,   203,   204,   546,   533,
     612,   558,   569,   224,   204,    96,    97,   559,   348,   203,
     204,   203,   204,   274,    98,    99,   424,   100,   427,   428,
     101,     8,   102,   556,   103,   173,   174,   175,   176,   177,
     377,   607,   429,   285,   104,   216,   217,   218,   219,   220,
     495,    14,   325,   326,   105,   417,  -197,   106,    53,  -197,
     165,    88,    89,    27,   389,   625,  -197,   332,   388,   591,
     283,   -92,   547,   154,   393,   430,   497,   607,   431,   579,
      71,   429,   498,   332,   273,   582,    77,   583,   211,    23,
     580,   212,    10,    11,    10,    11,   606,   420,   213,   284,
     497,   312,    88,    89,   408,   409,   498,   410,   411,    24,
     412,    54,    55,   404,   430,   349,   405,   431,   300,   301,
     302,   303,   443,   133,   332,   188,   165,   499,   497,   445,
     446,   447,   448,   449,   498,   558,    25,   451,   574,   575,
     576,   559,   216,   217,   218,   219,   220,   467,    12,   321,
      12,   549,   133,   379,   380,   381,  -197,   383,    46,  -197,
     584,    10,    11,   322,   552,   309,  -197,   558,   433,   402,
     165,   389,   141,   559,   553,   388,   216,   217,   218,   219,
     220,   478,   604,   181,   560,   579,   183,   184,   185,   191,
     197,   133,   476,   605,    17,   133,   622,    18,   585,   216,
     217,   218,   219,   220,   216,   217,   218,   219,   220,   558,
     487,   489,    50,   333,   545,   559,   599,    12,   493,   494,
      27,   309,    42,    43,    28,    29,   165,   510,   216,   217,
     218,   219,   188,   216,   217,   218,   219,   220,   408,   409,
     514,   410,   411,   541,   412,   406,   295,    58,   407,   521,
     522,   519,   520,   470,   145,   266,   471,    27,   267,   268,
     269,    28,    61,    62,   306,   307,   595,   248,   249,   250,
     251,   624,   146,    30,    31,    32,    -2,     1,   317,   468,
     470,    -7,   149,   581,   548,   459,   460,   509,   133,   133,
     147,   570,   216,   217,   218,   219,   220,   148,   338,   216,
     217,   218,   219,   220,   261,   537,   538,   150,   188,   188,
      30,    31,    32,   577,   347,   317,    30,    31,    32,   151,
     351,   352,   153,   354,   355,   356,   357,   358,   359,   360,
     361,   362,   363,   154,   364,   365,   366,   367,   368,   369,
     370,   371,   372,   373,   374,   375,   376,  -226,   312,   216,
     217,   218,   219,   220,  -227,   450,   567,   568,   214,   215,
     159,   390,   133,   161,   216,   217,   218,   219,   220,  -349,
     167,   133,   613,   169,   248,   249,   250,   251,   616,   216,
     217,   218,   219,   220,   254,   255,   256,   216,   217,   218,
      79,   159,   171,  -186,   421,   205,   221,   262,   313,   216,
     217,   218,   219,   220,   275,    67,   434,   280,   614,   615,
     282,   261,    91,    92,    93,    94,    95,   296,   204,   444,
     485,    68,    69,    70,    71,    72,    73,    74,    75,    76,
      77,    78,    79,    80,   186,   623,    82,    83,    84,    85,
      86,  -287,    87,  -290,   165,   310,    88,    89,    90,   248,
     249,   250,   251,   311,    91,    92,    93,    94,    95,   254,
     255,   256,   323,   324,   308,   229,   334,   335,   390,   400,
     378,   187,   418,   486,   415,    96,    97,   341,   342,   343,
     344,   345,   416,   419,    98,    99,   261,   100,   214,   215,
     101,   477,   102,   422,   103,  -187,   461,   462,   248,   249,
     250,   251,   482,  -228,   104,   423,   426,   488,   254,   255,
     256,   435,   438,   439,   105,   440,   441,   106,   442,   452,
     466,   453,   454,   133,   573,   455,   456,   513,   457,   216,
     217,   218,   219,   220,   465,   261,  -112,   515,   472,   474,
     473,   475,   481,   480,   133,   133,   483,   492,   523,   524,
     248,   249,   250,   251,   248,   249,   250,   251,   491,   506,
     254,   255,   256,   484,   254,   255,   256,   490,   535,   512,
     216,   525,   526,   527,   543,   542,   578,   544,   571,   572,
     588,  -140,  -141,   596,   590,   554,   619,   261,    67,   589,
     549,   261,   133,   133,   608,   609,   610,   599,   618,   604,
       7,   133,   133,   133,    68,    69,    70,    71,    72,    73,
      74,    75,    76,    77,    78,    79,    80,    81,   528,    82,
      83,    84,    85,    86,   346,    87,    26,   272,   403,    88,
      89,    90,   248,   249,   250,   251,   530,    91,    92,    93,
      94,    95,   534,   255,   256,   611,   529,   291,   140,   281,
     279,   458,   235,   236,   278,   437,   237,   597,    96,    97,
     463,   464,   502,   504,   598,   620,   508,    98,    99,   261,
     100,   563,   621,   101,   164,   102,   565,   103,   617,   331,
     178,   232,    82,    83,    84,    85,    86,   104,    87,     0,
     511,   587,   479,     0,   235,   236,     0,   105,   237,     0,
     106,     0,     0,   238,   239,   240,   241,   242,   243,   244,
     245,   246,   247,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   248,   249,   250,   251,     0,
       0,     0,   252,   253,     0,   254,   255,   256,     0,     0,
     257,   258,   259,   260,     0,   238,   239,   240,   241,   242,
     243,   244,   245,   246,   247,   235,   236,     0,     0,   237,
       0,     0,   261,     0,     0,     0,     0,   248,   249,   250,
     251,     0,     0,     0,   252,   253,     0,   254,   255,   256,
       0,     0,   257,   258,   259,   260,     0,   327,   328,   329,
     330,   313,   331,   178,     0,    82,    83,    84,    85,    86,
       0,    87,     0,     0,   261,     0,   238,   239,   240,   241,
     242,   243,   244,   245,   246,   247,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   248,   249,
     250,   251,     0,     0,     0,   252,   253,     0,   254,   255,
     256,     0,     0,   257,   258,   259,   260,     0,     0,     0,
       0,     0,    69,    70,    71,    72,    73,    74,     0,    76,
      77,    78,    79,    80,   178,   261,    82,    83,    84,    85,
      86,   192,    87,     0,     0,     0,    88,    89,    90,     0,
       0,     0,     0,     0,    91,    92,    93,    94,    95,   328,
     329,   330,     0,   331,   178,     0,    82,    83,    84,    85,
      86,     0,    87,     0,     0,    96,    97,     0,     0,     0,
       0,     0,     0,     0,    98,    99,     0,   100,     0,     0,
     101,    69,   102,     0,   103,    73,    74,     0,     0,     0,
       0,     0,    80,   178,   193,    82,    83,    84,    85,    86,
     192,    87,   194,     0,   105,     0,   195,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    96,    97,     0,     0,     0,     0,
       0,     0,     0,    98,     0,     0,   100,     0,     0,   101,
       0,   102,     0,   103,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   179,     0,     0,     0,     0,     0,     0,
       0,   194,     0,   180,     0,   195,    69,    70,    71,    72,
      73,    74,     0,    76,    77,    78,    79,    80,   315,     0,
      82,    83,    84,    85,    86,     0,    87,     0,     0,     0,
      88,    89,    90,     0,     0,     0,     0,     0,    91,    92,
      93,    94,    95,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   187,     0,     0,     0,    96,
      97,     0,     0,     0,     0,     0,     0,     0,    98,    99,
       0,   100,     0,     0,   101,     0,   102,     0,   103,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   193,     0,
       0,     0,    69,    70,    71,    72,    73,    74,   105,    76,
      77,    78,    79,    80,   304,     0,    82,    83,    84,    85,
      86,     0,    87,     0,     0,     0,    88,    89,    90,     0,
       0,     0,     0,     0,    91,    92,    93,    94,    95,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   305,     0,     0,     0,    96,    97,     0,     0,     0,
       0,     0,     0,     0,    98,    99,     0,   100,     0,     0,
     101,     0,   102,     0,   103,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   193,     0,     0,     0,    69,    70,
      71,    72,    73,    74,   105,    76,    77,    78,    79,    80,
     178,     0,    82,    83,    84,    85,    86,     0,    87,     0,
       0,     0,    88,    89,    90,     0,     0,     0,     0,     0,
      91,    92,    93,    94,    95,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    96,    97,     0,     0,     0,     0,     0,     0,     0,
      98,    99,     0,   100,     0,     0,   101,     0,   102,     0,
     103,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     193,     0,     0,     0,    69,     0,    71,    72,    73,    74,
     105,   227,    77,   228,     0,    80,   178,     0,    82,    83,
      84,    85,    86,     0,    87,    69,     0,    71,     0,    73,
      74,     0,     0,    77,     0,     0,    80,   178,     0,    82,
      83,    84,    85,    86,     0,    87,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    96,    97,     0,
       0,     0,     0,     0,     0,     0,    98,    99,     0,   100,
     229,     0,   101,     0,   102,     0,   103,     0,    96,    97,
       0,     0,     0,     0,     0,     0,   230,    98,    99,     0,
     100,     0,     0,   101,    69,   102,   180,   103,    73,    74,
       0,     0,     0,     0,     0,    80,   304,   179,    82,    83,
      84,    85,    86,     0,    87,    69,     0,   180,     0,    73,
      74,     0,     0,     0,     0,     0,    80,   178,     0,    82,
      83,    84,    85,    86,     0,    87,     0,     0,     0,     0,
       0,     0,     0,   305,     0,     0,     0,    96,    97,     0,
       0,     0,     0,     0,     0,     0,    98,     0,     0,   100,
       0,     0,   101,     0,   102,     0,   103,     0,    96,    97,
       0,     0,     0,     0,     0,     0,   179,    98,     0,     0,
     100,     0,     0,   101,     0,   102,   180,   103,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   179,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   180,   238,   239,
     240,   241,   242,   243,   244,   245,   246,   247,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     248,   249,   250,   251,     0,     0,     0,   252,   253,     0,
     254,   255,   256,     0,     0,   257,   258,   259,   260,     0,
       0,     0,     0,     0,   313,   238,   239,   240,   241,   242,
     243,   244,   245,   246,   247,     0,     0,   261,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   248,   249,   250,
     251,     0,     0,     0,   252,   253,     0,   254,   255,   256,
       0,     0,   257,   258,   259,   260,     0,     0,     0,     0,
       0,   486,   238,   239,   240,   241,   242,   243,   244,   245,
     246,   247,     0,     0,   261,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   248,   249,   250,   251,     0,     0,
       0,   252,   253,     0,   254,   255,   256,     0,     0,   257,
     258,   259,   260,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   261
  };

  const short
  database_parser::yycheck_[] =
  {
      70,   206,   104,   105,     8,   233,   104,   320,   121,   277,
     192,    37,    38,    22,   473,   474,    19,    26,   286,   119,
      23,   134,   121,    27,    28,    29,    67,    23,   100,    19,
     546,    19,   132,    23,   212,    23,    67,    68,    69,    70,
      71,   119,    46,    67,    68,    69,    70,    71,   106,   120,
      61,    62,    63,   131,   504,    23,   126,   159,   129,   237,
      46,     0,   120,   104,   136,   106,    52,    93,   138,   110,
     172,    39,    40,    41,    42,    43,    44,    45,    46,    47,
      48,    49,    50,    51,    52,     5,    54,    55,    56,    57,
      58,   193,    60,    61,    62,    63,    64,    65,    66,    52,
      53,   551,   618,   134,    72,    73,    74,    75,    76,   222,
     121,   213,   214,   215,    26,    27,   119,   120,   142,   578,
     579,    46,   125,   222,   120,    93,    94,    52,   230,   119,
     120,   119,   120,   142,   102,   103,   318,   105,    52,    53,
     108,     5,   110,   129,   112,    91,    92,    93,    94,    95,
     263,   565,   105,   157,   122,    67,    68,    69,    70,    71,
     119,   121,   203,   204,   132,    87,    22,   135,    37,    25,
      92,    64,    65,     8,   276,   134,    32,   205,   276,   132,
      15,    16,   495,    18,    17,   138,    46,   601,   141,   120,
      42,   105,    52,   221,   142,    47,    48,    49,    22,     5,
     131,    25,    37,    38,    37,    38,   131,   309,    32,   157,
      46,   123,    64,    65,    54,    55,    52,    57,    58,   121,
      60,    90,    91,   120,   138,   118,   123,   141,   174,   175,
     176,   177,   334,    38,   262,   276,    92,    97,    46,   341,
     342,   343,   344,   345,    52,    46,     6,   349,   516,   517,
     518,    52,    67,    68,    69,    70,    71,    23,    93,   120,
      93,    97,    67,   267,   268,   269,    22,   276,     5,    25,
     122,    37,    38,   134,   119,    87,    32,    46,   591,   288,
      92,   383,   121,    52,   129,   383,    67,    68,    69,    70,
      71,   131,   120,    98,    95,   120,   101,   102,   103,   104,
     105,   106,   404,   131,     4,   110,   131,     7,   536,    67,
      68,    69,    70,    71,    67,    68,    69,    70,    71,    46,
     422,   423,    37,   528,   139,    52,    95,    93,   430,   431,
       8,    87,    37,    38,    12,    13,    92,   439,    67,    68,
      69,    70,   383,    67,    68,    69,    70,    71,    54,    55,
     452,    57,    58,   134,    60,   120,   161,    37,   123,   461,
     462,   459,   460,   118,   121,     6,   121,     8,     9,    10,
      11,    12,    14,    15,   179,   180,   134,    99,   100,   101,
     102,   134,   121,    61,    62,    63,     0,     1,   193,   393,
     118,     5,    37,   121,   496,    34,    35,   438,   203,   204,
     121,   125,    67,    68,    69,    70,    71,   120,   213,    67,
      68,    69,    70,    71,   136,   485,   486,    37,   459,   460,
      61,    62,    63,   525,   229,   230,    61,    62,    63,   120,
     235,   236,   120,   238,   239,   240,   241,   242,   243,   244,
     245,   246,   247,    18,   249,   250,   251,   252,   253,   254,
     255,   256,   257,   258,   259,   260,   261,   124,   123,    67,
      68,    69,    70,    71,   124,   123,   507,   508,    26,    27,
     122,   276,   277,   122,    67,    68,    69,    70,    71,   122,
      54,   286,   584,    55,    99,   100,   101,   102,   590,    67,
      68,    69,    70,    71,   109,   110,   111,    67,    68,    69,
      50,   122,    97,   124,   309,   124,   124,   124,   123,    67,
      68,    69,    70,    71,   121,    23,   321,   118,   588,   589,
      16,   136,    72,    73,    74,    75,    76,   130,   120,   334,
     123,    39,    40,    41,    42,    43,    44,    45,    46,    47,
      48,    49,    50,    51,    52,   123,    54,    55,    56,    57,
      58,   120,    60,   120,    92,    56,    64,    65,    66,    99,
     100,   101,   102,   123,    72,    73,    74,    75,    76,   109,
     110,   111,   201,   202,   130,   106,    32,    52,   383,   121,
       7,    89,    56,   123,   120,    93,    94,   216,   217,   218,
     219,   220,   120,    57,   102,   103,   136,   105,    26,    27,
     108,   406,   110,    87,   112,   124,    34,    35,    99,   100,
     101,   102,   417,   124,   122,   133,    57,   422,   109,   110,
     111,   128,    88,    88,   132,    88,    88,   135,    88,    31,
      56,   121,   121,   438,   125,   121,   121,   442,   121,    67,
      68,    69,    70,    71,   121,   136,   124,   452,   119,   130,
     120,    16,    55,    54,   459,   460,    87,    34,   463,   464,
      99,   100,   101,   102,    99,   100,   101,   102,   120,   130,
     109,   110,   111,   131,   109,   110,   111,   131,   483,    43,
      67,    87,    95,    95,    57,   490,   130,   492,   125,   125,
     123,   121,   121,    97,   133,   120,    95,   136,    23,   123,
      97,   136,   507,   508,   121,   121,   121,    95,   140,   120,
       3,   516,   517,   518,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,   469,    54,
      55,    56,    57,    58,   222,    60,    21,   142,   290,    64,
      65,    66,    99,   100,   101,   102,   472,    72,    73,    74,
      75,    76,   475,   110,   111,   578,   470,   157,    40,   153,
     151,   383,    26,    27,   148,   324,    30,   552,    93,    94,
      34,    35,   435,   435,   554,   602,   437,   102,   103,   136,
     105,   506,   604,   108,    75,   110,   506,   112,   591,    51,
      52,   129,    54,    55,    56,    57,    58,   122,    60,    -1,
     440,   536,   413,    -1,    26,    27,    -1,   132,    30,    -1,
     135,    -1,    -1,    77,    78,    79,    80,    81,    82,    83,
      84,    85,    86,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    99,   100,   101,   102,    -1,
      -1,    -1,   106,   107,    -1,   109,   110,   111,    -1,    -1,
     114,   115,   116,   117,    -1,    77,    78,    79,    80,    81,
      82,    83,    84,    85,    86,    26,    27,    -1,    -1,    30,
      -1,    -1,   136,    -1,    -1,    -1,    -1,    99,   100,   101,
     102,    -1,    -1,    -1,   106,   107,    -1,   109,   110,   111,
      -1,    -1,   114,   115,   116,   117,    -1,    46,    47,    48,
      49,   123,    51,    52,    -1,    54,    55,    56,    57,    58,
      -1,    60,    -1,    -1,   136,    -1,    77,    78,    79,    80,
      81,    82,    83,    84,    85,    86,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    99,   100,
     101,   102,    -1,    -1,    -1,   106,   107,    -1,   109,   110,
     111,    -1,    -1,   114,   115,   116,   117,    -1,    -1,    -1,
      -1,    -1,    40,    41,    42,    43,    44,    45,    -1,    47,
      48,    49,    50,    51,    52,   136,    54,    55,    56,    57,
      58,    59,    60,    -1,    -1,    -1,    64,    65,    66,    -1,
      -1,    -1,    -1,    -1,    72,    73,    74,    75,    76,    47,
      48,    49,    -1,    51,    52,    -1,    54,    55,    56,    57,
      58,    -1,    60,    -1,    -1,    93,    94,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   102,   103,    -1,   105,    -1,    -1,
     108,    40,   110,    -1,   112,    44,    45,    -1,    -1,    -1,
      -1,    -1,    51,    52,   122,    54,    55,    56,    57,    58,
      59,    60,   130,    -1,   132,    -1,   134,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    93,    94,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   102,    -1,    -1,   105,    -1,    -1,   108,
      -1,   110,    -1,   112,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,   122,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   130,    -1,   132,    -1,   134,    40,    41,    42,    43,
      44,    45,    -1,    47,    48,    49,    50,    51,    52,    -1,
      54,    55,    56,    57,    58,    -1,    60,    -1,    -1,    -1,
      64,    65,    66,    -1,    -1,    -1,    -1,    -1,    72,    73,
      74,    75,    76,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    89,    -1,    -1,    -1,    93,
      94,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   102,   103,
      -1,   105,    -1,    -1,   108,    -1,   110,    -1,   112,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   122,    -1,
      -1,    -1,    40,    41,    42,    43,    44,    45,   132,    47,
      48,    49,    50,    51,    52,    -1,    54,    55,    56,    57,
      58,    -1,    60,    -1,    -1,    -1,    64,    65,    66,    -1,
      -1,    -1,    -1,    -1,    72,    73,    74,    75,    76,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    89,    -1,    -1,    -1,    93,    94,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   102,   103,    -1,   105,    -1,    -1,
     108,    -1,   110,    -1,   112,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   122,    -1,    -1,    -1,    40,    41,
      42,    43,    44,    45,   132,    47,    48,    49,    50,    51,
      52,    -1,    54,    55,    56,    57,    58,    -1,    60,    -1,
      -1,    -1,    64,    65,    66,    -1,    -1,    -1,    -1,    -1,
      72,    73,    74,    75,    76,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    93,    94,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     102,   103,    -1,   105,    -1,    -1,   108,    -1,   110,    -1,
     112,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
     122,    -1,    -1,    -1,    40,    -1,    42,    43,    44,    45,
     132,    47,    48,    49,    -1,    51,    52,    -1,    54,    55,
      56,    57,    58,    -1,    60,    40,    -1,    42,    -1,    44,
      45,    -1,    -1,    48,    -1,    -1,    51,    52,    -1,    54,
      55,    56,    57,    58,    -1,    60,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    93,    94,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   102,   103,    -1,   105,
     106,    -1,   108,    -1,   110,    -1,   112,    -1,    93,    94,
      -1,    -1,    -1,    -1,    -1,    -1,   122,   102,   103,    -1,
     105,    -1,    -1,   108,    40,   110,   132,   112,    44,    45,
      -1,    -1,    -1,    -1,    -1,    51,    52,   122,    54,    55,
      56,    57,    58,    -1,    60,    40,    -1,   132,    -1,    44,
      45,    -1,    -1,    -1,    -1,    -1,    51,    52,    -1,    54,
      55,    56,    57,    58,    -1,    60,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    89,    -1,    -1,    -1,    93,    94,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   102,    -1,    -1,   105,
      -1,    -1,   108,    -1,   110,    -1,   112,    -1,    93,    94,
      -1,    -1,    -1,    -1,    -1,    -1,   122,   102,    -1,    -1,
     105,    -1,    -1,   108,    -1,   110,   132,   112,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   122,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,   132,    77,    78,
      79,    80,    81,    82,    83,    84,    85,    86,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      99,   100,   101,   102,    -1,    -1,    -1,   106,   107,    -1,
     109,   110,   111,    -1,    -1,   114,   115,   116,   117,    -1,
      -1,    -1,    -1,    -1,   123,    77,    78,    79,    80,    81,
      82,    83,    84,    85,    86,    -1,    -1,   136,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    99,   100,   101,
     102,    -1,    -1,    -1,   106,   107,    -1,   109,   110,   111,
      -1,    -1,   114,   115,   116,   117,    -1,    -1,    -1,    -1,
      -1,   123,    77,    78,    79,    80,    81,    82,    83,    84,
      85,    86,    -1,    -1,   136,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    99,   100,   101,   102,    -1,    -1,
      -1,   106,   107,    -1,   109,   110,   111,    -1,    -1,   114,
     115,   116,   117,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   136
  };

  const short
  database_parser::yystos_[] =
  {
       0,     1,   153,   154,   155,   156,     0,   155,     5,   169,
      37,    38,    93,   190,   121,   170,   172,     4,     7,   173,
     175,   176,   180,     5,   121,     6,   180,     8,    12,    13,
      61,    62,    63,   181,   186,   188,   191,   192,   193,   215,
     216,   217,    37,    38,   174,   177,     5,   190,   190,   190,
      37,   222,   223,    37,    90,    91,   224,   225,    37,   218,
     219,    14,    15,   194,   195,   196,   197,    23,    39,    40,
      41,    42,    43,    44,    45,    46,    47,    48,    49,    50,
      51,    52,    54,    55,    56,    57,    58,    60,    64,    65,
      66,    72,    73,    74,    75,    76,    93,    94,   102,   103,
     105,   108,   110,   112,   122,   132,   135,   165,   167,   213,
     215,   230,   231,   246,   247,   248,   249,   250,   251,   254,
     255,   259,   260,   263,   264,   267,   268,   270,   271,   272,
     273,   274,   275,   283,   284,   285,   289,   290,   295,   121,
     217,   121,   178,   171,   190,   121,   121,   121,   120,    37,
      37,   120,   220,   120,    18,   204,   205,   198,   230,   122,
     252,   122,   281,   281,   252,    92,   286,    54,   276,    55,
     278,    97,   269,   271,   271,   271,   271,   271,    52,   122,
     132,   283,   265,   283,   283,   283,    52,    89,   230,   231,
     254,   283,    59,   122,   130,   134,   254,   283,   294,   230,
     230,    19,    23,   119,   120,   124,   157,   158,   159,   162,
     164,    22,    25,    32,    26,    27,    67,    68,    69,    70,
      71,   124,   160,   161,   162,   164,   281,    47,    49,   106,
     122,   262,   263,   280,   283,    26,    27,    30,    77,    78,
      79,    80,    81,    82,    83,    84,    85,    86,    99,   100,
     101,   102,   106,   107,   109,   110,   111,   114,   115,   116,
     117,   136,   124,   163,   164,   281,     6,     9,    10,    11,
     179,   182,   186,   188,   215,   121,   189,   187,   223,   225,
     118,   219,    16,    15,   188,   190,   199,   200,   201,   202,
     203,   204,   253,   254,   282,   283,   130,   277,   279,   254,
     271,   271,   271,   271,    52,    89,   283,   283,   130,    87,
      56,   123,   123,   123,   280,    52,   254,   283,   291,   292,
     134,   120,   134,   269,   269,   230,   230,    46,    47,    48,
      49,    51,   285,   158,    32,    52,   249,   254,   283,   254,
     254,   269,   269,   269,   269,   269,   161,   283,   254,   118,
     260,   283,   283,   249,   283,   283,   283,   283,   283,   283,
     283,   283,   283,   283,   283,   283,   283,   283,   283,   283,
     283,   283,   283,   283,   283,   283,   283,   164,     7,   190,
     190,   190,   214,   215,   226,   227,   228,   229,   231,   254,
     283,   213,   221,    17,   190,   206,   207,   208,   210,   211,
     121,   213,   215,   196,   120,   123,   120,   123,    54,    55,
      57,    58,    60,   287,   288,   120,   120,    87,    56,    57,
     254,   283,    87,   133,   280,   293,    57,    52,    53,   105,
     138,   141,   257,   258,   283,   128,   232,   232,    88,    88,
      88,    88,    88,   254,   283,   254,   254,   254,   254,   254,
     123,   254,    31,   121,   121,   121,   121,   121,   226,    34,
      35,    34,    35,    34,    35,   121,    56,    23,   190,   212,
     118,   121,   119,   120,   130,    16,   254,   283,   131,   288,
      54,    55,   283,    87,   131,   123,   123,   254,   283,   254,
     131,   120,    34,   254,   254,   119,   132,    46,    52,    97,
     233,   234,   235,   236,   237,   238,   130,   239,   239,   230,
     254,   264,    43,   283,   254,   283,   183,   184,   185,   231,
     231,   254,   254,   283,   283,    87,    95,    95,   157,   207,
     208,   210,   209,   210,   206,   283,   266,   281,   281,   166,
     168,   134,   283,    57,   283,   139,   142,   258,   254,    97,
     235,   237,   119,   129,   120,   129,   129,   238,    46,    52,
      95,   240,   241,   242,   243,   244,   245,   230,   230,   125,
     125,   125,   125,   125,   213,   213,   213,   254,   130,   120,
     131,   121,    47,    49,   122,   260,   261,   267,   123,   123,
     133,   132,   256,   258,   256,   134,    97,   234,   236,    95,
     242,   244,   119,   131,   120,   131,   131,   245,   121,   121,
     121,   209,   210,   254,   281,   281,   254,   257,   140,    95,
     241,   243,   131,   123,   134,   134,   256
  };

  const short
  database_parser::yyr1_[] =
  {
       0,   152,   153,   153,   153,   154,   154,   156,   155,   157,
     157,   158,   158,   158,   159,   160,   160,   161,   161,   162,
     162,   162,   163,   163,   164,   165,   166,   165,   165,   167,
     168,   167,   167,   170,   169,   171,   171,   172,   172,   173,
     174,   174,   175,   175,   177,   176,   178,   178,   179,   179,
     179,   180,   180,   181,   181,   181,   181,   183,   182,   182,
     184,   182,   185,   182,   187,   186,   189,   188,   190,   190,
     190,   191,   192,   193,   194,   195,   194,   196,   196,   197,
     198,   198,   199,   200,   200,   201,   200,   200,   200,   202,
     203,   204,   205,   205,   206,   206,   207,   207,   208,   208,
     208,   208,   208,   209,   209,   210,   210,   210,   210,   210,
     210,   211,   212,   211,   213,   213,   214,   214,   215,   216,
     216,   217,   217,   217,   218,   218,   220,   221,   219,   222,
     222,   223,   224,   224,   225,   225,   225,   226,   226,   226,
     227,   227,   228,   228,   229,   229,   230,   230,   231,   231,
     231,   231,   231,   231,   231,   231,   231,   231,   232,   232,
     232,   232,   233,   233,   234,   235,   235,   236,   237,   237,
     238,   238,   239,   239,   239,   239,   240,   240,   241,   242,
     242,   243,   244,   244,   245,   245,   246,   246,   247,   247,
     248,   248,   248,   248,   248,   248,   248,   249,   250,   250,
     250,   250,   250,   251,   251,   252,   253,   253,   254,   254,
     254,   254,   254,   254,   254,   255,   256,   256,   257,   257,
     257,   258,   258,   258,   258,   258,   259,   259,   259,   260,
     260,   260,   261,   261,   261,   261,   261,   262,   262,   263,
     263,   263,   263,   264,   264,   264,   264,   264,   264,   264,
     264,   264,   264,   264,   264,   264,   264,   264,   264,   264,
     265,   266,   264,   267,   268,   268,   269,   269,   270,   270,
     270,   270,   270,   270,   270,   271,   271,   271,   271,   271,
     271,   272,   273,   273,   274,   275,   276,   277,   276,   278,
     279,   278,   280,   280,   281,   282,   282,   283,   283,   283,
     283,   284,   284,   284,   284,   284,   285,   285,   285,   285,
     285,   285,   285,   285,   286,   286,   287,   287,   288,   288,
     288,   288,   288,   289,   289,   289,   289,   289,   289,   289,
     289,   290,   290,   290,   290,   290,   290,   290,   290,   290,
     290,   290,   292,   291,   293,   291,   294,   294,   295,   295
  };

  const signed char
  database_parser::yyr2_[] =
  {
       0,     2,     0,     1,     1,     2,     1,     0,     2,     1,
       2,     1,     1,     1,     5,     1,     2,     1,     1,     5,
       5,     5,     1,     2,     5,     6,     0,     8,     2,     6,
       0,     8,     2,     0,    10,     0,     1,     0,     2,     4,
       1,     1,     1,     2,     0,     7,     0,     2,     1,     1,
       1,     0,     2,     1,     1,     1,     1,     0,     6,     1,
       0,     6,     0,     6,     0,     6,     0,     6,     1,     1,
       1,     2,     2,     3,     1,     0,     2,     3,     1,     1,
       0,     2,     2,     5,     1,     0,     2,     1,     1,     2,
       2,     4,     0,     1,     1,     3,     1,     3,     0,     1,
       4,     3,     6,     1,     3,     1,     1,     2,     3,     2,
       3,     1,     0,     3,     1,     2,     1,     2,     2,     1,
       2,     2,     2,     2,     1,     3,     0,     0,     7,     1,
       3,     1,     1,     3,     1,     2,     2,     1,     1,     1,
       3,     3,     3,     3,     3,     3,     1,     1,     1,     1,
       2,     3,     3,     6,     6,     2,     3,     2,     0,     3,
       3,     3,     1,     3,     2,     1,     3,     2,     1,     2,
       1,     1,     0,     3,     3,     3,     1,     3,     2,     1,
       3,     2,     1,     2,     1,     1,     1,     3,     1,     1,
       3,     3,     3,     4,     4,     5,     5,     1,     1,     3,
       3,     3,     3,     2,     2,     3,     1,     3,     1,     2,
       1,     1,     3,     1,     1,     7,     1,     3,     0,     1,
       3,     1,     1,     3,     6,     4,     1,     1,     3,     2,
       4,     3,     1,     1,     1,     3,     1,     1,     3,     1,
       1,     1,     1,     1,     3,     3,     3,     3,     3,     3,
       3,     3,     3,     3,     3,     3,     3,     3,     3,     3,
       0,     0,     7,     2,     1,     1,     0,     1,     3,     4,
       4,     4,     4,     4,     1,     1,     2,     3,     3,     3,
       3,     1,     1,     1,     2,     2,     1,     0,     4,     1,
       0,     4,     0,     2,     3,     1,     3,     1,     1,     2,
       1,     1,     1,     1,     1,     3,     2,     1,     1,     1,
       1,     1,     1,     1,     0,     4,     1,     2,     1,     1,
       1,     1,     1,     2,     1,     2,     3,     3,     2,     3,
       3,     2,     1,     3,     6,     9,     3,     3,     3,     2,
       2,     2,     0,     2,     0,     4,     1,     3,     1,     1
  };


#if MLIDEBUG || 1
  // YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
  // First, the terminals, then, starting at \a YYNTOKENS, nonterminals.
  const char*
  const database_parser::yytname_[] =
  {
  "\"end of file\"", "error", "\"invalid token\"", "\"token error\"",
  "\"include\"", "\"theory\"", "\"end\"", "\"formal system\"",
  "\"definition\"", "\"postulate\"", "\"axiom\"", "\"rule\"",
  "\"conjecture\"", "\"theorem\"", "\"proof\"", "\"∎\"", "\"by\"",
  "\"premise\"", "\"result\"", "\"⊩\"", "\"or\"", "\"and\"", "\"not\"",
  "\"⊢\"", "\"≡\"", "\"≢\"", "\"≣\"", "\"≣̷\"", "\"fail\"", "\"succeed\"",
  "\"free for\"", "\"in\"", "\"free in\"", "\"use\"", "\"≔\"", "\"≕\"",
  "\"≝\"", "\"name\"", "\"label\"", "\"metapredicate constant\"",
  "\"function\"", "\"predicate\"", "\"predicate constant\"",
  "\"atom constant\"", "\"function constant\"", "\"term constant\"",
  "\"metaformula variable\"", "\"object formula variable\"",
  "\"predicate variable\"", "\"atom variable\"",
  "\"prefix formula variable\"", "\"function variable\"",
  "\"object variable\"", "\"code variable\"", "\"all variable\"",
  "\"exist variable\"", "\"function map variable\"", "\"Set variable\"",
  "\"set variable\"", "\"set variable definition\"",
  "\"implicit set variable\"", "\"identifier constant\"",
  "\"identifier variable\"", "\"identifier function\"", "\"∀\"", "\"∃\"",
  "\"¬\"", "\"∧\"", "\"∨\"", "\"⇒\"", "\"⇐\"", "\"⇔\"", "prefix_not_key",
  "prefix_and_key", "prefix_or_key", "prefix_implies_key",
  "prefix_equivalent_key", "\"<\"", "\">\"", "\"≤\"", "\"≥\"", "\"≮\"",
  "\"≯\"", "\"≰\"", "\"≱\"", "\"=\"", "\"≠\"", "\"↦\"", "\"⤇\"", "\"𝛌\"",
  "\"°\"", "\"•\"", "\"\342\202\223\"", "\"natural number value\"",
  "\"integer value\"", "\"subscript natural number value\"",
  "\"subscript integer value\"", "\"superscript natural number value\"",
  "\"superscript integer value\"", "\"!\"", "\"⋅\"", "\"+\"", "\"-\"",
  "\"Set\"", "\"Pow\"", "\"∅\"", "\"∈\"", "\"∉\"", "\"∁\"", "\"∪\"",
  "\"∩\"", "\"∖\"", "\"⋃\"", "\"⋂\"", "\"⊆\"", "\"⊊\"", "\"⊇\"", "\"⊋\"",
  "\":\"", "\";\"", "\",\"", "\".\"", "\"(\"", "\")\"", "\"[\"", "\"]\"",
  "\"⟨\"", "\"⟩\"", "\"⁽\"", "\"⁾\"", "\"₍\"", "\"₎\"", "\"{\"", "\"|\"",
  "\"}\"", "\"~\"", "\"/\"", "\"\\\\\"", "\"if\"", "\"then\"", "\"else\"",
  "\"while\"", "\"do\"", "\"loop\"", "\"for\"", "\"break\"",
  "\"continue\"", "\"throw\"", "\"try\"", "\"catch\"", "\"⊣\"",
  "unary_minus", "$accept", "file", "file_contents", "command", "$@1",
  "metaformula_substitution_sequence", "substitution_for_metaformula",
  "metaformula_substitution", "formula_substitution_sequence",
  "substitution_for_formula", "formula_substitution",
  "term_substitution_sequence", "term_substitution",
  "predicate_function_application", "$@2", "term_function_application",
  "$@3", "theory", "$@4", "end_theory_name", "include_theories",
  "include_theory", "theory_name", "theory_body", "formal_system", "$@5",
  "formal_system_body", "formal_system_body_item", "theory_body_list",
  "theory_body_item", "postulate", "$@6", "$@7", "$@8", "conjecture",
  "$@9", "definition_labelstatement", "$@10", "statement_name", "theorem",
  "theorem_statement", "theorem_head", "proof", "$@11", "compound-proof",
  "proof_head", "proof_lines", "statement_label", "proof_line", "$@12",
  "subproof", "subproof_statement", "proof_of_conclusion",
  "optional-result", "find_statement", "find_statement_list",
  "find_statement_sequence", "find_definition_sequence",
  "find_statement_item", "find_statement_name", "@13", "statement",
  "definition_statement", "identifier_declaration", "declarator_list",
  "declarator_identifier_list", "identifier_function_list",
  "identifier_function_name", "$@14", "$@15", "identifier_constant_list",
  "identifier_constant_name", "identifier_variable_list",
  "identifier_variable_name", "definition", "metaformula_definition",
  "object_formula_definition", "term_definition", "metaformula",
  "pure_metaformula", "optional_varied_variable_matrix",
  "varied_variable_conclusions", "varied_variable_conclusion",
  "varied_variable_premises", "varied_variable_premise",
  "varied_variable_set", "varied_variable",
  "optional_varied_in_reduction_variable_matrix",
  "varied_in_reduction_variable_conclusions",
  "varied_in_reduction_variable_conclusion",
  "varied_in_reduction_variable_premises",
  "varied_in_reduction_variable_premise",
  "varied_in_reduction_variable_set", "varied_in_reduction_variable",
  "simple_metaformula", "atomic_metaformula", "special_metaformula",
  "meta_object_free", "metapredicate", "metapredicate_function",
  "metapredicate_argument", "metapredicate_argument_body",
  "object_formula", "hoare_triple", "code_statement", "code_sequence",
  "code_term", "very_simple_formula", "quantized_formula",
  "simple_formula", "quantized_body", "atomic_formula", "predicate",
  "$@16", "$@17", "predicate_expression", "predicate_identifier",
  "optional_superscript_natural_number_value", "logic_formula",
  "prefix_logic_formula", "quantizer_declaration",
  "quantized_variable_list", "all_variable_list", "exist_variable_list",
  "all_identifier_list", "$@18", "exist_identifier_list", "$@19",
  "optional_in_term", "tuple", "tuple_body", "term", "simple_term",
  "term_identifier", "variable_exclusion_set", "variable_exclusion_list",
  "bound_variable", "function_term", "set_term",
  "implicit_set_identifier_list", "$@20", "$@21", "set_member_list",
  "function_term_identifier", YY_NULLPTR
  };
#endif


#if MLIDEBUG
  const short
  database_parser::yyrline_[] =
  {
       0,   645,   645,   646,   647,   656,   657,   662,   662,   667,
     668,   675,   676,   677,   682,   691,   692,   699,   700,   705,
     710,   715,   724,   725,   732,   741,   744,   744,   747,   752,
     755,   755,   758,   764,   763,   782,   783,   788,   789,   793,
     805,   806,   811,   812,   818,   817,   825,   826,   831,   832,
     833,   838,   839,   849,   850,   851,   853,   859,   858,   864,
     866,   865,   878,   877,   894,   893,   903,   902,   913,   914,
     915,   920,   931,   942,   952,   953,   953,   967,   972,   977,
     986,   987,   992,  1000,  1032,  1042,  1042,  1046,  1057,  1062,
    1072,  1082,  1093,  1094,  1099,  1100,  1108,  1111,  1119,  1120,
    1122,  1126,  1130,  1139,  1141,  1149,  1152,  1155,  1168,  1182,
    1187,  1197,  1211,  1211,  1253,  1254,  1298,  1299,  1306,  1311,
    1312,  1317,  1318,  1319,  1324,  1325,  1336,  1337,  1336,  1371,
    1372,  1377,  1392,  1393,  1398,  1409,  1420,  1435,  1436,  1437,
    1442,  1445,  1457,  1460,  1472,  1481,  1488,  1489,  1494,  1495,
    1496,  1499,  1502,  1505,  1573,  1634,  1636,  1637,  1643,  1644,
    1645,  1646,  1650,  1651,  1664,  1676,  1677,  1689,  1701,  1702,
    1713,  1718,  1728,  1729,  1730,  1731,  1735,  1736,  1749,  1761,
    1762,  1774,  1786,  1787,  1798,  1803,  1871,  1872,  1877,  1878,
    1890,  1893,  1896,  1899,  1902,  1905,  1909,  1917,  1922,  1923,
    1926,  1929,  1932,  1939,  1943,  1951,  1956,  1960,  1968,  1969,
    1972,  1973,  1974,  1975,  1976,  1981,  1992,  1993,  1998,  1999,
    2000,  2005,  2006,  2007,  2008,  2009,  2014,  2015,  2016,  2021,
    2026,  2031,  2040,  2041,  2042,  2043,  2044,  2050,  2051,  2055,
    2056,  2057,  2058,  2064,  2065,  2066,  2068,  2069,  2070,  2071,
    2072,  2073,  2074,  2075,  2077,  2078,  2079,  2080,  2081,  2082,
    2083,  2084,  2083,  2094,  2102,  2103,  2108,  2109,  2121,  2127,
    2133,  2139,  2145,  2151,  2157,  2162,  2163,  2167,  2171,  2175,
    2179,  2187,  2191,  2192,  2197,  2202,  2207,  2211,  2211,  2221,
    2225,  2225,  2236,  2237,  2244,  2249,  2254,  2263,  2264,  2265,
    2268,  2273,  2274,  2275,  2276,  2277,  2282,  2288,  2289,  2290,
    2291,  2292,  2293,  2294,  2299,  2300,  2305,  2306,  2315,  2316,
    2317,  2318,  2319,  2324,  2327,  2328,  2332,  2336,  2340,  2344,
    2348,  2356,  2357,  2358,  2359,  2363,  2371,  2375,  2379,  2383,
    2387,  2391,  2399,  2399,  2404,  2404,  2414,  2418,  2427,  2428
  };

  void
  database_parser::yy_stack_print_ () const
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
  database_parser::yy_reduce_print_ (int yyrule) const
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

  database_parser::symbol_kind_type
  database_parser::yytranslate_ (int t)
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
     145,   146,   147,   148,   149,   150,   151
    };
    // Last valid token kind.
    const int code_max = 406;

    if (t <= 0)
      return symbol_kind::S_YYEOF;
    else if (t <= code_max)
      return static_cast <symbol_kind_type> (translate_table[t]);
    else
      return symbol_kind::S_YYUNDEF;
  }

#line 22 "../../mli-root/src/database-parser.yy"
} // mli
#line 5006 "../../mli-root/src/database-parser.cc"

#line 2432 "../../mli-root/src/database-parser.yy"


  extern std::istream::pos_type line_position;

namespace mli {

  void database_parser::error(const location_type& loc, const std::string& errstr) {
    diagnostic(loc, errstr, mlilex.in(), line_position);
  }


  void theory_database::read(std::istream& is) {
    mli::database_lexer lex(is, std::cout);

    mli::database_parser p(*this, lex);

    if (p.parse() != 0)
      is.setstate(std::ios::failbit);
    else
      is.clear(is.rdstate() & ~(std::ios::failbit | std::ios::badbit));
  }

} // namespace mli

