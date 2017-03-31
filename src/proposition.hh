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

#ifndef header_proposition_hh
#define header_proposition_hh

#include "MLI.hh"

#include "substitution.hh"
#include "database.hh"


namespace mli {

class supposition : public named_statement {
public:
  enum type { postulate_, conjecture_ };
  type type_;
  
  bool write_postulate_;

  supposition() : type_(postulate_), write_postulate_(false) {}

  clone_declare(supposition);
  copy_declare(supposition);

  supposition(type tp, const std::string& name, const ref<formula>& st, bool wp = false)
   : type_(tp), named_statement(name, st), write_postulate_(wp) {}

  virtual ref<formula> rename(level, sublevel) const;
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  virtual void declared(std::set<ref<variable> >&) const;
    
  // Statement access:
  virtual statement_type get_statement_type() const { return a_proposition; }

  virtual ref<formula> get_statement() const { return statement_; }
  virtual ref<formula> head() const { return statement_->head(); }
  virtual ref<formula> body() const { return statement_->body(); }

  // Proving & solving.
  virtual bool prove() { return (type_ == postulate_); }
  virtual bool is_proved() const { return (type_ == postulate_); }

  virtual void unspecialize(depth d, bool b) { statement_->unspecialize(d, b); }

  // Variable renumbering:
  virtual void set_bind(bind& b, name_variable_table& vs) { statement_->set_bind(b, vs); }

  virtual void write(std::ostream&, write_style) const;
};

inline std::ostream& operator<<(std::ostream& os, const supposition& x) {
  x.write(os, write_default);  return os;
}


class premise : public labelstatement {
public:
  ref<labelstatement> labelstatement_;

  premise() {}

  clone_declare(premise);
  copy_declare(premise);

  premise(const ref<labelstatement>& ls)
   : labelstatement_(ls) {}

  virtual ref<formula> rename(level, sublevel) const;
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  virtual void declared(std::set<ref<variable> >&) const;
    
  virtual std::string name() const { return labelstatement_->name(); }
  virtual statement_type get_statement_type() const { return a_proposition; }

  virtual ref<formula> get_statement() const { return labelstatement_->body(); }
  virtual ref<formula> head() const { return (formula*)0; }
  virtual ref<formula> body() const { return labelstatement_->body(); }

  // Proving & solving.
  virtual bool prove() { return true; }
  virtual bool is_proved() const { return true; }

  virtual void unspecialize(depth d, bool b) { labelstatement_->unspecialize(d, b); }

  // Variable renumbering:
  virtual void set_bind(bind& b, name_variable_table& vs) { labelstatement_->set_bind(b, vs); }

  virtual void write(std::ostream&, write_style) const;
};

inline std::ostream& operator<<(std::ostream& os, const premise& x) {
  x.write(os, write_default);  return os;
}


class proof_line : public named_statement {
public:
  ref<database> database_;  // Database to be used when proving formula_.
  bool is_conclusion_;      // True if formula_ is theorem conclusion, otherwise false.
  depth depth_;             // Proof/(sub)theorem nesting depth.
  std::list<ref<proof> > proofs_;  // Found proofs.

  proof_line() : depth_(0) {}

  clone_declare(proof_line);
  copy_declare(proof_line);

  proof_line(const std::string& name, const ref<formula>& f, const ref<database>& d,
    bool is_conclusion, depth dp)
   : named_statement(name, f), database_(d),
     is_conclusion_(is_conclusion), depth_(dp) {}

  virtual ref<formula> rename(level, sublevel) const;
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  virtual void declared(std::set<ref<variable> >&) const;

  bool is_conclusion() const { return is_conclusion_; }

  // Statement access:
  virtual statement_type get_statement_type() const { return a_proposition; }

  // Proving & solving.
  virtual bool prove();
  virtual bool is_proved() const { return !proofs_.empty(); }

  virtual void unspecialize(depth, bool);

  virtual void write(std::ostream&, write_style) const;
};

inline std::ostream& operator<<(std::ostream& os, const proof_line& x) {
  x.write(os, write_default);  return os;
}


class theorem : public named_statement {
public:
  typedef std::list<ref<labelstatement> > proof_list_type;
  typedef proof_list_type::size_type size_type;
  typedef proof_list_type::iterator iterator;
  typedef proof_list_type::const_iterator const_iterator;

  enum type { lemma_, proposition_, theorem_, corollary_, claim_ };
  type type_;                // Type: theorem, lemma etc.
  ref<database> theory_;     // Theory used, with axioms and proved statements.
  proof_list_type proof_lines_; // Proof.
  bool proved_;        // True if successfully proved; otherwise false.
  depth depth_;        // Proof/(sub)theorem nesting depth.

  theorem() : proved_(false), type_(theorem_), depth_(0) {}

  clone_declare(theorem);
  copy_declare(theorem);

  theorem(type tp, const std::string& name, 
    const ref<formula>& st, const ref<theory>& th, depth dp)
   : type_(tp), named_statement(name, st), theory_(th), depth_(dp) {}

  theorem(type tp, const std::string& name, 
    const ref<formula>& st, const ref<database>& d, depth dp)
   : type_(tp), named_statement(name, st), theory_(d), depth_(dp) {}

  virtual ref<formula> rename(level, sublevel) const;
  virtual ref<formula> substitute(const ref<substitution>&, substitute_environment) const;

  virtual void declared(std::set<ref<variable> >&) const;

  ref<database> get_theory() const { return theory_; }
  
  // Append a proof line with no local variables, which is also the return value:
  ref<labelstatement> push_back(const std::string& name, const ref<formula>& f, const ref<database>& d,
      bool is_conclusion, depth dp) {
    ref<labelstatement> st = new proof_line(name, f, d, is_conclusion, dp);
    proof_lines_.push_back(st);
    return st;
  }
    
  // Append a labelstatement, like a substatement with proof:
  ref<labelstatement> push_back(const ref<labelstatement>& st)  {
    proof_lines_.push_back(st);
    return st;
  }

  virtual statement_type get_statement_type() const { return a_proposition; }

  virtual bool prove();
  virtual bool is_proved() const { return proved_; }

  virtual void unspecialize(depth, bool);

  virtual void write(std::ostream&, write_style) const;
};

inline std::ostream& operator<<(std::ostream& os, const theorem& x) {
  x.write(os, write_default);  return os;
}


class labelstatement_substitution : public labelstatement {
public:
  ref<labelstatement> labelstatement_;
  ref<substitution> substitution_;

  labelstatement_substitution() {}

  clone_declare(labelstatement_substitution);
  copy_declare(labelstatement_substitution);

  labelstatement_substitution(const ref<labelstatement>& p, const ref<substitution>& s)
   : labelstatement_(p), substitution_(s) { labelstatement_->set_bind(); }

  virtual void declared(std::set<ref<variable> >& vs) const { labelstatement_->declared(vs); }

  virtual statement_type get_statement_type() const { return a_proposition; }

  virtual ref<formula> get_statement() const;
  virtual ref<formula> head() const;
  virtual ref<formula> body() const;

  virtual bool prove() { return labelstatement_->prove(); }
  virtual bool is_proved() const { return labelstatement_->is_proved(); }

  virtual void unspecialize(depth d, bool b) { labelstatement_->unspecialize(d, b); }

  // Variable renumbering:
  virtual void set_bind(bind& b, name_variable_table& vs) {
    labelstatement_->set_bind(b, vs); substitution_->set_bind(b, vs); }

  virtual void write(std::ostream&, write_style) const;
};

inline std::ostream& operator<<(std::ostream& os, const labelstatement_substitution& x) {
  x.write(os, write_default);  return os;
}


} // namespace mli


#endif // header_proposition_h

