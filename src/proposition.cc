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

#include "proposition.hh"

// #include "database.hh"
// #include "substitution.hh"
#include "definition.hh"

namespace mli {


class spaces {
  int margin_, tab_;
public:
  spaces(int margin, int tab) : margin_(margin), tab_(tab) {}
  friend std::ostream& operator<<(std::ostream&, const spaces&);
};

std::ostream& operator<<(std::ostream& os, const spaces& sp) {
  for (int j = 0; j < sp.margin_ * sp.tab_; ++j)  os << ' ';
  return os;
}

template<class Vs> // A class whose iterators dereference to class variable.
void write_variable_declaration(const Vs& vs, std::ostream& os) {
  if (!vs.empty()) {
    typename Vs::const_iterator i, i0 = vs.begin(), i1 = vs.end();
    variable::type vt0 = variable::none_, vt1;
    for (i = i0; i != i1; ++i) {
      vt1 = (*i)->type_;
      if (vt0 != vt1) {
        if (vt0 != variable::none_)  os << " ";
        os << variable::type_name(vt1) << " ";
      }
      else if (i != i0)  os << ", ";
      vt0 = vt1;
      os << *i;
    }
    os << ".";
  }
}


void named_definition::declared(std::set<ref<variable> >& vs) const {
  statement_->contains(vs, declared_occurrence);
}

void named_definition::write(std::ostream& os, write_style ws) const {
  bool show_type = ws & write_type;
  bool show_name = ws & write_name;
  bool show_statement = ws & write_statement;
  bool show_proof = ws & write_proof;
  int proof_margin = (ws & write_proof_margin_level); // Value with indent.
  if (!(ws & write_proof_indent) && proof_margin > 0)  --proof_margin;
  int proof_tab = (ws & write_proof_margin_tab) >> 4;
  os << spaces(proof_margin, proof_tab);
  if (show_type)
    os << "definition";
  if (show_type && show_name)
    os << " ";
  if (show_name) 
    os << name_;
  if ((show_type || show_name) && show_statement)
    os << ". ";
  if (show_statement) {
    std::set<ref<variable> > vs;
    declared(vs);
    write_variable_declaration(vs, os);
    os << "\n";
    os << spaces(proof_margin+1, proof_tab);
    statement_->write(os, ws);
    os << ".";
  }
}


clone_source(supposition)
copy_source(supposition)

ref<formula> supposition::rename(level lv, sublevel sl) const {
  supposition* rp = new supposition(*this);
  ref<formula> rt(rp);
  rp->statement_ = statement_->rename(lv, sl);
  return rt;
}

ref<formula> supposition::substitute(const ref<substitution>& s, substitute_environment vt) const {
  supposition* rp = new supposition(*this);
  ref<formula> rt(rp);
  rp->statement_ = statement_->substitute(s, vt);
  return rt;
}

void supposition::declared(std::set<ref<variable> >& vs) const {
  statement_->contains(vs, declared_occurrence);
}

void supposition::write(std::ostream& os, write_style ws) const {
  bool show_type = ws & write_type;
  bool show_name = ws & write_name;
  bool show_statement = ws & write_statement;
  bool show_proof = ws & write_proof;
  if (show_type)
    switch (type_) {
      case postulate_: {
        if (write_postulate_) { os << "postulate"; break; }
        const sequence* sp = cast_pointer<sequence>(statement_->body());
        if (sp == 0 || sp->formulas_.size() == 0)
           os << "axiom";
        else
           os << "rule";
        break;
	  }
      case conjecture_:  os << "conjecture"; break;
    }
  if (show_type && show_name)
    os << " ";
  if (show_name)
    os << name_;
  if ((show_type || show_name) && show_statement)
    os << ". ";
  if (show_statement) {
    std::set<ref<variable> > vs;
    declared(vs);
    write_variable_declaration(vs, os);
    os << "\n  ";
    statement_->write(os, ws);
    os << ".";
  }
}


clone_source(premise)
copy_source(premise)

ref<formula> premise::rename(level lv, sublevel sl) const {
  premise* rp = new premise(*this);
  ref<formula> rt(rp);
  rp->labelstatement_ = ref<labelstatement>(labelstatement_->rename(lv, sl));
  return rt;
}

ref<formula> premise::substitute(const ref<substitution>& s, substitute_environment vt) const {
  premise* rp = new premise(*this);
  ref<formula> rt(rp);
  rp->labelstatement_ = ref<labelstatement>(labelstatement_->substitute(s, vt));
  return rt;
}

void premise::declared(std::set<ref<variable> >& vs) const {
  labelstatement_->body()->contains(vs, declared_occurrence);
}

void premise::write(std::ostream& os, write_style ws) const {
  bool show_type = ws & write_type;
  bool show_name = ws & write_name;
  bool show_statement = ws & write_statement;
  bool show_proof = ws & write_proof;
  // Even though "premise" is the type, it will always be needed in writeouts, whereas
  // the name of the labelstatement which it belongs is normally not needed.
  // So always write "premise", and add name if both type and name is requested:
  os << "premise";
  if (show_type && show_name)
    os << " " << labelstatement_->name();
  if ((show_type || show_name) && show_statement)
    os << ". ";
  if (show_statement) {
    std::set<ref<variable> > vs;
    declared(vs);
    write_variable_declaration(vs, os);
    os << "\n  ";
    labelstatement_->body()->write(os, ws);
    os << ".";
  }
}


clone_source(proof_line)
copy_source(proof_line)

ref<formula> proof_line::rename(level lv, sublevel sl) const {
  proof_line* rp = new proof_line(*this);
  ref<formula> rt(rp);
  rp->statement_ = statement_->rename(lv, sl);
  return rt;
}

ref<formula> proof_line::substitute(const ref<substitution>& s, substitute_environment vt) const {
  proof_line* rp = new proof_line(*this);
  ref<formula> rt(rp);
  rp->statement_ = statement_->substitute(s, vt);
  return rt;
}

void proof_line::declared(std::set<ref<variable> >& vs) const {
  std::set<ref<variable> > vs0;
  statement_->contains(vs0, declared_occurrence);
  std::set<ref<variable> >::iterator i;
  for (i = vs0.begin(); i != vs0.end(); ++i) {
    const variable* vp = (const variable*)(*i);
    if (vp == 0)  continue;
    if (vp->depth_ == depth_)
      vs.insert(*i);
  }
}

bool proof_line::prove() {
  if (trace_value & (trace_result | trace_proof)) {
    std::clog << "Proving ";
    write(std::clog, write_style(write_name | write_statement));
    std::clog << std::flush;
    std::clog << "\n" << std::flush;
  }
  // Make proofline statement variables unspecializable in course of proof:
  // The depth of these variables is one higher than that of the theorem
  // statement variables.
  unspecialize(depth_, true);
  proofs_ = database_->prove(statement_, 1);
  unspecialize(depth_, false);
  if (trace_value & (trace_result | trace_proof)) {
    std::set<ref<variable> > vs;
    statement_->contains(vs, any_occurrence); // Find variables:
    show_solution(std::clog, write_default, vs);
    std::clog << "\n" << std::flush;
    show_solution(std::clog, proofs_);
    std::clog << std::endl;
#if 0
    // Not needed to show the variables that gets new values by the substitutions, as
    // all variables will be unspecializable, in effect fixed. It might be the case
    // though that some bound variables will get unspecialized new values.
    show_solution(std::clog, write_default, vs, proofs_);
#endif
  }
  return is_proved();
}

void proof_line::unspecialize(depth x, bool y) {
  statement_->unspecialize(x, y);
}

void proof_line::write(std::ostream& os, write_style ws) const {
  bool show_type = ws & write_type;
  bool show_name = ws & write_name;
  bool show_statement = ws & write_statement;
  bool show_unproved = ws & write_unproved;
  bool show_proof = ws & write_proof;
  int proof_margin = (ws & write_proof_margin_level); // Value with indent.
  if (!(ws & write_proof_indent) && proof_margin > 0)  --proof_margin;
  int proof_tab = (ws & write_proof_margin_tab) >> 4;
  // If proof line is conclusion and displays its conclusion,
  // only show its name if != "conclusion":
  if (is_conclusion_ && show_statement && name_ == "conclusion")
    show_name = false;
  os << spaces(proof_margin, proof_tab);
  if (show_name)
    os << name_;
  if (show_unproved && !is_proved()) {
    if (show_name && show_statement)
      os << " ";
    if (show_statement) {
      os << "[*unproved*]";
      if (!show_name)  os << " "; // Because no "." will be output.
    }
  }
  if (show_name && show_statement)
    os << ". ";
  if (show_statement) {
    if (is_conclusion_)
      os << "conclusion";
    else {
      std::set<ref<variable> > vs;
      declared(vs);
      write_variable_declaration(vs, os);
      os << " " << statement_;
    }
    if (show_proof && !database_->empty()) {
      os << " by ";
      database_->write(os, write_style(write_name | write_type));
    }
    os << ".";
  }
}


clone_source(theorem)
copy_source(theorem)

ref<formula> theorem::rename(level lv, sublevel sl) const {
  theorem* rp = new theorem(*this);
  ref<formula> rt(rp);
  rp->statement_ = statement_->rename(lv, sl);
  return rt;
}

ref<formula> theorem::substitute(const ref<substitution>& s, substitute_environment vt) const {
  theorem* rp = new theorem(*this);
  ref<formula> rt(rp);
  rp->statement_ = statement_->substitute(s, vt);
  return rt;
}

void theorem::declared(std::set<ref<variable> >& vs) const {
  std::set<ref<variable> > vs0;
  statement_->contains(vs0, declared_occurrence);
  std::set<ref<variable> >::iterator i;
  for (i = vs0.begin(); i != vs0.end(); ++i) {
    const variable* vp = (const variable*)(*i);
    if (vp == 0)  continue;
    if (vp->depth_ == depth_)
      vs.insert(*i);
  }
}

// The theorem is proved if it has a successful, non-empty proof,
// where the last proved formula is the one of the theorem conclusion.
// This assumes that each line of the proof is proved by axioms,
// premises of the theorem conclusion, and earlier proved formulas
// of the proof.
bool theorem::prove() {
  if (trace_value & (trace_result | trace_proof)) {
    std::clog << "\nProving ";
    write(std::clog, write_style(write_name | write_type | write_statement));
    std::clog << "\n" << std::flush;
  }
  proved_ = false;
  bool successful_so_far = true;
  iterator i, i0 = proof_lines_.begin(), i1 = proof_lines_.end();
  // Make theorem statement variables unspecializable in course of proof:
  unspecialize(depth_, true);
  for (i = i0; i != i1; ++i)
    if (!(*i)->prove())  successful_so_far = false;
  unspecialize(depth_, false);
  if (!proof_lines_.empty() && successful_so_far) {
    proof_line* plp = cast_pointer<proof_line>(proof_lines_.back());
    if (plp != 0 && plp->is_conclusion())
      proved_ = true;
  }
  return proved_;
}

void theorem::unspecialize(depth x, bool y) {
  statement_->unspecialize(x, y);  
  iterator i, i0 = proof_lines_.begin(), i1 = proof_lines_.end();
  for (i = i0; i != i1; ++i) {
    (*i)->unspecialize(x, y);
  }  
}

void theorem::write(std::ostream& os, write_style ws) const {
  bool show_type = ws & write_type;
  bool show_name = ws & write_name;
  bool show_statement = ws & write_statement;
  bool show_unproved = ws & write_unproved;
  bool show_proof = ws & write_proof;
  bool show_proof_begin_newline = ws & write_proof_begin_newline;
  bool show_oneline_proof_begin_no_newline = ws & write_oneline_proof_begin_no_newline;
  bool show_proof_end_newline = ws & write_proof_end_newline;
  bool show_oneline_proof_end_no_newline = ws & write_oneline_proof_end_no_newline;
  int proof_margin = (ws & write_proof_margin_level);
  int proof_tab = (ws & write_proof_margin_tab) >> 4;
  int new_proof_margin = (proof_margin < 15)? proof_margin + 1 : proof_margin;
  write_style new_ws = write_style(new_proof_margin | (ws & ~write_proof_margin_level));
  os << spaces(proof_margin, proof_tab);
  if (show_type) 
    switch (type_) {
      case lemma_:       os << "lemma"; break;
      case proposition_: os << "proposition"; break;
      case theorem_:     os << "theorem"; break;
      case corollary_:   os << "corollary"; break;
      case claim_:       os << "claim"; break;
    };
  if (show_type && show_name)
    os << " ";
  if (show_name)
    os << name_;
  if (show_unproved && !is_proved()) {
    if ((show_type || show_name) && show_statement)
      os << " ";
    if (show_statement)
      os << "[*unproved*]";
  }
  if ((show_type || write_name) && show_statement)
    os << ". ";
  if (show_statement) {
    std::set<ref<variable> > vs;
    declared(vs);
    write_variable_declaration(vs, os);
    os << "\n  ";
    statement_->write(os, ws);
    os << ".";
  }
  if (show_statement && show_proof)
    os << "\n";
  if (show_proof) {
    os << spaces(proof_margin, proof_tab) << "proof.";
    if ((show_oneline_proof_begin_no_newline && proof_lines_.size() <= 1)
        || !show_proof_begin_newline)
      os << " ";
    else
      os << "\n";
    const_iterator i, i0 = proof_lines_.begin(), i1 = proof_lines_.end();
    for (i = i0; i != i1; ++i) {
      if (i != i0)  os << "\n";
      (*i)->write(os, new_ws);
    }
    if (!proof_lines_.empty()) {
      if (!cast_reference<proof_line>(proof_lines_.back()).is_conclusion()) {
        os << spaces(proof_margin, proof_tab);
        os << "\n[*Last formula of proof is not theorem conclusion.*]";
      }
      else if (!proved_ && cast_reference<proof_line>(proof_lines_.back()).is_proved()) {
        os << spaces(proof_margin, proof_tab);
        os << "\n[*Statement is proved, but some proof lines are unproved.*]";
      }
    }
    if (show_oneline_proof_end_no_newline && proof_lines_.size() <= 1) {
      if (proof_lines_.size() == 1)  os << " ";
      // If no proof lines: a space has already been outout after "proof."
    }
    else if (!show_proof_end_newline)
      os << " ";
    else
      os << "\n" << spaces(proof_margin, proof_tab);
    os << "∎";
  }
}


clone_source(labelstatement_substitution)
copy_source(labelstatement_substitution)

ref<formula> labelstatement_substitution::get_statement() const {
#if 1
  return labelstatement_->get_statement();
#else
  return labelstatement_.get_statement().substitute(substitution_);
#endif
}

ref<formula> labelstatement_substitution::head() const {
#if 1
  return labelstatement_->head();
#else
  return labelstatement_.head().substitute(substitution_);
#endif
}

ref<formula> labelstatement_substitution::body() const {
#if 1
  return labelstatement_->body();
#else
  return labelstatement_->body()->substitute(substitution_);
#endif
}

void labelstatement_substitution::write(std::ostream& os, write_style ws) const {
#if 1
  write_style show_type_name = write_style(ws & (write_name | write_type));
  bool show_statement = ws & write_statement;
  if (show_type_name) {
    labelstatement_->write(os, write_style(write_name | write_type));
    substitution_->write(os, ws);
  }
  if (show_type_name && show_statement)
    os << ". ";
  if (show_statement)
    labelstatement_->write(os, ws);
  if (show_type_name && show_statement)
    os << ".";
#else
  labelstatement_.write(os, ws);
  substitution_.write(os, ws);
#endif
}


} // namespace mli

