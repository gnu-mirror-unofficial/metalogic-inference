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

#pragma once

#include "MLI.hh"
#include "substitution.hh"

#include <list>

namespace mli {

  /* Calculation of proofs:

  The inference-engine maintains an inference-tree with edges an alternative,
  a pair (s, g) where s is a substitution, and g is a goal (formula) that
  must be proved for the completetion of the proof. Each path from the root
  in the inference-tree corresponds to a proof-line. The proof-line is 
  successful if the last edge has an empty (trivially true) goal. The proof
  line is a failure if an end-goal cannot be extended with a new edge. The
  inference-tree can be extended by choosing an arbitrary end-edge, and see
  if the end-goal can, via unification, produce a list of new alternatives,
  which then can be inserted as edges into the inference-tree. Currently,
  a breadth-frist search is used; one point is that if there is a finite proof,
  it will always be found.
  */

} // namespace mli

