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


namespace mli {

  // The kleenean type is used for delayed evaluations, created by Hans Åberg and named
  // in honor of S. C. Kleene, as it is the same as in "Introduction to Metamathematics",
  // ch. 12, §64, p. 334, where it is called 3-valued logic in the strong sense.
  //
  // The semantics of the kleenean logical operators is the same as of the boolean operators
  // mapped under the sets 𝕗 ≔ {false}, 𝕦 ≔ {false, true}, 𝕥 ≔ {true}, but it is convenient
  // to identify the boolean type with its embedding in the kleenean type via implicit conversions.
  // Thus, 𝕗 = false, 𝕥 = true, and in addition, 𝕦 = undefined, an additional kleenean value.
  //
  // Kleenan conversion to a signed integral type: 𝕗 ↦ 0, 𝕦 ↦ -1, 𝕥 ↦ 1.
  // Signed integral x conversion to kleenean: x = 0 ↦ 𝕗, x < 0 ↦ 𝕦, x > 0 ↦ 𝕥.
  //
  // A C++ limitation makes it impossible to allow the kleenean type to be implicitly
  // converted to an integral type, as for use in switch statements, while at the same
  // time avoiding implicit conversion to the boolean type, as in if statements. So care
  // must be taken in if statements to make sure there is not an accidental conversion
  // from kleenean to bool.
  //
  // Following a C tradition to not spell out the names properly, the type could have been
  // named 'kleen', but that can easily be added at need in C++ by 'using kleen = kleenean'.

  /* Kleenean truth tables:
    The kleenean type extend the boolean type bool, so it is safe to convert from
    bool to kleenean, but not conversely. The bool values false and true are
    converted to the same kleenean values, called 𝕗 and 𝕥. The kleenean type
    also have a value undefined 𝕦.

    Values: false = 𝕗, undefined = 𝕦, true = 𝕥; false and true the same as for bool.
    Operators: !x = ¬x, x || y = x∨y, and x && y = x∧y, same as for bool for
    the false and true values.

      !x = ¬x
      𝕗 | 𝕥
      𝕦 | 𝕦
      𝕥 | 𝕗

      x || y = x∨y
          𝕗 𝕦 𝕥
      𝕗 | 𝕗 𝕦 𝕥
      𝕦 | 𝕦 𝕦 𝕥
      𝕥 | 𝕥 𝕥 𝕥

      x && y = x∧y
          𝕗 𝕦 𝕥
      𝕗 | 𝕗 𝕗 𝕗
      𝕦 | 𝕗 𝕦 𝕦
      𝕥 | 𝕗 𝕦 𝕥
  */

  class kleenean {
    int8_t value_ = 0;

  public:
    constexpr kleenean() {}
    constexpr kleenean(bool b) : value_(b) {}

    explicit constexpr kleenean(int x)
     : value_(x < 0? -1 : (bool)x) {}

    constexpr operator int8_t() { return value_; }
    constexpr operator const int8_t() const { return value_; }

    friend constexpr kleenean operator!(kleenean);

    // Variations with bool added to admit implicit conversions:

    friend constexpr kleenean operator||(kleenean, kleenean);
    friend constexpr kleenean operator||(kleenean, bool);
    friend constexpr kleenean operator||(bool, kleenean);

    friend constexpr kleenean operator&&(kleenean, kleenean);
    friend constexpr kleenean operator&&(kleenean, bool);
    friend constexpr kleenean operator&&(bool, kleenean);

    friend constexpr bool operator==(kleenean, kleenean);
    friend constexpr bool operator==(kleenean, bool);
    friend constexpr bool operator==(bool, kleenean);

    friend constexpr bool operator!=(kleenean, kleenean);
    friend constexpr bool operator!=(kleenean, bool);
    friend constexpr bool operator!=(bool, kleenean);

    friend std::ostream& operator<<(std::ostream&, kleenean);
  };


  constexpr kleenean undefined(-1);


  constexpr kleenean operator!(kleenean x) {
    if (x == undefined)
      return undefined;
    return !x.value_;
  }


  constexpr kleenean operator||(kleenean x, kleenean y) {
    if (x.value_ == true || y.value_ == true)  return true;
    if (x.value_ == false && y.value_ == false)  return false;
    return undefined;
  }

  constexpr kleenean operator||(kleenean x, bool y) { return x || (kleenean)y; }
  constexpr kleenean operator||(bool x, kleenean y) { return (kleenean)x || y; }


  constexpr kleenean operator&&(kleenean x, kleenean y) {
    if (x.value_ == false || y.value_ == false)  return false;
    if (x.value_ == true && y.value_ == true)  return true;
    return undefined;
  }

  constexpr kleenean operator&&(kleenean x, bool y) { return x && (kleenean)y; }
  constexpr kleenean operator&&(bool x, kleenean y) { return (kleenean)x && y; }


  constexpr bool operator==(kleenean x, kleenean y) { return (x.value_ == y.value_); }

  constexpr bool operator==(kleenean x, bool y) { return (x == (kleenean)y); }
  constexpr bool operator==(bool x, kleenean y) { return ((kleenean)x == y); }


  constexpr bool operator!=(kleenean x, kleenean y) { return (x.value_ != y.value_); }

  constexpr bool operator!=(kleenean x, bool y) { return (x != (kleenean)y); }
  constexpr bool operator!=(bool x, kleenean y) { return ((kleenean)x != y); }


  inline std::ostream& operator<<(std::ostream& os, kleenean x) {
    switch (x) {
      case false: os << "𝕗"; break;
      case undefined: os << "𝕦"; break;
      case true: os << "𝕥"; break;

      default: os << "𝕗𝕦𝕥?"; break;
    }

    return os;
  }

} // namespace mli


