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


#pragma once


namespace mli {

  // The kleenean type is used for delayed evaluations, created by Hans Γberg and named
  // in honor of S. C. Kleene, as it is the same as in "Introduction to Metamathematics",
  // ch. 12, Β§64, p. 334, where it is called 3-valued logic in the strong sense.
  //
  // The semantics of the kleenean logical operators is the same as of the boolean operators
  // mapped under the sets π β {false}, π¦ β {false, true}, π₯ β {true}, but it is convenient
  // to identify the boolean type with its embedding in the kleenean type via implicit conversions.
  // Thus, π = false, π₯ = true, and in addition, π¦ = undefined, an additional kleenean value.
  //
  // Kleenan conversion to a signed integral type: π β¦ 0, π¦ β¦ -1, π₯ β¦ 1.
  // Signed integral x conversion to kleenean: x = 0 β¦ π, x < 0 β¦ π¦, x > 0 β¦ π₯.
  //
  // C++ limitations make it difficult to fully allow the kleenean type to be implicitly
  // converted to an integral type, as for use in switch statements, while at the same
  // time avoiding implicit conversion to the boolean type, as in if statements. So care
  // must be taken in if statements to make sure there is not an accidental conversion
  // from kleenean to bool.
  // Currently, 'operator int' is implicit, while 'operator bool' is deleted, which seems
  // to provide a reasonable tradeoff.
  //
  // Following a C tradition to not spell out the names properly, the type could have been
  // named 'kleen', but that can easily be added at need in C++ by 'using kleen = kleenean'.

  /* Kleenean truth tables:
    The kleenean type extends the boolean type bool, so it is safe to convert from
    bool to kleenean, but not conversely. The bool values false and true are
    converted to the same kleenean values, called π and π₯. The kleenean type
    also has a value undefined π¦.

    Values: false = π, undefined = π¦, true = π₯; false and true the same as for bool.
    Operators: !x = Β¬x, x || y = x β¨ y, and x && y = x β§ y, same as for bool for
    the false and true values.

      !x = Β¬x
      π | π₯
      π¦ | π¦
      π₯ | π

      x || y = x β¨ y
          π π¦ π₯
      π | π π¦ π₯
      π¦ | π¦ π¦ π₯
      π₯ | π₯ π₯ π₯

      x && y = x β§ y
          π π¦ π₯
      π | π π π
      π¦ | π π¦ π¦
      π₯ | π π¦ π₯
  */

  class kleenean {
    int8_t value_ = 0;

  public:
    constexpr kleenean() {}
    constexpr kleenean(bool b) : value_(b) {}

    explicit constexpr kleenean(int x)
     : value_(x < 0? -1 : (bool)x) {}

    // For use with: switch ((int)x) {case false: β¦ case undefined: β¦ case true: β¦}
    constexpr operator int() { return value_; }
    constexpr operator const int() const { return value_; }

    // To avoid implicit conversion in boolean expressions, as in "if" statements.
    operator bool() = delete;
    operator bool() const = delete;

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
    switch ((int)x) {
      case false: os << "π"; break;
      case undefined: os << "π¦"; break;
      case true: os << "π₯"; break;

      default: os << "ππ¦π₯?"; break;
    }

    return os;
  }

} // namespace mli


