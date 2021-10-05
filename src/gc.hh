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

#include <new>

#include <thread>
#define GC_THREADS
#include <gc/gc.h>


// GC uncollectible allocations; to avoid memory leaks,
// explicitly deallocate using operator delete.
void* operator new(std::size_t n);
void operator delete(void*) noexcept;
void* operator new[](std::size_t n);
void operator delete[](void*) noexcept;


// Placeholder value, to select GC collectible operator new.
struct collect_t {};
constexpr collect_t collect{};


// GC collectible allocations; deallocated, if found, during GC time.
// If finalized using finalize<A>, the destructor ~A will also be called.
void* operator new(std::size_t n, collect_t);

// Cannot be explicitly called: only invoked if an exception is thrown in operator new:
void operator delete(void* p, collect_t) noexcept;


namespace mli {

  // Register a finalizer cleanup function that calls the destructor A::~A().
  // Return is the argument, so that the function can be chained with operator new:
  //   return finalize(new A(...));
  //
  // Note: Function GC_register_finalizer_ignore_self causes warnings of the form:
  //   GC Warning: Finalization cycle involving 0x<address>
  // Therefore, GC_register_finalizer_no_order is used.
  template<class A>
  inline A* finalize(A* ap) {
    GC_finalization_proc f0;  // Already registered finalization function.
    void* dp0;                // Already registered finalization data.

    void* base = GC_base((void*)ap);                // Base of allocated object.
    void* diff = (void*)((char*)ap - (char*)base);  // Object displacement.

    // Finalization cleanup function.
    //   xp = pointer to allocated object
    //   d = displacement to A* pointer.
    GC_finalization_proc f1 = [](void* xp, void* d) {
      A* bp = ((A*)((char*)xp + (ptrdiff_t)d));
      ((A*)((char*)xp + (ptrdiff_t)d))->~A();
      GC_register_finalizer_no_order(GC_base(xp), 0, 0, 0, 0);
    };

    if (0 != base)  {
      GC_register_finalizer_no_order(base, f1, diff, &f0, &dp0);

      if (0 != f0)
        GC_register_finalizer_no_order(base, f0, dp0, 0, 0  );
    }

    return ap;
  }

} // namespace mli



