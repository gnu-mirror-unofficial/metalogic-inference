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

#include <stdexcept>

#include "gc.hh"


  // The Boehm GC must be initialized on some platforms using GC_INIT. But
  // because global C++ objects may be initialized before 'main' starts running,
  // GC_INIT is here called in the first call to 'operator new' or 'operator new[]'.

  // Note that the GC_MALLOC macro does not admit being treated as a function pointer.
  // So for GC debugging, replace it with the appropriate function pointer.


// The functions gc_uninitialized and gc_uninitialized_uncollectable make sure
// That GC_INIT is called on the first allocation, making sure it occurs before
// C++ global object allocations.

typedef void* (*malloc_ptr)(size_t);

extern malloc_ptr gc_c;
extern malloc_ptr gc_u;

void* gc_uninitialized(size_t n) {
  gc_c = &GC_malloc; // Or GC_MALLOC
  gc_u = &GC_malloc_uncollectable; // Or GC_MALLOC_UNCOLLECTABLE
  GC_INIT();
  GC_allow_register_threads();
  return gc_c(n);
}

void* gc_uninitialized_uncollectable(size_t n) {
  gc_u = &GC_malloc_uncollectable; // Or GC_MALLOC_UNCOLLECTABLE
  gc_c = &GC_malloc; // Or GC_MALLOC
  GC_INIT();
  GC_allow_register_threads();
  return gc_u(n);
}


malloc_ptr gc_c = gc_uninitialized;
malloc_ptr gc_u = gc_uninitialized_uncollectable;


void* operator new(std::size_t n, collect_t) {
  void* p = gc_c(n);
  if (p == nullptr)  throw std::bad_alloc();
  return p;
}

void operator delete(void* p, collect_t) noexcept {}


void* operator new(std::size_t n) {
  void* p = gc_u(n); // Or GC_MALLOC_UNCOLLECTABLE
  if (p == nullptr)  throw std::bad_alloc();
  return p;
}

void operator delete(void* p) noexcept { GC_free(p); } // Or GC_FREE


void* operator new[](std::size_t n) {
  void* p = gc_u(n); // Or GC_MALLOC_UNCOLLECTABLE
  if (p == nullptr)  throw std::bad_alloc();
  return p;
}

void operator delete[](void* p) noexcept { GC_free(p); } // Or GC_FREE
