/* Copyright (C) 2021 Magnus Lång
 *
 * This file is part of Nidhugg.
 *
 * Nidhugg is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Nidhugg is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see
 * <http://www.gnu.org/licenses/>.
 */

#include <config.h>
#ifndef __GEN_SET_H__
#define __GEN_SET_H__

#include "GenHash.h"
#include "GenMap.h"

#ifndef NDEBUG
/* For reference-count */
#  include <atomic>
#  include <memory>
#endif
#include <utility>
#include <cstdint>

namespace gen {
  namespace impl {
    struct empty{};
  }

  template<typename T, typename Hash = hash<T>, class KeyEqual = std::equal_to<T>>
  class set : private map<T, impl::empty, Hash, KeyEqual, std::tuple<const T, impl::empty>> {
    typedef T elem_type;
    typedef map<T, impl::empty, Hash, KeyEqual, std::tuple<const T, impl::empty>>
      map;
    typedef typename map::size_type size_type;
    typedef typename map::fast_size_type fast_size_type;

  public:
    // /* Empty */
    // set(){};
    // /* Copy-on-write duplicate another set. It must not be modified after this. */
    // explicit set(const set &other) : map(other) {}
    // /* Steal another set. It will be empty after this. It is allowed to steal
    //  * a set that has COW references, but then the new set may not be
    //  * modified. */
    // set(set &&other) : map(other) {}
    // ~set(){}
    // /* Copy-on-write duplicate another set. It must not be modified after this. */
    // set &operator=(const set &other) { ((map&)*this) = other; return *this; }
    // /* Steal another set. Its contents will be swapped with this one. It
    //  * is allowed to steal a set that has COW references, but then *this
    //  * may not be modified further. */
    // map &operator=(map &&other) { ((map&)*this) = other; return *this; }

    /* Swap contents and ownership with another set */
    void swap(set &other) { ((map&)*this).swap(other); };

    size_type size() const noexcept { return ((map&)*this).size(); }
    /* It would be nice to return bool, but we need to refactor map to do that. */
    void insert(const T &k) { ((map&)*this).mut(k); }
    bool contains(const T &k) const { return ((map&)*this).find(k) != nullptr; }
    fast_size_type count(const T &k) const { return contains(k); }

    template<class Fn> void for_each(Fn &&f) const;
  };

  template<typename T, typename Hash, class KeyEqual>
  inline void swap(set<T,Hash,KeyEqual> &a, set<T,Hash,KeyEqual> &b) {
    a.swap(b);
  }

  template<typename T, typename Hash, class KeyEqual, class Fn>
  inline void for_each(const set<T,Hash,KeyEqual> &v, Fn&& f) {
    return v.for_each(std::forward<Fn>(f));
  }
}

/* Start implementation */

#include <cassert>

namespace gen {

  template<typename T, typename Hash, class KeyEqual>
  template<typename Fn>
  void set<T,Hash,KeyEqual>::for_each(Fn &&f) const {
    ((map&)*this).for_each([f](const std::tuple<const T, impl::empty> &t) {
      f(std::get<0>(t));
    });
  }

}

#endif
