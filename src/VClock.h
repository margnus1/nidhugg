/* Copyright (C) 2014-2017 Carl Leonardsson
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

#ifndef __VCLOCK_H__
#define __VCLOCK_H__

#include "IID.h"

#include <map>
#include <ostream>
#include <string>
#include <vector>

#include <llvm/Support/raw_ostream.h>

/* A VClock<DOM> is a vector clock - a function from some domain DOM
 * to natural numbers.
 */
template<typename DOM>
class VClock {
public:
  /* Create a vector clock where each clock is initialized to 0. */
  VClock();
  /* Create a vector clock where each d among the keys of m is
   * initialized to m[d], and all other clocks are initialized to
   * 0. */
  VClock(const std::map<DOM,int> &m);
  /* Create a vector clock which is a copy of vc. */
  VClock(const VClock<DOM> &vc);
  /* Create a vector clock that is a translation of vc, where the
   * clock of t[i] is initialized to vc[i]. The clocks of all d which
   * do not occur in t are initialized to 0.
   */
  VClock(const VClock<int> &vc, const std::vector<DOM> &t);
  /* Create a vector clock where for each pair (d,i) in il, the clock
   * of d is initialized to i. All other clocks are initialized to
   * 0. */
  VClock(const std::initializer_list<std::pair<DOM,int> > &il);
  virtual ~VClock();
  VClock &operator=(const VClock<DOM> &vc);
  /* A vector clock v such that the clock of d in v takes the value
   * max((*this)[d],vc[d]) for all d.
   */
  VClock operator+(const VClock<DOM> &vc) const;
  /* Assign this vector clock to (*this + vc). */
  VClock &operator+=(const VClock<DOM> &vc);
  /* The value of the clock of d. */
  int operator[](const DOM &d) const;
  int &operator[](const DOM &d);

  /* Returns the number of processes with non-zero clocks. */
  int get_nonzero_count() const;

  bool includes(const IID<DOM> &iid) const {
    return iid.get_index() <= (*this)[iid.get_pid()];
  };

  /* *** Partial order comparisons ***
   *
   * A vector clock u is considered strictly less than a vector clock
   * v iff for all d in DOM, it holds that u[d] <= v[d], and there is
   * at least one d such that u[d] < v[d].
   */
  bool lt(const VClock<DOM> &vc) const;
  bool leq(const VClock<DOM> &vc) const;
  bool gt(const VClock<DOM> &vc) const;
  bool geq(const VClock<DOM> &vc) const;

  /* *** Total order comparisons *** */
  bool operator==(const VClock<DOM> &vc) const;
  bool operator!=(const VClock<DOM> &vc) const;
  bool operator<(const VClock<DOM> &vc) const;
  bool operator<=(const VClock<DOM> &vc) const;
  bool operator>(const VClock<DOM> &vc) const;
  bool operator>=(const VClock<DOM> &vc) const;

  std::string to_string() const;
private:
  std::map<DOM,int> clocks;
};

class VClockRef final {
  friend class VClockVec;
  friend class VClock<int>;
  VClockRef(int* base, unsigned size) : base(base), _size(size) {}
  int* base;
  unsigned _size;
public:
  VClockRef &operator=(const VClock<int> vc);
  /* Assign this vector clock to (*this - vc). */
  VClockRef &operator-=(const VClockRef vc);
  unsigned size() const { return _size; }
  int operator[](int d) const { assert(d >= 0 && unsigned(d) < _size); return base[d]; };
  int &operator[](int d) { assert(d >= 0 && unsigned(d) < _size); return base[d]; };

  bool includes(const IID<int> &iid) const {
    return iid.get_index() <= (*this)[iid.get_pid()];
  };

  bool reverse_includes(const IID<int> &iid) const {
    return iid.get_index() >= (*this)[iid.get_pid()];
  };

  /* *** Partial order comparisons ***
   *
   * A vector clock u is considered strictly less than a vector clock
   * v iff for all d in DOM, it holds that u[d] <= v[d], and there is
   * at least one d such that u[d] < v[d].
   */
  bool lt(const VClockRef vc) const;
};

template<>
class VClock<int> final {
public:
  /* Create a vector clock where each clock is initialized to 0. */
  VClock();
  /* Create a vector clock where each d among the keys of m is
   * initialized to m[d], and all other clocks are initialized to
   * 0. */
  VClock(const std::map<int,int> &m);
  /* Create a vector clock where each d s.t. 0 <= d < m.size() is
   * initialized to m[d], and all other clocks are initialized to
   * 0. */
  VClock(const std::vector<int> &m);
  VClock(std::vector<int> &&m);
  /* Create a vector clock which is a copy of vc. */
  VClock(const VClock<int> &vc);
  VClock(VClock<int> &&vc);
  VClock(VClockRef ref);
  /* Create a vector clock that is a translation of vc, where the
   * clock of t[i] is initialized to vc[i]. The clocks of all d which
   * do not occur in t are initialized to 0.
   */
  VClock(const VClock<int> &vc, const std::vector<int> &t);
  /* Create a vector clock where for each pair (d,i) in il, the clock
   * of d is initialized to i. All other clocks are initialized to
   * 0. */
  VClock(const std::initializer_list<std::pair<int,int> > &il);
  /* Create a vector clock where the i:th clock is initialized to the
   * i:th element in il if there are more than i elements in il, or
   * initialized to 0 otherwise. */
  VClock(const std::initializer_list<int> &il);
  virtual ~VClock();
  VClock &operator=(const VClock<int> &vc);
  VClock &operator=(VClock<int> &&vc);
  /* A vector clock v such that the clock of d in v takes the value
   * max((*this)[d],vc[d]) for all d.
   */
  VClock operator+(const VClock<int> &vc) const;
  /* Assign this vector clock to (*this + vc). */
  VClock &operator+=(const VClock<int> &vc);
  /* A vector clock v such that the clock of d in v takes the value
   * min((*this)[d],vc[d]) for all d.
   */
  VClock operator-(const VClock<int> &vc) const;
  /* Assign this vector clock to (*this - vc). */
  VClock &operator-=(const VClock<int> &vc);
  /* The value of the clock of d. */
  int operator[](int d) const;
  int &operator[](int d);

  /* Returns the number of processes with non-zero clocks. */
  int get_nonzero_count() const;

  /* Returns the length of the shortest prefix that includes the last
   * nonzero element.
   */
  std::size_t size() const;
  std::size_t size_ub() const { return vec.size(); }

  bool includes(const IID<int> &iid) const {
    return iid.get_index() <= (*this)[iid.get_pid()];
  };

  bool reverse_includes(const IID<int> &iid) const {
    return iid.get_index() >= (*this)[iid.get_pid()];
  };

  /* *** Partial order comparisons ***
   *
   * A vector clock u is considered strictly less than a vector clock
   * v iff for all d, it holds that u[d] <= v[d], and there is at
   * least one d such that u[d] < v[d].
   */
  bool lt(const VClock<int> &vc) const;
  bool leq(const VClock<int> &vc) const;
  bool gt(const VClock<int> &vc) const;
  bool geq(const VClock<int> &vc) const;
  /* A vector clock u intersects a (below) clock v if there is at least
   * one d within the domain of v such that u[d] >= v[d]
   */
  bool intersects_below(const VClock<int> &vc) const;

  /* *** Total order comparisons *** */
  bool operator==(const VClock<int> &vc) const;
  bool operator!=(const VClock<int> &vc) const;
  bool operator<(const VClock<int> &vc) const;
  bool operator<=(const VClock<int> &vc) const;
  bool operator>(const VClock<int> &vc) const;
  bool operator>=(const VClock<int> &vc) const;

  std::string to_string() const;
private:
  std::vector<int> vec;
};

class VClockVec final {
public:
  VClockVec() : clock_size(0) {}
  VClockVec(unsigned clock_size, std::size_t size)
    : vec(clock_size*size), clock_size(clock_size) {}
  typedef VClockRef Ref;
  Ref operator[](int d) {
    assert (d >= 0 && (std::size_t(d)+1)*clock_size <= vec.size());
    return { vec.data() + (d*clock_size), clock_size };
  }
  void assign(unsigned clock_size, std::size_t count, const VClock<int> &init);
private:
  std::vector<int> vec;
  unsigned clock_size;
};

template<typename DOM>
std::ostream &operator<<(std::ostream &os, const VClock<DOM> &vc){
  return os << vc.to_string();
}

template<typename DOM>
llvm::raw_ostream &operator<<(llvm::raw_ostream &os, const VClock<DOM> &vc){
  return os << vc.to_string();
}

#include "VClock.tcc"

#endif
