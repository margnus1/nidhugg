/* Copyright (C) 2017 Magnus Lång
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

#ifndef __OPTION_H__
#define __OPTION_H__

#include <algorithm>
#include <cassert>
#include <type_traits>

template<typename Value>
class Option {
public:
  Option() : _has_value(false) {}
  Option(std::nullptr_t) : _has_value(false) {}
  Option(Value value) : _has_value(true), value(std::move(value)) {}
  ~Option() { if (_has_value) value.~Value(); }
  Option(const Option &o) : _has_value(o._has_value) {
    if (_has_value) new((void*)&value) Value(o.value);
  }
  Option(Option &&o) : _has_value(o._has_value) {
    if (_has_value) new((void*)&value) Value(std::move(o.value));
  }
  Option &operator=(const Option &o) {
    if (_has_value) value.~Value();
    if ((_has_value = o._has_value)) new((void*)&value) Value(o.value);
    return *this;
  }
  Option &operator=(Option &&o) {
    if (_has_value) value.~Value();
    if ((_has_value = o._has_value)) new((void*)&value) Value(std::move(o.value));
    return *this;
  }

  void reset() {
    if (std::exchange(_has_value, false)) value.~Value();
  }

  operator bool() const noexcept { return _has_value; }
  constexpr bool has_value() const { return _has_value; }
  Value const& operator *() const { assert(_has_value); return value; }
  Value& operator *() { assert(_has_value); return value; }
  Value const *operator ->() const { assert(_has_value); return &value; }
  Value *operator ->() { assert(_has_value); return &value; }

  Value const &value_or(const Value &def) const {
    if (_has_value) return value;
    else return def;
  }

  /* Monadic bind; transform the value of the option (if any) */
  template<typename F> auto map(F f) const ->
    Option<typename std::result_of<F(const Value&)>::type> {
    if (!_has_value) return {};
    else return f(value);
  }

private:
  bool _has_value;
  union{
    Value value;
  };
};

#endif
