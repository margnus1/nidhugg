/* Copyright (C) 2019 Magnus Lång
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

#include "AwaitCond.h"
#include <cstring>

bool AwaitCond::satisfied_by(const void *data, std::size_t size) const {
  int cmp = std::memcmp(data, operand.get(), size);
  unsigned shift;
  if (cmp < 0) {
    shift = 2;
  } else if (cmp == 0) {
    shift = 1;
  } else {
    shift = 0;
  }
  return (static_cast<int>(op) >> shift) & 0b1;
}

const char *AwaitCond::name(Op op) {
  const static char *names[] = {
    nullptr, "GT", "EQ", "GE", "LT", "NE", "LE",
  };
  return names[op];
}
