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
#include <climits>
/* One of these contains llvm::sys::IsBigEndianHost */
#include <llvm/Support/Host.h>          /* On llvm < 11 */
#include <llvm/Support/SwapByteOrder.h> /* On llvm >= 11 */

namespace {
  int smemcmp(const void *lhs, const void *rhs, std::size_t count) {
    if (!count) return 0;
    std::size_t big_byte_index;
    if (llvm::sys::IsBigEndianHost) {
      big_byte_index = count-1;
    } else {
      big_byte_index = 0;
    }
    bool lsign = ((const char*)lhs)[big_byte_index] >> (CHAR_BIT-1);
    bool rsign = ((const char*)rhs)[big_byte_index] >> (CHAR_BIT-1);
    if (lsign != rsign) return lsign ? -1 : 1;
    return std::memcmp(lhs, rhs, count);
  }
}

bool AwaitCond::satisfied_by(const void *data, std::size_t size) const {
  int cmp;
  if ((cmp >> 3) & 0b1) {
    cmp = smemcmp(data, operand.get(), size);
  } else {
    cmp = std::memcmp(data, operand.get(), size);
  }
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
    nullptr, "UGT", "EQ", "UGE", "ULT", "NE", "ULE",
  };
  return names[op];
}
