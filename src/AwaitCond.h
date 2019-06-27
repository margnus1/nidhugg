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

#include <config.h>

#ifndef __AWAIT_COND_H__
#define __AWAIT_COND_H__

#include "SymAddr.h"

struct AwaitCond {
  enum Op : int {
    None,
    GT = 0b001,
    EQ = 0b010,
    GE = 0b011,
    LT = 0b100,
    NE = 0b101,
    LE = 0b110,
  } op;
  SymData::block_type operand;

  static const char *name(Op op);

  bool satisfied_by(const SymData &data) const {
    return satisfied_by(data.get_block(), data.get_ref().size);
  }
  bool satisfied_by(const void *data, std::size_t size) const;
};

#endif
