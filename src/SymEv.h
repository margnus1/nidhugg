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

#ifndef __SYM_EV_H__
#define __SYM_EV_H__

#include <functional>

#include <llvm/Support/raw_ostream.h>

#include "MRef.h"
#include "SymAddr.h"
#include "RMWAction.h"

/* Symbolic representation of an event */
struct SymEv {
  public:
  enum kind {
    NONE,

    NONDET,

    LOAD,
    STORE,
    LOCAL_STORE,
    STORE_COMMIT,
    FULLMEM, /* Observe & clobber everything */

    RMW,
    CMPXHG,
    CMPXHGFAIL,

    FENCE,

    M_INIT,
    M_LOCK,
    M_TRYLOCK,
    M_TRYLOCK_FAIL,
    M_UNLOCK,
    M_DELETE,

    C_INIT,
    C_SIGNAL,
    C_BRDCST,
    C_WAIT,
    C_AWAKE,
    C_DELETE,

    SPAWN,
    JOIN,

    UNOBS_STORE,
  } kind;
  enum class fence_kind {
    FULL,
  };
  union arg {
  public:
    SymAddrSize addr;
    int num;
    fence_kind kind;

    arg() {}
    arg(SymAddrSize addr) : addr(addr) {}
    arg(int num) : num(num) {}
    arg(fence_kind kind) : kind(kind) {}
    // ~arg_union() {}
  } arg;
  union arg2 {
  public:
    RmwAction::Kind rmw_kind;
    int num;

    arg2() {}
    arg2(RmwAction::Kind kind) : rmw_kind(kind) {}
    arg2(int num) : num(num) {}
  } arg2;
  bool _rmw_result_used;
  SymData::block_type _expected, _written;

  SymEv() : kind(NONE) {};
  static SymEv None() { return {NONE, {}}; }
  static SymEv Nondet(int count) { return {NONDET, count}; }

  static SymEv Load(SymAddrSize addr) { return {LOAD, addr}; }
  static SymEv Store(SymData addr) { return {STORE, std::move(addr)}; }
  static SymEv LocalStore(SymData addr, int num) {
    return {LOCAL_STORE, std::move(addr), num};
  }
  static SymEv StoreCommit(SymData addr, int num) {
    return {STORE_COMMIT, std::move(addr), num};
  }
  static SymEv Rmw(SymData addr, RmwAction action) {
    assert(addr.get_block());
    return {RMW, std::move(addr), std::move(action)};
  }
  static SymEv CmpXhg(SymData addr, SymData::block_type expected) {
    return {CMPXHG, addr, expected};
  }
  static SymEv CmpXhgFail(SymData addr, SymData::block_type expected) {
    return {CMPXHGFAIL, addr, expected};
  }
  static SymEv Fullmem() { return {FULLMEM, {}}; }
  static SymEv Fence(fence_kind kind) { return {FENCE, {kind}}; }

  static SymEv MInit(SymAddrSize addr) { return {M_INIT, addr}; }
  static SymEv MLock(SymAddrSize addr) { return {M_LOCK, addr}; }
  static SymEv MTryLock(SymAddrSize addr) { return {M_TRYLOCK, addr}; }
  static SymEv MTryLockFail(SymAddrSize addr) { return {M_TRYLOCK_FAIL, addr}; }
  static SymEv MUnlock(SymAddrSize addr) { return {M_UNLOCK, addr}; }
  static SymEv MDelete(SymAddrSize addr) { return {M_DELETE, addr}; }

  static SymEv CInit(SymAddrSize addr) { return {C_INIT, addr}; }
  static SymEv CSignal(SymAddrSize addr) { return {C_SIGNAL, addr}; }
  static SymEv CBrdcst(SymAddrSize addr) { return {C_BRDCST, addr}; }
  static SymEv CWait(SymAddrSize cond) { return {C_WAIT, cond}; }
  static SymEv CAwake(SymAddrSize cond) { return {C_AWAKE, cond}; }
  static SymEv CDelete(SymAddrSize addr) { return {C_DELETE, addr}; }

  static SymEv Spawn(int proc) { return {SPAWN, proc}; }
  static SymEv Join(int proc) { return {JOIN, proc}; }

  static SymEv UnobsStore(SymData addr) {
    return {UNOBS_STORE, std::move(addr)};
  }

  bool is_compatible_with(SymEv other) const;
  std::string to_string(std::function<std::string(int)> pid_str
                        = (std::string(&)(int))std::to_string) const;

  bool operator==(const SymEv &s) const;
  bool operator!=(const SymEv &s) const { return !(*this == s); };

  bool has_addr() const;
  bool has_num() const;
  bool has_num2() const { return kind == LOCAL_STORE || kind == STORE_COMMIT; }
  bool has_data() const;
  bool has_expected() const;
  bool has_rmwaction() const { return kind == RMW; }
  bool has_fence_kind() const { return kind == FENCE; }
  bool empty() const { return kind == NONE; }
  const SymAddrSize &addr()   const { assert(has_addr()); return arg.addr; }
	int          num()    const { assert(has_num());  return arg.num; }
	int          num2()   const { assert(has_num2()); return arg2.num; }
  SymData data() const { assert(has_data()); return {arg.addr, _written}; }
  SymData expected() const {
    assert(has_expected());
    return {arg.addr, _expected};
  }
  RmwAction rmwaction() const {
    assert(has_rmwaction());
    assert(_expected);
    return {arg2.rmw_kind, _expected, _rmw_result_used};
  }
  RmwAction::Kind rmw_kind() const {
    assert(has_rmwaction());
    return arg2.rmw_kind;
  }
  bool rmw_result_used() const {
    assert(has_rmwaction());
    return _rmw_result_used;
  }
  fence_kind fence_kind() const { return arg.kind; }

  void purge_data();
  void set_observed(bool observed);

private:
  SymEv(enum kind kind, union arg arg) : kind(kind), arg(arg) {};
  SymEv(enum kind kind, SymData addr_written)
    : kind(kind), arg(std::move(addr_written.get_ref())),
      _written(std::move(addr_written.get_shared_block())) {};
  SymEv(enum kind kind, SymData addr_written, SymData::block_type expected)
    : kind(kind), arg(std::move(addr_written.get_ref())),
      _expected(std::move(expected)),
      _written(std::move(addr_written.get_shared_block())) {};
  SymEv(enum kind kind, SymData addr_written, RmwAction action)
    : kind(kind), arg(addr_written.get_ref()), arg2(action.kind),
      _rmw_result_used(action.result_used),
      _expected(std::move(action.operand)),
      _written(std::move(addr_written.get_shared_block())) {
      assert(has_data());
    };
  SymEv(enum kind kind, SymData addr_written, int num)
    : kind(kind), arg(addr_written.get_ref()), arg2(num),
      _written(std::move(addr_written.get_shared_block())) {
      assert(has_data());
    };
};

inline std::ostream &operator<<(std::ostream &os, const SymEv &e){
  return os << e.to_string();
}

inline llvm::raw_ostream &operator<<(llvm::raw_ostream &os, const SymEv &e){
  return os << e.to_string();
}

#endif
