/* Copyright (C) 2018 Magnus Lång and Tuan Phong Ngo
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

#include "Debug.h"
#include "RFSCTraceBuilder.h"
#include "PrefixHeuristic.h"
#include "Timing.h"
#include "TraceUtil.h"

#include <algorithm>
#include <sstream>
#include <stdexcept>
#include <boost/variant/get.hpp>

#define ANSIRed "\x1b[91m"
#define ANSIRst "\x1b[m"

#ifndef NDEBUG
#  define IFDEBUG(X) X
#else
#  define IFDEBUG(X)
#endif

static Timing::Context analysis_context("analysis");
static Timing::Context vclocks_context("vclocks");
static Timing::Context unfolding_context("unfolding");
static Timing::Context neighbours_context("neighbours");
static Timing::Context try_read_from_context("try_read_from");
static Timing::Context ponder_mutex_context("ponder_mutex");
static Timing::Context graph_context("graph");
static Timing::Context sat_context("sat");

RFSCTraceBuilder::RFSCTraceBuilder(RFSCDecisionTree &desicion_tree_,
                                   RFSCUnfoldingTree &unfolding_tree_,
                                   const Configuration &conf)
    : TSOPSOTraceBuilder(conf),
      unfolding_tree(unfolding_tree_),
      decision_tree(desicion_tree_) {
    threads.push_back(Thread(CPid(), -1));
    prefix_idx = -1;
    replay = false;
    cancelled = false;
    last_full_memory_conflict = -1;
    last_md = 0;
    replay_point = 0;
    tasks_created = 0;
}

RFSCTraceBuilder::~RFSCTraceBuilder(){
}

bool RFSCTraceBuilder::schedule(int *proc, int *aux, int *alt, bool *dryrun){
  if (cancelled) {
    assert(!std::any_of(threads.begin(), threads.end(), [](const Thread &t) {
                                                          return t.available;
                                                        }));
    return false;
  }
  *dryrun = false;
  *alt = 0;
  *aux = -1; /* No auxilliary threads in SC */
  if(replay){
    /* Are we done with the current Event? */
    if (0 <= prefix_idx
        && threads[curev().iid.get_pid()].last_event_index()
           < curev().iid.get_index() + curev().size - 1) {
      /* Continue executing the current Event */
      IPid pid = curev().iid.get_pid();
      *proc = pid;
      *alt = 0;
      if(!(threads[pid].available)) {
        llvm::dbgs() << "Trying to play process " << threads[pid].cpid << ", but it is blocked\n";
        llvm::dbgs() << "At replay step " << prefix_idx << ", iid "
                     << iid_string(IID<IPid>(pid, threads[curev().iid.get_pid()].last_event_index()))
                     << "\n";
        abort();
      }
      threads[pid].event_indices.push_back(prefix_idx);
      assert(threads[pid].event_indices.size() < ulong(curev().iid.get_index() + curev().size));
      return true;
    } else if(prefix_idx + 1 == int(prefix.size())
              && planned_awaits.empty()) {
      /* We are done replaying. Continue below... */
      assert(prefix_idx < 0 || (curev().sym.empty() ^ seen_effect)
             || (errors.size() && errors.back()->get_location()
                 == IID<CPid>(threads[curev().iid.get_pid()].cpid,
                              curev().iid.get_index()))
             || !blocking_awaits.empty());
      replay = false;
    } else {
      if (prefix_idx + 1 == int(prefix.size())) {
        /* We'll replay an event from planned_awaits */
        PlannedAwait &plan = planned_awaits.back();
        prefix.emplace_back(plan.iid);
        prefix.back().pinned = plan.pinned;
        prefix.back().set_decision(std::move(plan.decision_ptr));
        planned_awaits.pop_back();
      } else {
        /* Go to the next event. */
        assert(prefix_idx < 0 || (curev().sym.empty() ^ seen_effect)
               || (errors.size() && errors.back()->get_location()
                   == IID<CPid>(threads[curev().iid.get_pid()].cpid,
                                curev().iid.get_index())));
      }
      seen_effect = false;
      ++prefix_idx;
      IPid pid = curev().iid.get_pid();
      *proc = pid;
      *alt = curev().alt;
      assert(threads[pid].available);
      threads[pid].event_indices.push_back(prefix_idx);
      assert(threads[pid].event_indices.size() == ulong(curev().iid.get_index()));
      return true;
    }
  }

  assert(!replay);
  /* Create a new Event */

  // TEMP: Until we have a SymEv for store()
  // assert(prefix_idx < 0 || !!curev().sym.size() == curev().may_conflict);

  /* Should we merge the last two events? */
  if(prefix.size() > 1 &&
     prefix[prefix.size()-1].iid.get_pid()
     == prefix[prefix.size()-2].iid.get_pid() &&
     !prefix[prefix.size()-1].may_conflict){
    assert(curev().sym.empty()); /* Would need to be copied */
    assert(curev().sym.empty()); /* Can't happen */
    int old_size = curev().size;
    assert(old_size >= 1);
    assert(replay_point <= prefix_idx+1);
    if (replay_point == prefix_idx+1) replay_point--;
    prefix.pop_back();
    --prefix_idx;
    curev().size += old_size;
    IPid p = curev().iid.get_pid();
    assert(int(threads[p].event_indices.back()) == prefix_idx + 1);
    for (unsigned i = threads[p].event_indices.size() - old_size;
         i < threads[p].event_indices.size(); ++i) {
      threads[p].event_indices[i] = prefix_idx;
    }
  }


  /* Find an available thread. */
  for(unsigned p = 0; p < threads.size(); ++p){ // Loop through real threads
#ifndef NDEBUG
    if (!threads[p].event_indices.empty()) {
      const Event &e = prefix[threads[p].event_indices.back()];
      assert(e.iid.get_index() + e.size - 1 == threads[p].last_event_index());
    }
#endif
    if(threads[p].available &&
       (conf.max_search_depth < 0 || threads[p].last_event_index() < conf.max_search_depth)){
      /* Create a new Event */
      seen_effect = false;
      ++prefix_idx;
      assert(prefix_idx == int(prefix.size()));
      threads[p].event_indices.push_back(prefix_idx);
      prefix.emplace_back(IID<IPid>(IPid(p),threads[p].last_event_index()));
      *proc = p;
      return true;
    }
  }

  return false; // No available threads
}

void RFSCTraceBuilder::refuse_schedule(){
  assert(prefix_idx == int(prefix.size())-1);
  assert(curev().size == 1);
  assert(!curev().may_conflict);
  IPid last_pid = curev().iid.get_pid();
  prefix.pop_back();
  assert(int(threads[last_pid].event_indices.back()) == prefix_idx);
  threads[last_pid].event_indices.pop_back();
  assert(threads[last_pid].event_indices.empty() ||
         int(threads[last_pid].event_indices.back()) != prefix_idx);
  --prefix_idx;
  mark_unavailable(last_pid);
}

void RFSCTraceBuilder::mark_available(int proc, int aux){
  threads[ipid(proc,aux)].available = true;
}

void RFSCTraceBuilder::mark_unavailable(int proc, int aux){
  threads[ipid(proc,aux)].available = false;
}

bool RFSCTraceBuilder::is_replaying() const {
  return prefix_idx < replay_point;
}

void RFSCTraceBuilder::cancel_replay(){
  assert(replay == is_replaying());
  cancelled = true;
  replay = false;

  /* Find last decision, the one that caused this failure, and then
   * prune all later decisions. */
  int blame = -1; /* -1: All executions lead to this failure */
  DecisionNode *blamee = nullptr;
  for (int i = 0; i <= prefix_idx; ++i) {
    if (prefix[i].get_decision_depth() > blame) {
      blame = prefix[i].get_decision_depth();
      blamee = prefix[i].decision_ptr.get();
    }
  }
  if (blame != -1) {
    blamee->prune_decisions();
  }
}

void RFSCTraceBuilder::metadata(const llvm::MDNode *md){
  if(curev().md == 0){
    curev().md = md;
  }
  last_md = md;
}

bool RFSCTraceBuilder::sleepset_is_empty() const{
  return !was_redundant;
}

Trace *RFSCTraceBuilder::get_trace() const{
  std::vector<IID<CPid> > cmp;
  SrcLocVectorBuilder cmp_md;
  std::vector<Error*> errs;
  for(unsigned i = 0; i < prefix.size(); ++i){
    cmp.push_back(IID<CPid>(threads[prefix[i].iid.get_pid()].cpid,prefix[i].iid.get_index()));
    cmp_md.push_from(prefix[i].md);
  };
  for(unsigned i = 0; i < errors.size(); ++i){
    errs.push_back(errors[i]->clone());
  }
  Trace *t = new IIDSeqTrace(cmp,cmp_md.build(),errs);
  t->set_blocked(!sleepset_is_empty());
  return t;
}

bool RFSCTraceBuilder::reset(){
  work_item = decision_tree.get_next_work_task();

  while (work_item != nullptr && work_item->is_pruned()) {
    tasks_created--;
    work_item = decision_tree.get_next_work_task();
  }

  if (work_item == nullptr) {
    /* DecisionNodes have been pruned and its trailing thread-task need to return. */
    return false;
  }

  Leaf l = std::move(work_item->leaf);
  const auto &unf = work_item->unfold_node;

  assert(!l.is_bottom());
  if (conf.debug_print_on_reset && !l.prefix.empty())
    llvm::dbgs() << "Backtracking to decision node " << (work_item->depth)
                 << ", replaying " << l.prefix.size() << " events to read from "
                 << (unf ? std::to_string(unf->seqno) : "init") << "\n";

  assert(l.prefix.empty() == (work_item->depth == -1));

  assert(planned_awaits.empty());
  std::vector<Event> new_prefix;
  new_prefix.reserve(l.prefix.size()); // Overestimate; also includes blocked events
  std::vector<int> iid_map;
  for (Branch &b : l.prefix) {
    int index = (int(iid_map.size()) <= b.pid) ? 1 : iid_map[b.pid];
    IID<IPid> iid(b.pid, index);
    if (b.blocked) {
      planned_awaits.emplace_back(iid, depth_to_decision(b.decision_depth, work_item), b.pinned);
    } else {
      new_prefix.emplace_back(iid);
      new_prefix.back().size = b.size;
      new_prefix.back().sym = std::move(b.sym);
      new_prefix.back().pinned = b.pinned;
      new_prefix.back().set_branch_decision(b.decision_depth, work_item);
      iid_map_step(iid_map, new_prefix.back());
    }
  }

  replay_point = new_prefix.size();

#ifndef NDEBUG
  for (int d = 0; d < work_item->depth; ++d) {
    assert(std::any_of(new_prefix.begin(), new_prefix.end(),
                       [&](const Event &e) { return e.get_decision_depth() == d; })
           + std::any_of(planned_awaits.begin(), planned_awaits.end(),
                         [d](const PlannedAwait &a) { return a.decision_ptr->depth == d; })
           == 1);
  }
#endif

  prefix = std::move(new_prefix);

  CPS = CPidSystem();
  threads.clear();
  threads.push_back(Thread(CPid(),-1));
  mutexes.clear();
  cond_vars.clear();
  mem.clear();
  mutex_deadlocks.clear();
  blocking_awaits.clear();
  last_full_memory_conflict = -1;
  prefix_idx = -1;
  replay = true;
  cancelled = false;
  last_md = 0;
  tasks_created = 0;
  reset_cond_branch_log();
  prefix_first_unblock_jump.reset();
  was_redundant = false;

  return true;
}

IID<CPid> RFSCTraceBuilder::get_iid() const{
  IPid pid = curev().iid.get_pid();
  int idx = curev().iid.get_index();
  return IID<CPid>(threads[pid].cpid,idx);
}

static std::string rpad(std::string s, int n){
  while(int(s.size()) < n) s += " ";
  return s;
}

static std::string lpad(const std::string &s, int n){
  return std::string(std::max(0, n - int(s.size())), ' ') + s;
}

std::string RFSCTraceBuilder::iid_string(std::size_t pos) const{
  return iid_string(prefix[pos]);
}

std::string RFSCTraceBuilder::iid_string(const Event &event) const{
  IPid pid = event.iid.get_pid();
  int index = event.iid.get_index();
  std::stringstream ss;
  ss << "(" << threads[pid].cpid << "," << index;
  if(event.size > 1){
    ss << "-" << index + event.size - 1;
  }
  ss << ")";
  if(event.alt != 0){
    ss << "-alt:" << event.alt;
  }
  return ss.str();
}

std::string RFSCTraceBuilder::iid_string(const std::pair<IPid,BlockedAwait> &pa) const{
  std::stringstream ss;
  ss << "(" << threads[pa.first].cpid << "," << pa.second.index << ")";
  return ss.str();
}

std::string RFSCTraceBuilder::iid_string(IID<IPid> iid) const{
  if (Option<unsigned> event
      = try_find_process_event(iid.get_pid(), iid.get_index())) {
    return iid_string(*event);
  } else {
    /* May be a blocked event */
    std::stringstream ss;
    ss << "(" << threads[iid.get_pid()].cpid << "," << iid.get_index() << ")";
    return ss.str();
  }
}

std::string RFSCTraceBuilder::iid_string(const TraceOverlay &trace,
                                         IID<IPid> iid) const {
  if (Option<unsigned> event
      = trace.try_find_process_event(iid.get_pid(), iid.get_index())) {
    return iid_string(trace, *event);
  } else {
    /* May be a blocked event */
    std::stringstream ss;
    ss << "(" << threads[iid.get_pid()].cpid << "," << iid.get_index() << ")";
    return ss.str();
  }
}

std::string RFSCTraceBuilder::iid_string(const TraceOverlay &trace,
                                         std::size_t pos) const {
  TraceOverlay::TraceEventConstRef event = trace.prefix_at(pos);
  IPid pid = event.iid().get_pid();
  int index = event.iid().get_index();
  std::stringstream ss;
  ss << "(" << threads[pid].cpid << "," << index;
  if(event.size() > 1){
    ss << "-" << index + event.size() - 1;
  }
  ss << ")";
  // if(event.alt != 0){
  //   ss << "-alt:" << event.alt;
  // }
  return ss.str();
}

void RFSCTraceBuilder::debug_print() const {
  debug_print(top_clock());
}

void RFSCTraceBuilder::debug_print(VClock<IPid> horizon) const {
  llvm::dbgs() << "RFSCTraceBuilder (debug print, replay until " << replay_point;
  if (was_redundant) llvm::dbgs() << ", redundant";
  llvm::dbgs() << "):\n";
  int idx_offs = 0;
  int iid_offs = 0;
  int dec_offs = 0;
  int unf_offs = 0;
  int rf_offs = 0;
  int clock_offs = 0;

  for(unsigned i = 0; i < prefix.size(); ++i){
    IPid ipid = prefix[i].iid.get_pid();
    idx_offs = std::max(idx_offs,int(std::to_string(i).size()));
    iid_offs = std::max(iid_offs,2*ipid+int(iid_string(i).size()));
    dec_offs = std::max(dec_offs,int(std::to_string(prefix[i].get_decision_depth()).size())
                        + (prefix[i].pinned ? 1 : 0));
    unf_offs = std::max(unf_offs,int(std::to_string(prefix[i].event->seqno).size()));
    rf_offs = std::max(rf_offs,prefix[i].read_from ?
                       int(std::to_string(*prefix[i].read_from).size())
                       : 1);
    clock_offs = std::max(clock_offs,int(prefix[i].clock.to_string().size()));
  }

  for (auto &addr_awaits : blocking_awaits) {
    for (auto &pid_await : addr_awaits.second) {
      IPid ipid = pid_await.first;
      const BlockedAwait &aw = pid_await.second;
      idx_offs = std::max(idx_offs,1);
      iid_offs = std::max(iid_offs,2*ipid+int(iid_string(pid_await).size()));
      dec_offs = std::max(dec_offs,int(std::to_string(aw.get_decision_depth()).size()));
      unf_offs = std::max(unf_offs,1);
      rf_offs = std::max(rf_offs, int(std::to_string(aw.read_from).size()));
      clock_offs = std::max(clock_offs,1);
    }
  }

  for(unsigned i = 0; i < prefix.size(); ++i){
    IPid ipid = prefix[i].iid.get_pid();
    llvm::dbgs() << (horizon.reverse_includes(prefix[i].iid) ? "-" : " ")
                 << lpad(std::to_string(i),idx_offs)
                 << rpad("",1+ipid*2)
                 << rpad(iid_string(i),iid_offs-ipid*2)
                 << " " << lpad((prefix[i].pinned ? "*" : "")
                                + std::to_string(prefix[i].get_decision_depth()),dec_offs)
                 << " " << lpad(std::to_string(prefix[i].event->seqno),unf_offs)
                 << " " << lpad(prefix[i].read_from ? std::to_string(*prefix[i].read_from) : "-",rf_offs)
                 << " " << rpad(prefix[i].clock.to_string(),clock_offs)
                 << " " << prefix[i].sym.to_string() << "\n";
  }
  for (auto &addr_awaits : blocking_awaits) {
    for (auto &pid_await : addr_awaits.second) {
      IPid ipid = pid_await.first;
      const BlockedAwait &aw = pid_await.second;
      llvm::dbgs() << " " << lpad("b",idx_offs)
                 << rpad("",1+ipid*2)
                 << rpad(iid_string(pid_await),iid_offs-ipid*2)
                 << " " << lpad(std::to_string(aw.get_decision_depth()),dec_offs)
                 << " " << lpad("-",unf_offs)
                 << " " << lpad(std::to_string(aw.read_from),rf_offs)
                 << " " << rpad("-",clock_offs)
                 << " Blocked" << SymEv::LoadAwait(addr_awaits.first, aw.cond).to_string() << "\n";
    }
  }
  if(errors.size()){
    llvm::dbgs() << "Errors:\n";
    for(unsigned i = 0; i < errors.size(); ++i){
      llvm::dbgs() << "  Error #" << i+1 << ": "
                   << errors[i]->to_string() << "\n";
    }
  }
}

bool RFSCTraceBuilder::spawn(){
  IPid parent_ipid = curev().iid.get_pid();
  CPid child_cpid = CPS.spawn(threads[parent_ipid].cpid);
  threads.push_back(Thread(child_cpid,prefix_idx));
  curev().may_conflict = true;
  return record_symbolic(SymEv::Spawn(threads.size() - 1));
}

bool RFSCTraceBuilder::store(const SymData &sd){
  assert(false && "Cannot happen");
  abort();
  return true;
}

bool RFSCTraceBuilder::atomic_store(const SymData &sd){
  if (!record_symbolic(SymEv::Store(sd))) return false;
  do_atomic_store(sd);
  return true;
}

void RFSCTraceBuilder::do_atomic_store(const SymData &sd){
  const SymAddrSize &ml = sd.get_ref();
  curev().may_conflict = true;

  /* See previous updates reads to ml */
  for(SymAddr b : ml){
    ByteInfo &bi = mem[b];

    /* Register in memory */
    bi.last_update = prefix_idx;
  }
}

bool RFSCTraceBuilder::atomic_rmw(const SymData &sd){
  if (!record_symbolic(SymEv::Rmw(sd))) return false;
  do_load(sd.get_ref());
  do_atomic_store(sd);
  return true;
}

bool RFSCTraceBuilder::load(const SymAddrSize &ml){
  if (!record_symbolic(SymEv::Load(ml))) return false;
  do_load(ml);
  return true;
}

void RFSCTraceBuilder::do_load(const SymAddrSize &ml){
  curev().may_conflict = true;
  int lu = mem[ml.addr].last_update;
  curev().read_from = lu;

  assert(lu == -1 || get_addr(lu) == ml);
  assert(std::all_of(ml.begin(), ml.end(), [lu,this](SymAddr b) {
             return mem[b].last_update == lu;
           }));
}

bool RFSCTraceBuilder::load_await(const SymAddrSize &ml, AwaitCond cond) {
  if (!record_symbolic(SymEv::LoadAwait(ml, std::move(cond)))) return false;

  /* We delete the blocking_awaits entry here, because doing so on
   * writes is more complicated and duplicates logic in Interpreter. */
  auto ml_await = blocking_awaits.find(ml);
  if (ml_await != blocking_awaits.end()) {
    IPid current = curev().iid.get_pid();
    auto it = ml_await->second.find(current);
    assert(!curev().decision_ptr);
    assert(it != ml_await->second.end());
    if (it->second.decision_ptr) {
      std::swap(curev().decision_ptr, it->second.decision_ptr);
      if (!prefix_first_unblock_jump
          || curev().decision_ptr->depth
          < prefix[*prefix_first_unblock_jump].decision_ptr->depth) {
        prefix_first_unblock_jump = prefix_idx;
      }
    }
    curev().planned_read_from = it->second.planned_read_from;
    ml_await->second.erase(it);
    /* Delete the memory location if it became empty */
    if (ml_await->second.empty())
      blocking_awaits.erase(ml_await);
    if (conf.debug_print_on_reset)
      llvm::dbgs() << "Clearing blocking await by " << threads[current].cpid
                   << "\n";
  }

  do_load(ml);
  return true;
}

bool RFSCTraceBuilder::load_await_fail(const SymAddrSize &ml, AwaitCond cond) {
  IPid current = curev().iid.get_pid();
  int  index   = curev().iid.get_index();
  auto &ml_awaits = blocking_awaits[ml];

  if (conf.debug_print_on_reset)
    llvm::dbgs() << "Detecting blocking await by " << threads[current].cpid
                 << "\n";

  auto ret = ml_awaits.try_emplace(current, index, std::move(cond));
  assert(ret.second);
  BlockedAwait &aw = ret.first->second;
  if (replay) {
    aw.pinned = curev().pinned;
    aw.decision_ptr = std::move(curev().decision_ptr);
    aw.planned_read_from = mem[ml.addr].last_update;
  }
  aw.index = curev().iid.get_index();
  return true;
}

bool RFSCTraceBuilder::compare_exchange
(const SymData &sd, const SymData::block_type expected, bool success){
  if(success){
    if (!record_symbolic(SymEv::CmpXhg(sd, expected))) return false;
    do_load(sd.get_ref());
    do_atomic_store(sd);
  }else{
    if (!record_symbolic(SymEv::CmpXhgFail(sd, expected))) return false;
    do_load(sd.get_ref());
  }
  return true;
}

bool RFSCTraceBuilder::full_memory_conflict(){
  invalid_input_error("RFSC does not support black-box functions with memory effects");
  return false;
  if (!record_symbolic(SymEv::Fullmem())) return false;
  curev().may_conflict = true;

  // /* See all pervious memory accesses */
  // for(auto it = mem.begin(); it != mem.end(); ++it){
  //   do_load(it->second);
  // }
  // last_full_memory_conflict = prefix_idx;

  // /* No later access can have a conflict with any earlier access */
  // mem.clear();
  return true;
}

bool RFSCTraceBuilder::fence(){
  return true;
}

bool RFSCTraceBuilder::join(int tgt_proc){
  if (!record_symbolic(SymEv::Join(tgt_proc))) return false;
  curev().may_conflict = true;
  add_happens_after_thread(prefix_idx, tgt_proc);
  return true;
}

bool RFSCTraceBuilder::mutex_lock(const SymAddrSize &ml){
  if (!record_symbolic(SymEv::MLock(ml))) return false;

  Mutex &mutex = mutexes[ml.addr];
  curev().may_conflict = true;
  curev().read_from = mutex.last_access;

  mutex.last_lock = mutex.last_access = prefix_idx;
  mutex.locked = true;
  return true;
}

bool RFSCTraceBuilder::mutex_lock_fail(const SymAddrSize &ml){
  assert(!conf.mutex_require_init || mutexes.count(ml.addr));
  IFDEBUG(Mutex &mutex = mutexes[ml.addr];)
  assert(0 <= mutex.last_lock && mutex.locked);

  IPid current = curev().iid.get_pid();
  auto &deadlocks = mutex_deadlocks[ml.addr];
  assert(!std::any_of(deadlocks.cbegin(), deadlocks.cend(),
                      [current](IPid blocked) {
                        return blocked == current;
                      }));
  deadlocks.push_back(current);
  return true;
}

bool RFSCTraceBuilder::mutex_trylock(const SymAddrSize &ml){
  Mutex &mutex = mutexes[ml.addr];
  if (!record_symbolic(mutex.locked ? SymEv::MTryLockFail(ml) : SymEv::MTryLock(ml)))
    return false;
  curev().read_from = mutex.last_access;
  curev().may_conflict = true;

  mutex.last_access = prefix_idx;
  if(!mutex.locked){ // Mutex is free
    mutex.last_lock = prefix_idx;
    mutex.locked = true;
  }
  return true;
}

bool RFSCTraceBuilder::mutex_unlock(const SymAddrSize &ml){
  if (!record_symbolic(SymEv::MUnlock(ml))) return false;
  Mutex &mutex = mutexes[ml.addr];
  curev().read_from = mutex.last_access;
  curev().may_conflict = true;
  assert(0 <= mutex.last_access);

  mutex.last_access = prefix_idx;
  mutex.locked = false;

  /* No one is blocking anymore! Yay! */
  mutex_deadlocks.erase(ml.addr);
  return true;
}

bool RFSCTraceBuilder::mutex_init(const SymAddrSize &ml){
  if (!record_symbolic(SymEv::MInit(ml))) return false;
  assert(mutexes.count(ml.addr) == 0);
  curev().read_from = -1;
  curev().may_conflict = true;
  mutexes[ml.addr] = Mutex(prefix_idx);
  return true;
}

bool RFSCTraceBuilder::mutex_destroy(const SymAddrSize &ml){
  if (!record_symbolic(SymEv::MDelete(ml))) return false;
  Mutex &mutex = mutexes[ml.addr];
  curev().read_from = mutex.last_access;
  curev().may_conflict = true;

  mutex.last_access = prefix_idx;
  mutex.locked = false;
  return true;
}

bool RFSCTraceBuilder::cond_init(const SymAddrSize &ml){
  invalid_input_error("RFSC does not support condition variables");
  return false;
  if (!record_symbolic(SymEv::CInit(ml))) return false;
  if(cond_vars.count(ml.addr)){
    pthreads_error("Condition variable initiated twice.");
    return false;
  }
  curev().may_conflict = true;
  cond_vars[ml.addr] = CondVar(prefix_idx);
  return true;
}

bool RFSCTraceBuilder::cond_signal(const SymAddrSize &ml){
  invalid_input_error("RFSC does not support condition variables");
  return false;
  if (!record_symbolic(SymEv::CSignal(ml))) return false;
  curev().may_conflict = true;

  auto it = cond_vars.find(ml.addr);
  if(it == cond_vars.end()){
    pthreads_error("cond_signal called with uninitialized condition variable.");
    return false;
  }
  CondVar &cond_var = it->second;
  VecSet<int> seen_events = {last_full_memory_conflict};
  if(cond_var.waiters.size() > 1){
    if (!register_alternatives(cond_var.waiters.size())) return false;
  }
  assert(0 <= curev().alt);
  assert(cond_var.waiters.empty() || curev().alt < int(cond_var.waiters.size()));
  if(cond_var.waiters.size()){
    /* Wake up the alt:th waiter. */
    int i = cond_var.waiters[curev().alt];
    assert(0 <= i && i < prefix_idx);
    IPid ipid = prefix[i].iid.get_pid();
    assert(!threads[ipid].available);
    threads[ipid].available = true;
    seen_events.insert(i);

    /* Remove waiter from cond_var.waiters */
    for(int j = curev().alt; j < int(cond_var.waiters.size())-1; ++j){
      cond_var.waiters[j] = cond_var.waiters[j+1];
    }
    cond_var.waiters.pop_back();
  }
  cond_var.last_signal = prefix_idx;

  return true;
}

bool RFSCTraceBuilder::cond_broadcast(const SymAddrSize &ml){
  invalid_input_error("RFSC does not support condition variables");
  return false;
  if (!record_symbolic(SymEv::CBrdcst(ml))) return false;
  curev().may_conflict = true;

  auto it = cond_vars.find(ml.addr);
  if(it == cond_vars.end()){
    pthreads_error("cond_broadcast called with uninitialized condition variable.");
    return false;
  }
  CondVar &cond_var = it->second;
  for(int i : cond_var.waiters){
    assert(0 <= i && i < prefix_idx);
    IPid ipid = prefix[i].iid.get_pid();
    assert(!threads[ipid].available);
    threads[ipid].available = true;
    // seen_events.insert(i);
  }
  cond_var.waiters.clear();
  cond_var.last_signal = prefix_idx;

  return true;
}

bool RFSCTraceBuilder::cond_wait(const SymAddrSize &cond_ml, const SymAddrSize &mutex_ml){
  invalid_input_error("RFSC does not support condition variables");
  return false;
  {
    auto it = mutexes.find(mutex_ml.addr);
    if(it == mutexes.end()){
      if(conf.mutex_require_init){
        pthreads_error("cond_wait called with uninitialized mutex object.");
      }else{
        pthreads_error("cond_wait called with unlocked mutex object.");
      }
      return false;
    }
    Mutex &mtx = it->second;
    if(mtx.last_lock < 0 || prefix[mtx.last_lock].iid.get_pid() != curev().iid.get_pid()){
      pthreads_error("cond_wait called with mutex which is not locked by the same thread.");
      return false;
    }
  }

  if (!mutex_unlock(mutex_ml)) return false;
  if (!record_symbolic(SymEv::CWait(cond_ml))) return false;
  curev().may_conflict = true;

  IPid pid = curev().iid.get_pid();

  auto it = cond_vars.find(cond_ml.addr);
  if(it == cond_vars.end()){
    pthreads_error("cond_wait called with uninitialized condition variable.");
    return false;
  }
  it->second.waiters.push_back(prefix_idx);
  threads[pid].available = false;

  return true;
}

bool RFSCTraceBuilder::cond_awake(const SymAddrSize &cond_ml, const SymAddrSize &mutex_ml){
  invalid_input_error("RFSC does not support condition variables");
  return false;
  assert(cond_vars.count(cond_ml.addr));
  CondVar &cond_var = cond_vars[cond_ml.addr];
  add_happens_after(prefix_idx, cond_var.last_signal);

  if (!mutex_lock(mutex_ml)) return false;
  if (!record_symbolic(SymEv::CAwake(cond_ml))) return false;
  curev().may_conflict = true;

  return true;
}

int RFSCTraceBuilder::cond_destroy(const SymAddrSize &ml){
  invalid_input_error("RFSC does not support condition variables");
  return false;
  const int err = (EBUSY == 1) ? 2 : 1; // Chose an error value different from EBUSY
  if (!record_symbolic(SymEv::CDelete(ml))) return err;

  curev().may_conflict = true;

  auto it = cond_vars.find(ml.addr);
  if(it == cond_vars.end()){
    pthreads_error("cond_destroy called on uninitialized condition variable.");
    return err;
  }
  CondVar &cond_var = it->second;

  int rv = cond_var.waiters.size() ? EBUSY : 0;
  cond_vars.erase(ml.addr);
  return rv;
}

bool RFSCTraceBuilder::register_alternatives(int alt_count){
  invalid_input_error("RFSC does not support nondeterministic events");
  return false;
  curev().may_conflict = true;
  if (!record_symbolic(SymEv::Nondet(alt_count))) return false;
  // if(curev().alt == 0) {
  //   for(int i = curev().alt+1; i < alt_count; ++i){
  //     curev().races.push_back(Race::Nondet(prefix_idx, i));
  //   }
  // }
  return true;
}

template <class Iter>
static void rev_recompute_data
(SymData &data, VecSet<SymAddr> &needed, Iter end, Iter begin){
  for (auto pi = end; !needed.empty() && (pi != begin);){
    const SymEv &p = *(--pi);
    switch(p.kind){
    case SymEv::STORE:
    case SymEv::UNOBS_STORE:
    case SymEv::RMW:
    case SymEv::CMPXHG:
      if (data.get_ref().overlaps(p.addr())) {
        for (SymAddr a : p.addr()) {
          if (needed.erase(a)) {
            data[a] = p.data()[a];
          }
        }
      }
      break;
    default:
      break;
    }
  }
}

void RFSCTraceBuilder::add_happens_after(unsigned second, unsigned first){
  assert(first != ~0u);
  assert(second != ~0u);
  assert(first != second);
  assert(first < second);
  assert((long long)second <= prefix_idx);

  std::vector<unsigned> &vec = prefix[second].happens_after;
  if (vec.size() && vec.back() == first) return;

  vec.push_back(first);
}

void RFSCTraceBuilder::add_happens_after_thread(unsigned second, IPid thread){
  assert((int)second == prefix_idx);
  if (threads[thread].event_indices.empty()) return;
  add_happens_after(second, threads[thread].event_indices.back());
}

/* Filter the sequence first..last from all elements that are less than
 * any other item. The sequence is modified in place and an iterator to
 * the position beyond the last included element is returned.
 *
 * Assumes less is transitive and asymetric (a strict partial order)
 */
template< class It, class LessFn >
static It frontier_filter(It first, It last, LessFn less){
  It fill = first;
  for (It current = first; current != last; ++current){
    bool include = true;
    for (It check = first; include && check != fill;){
      if (less(*current, *check)){
        include = false;
        break;
      }
      if (less(*check, *current)){
        /* Drop check from fill set */
        --fill;
        std::swap(*check, *fill);
      }else{
        ++check;
      }
    }
    if (include){
      /* Add current to fill set */
      if (fill != current) std::swap(*fill, *current);
      ++fill;
    }
  }
  return fill;
}

void RFSCTraceBuilder::
maybe_add_spawn_happens_after(TraceOverlay::TraceEvent &event) const {
  const auto &iid = event.iid;
  IPid ipid = iid.get_pid();
  int iidx = iid.get_index();
  if (iidx <= 1) {
    assert(iidx == 1);
    const Thread &t = threads[ipid];
    /* The first event of a thread happens after the spawn event that
     * created it.
     */
    if (t.spawn_event >= 0) {
      event.add_happens_after(t.spawn_event);
    }
  }
}

void RFSCTraceBuilder::maybe_add_spawn_happens_after(unsigned i) {
  const auto &iid = prefix[i].iid;
  IPid ipid = iid.get_pid();
  int iidx = iid.get_index();
  if (iidx <= 1) {
    assert(iidx == 1);
    const Thread &t = threads[ipid];
    /* The first event of a thread happens after the spawn event that
     * created it.
     */
    if (t.spawn_event >= 0)
      add_happens_after(i, t.spawn_event);
  }
}

int RFSCTraceBuilder::
compute_above_clock(VClock<IPid> &clock, IID<IPid> iid,
                    const std::vector<unsigned> &happens_after) const{
  int last = -1;
  IPid ipid = iid.get_pid();
  int iidx = iid.get_index();
  if (iidx > 1) {
    last = find_process_event(ipid, iidx-1);
    clock = prefix[last].clock;
  } else {
    clock = VClock<IPid>();
  }
  clock[ipid] = iidx;

  /* First add the non-reversible edges */
  for (unsigned j : happens_after){
    clock += prefix[j].clock;
  }

  return last;
}

int RFSCTraceBuilder::compute_above_clock(unsigned i) {
#ifndef NDEBUG
  for (unsigned j : prefix[i].happens_after) assert(j < i);
#endif

  int last = compute_above_clock(prefix[i].clock, prefix[i].iid,
                                 prefix[i].happens_after);
  prefix[i].above_clock = prefix[i].clock;
  return last;
}

VClock<int> RFSCTraceBuilder::
compute_above_clock(TraceOverlay::TraceEventConstRef event) const {
  VClock<IPid> clock;
  compute_above_clock(clock, event.iid(), event.happens_after());
  return clock;
}

void RFSCTraceBuilder::compute_vclocks(){
  Timing::Guard timing_guard(vclocks_context);

  std::vector<llvm::SmallVector<unsigned,2>> happens_after(prefix.size());
  for (unsigned i = 0; i < prefix.size(); i++){
    /* First add the non-reversible edges */
    maybe_add_spawn_happens_after(i);
    int last = compute_above_clock(i);

    if (last != -1) happens_after[last].push_back(i);
    for (unsigned j : prefix[i].happens_after){
      happens_after[j].push_back(i);
    }

    /* Then add read-from */
    if (prefix[i].read_from && *prefix[i].read_from != -1) {
      prefix[i].clock += prefix[*prefix[i].read_from].clock;
      happens_after[*prefix[i].read_from].push_back(i);
    }
  }

  /* The top of our vector clock lattice, initial value of the below
   * clock (excluding itself) for evey event */
  below_clocks.assign(threads.size(), prefix.size(), top_clock());
  for (unsigned i = prefix.size();;) {
    if (i == 0) break;
    auto clock = below_clocks[--i];
    Event &e = prefix[i];
    clock[e.iid.get_pid()] = e.iid.get_index();
    for (unsigned j : happens_after[i]) {
      assert (i < j);
      clock -= below_clocks[j];
    }
  }
}

VClock<int> RFSCTraceBuilder::top_clock() const {
  std::vector<int> top(threads.size());
  for (unsigned i = 0; i < threads.size(); ++i)
    top[i] = threads[i].event_indices.size()+1;
  return VClock<IPid>(std::move(top));
}

namespace {
  const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> unf_null_ptr;
}

const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> &
RFSCTraceBuilder::get_unf_parent(IID<IPid> iid) const {
  const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> *parent;
  IPid p = iid.get_pid();
  if (iid.get_index() == 1) {
    parent = &unf_null_ptr;
  } else {
    int par_idx = find_process_event(p, iid.get_index()-1);
    parent = &prefix[par_idx].event;
  }
  return *parent;
}

const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> &
RFSCTraceBuilder::get_unf_read_from(int read_from) const {
  if (read_from == -1) {
    return unf_null_ptr;
  } else {
    return prefix[read_from].event;
  }
}

void RFSCTraceBuilder::compute_unfolding_and_plan() {
  Timing::Guard timing_guard(unfolding_context);

  std::vector<unsigned> jumps;
  const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> null_ptr;

  /* Compute unfolding events for prefix */
  for (unsigned i = 0; i < prefix.size(); ++i) {
    const auto &last_decision = prefix[i].decision_ptr;
    assert(!last_decision || work_item->depth >= last_decision->depth);

    const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> &parent
      = get_unf_parent(prefix[i].iid);
    assert(!prefix[i].event);
    if (!prefix[i].may_conflict && (parent != nullptr)) {
      prefix[i].event = parent;
      continue;
    }
    if (prefix[i].planned_read_from &&
        *prefix[i].planned_read_from != *prefix[i].read_from) {
      jumps.push_back(i);
    }
    /* First, build unfolding nodes as-executed. */
    const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> &read_from
      = get_unf_read_from(prefix[i].read_from.value_or(-1));

    prefix[i].event = unfolding_tree.find_unfolding_node
      (threads[prefix[i].iid.get_pid()].cpid, parent, read_from);
  }

  assert(prefix_first_unblock_jump.has_value() == !jumps.empty());
  /* Then, for the first prefix call, substitute unfolding nodes as
   * planned, and also fake read-from edges
   */
  std::vector<Option<int>> stashed_read_froms;
  for (unsigned i : jumps) {
    stashed_read_froms.push_back(std::exchange(prefix[i].read_from,
                                               prefix[i].planned_read_from));
    const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> &read_from
      = get_unf_read_from(prefix[i].planned_read_from.value_or(-1));
    IID<IPid> iid = prefix[i].iid;
    prefix[i].event = unfolding_tree.find_unfolding_node
      (threads[iid.get_pid()].cpid, get_unf_parent(iid), read_from);
  }

  /* Build horizon clock for first plan call (includes all events if no
   * jumps have taken place) */
  VClock<IPid> first_plan_horizon = top_clock();
  for (unsigned i : jumps) {
    VClock<IPid> below_excluding_self = below_clocks[i];
    below_excluding_self[prefix[i].iid.get_pid()]++;
    first_plan_horizon -= below_excluding_self;
  }

  /* Build decision nodes as-planned */
  auto deepest_node = work_item;

  /* Assign decision pointers to prefix for first jump */
  for (unsigned i = 0; i < prefix.size(); ++i) {
    /* These nodes would both go unused and have incorrect unfolding
     * events. */
    if (first_plan_horizon.reverse_includes(prefix[i].iid)) continue;
    if (int(i) >= replay_point) {
      if (is_load(i)) {
        assert(!prefix[i].pinned);
        assert((std::count(jumps.begin(), jumps.end(), i) != 0)
               == (prefix[i].decision_ptr != nullptr));
        if (!prefix[i].decision_ptr) {
          const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> &decision
            = is_lock_type(i) ? prefix[i].event : prefix[i].event->read_from;
          deepest_node = decision_tree.new_decision_node(std::move(deepest_node), decision);
          prefix[i].set_decision(deepest_node);
        }
      } else {
        assert(!prefix[i].pinned);
        assert(!prefix[i].decision_ptr);
      }
    }
  }

  /* Assign decision pointers to blocking awaits for first jump */
  for (auto &addr_awaits : blocking_awaits) {
    for (auto &pid_cond : addr_awaits.second) {
      BlockedAwait &aw = pid_cond.second;
      assert(!aw.pinned);
      /* XXX: Unnecessary insertion */
      aw.read_from = mem[addr_awaits.first.addr].last_update;
      int read_from = aw.planned_read_from.value_or(aw.read_from);
      const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> &decision
        = read_from == -1 ? nullptr : prefix[read_from].event;
      if (aw.decision_ptr) {
        assert(aw.decision_ptr->unfold_node == decision.get());
      } else {
        deepest_node = decision_tree.new_decision_node(std::move(deepest_node), decision);
        aw.decision_ptr = deepest_node;
      }
    }
  }

  /* XXX: Before we do this, we really should allocate the decision node
   * for the jump; otherwise, it might be rediscovered and scheduled by
   * jump(), leading to unnecessary redundant execution. */
  if (conf.debug_print_on_reset && !jumps.empty()) {
    llvm::dbgs() << "There are some decision jumps ([";
    for (unsigned i : jumps) llvm::dbgs() << i << ",";
    llvm::dbgs() << "]), first we pretend they're not there\n";
  }
  plan(first_plan_horizon, jumps);

  /* Now, if we're jumping (i.e. as-planned and as-executed traces
   * differ), we need to assign correct unfolding nodes and rebuild our
   * decision pointers to be able to do planning for the trace
   * as-executed. */
  if (!jumps.empty()) {
    /* Reset unfolding nodes and read-froms to as-executed */
    for (unsigned ix = 0; ix < jumps.size(); ++ix) {
      unsigned i = jumps[ix];
      prefix[i].read_from = stashed_read_froms[ix];
      const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> &read_from
        = get_unf_read_from(prefix[i].read_from.value_or(-1));
      IID<IPid> iid = prefix[i].iid;
      prefix[i].event = unfolding_tree.find_unfolding_node
        (threads[iid.get_pid()].cpid, get_unf_parent(iid), read_from);
    }

    /* Look for a decision-tree jump */
    Option<int> jump_depth = prefix_first_unblock_jump.map
      ([this](unsigned ix) { return prefix[ix].decision_ptr->depth; });
    bool first_jump_is_await = false;
    std::pair<IPid,BlockedAwait> *await_jump = nullptr;
    for (auto &addr_awaits : blocking_awaits) {
      const SymAddrSize &addr = addr_awaits.first;
      for (auto &pid_cond : addr_awaits.second) {
        BlockedAwait &aw = pid_cond.second;
        assert(!aw.pinned);
        /* XXX: Unnecessary insertion */
        aw.read_from = mem[addr.addr].last_update;
        const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> &decision
          = aw.read_from == -1 ? nullptr : prefix[aw.read_from].event;
        if (aw.decision_ptr && aw.decision_ptr->unfold_node != decision.get()
            && (!jump_depth || aw.decision_ptr->depth < *jump_depth)) {
          assert(aw.planned_read_from &&
                 *aw.planned_read_from != aw.read_from);
          jump_depth = aw.decision_ptr->depth;
          await_jump = &pid_cond;
          first_jump_is_await = true;
        }
      }
    }

    std::exchange(deepest_node, work_item);

    /* Go to the right place in the decision tree for the jump */
    std::vector<bool> jump_keep;
    assert(jump_depth);
    {
      std::shared_ptr<DecisionNode> *node;
      if (conf.debug_print_on_reset)
        llvm::dbgs() << "Handling decision jump at depth " << *jump_depth << "\n";
      int read_from;
      if (first_jump_is_await) {
        node = &await_jump->second.decision_ptr;
        read_from = await_jump->second.read_from;
        if (conf.debug_print_on_reset)
          llvm::dbgs() << "Blocked await "
                       << iid_string(*await_jump)
                       << " now reading "
                       << (read_from != -1 ? iid_string(read_from) : "init") << "\n";
      } else {
        unsigned ix = *prefix_first_unblock_jump;
        node = &prefix[ix].decision_ptr;
        read_from = *prefix[ix].read_from;
        if (conf.debug_print_on_reset)
          llvm::dbgs() << "Await " << iid_string(ix) << " unblocked reading "
                       << (read_from != -1 ? iid_string(read_from) : "init") << "\n";
      }
      const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> &decision
        = read_from == -1 ? nullptr : prefix[read_from].event;
      if (!(*node)->try_alloc_unf(decision)) {
        if (conf.debug_print_on_reset)
          llvm::dbgs() << "This is redundant, bailing out\n";
        was_redundant = true;
        return;
      } else {
        /* Ugly, but we can't use construct_sibling() since it adds the
         * new node to the scheduler queue (!) */
        *node = (*node)->make_sibling(decision.get(), Leaf());
      }
      jump_keep = causal_past((*node)->depth, TraceOverlay(this, {}), true);
      deepest_node = *node;
    }

    /* Assign new decision pointers to prefix */
    for (unsigned i = 0; i < prefix.size(); ++i) {
      if (jump_keep[i]) {
        if (prefix[i].decision_ptr && prefix[i].get_decision_depth() <= *jump_depth) {
          /* Keep it */
          assert(prefix[i].decision_ptr->unfold_node == prefix[i].event->read_from.get());
        } else {
          prefix[i].set_decision(nullptr);
          /* For consistency, we should not set non-decision-nodes as pinned */
          if (is_load(i)) prefix[i].pinned = true;
        }
      } else {
        if (is_load(i)) {
          assert(prefix[i].get_decision_depth() == -1
                 || prefix[i].get_decision_depth() > *jump_depth);
          prefix[i].pinned = false;
          const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> &decision
            = is_lock_type(i) ? prefix[i].event : prefix[i].event->read_from;
          deepest_node = decision_tree.new_decision_node(std::move(deepest_node), decision);
          prefix[i].set_decision(deepest_node);
        } else {
          assert(!prefix[i].pinned);
          assert(!prefix[i].decision_ptr);
        }
      }
    }

    /* Assign new decision pointers to blocking awaits */
    for (auto &addr_awaits : blocking_awaits) {
      for (auto &pid_cond : addr_awaits.second) {
        BlockedAwait &aw = pid_cond.second;
        assert(!aw.pinned);
        const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> &decision
          = aw.read_from == -1 ? nullptr : prefix[aw.read_from].event;
        if (aw.decision_ptr && aw.decision_ptr->depth <= *jump_depth) {
          assert(aw.decision_ptr->unfold_node == decision.get());
        } else {
          deepest_node = decision_tree.new_decision_node(std::move(deepest_node), decision);
          aw.decision_ptr = deepest_node;
        }
      }
    }
    work_item = std::move(deepest_node);
    plan(top_clock(), {});
  }
}

std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> RFSCTraceBuilder::
unfold_find_unfolding_node(IPid p, int index, Option<int> prefix_rf) {
  const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> null_ptr;
  const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> *parent;
  if (index == 1) {
    parent = &null_ptr;
  } else {
    int par_idx = find_process_event(p, index-1);
    parent = &prefix[par_idx].event;
  }
  const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> *read_from = &null_ptr;
  if (prefix_rf && *prefix_rf != -1) {
    read_from = &prefix[*prefix_rf].event;
  }
  return unfolding_tree.find_unfolding_node(threads[p].cpid, *parent,
                                            *read_from);
}


std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode>
RFSCTraceBuilder::unfold_alternative
(unsigned i, const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> &read_from) {
  std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> &parent
    = prefix[i].event->parent;
  IPid p = prefix[i].iid.get_pid();

  return unfolding_tree.find_unfolding_node(threads[p].cpid, parent, read_from);
}

bool RFSCTraceBuilder::record_symbolic(SymEv event){
  if (!replay) {
    assert(!seen_effect);
    /* New event */
    curev().sym = std::move(event);
    seen_effect = true;
  } else {
    /* Replay. SymEv::set() asserts that this is the same event as last time. */
    SymEv &last = curev().sym;
    assert(!seen_effect);
    if (!last.is_compatible_with(event)) {
      auto pid_str = [this](IPid p) { return threads[p].cpid.to_string(); };
      nondeterminism_error("Event with effect " + last.to_string(pid_str)
                           + " became " + event.to_string(pid_str)
                           + " when replayed");
      return false;
    }
    last = event;
    seen_effect = true;
  }
  return true;
}

static bool symev_is_lock_type(const SymEv &e) {
  return e.kind == SymEv::M_INIT  || e.kind == SymEv::M_LOCK
    || e.kind == SymEv::M_TRYLOCK || e.kind == SymEv::M_TRYLOCK_FAIL
    || e.kind == SymEv::M_UNLOCK  || e.kind == SymEv::M_DELETE;
}

static bool symev_is_load(const SymEv &e) {
  return e.kind == SymEv::LOAD || e.kind == SymEv::LOAD_AWAIT
    || e.kind == SymEv::RMW
    || e.kind == SymEv::CMPXHG || e.kind == SymEv::CMPXHGFAIL
    || symev_is_lock_type(e);
}

static bool is_load(const RFSCTraceBuilder::TraceOverlay &trace, unsigned i) {
  return symev_is_load(trace.prefix_at(i).sym());
}

bool RFSCTraceBuilder::is_load(unsigned i) const {
  return symev_is_load(prefix[i].sym);
}

bool RFSCTraceBuilder::is_lock(unsigned i) const {
  return prefix[i].sym.kind == SymEv::M_LOCK;
}

bool RFSCTraceBuilder::does_lock(unsigned i) const {
  auto kind = prefix[i].sym.kind;
  return kind == SymEv::M_LOCK || kind == SymEv::M_TRYLOCK;
}

bool RFSCTraceBuilder::is_trylock_fail(unsigned i) const {
  return prefix[i].sym.kind == SymEv::M_TRYLOCK_FAIL;
}

bool RFSCTraceBuilder::is_unlock(unsigned i) const {
  return prefix[i].sym.kind == SymEv::M_UNLOCK;
}

bool RFSCTraceBuilder::is_minit(unsigned i) const {
  return prefix[i].sym.kind == SymEv::M_INIT;
}

bool RFSCTraceBuilder::is_mdelete(unsigned i) const {
  return prefix[i].sym.kind == SymEv::M_DELETE;
}

bool RFSCTraceBuilder::is_lock_type(unsigned i) const {
  return symev_is_lock_type(prefix[i].sym);
}

static bool symev_is_store(const SymEv &e) {
  return e.kind == SymEv::STORE || e.kind == SymEv::CMPXHG
    || e.kind == SymEv::RMW || symev_is_lock_type(e);
}

static bool is_store(const RFSCTraceBuilder::TraceOverlay &trace, unsigned i) {
  return symev_is_store(trace.prefix_at(i).sym());
}

bool RFSCTraceBuilder::is_store(unsigned i) const {
  return symev_is_store(prefix[i].sym);
}

bool RFSCTraceBuilder::is_cmpxhgfail(unsigned i) const {
  return prefix[i].sym.kind == SymEv::CMPXHGFAIL;
}

bool RFSCTraceBuilder::is_store_when_reading_from(unsigned i, int read_from) const {
  const SymEv &e = prefix[i].sym;
  if (e.kind == SymEv::STORE || e.kind == SymEv::RMW || symev_is_lock_type(e))
    return true;
  if (e.kind != SymEv::CMPXHG && e.kind != SymEv::CMPXHGFAIL) return false;
  SymData expected = e.expected();
  SymData actual = get_data(read_from, e.addr());
  assert(e.addr() == actual.get_ref());
  return memcmp(expected.get_block(), actual.get_block(), e.addr().size) == 0;
}

static SymAddrSize symev_get_addr(const SymEv &e) {
  if (e.has_addr()) {
    return e.addr();
  }
  abort();
}

static SymAddrSize get_addr(const RFSCTraceBuilder::TraceOverlay &trace, unsigned i) {
  return symev_get_addr(trace.prefix_at(i).sym());
}

SymAddrSize RFSCTraceBuilder::get_addr(unsigned i) const {
  return symev_get_addr(prefix[i].sym);
}

static SymData get_data(const RFSCTraceBuilder::TraceOverlay &trace, int i,
                        const SymAddrSize &addr) {
  if (i == -1) {
    SymData ret(addr, addr.size);
    memset(ret.get_block(), 0, addr.size);
    return ret;
  }
  const SymEv &e = trace.prefix_at(i).sym();
  assert(e.has_data());
  assert(e.addr() == addr);
  return e.data();
}

SymData RFSCTraceBuilder::get_data(int i, const SymAddrSize &addr) const {
  return ::get_data(TraceOverlay(this, {}), i, addr);
}

bool RFSCTraceBuilder::rf_satisfies_cond(const TraceOverlay &trace, int r, int w) {
  assert(::is_load(trace, r));
  const SymEv &re = trace.prefix_at(r).sym();
  if (!re.has_cond()) return true;
  return re.cond().satisfied_by(::get_data(trace, w, re.addr()));
}

bool RFSCTraceBuilder::rf_satisfies_cond(int r, int w) const {
  return rf_satisfies_cond(TraceOverlay(this, {}), r, w);
}

static std::ptrdiff_t delete_from_back(gen::vector<int> &vec, int val) {
  for (auto ix = vec.size();;) {
    assert(ix != 0 && "Element must exist");
    --ix;
    if (val == vec[ix]) {
      std::swap(vec.mut(ix), vec.mut(vec.size()-1));
      vec.pop_back();
      return ix;
    }
  }
}

void RFSCTraceBuilder::
recompute_cmpxhg_success(unsigned idx, TraceOverlay &trace) const {
  auto &ev = trace.prefix_mut(idx);
  SymEv &e = ev.sym;
  if (e.kind == SymEv::M_TRYLOCK || e.kind == SymEv::M_TRYLOCK_FAIL) {
    bool before = e.kind == SymEv::M_TRYLOCK;
    bool after = *ev.read_from == -1 || !does_lock(*ev.read_from);
    SymAddrSize addr = e.addr();
    gen::vector<int> &writes = trace.writes_by_addr.mut(addr.addr);
    if (after && !before) {
      e = SymEv::MTryLock(addr);
      writes.push_back(idx);
    } else if (before && !after) {
      e = SymEv::MTryLockFail(addr);
      delete_from_back(writes, idx);
    }
    return;
  }
  if (e.kind != SymEv::CMPXHG && e.kind != SymEv::CMPXHGFAIL) {
    return;
  }
  SymAddrSize addr = e.addr();
  gen::vector<int> &writes = trace.writes_by_addr.mut(addr.addr);
  bool before = e.kind == SymEv::CMPXHG;
  SymData expected = e.expected();
  SymData actual = get_data(*ev.read_from, addr);
  bool after = memcmp(expected.get_block(), actual.get_block(), addr.size) == 0;
  if (after) {
    e = SymEv::CmpXhg(e.data(), e.expected().get_shared_block());
  } else {
    e = SymEv::CmpXhgFail(e.data(), e.expected().get_shared_block());
  }
  // assert(recompute_cmpxhg_success(idx, writes).kind == CmpXhgUndoLog::NONE);
  if (after && !before) {
    writes.push_back(idx);
  } else if (before && !after) {
    delete_from_back(writes, idx);
  }
}

bool RFSCTraceBuilder::happens_before(const Event &e,
                                     const VClock<int> &c) const {
  return c.includes(e.iid);
}

bool RFSCTraceBuilder::can_rf_by_vclocks
(int r, int ow, int w) const {
  /* Is the write after the read? */
  if (w != -1 && happens_before(prefix[r], prefix[w].clock)) abort();

  /* Is the original write always before the read, and the new write
   * before the original?
   */
  if (ow != -1 && (w == -1 || happens_before(prefix[w], prefix[ow].clock))) {
    if (happens_before(prefix[ow], prefix[r].above_clock)) return false;
  }

  return true;
}

bool RFSCTraceBuilder::
can_swap_by_vclocks(int r, const VClock<IPid> &w_above_clock) const {
  if (happens_before(prefix[r], w_above_clock)) return false;
  return true;
}

bool RFSCTraceBuilder::can_swap_by_vclocks(int r, int w) const {
  return can_swap_by_vclocks(r, prefix[w].above_clock);
}

bool RFSCTraceBuilder::can_swap_lock_by_vclocks(int f, int u, int s) const {
  if (happens_before(prefix[f], prefix[s].above_clock)) return false;
  return true;
}

void RFSCTraceBuilder::compute_prefixes() {
  prefix_idx = int(prefix.size());
  Timing::Guard analysis_timing_guard(analysis_context);
  compute_vclocks();

  compute_unfolding_and_plan();
}

void RFSCTraceBuilder::plan(VClock<IPid> horizon,
                            std::vector<unsigned> blocked_in_prefix) {
  if(conf.debug_print_on_reset){
    llvm::dbgs() << " === RFSCTraceBuilder state ===\n";
    debug_print(horizon);
    llvm::dbgs() << " ==============================\n";
  }

  Timing::Guard neighbours_timing_guard(neighbours_context);
  if (conf.debug_print_on_reset)
    llvm::dbgs() << "Computing prefixes (horizon = " << horizon << ")\n";

  auto pretty_index_t = [this] (const TraceOverlay &trace, int i) -> std::string {
    if (i==-1) return "init event";
    return std::to_string(trace.prefix_at(i).decision_depth()) // + "("
      // + std::to_string(trace.prefix_at(i).unf_node()->seqno) + "):"
      + iid_string(trace, i) + trace.prefix_at(i).sym().to_string();
  };
  auto pretty_index = [&] (int i) -> std::string {
    return pretty_index_t(TraceOverlay(this, {}), i);
  };


  gen::map<SymAddr,gen::vector<int>> writes_by_address;
  std::map<SymAddr,std::vector<int>> cmpxhgfail_by_address;
  std::vector<std::unordered_map<SymAddr,std::vector<unsigned>>>
    writes_by_process_and_address(threads.size());
  for (unsigned j = 0; j < prefix.size(); ++j) {
    if (horizon.reverse_includes(prefix[j].iid)) continue;
    if (is_store(j))      writes_by_address.mut(get_addr(j).addr).push_back(j);
    if (is_store(j))
      writes_by_process_and_address[prefix[j].iid.get_pid()][get_addr(j).addr]
        .push_back(j);
    if (is_cmpxhgfail(j)) cmpxhgfail_by_address[get_addr(j).addr].push_back(j);
  }
  // for (std::pair<SymAddr,std::vector<int>> &pair : writes_by_address) {
  //   pair.second.push_back(-1);
  // }

  TraceOverlay horizon_overlay(this, writes_by_address);
  for (unsigned p = 0; p < threads.size(); ++p) {
    if (horizon[p] < threads[p].last_event_index()) {
      const int i = find_process_event(p, horizon[p]);
      auto &e = horizon_overlay.prefix_mut(i);
      if (e.iid.get_index() < horizon[p]) {
        e.size = 1;
        e.modified = true;
        if (conf.debug_print_on_reset)
          llvm::dbgs() << "Truncating " << i << " by horizon\n";
      } else {
        assert(e.iid.get_index() == horizon[p]);
        e.deleted = true;
        if (conf.debug_print_on_reset)
          llvm::dbgs() << "Deleting " << i << " by horizon\n";
      }
    }
  }
  for (unsigned i : blocked_in_prefix) {
    auto &e = horizon_overlay.prefix_mut(i);
    assert(!e.pinned);
    e.modified = false; // We're deleting it now
    e.deleted = true;
    SymAddrSize addr = e.sym.addr();
    AwaitCond cond = e.sym.cond();
    auto ret = horizon_overlay.blocking_awaits[addr].try_emplace
      (e.iid.get_pid(), e.iid.get_index(), cond);
    assert(ret.second);
    BlockedAwait &aw = ret.first->second;
    assert(e.decision_ptr == prefix[i].decision_ptr.get());
    aw.decision_ptr = prefix[i].decision_ptr;
    aw.read_from = *e.read_from;
    aw.deleted_unblocked_position_in_prefix = i;
  }

  /* See if any blocking await can be satisfied */
  for (auto &addr_awaits : horizon_overlay.blocking_awaits) {
    const SymAddrSize &addr = addr_awaits.first;
    for (auto &pid_cond : addr_awaits.second) {
      TraceOverlay ol(horizon_overlay);
      IPid pid = pid_cond.first;
      const BlockedAwait &aw = pid_cond.second;
      const AwaitCond &cond = aw.cond;
      assert(unsigned(prefix_idx) == prefix.size());
      auto iidx = pid_cond.second.index;
      unsigned i = aw.deleted_unblocked_position_in_prefix.value_or(prefix_idx);
      TraceOverlay::TraceEvent *ep;
      if (aw.deleted_unblocked_position_in_prefix) {
        ep = &ol.prefix_mut(i);
        ep->deleted = false;
        ep->modified = true;
        ep->size = 1;
        assert(!ep->pinned);
        assert(ep->iid == IID<IPid>(pid, iidx));
        assert(ep->sym == SymEv::LoadAwait(addr, cond));
      } else {
        ep = &ol.prefix_emplace_back(IID<IPid>(pid, iidx),
                                     SymEv::LoadAwait(addr, cond));
      }
      auto &e = *ep;
      maybe_add_spawn_happens_after(e);
      ol.blocking_awaits[addr].erase(pid);

      const std::shared_ptr<DecisionNode> &decision = pid_cond.second.decision_ptr;
      e.decision_ptr = decision.get();

      auto try_read_from = [&](int j) {
          assert(1);
          if (!rf_satisfies_cond(ol, i, j)) return;
          const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> &alt
            = j == -1 ? nullptr : prefix[j].event;
          assert(decision);
          /* XXX: Inefficiency: we could transfer reference ownership into here */
          if (!decision->try_alloc_unf(alt)) return;

          if (conf.debug_print_on_reset)
            llvm::dbgs() << "Trying to satisfy deadlocked " << pretty_index_t(ol, i)
                         << " reading from " << pretty_index_t(ol, j);
          e.read_from = j;

          Leaf solution = try_sat(i, ol);
          if (solution.is_bottom()) return;

          /* We can satisfy this await. Commit to the decision node we
           * allocated above and immediately start exploring this new
           * trace. */
          decision_tree.construct_sibling(*decision, alt.get(),
                                          std::move(solution));
          tasks_created++;
        };

      const VClock<IPid> above = compute_above_clock(e);

      try_read_from(-1);
      for (unsigned p = 0; p < threads.size(); ++p) {
        const std::vector<unsigned> &writes
          = writes_by_process_and_address[p][addr.addr];
        auto start = std::upper_bound(writes.begin(), writes.end(), above[p],
                                      [this](int index, unsigned w) {
                                        return index < prefix[w].iid.get_index();
                                      });
        if (start != writes.begin()) --start;
        for (auto it = start; it != writes.end(); ++it) {
          try_read_from(*it);
        }
      }

      assert(prefix_idx == int(prefix.size()));
    }
  }

  assert(prefix_idx == int(prefix.size()));
  /* No. Proceed with */
  for (unsigned i = 0; i < prefix.size(); ++i) {
    if (horizon.reverse_includes(prefix[i].iid)) continue;
    auto try_swap = [&](int i, int j) {
        int original_read_from = *prefix[i].read_from;
        std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> alt
          = unfold_alternative(j, prefix[i].event->read_from);
        DecisionNode &decision = *prefix[i].decision_ptr;
        // Returns false if unfolding node is already known and therefore does not have to be further evaluated
        if (!decision.try_alloc_unf(alt)) return;
        if (!can_swap_by_vclocks(i, j)) return;
        if (conf.debug_print_on_reset) {
          llvm::dbgs() << "Trying to swap " << pretty_index(i)
                       << " and " << pretty_index(j)
                       << ", after " << pretty_index(original_read_from);
        }
        TraceOverlay ol(horizon_overlay, {unsigned(i), unsigned(j)});
        ol.prefix_mut(j).read_from = original_read_from;
        ol.prefix_mut(i).decision_swap(ol.prefix_mut(j));

        Leaf solution = try_sat(j, ol);
        if (!solution.is_bottom()) {
          decision_tree.construct_sibling(decision, alt.get(),
                                          std::move(solution));
          tasks_created++;
        }
      };
    auto try_swap_lock = [&](int i, int unlock, int j) {
        assert(does_lock(i) && is_unlock(unlock) && is_lock(j)
               && *prefix[j].read_from == int(unlock));
        std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> alt
          = unfold_alternative(j, prefix[i].event->read_from);
        DecisionNode &decision = *prefix[i].decision_ptr;
        if (!decision.try_alloc_unf(alt)) return;
        if (!can_swap_lock_by_vclocks(i, unlock, j)) return;
        int original_read_from = *prefix[i].read_from;
        if (conf.debug_print_on_reset)
          llvm::dbgs() << "Trying to swap " << pretty_index(i)
                       << " and " << pretty_index(j)
                       << ", after " << pretty_index(original_read_from);
        TraceOverlay ol(horizon_overlay, {unsigned(i), unsigned(j)});
        ol.prefix_mut(j).read_from = original_read_from;
        ol.prefix_mut(i).decision_swap(ol.prefix_mut(j));

        Leaf solution = try_sat(j, ol);
        if (!solution.is_bottom()) {
          decision_tree.construct_sibling(decision, alt.get(),
                                          std::move(solution));
          tasks_created++;
        }
      };
    auto try_swap_blocked = [&](int i, IPid jp, SymEv sym) {
        int original_read_from = *prefix[i].read_from;
        auto jidx = threads[jp].last_event_index()+1;
        std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> alt
          = unfold_find_unfolding_node(jp, jidx, original_read_from);
        DecisionNode &decision = *prefix[i].decision_ptr;
        if (!decision.try_alloc_unf(alt)) return;
        /* Ouch. We should do this on TraceOverlay instead. The blocker
         * is the can_swap_by_vclocks use below. */
        int j = prefix_idx++;
        assert(prefix.size() == size_t(j));
        prefix.emplace_back(IID<IPid>(jp, jidx), 0, std::move(sym));
        prefix[j].event = alt; // Only for debug print
        threads[jp].event_indices.push_back(j); // Not needed?
        maybe_add_spawn_happens_after(j);
        compute_above_clock(j);
        horizon_overlay._prefix_size++;

        if (can_swap_by_vclocks(i, j)) {
          if (conf.debug_print_on_reset)
            llvm::dbgs() << "Trying to replace " << pretty_index(i)
                         << " with deadlocked " << pretty_index(j)
                         << ", after " << pretty_index(original_read_from);
          TraceOverlay ol(horizon_overlay, {unsigned(i), unsigned(j)});
          ol.prefix_mut(j).read_from = original_read_from;
          ol.prefix_mut(i).decision_swap(ol.prefix_mut(j));
          assert(!ol.prefix_at(i).pinned());
          ol.prefix_mut(i).pinned = true;
          ol.prefix_mut(i).deleted = true;

          Leaf solution = try_sat(j, ol);
          if (!solution.is_bottom()) {
            decision_tree.construct_sibling(decision, alt.get(),
                                            std::move(solution));
            tasks_created++;
          }
        }

        /* Delete j */
        threads[jp].event_indices.pop_back();
        prefix.pop_back();
        horizon_overlay._prefix_size--;
        --prefix_idx;
      };
    if (!prefix[i].pinned && is_lock_type(i)) {
      Timing::Guard ponder_mutex_guard(ponder_mutex_context);
      auto addr = get_addr(i);
      const gen::vector<int> &accesses = writes_by_address[addr.addr];
      auto next = std::upper_bound(accesses.begin(), accesses.end(), i);
      if (next == accesses.end()) {
        if (does_lock(i)) {
          for (IPid other : mutex_deadlocks[addr.addr]) {
            try_swap_blocked(i, other, SymEv::MLock(addr));
          }
        }
        continue;
      }
      unsigned j = *next;
      assert(*prefix[j].read_from == int(i));
      if (is_unlock(i) && is_lock(j)) continue;

      try_swap(i, j);

      if (!does_lock(i)) continue;
      while (is_trylock_fail(*next)) {
        if (++next == accesses.end()) break;
      }
      if (next == accesses.end() || !is_unlock(*next)) continue;
      unsigned unlock = *next;
      if (++next == accesses.end()) continue;
      unsigned relock = *next;
      if (!is_lock(relock)) continue;
      try_swap_lock(i, unlock, relock);
    } else if (!prefix[i].pinned && is_load(i)) {
      auto addr = get_addr(i);
      const gen::vector<int> &possible_writes = writes_by_address[addr.addr];
      int original_read_from = *prefix[i].read_from;
      assert(std::any_of(possible_writes.begin(), possible_writes.end(),
             [=](int i) { return i == original_read_from; })
           || original_read_from == -1);

      DecisionNode &decision = *prefix[i].decision_ptr;

      auto try_read_from_rmw = [&](int j) {
        Timing::Guard analysis_timing_guard(try_read_from_context);
        assert(j != -1 && j > int(i) && is_store(i) && is_load(j)
               && is_store_when_reading_from(j, original_read_from));
        /* Can only swap ajacent RMWs */
        if (*prefix[j].read_from != int(i)) return;
        std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> read_from
          = unfold_alternative(j, prefix[i].event->read_from);
        if (!decision.try_alloc_unf(read_from)) return;
        if (!can_swap_by_vclocks(i, j)) return;
        if (conf.debug_print_on_reset)
          llvm::dbgs() << "Trying to swap " << pretty_index(i)
                       << " and " << pretty_index(j)
                       << ", reading from " << pretty_index(original_read_from);
        TraceOverlay ol(horizon_overlay, {i, unsigned(j)});
        ol.prefix_mut(j).read_from = original_read_from;
        ol.prefix_mut(i).read_from = j;
        recompute_cmpxhg_success(j, ol);
        recompute_cmpxhg_success(i, ol);

        Leaf solution = try_sat(i, ol);
        if (!solution.is_bottom()) {
          decision_tree.construct_sibling(decision, read_from.get(),
                                          std::move(solution));
          tasks_created++;
        }
      };
      auto try_read_from = [&](int j) {
        Timing::Guard analysis_timing_guard(try_read_from_context);
        if (j == original_read_from || j == int(i)) return;
        if (j != -1 && j > int(i) && is_store(i) && is_load(j)) {
          if (!is_store_when_reading_from(j, original_read_from)) return;
          /* RMW pair */
          try_read_from_rmw(j);
        } else {
          const std::shared_ptr<RFSCUnfoldingTree::UnfoldingNode> &read_from =
            j == -1 ? nullptr : prefix[j].event;
          if (!decision.try_alloc_unf(read_from)) return;
          if (!can_rf_by_vclocks(i, original_read_from, j))
            return;
          if (conf.debug_print_on_reset)
            llvm::dbgs() << "Trying to make " << pretty_index(i)
                         << " read from " << pretty_index(j)
                         << " instead of " << pretty_index(original_read_from);
          TraceOverlay ol(horizon_overlay, {unsigned(i)});
          last_change_ty last_change;
          if (!rf_satisfies_cond(i, j)) {
            ol.prefix_mut(i).deleted = true;
            const auto &addr = get_addr(i);
            const IID<IPid> iid = prefix[i].iid;
            auto ret =
              ol.blocking_awaits[addr].try_emplace
              (iid.get_pid(), iid.get_index(), prefix[i].sym.cond());
            assert(ret.second);
            ret.first->second.read_from = j;
            ret.first->second.decision_ptr = prefix[i].decision_ptr;
            assert(ret.first->second.get_decision_depth()
                   == prefix[i].get_decision_depth());
            last_change = BlockedChange{addr, iid.get_pid()};
          } else {
            ol.prefix_mut(i).read_from = j;
            recompute_cmpxhg_success(i, ol);
            last_change = i;
          }

          Leaf solution = try_sat(last_change, ol);
          if (!solution.is_bottom()) {
            decision_tree.construct_sibling(decision, read_from.get(), std::move(solution));
            tasks_created++;
          }
        }
      };

      const VClock<IPid> &above = prefix[i].above_clock;
      const auto below = below_clocks[i];
      for (unsigned p = 0; p < threads.size(); ++p) {
        const std::vector<unsigned> &writes
          = writes_by_process_and_address[p][addr.addr];
        auto start = std::upper_bound(writes.begin(), writes.end(), above[p],
                                      [this](int index, unsigned w) {
                                        return index < prefix[w].iid.get_index();
                                      });
        if (start != writes.begin()) --start;

        auto end = std::lower_bound(writes.begin(), writes.end(), below[p],
                                    [this](unsigned w, int index) {
                                      return prefix[w].iid.get_index() < index;
                                    });
        /* Ugly hack:
         * If i and *end are rmw's, we need to consider swapping i and
         * *end. Since this is considered by calling
         * try_read_from(*end), we make sure that *end is not filtered
         * here, even though it's not in the visible set.
         */
        if (is_store(i) && end != writes.end() && is_load(*end)) ++end;
        assert(start <= end);
        for (auto it = start; it != end; ++it) {
          assert(!horizon.reverse_includes(prefix[*it].iid));
          try_read_from(*it);
        }
      }
      try_read_from(-1);
      if (is_store(i)) {
        for (int j : cmpxhgfail_by_address[addr.addr]) {
          if (j > int(i) && is_store_when_reading_from(j, original_read_from)) {
            try_read_from_rmw(j);
          }
        }
      }
    }
  }
}

void RFSCTraceBuilder::output_formula
(SatSolver &sat, const TraceOverlay &trace,
 const std::vector<bool> &keep){
  unsigned no_keep = 0;
  std::vector<unsigned> var;
  for (unsigned i = 0; i < trace.prefix_size(); ++i) {
    var.push_back(no_keep);
    if (keep[i]) no_keep++;
  }

  sat.alloc_variables(no_keep);
  /* PO */
  for (unsigned i = 0; i < trace.prefix_size(); ++i) {
    if (!keep[i]) continue;
    if (Option<unsigned> pred = trace.po_predecessor(i)) {
      assert(*pred != i);
      sat.add_edge(var[*pred], var[i]);
    }
  }

  /* Read-from and SC consistency */
  for (unsigned r = 0; r < trace.prefix_size(); ++r) {
    if (!keep[r] || !trace.prefix_at(r).read_from()) continue;
    int w = *trace.prefix_at(r).read_from();
    assert(int(r) != w);
    if (w == -1) {
      for (int j : trace.writes_by_addr[::get_addr(trace, r).addr]) {
        if (j == int(r) || !keep[j]) continue;
        sat.add_edge(var[r], var[j]);
      }
    } else {
      sat.add_edge(var[w], var[r]);
      for (int j : trace.writes_by_addr[::get_addr(trace, r).addr]) {
        if (j == w || j == int(r) || !keep[j]) continue;
        sat.add_edge_disj(var[j], var[w],
                          var[r], var[j]);
      }
    }
  }

  /* Other happens-after edges (such as thread spawn and join) */
  for (unsigned i = 0; i < trace.prefix_size(); ++i) {
    if (!keep[i]) continue;
    for (unsigned j : trace.prefix_at(i).happens_after()) {
      sat.add_edge(var[j], var[i]);
    }
  }
}

template<typename T, typename F> auto map(const std::vector<T> &vec, F f)
  -> std::vector<typename std::result_of<F(const T&)>::type> {
  std::vector<typename std::result_of<F(const T&)>::type> ret;
  ret.reserve(vec.size());
  for (const T &e : vec) ret.emplace_back(f(e));
  return ret;
}

template<typename F> auto map(const RFSCTraceBuilder::TraceOverlay &vec, F f)
  -> std::vector<typename std::result_of<F(RFSCTraceBuilder::TraceOverlay::TraceEventConstRef)>::type> {
  std::vector<typename std::result_of<F(RFSCTraceBuilder::TraceOverlay::TraceEventConstRef)>::type> ret;
  ret.reserve(vec.prefix_size());
  for (unsigned i = 0; i < vec.prefix_size(); ++i)
    ret.emplace_back(f(vec.prefix_at(i)));
  return ret;
}

static void add_event_to_graph(SaturatedGraph &g, const RFSCTraceBuilder::TraceOverlay &trace, unsigned i) {
  SaturatedGraph::EventKind kind = SaturatedGraph::NONE;
  SymAddr addr;
  if (is_load(trace, i)) {
    if (is_store(trace, i)) kind = SaturatedGraph::RMW;
    else kind = SaturatedGraph::LOAD;
  } else if (is_store(trace, i)) {
    kind = SaturatedGraph::STORE;
  }
  if (kind != SaturatedGraph::NONE)
    addr = get_addr(trace, i).addr;
  Option<IID<int>> read_from;
  if (trace.prefix_at(i).read_from() && *trace.prefix_at(i).read_from() != -1)
    read_from = trace.prefix_at(*trace.prefix_at(i).read_from()).iid();
  IID<int> iid = trace.prefix_at(i).iid();
  g.add_event(iid.get_pid(), iid, kind, addr,
              read_from, map(trace.prefix_at(i).happens_after(),
                             [&trace](unsigned j){return trace.prefix_at(j).iid();}));
}

const SaturatedGraph &RFSCTraceBuilder::get_cached_graph
(DecisionNode &decision, const TraceOverlay &trace) const {
  const int depth = decision.depth;
  return decision.get_saturated_graph(
    [this, depth, &trace](SaturatedGraph &g) {
      std::vector<bool> keep = causal_past(depth-1, trace);
      for (unsigned i = 0; i < trace.prefix_size(); ++i) {
        if (keep[i] && !g.has_event(trace.prefix_at(i).iid())) {
          add_event_to_graph(g, trace, i);
        }
      }

      IFDEBUG(bool g_acyclic = ) g.saturate();
      assert(g_acyclic);
    });
}

Leaf
RFSCTraceBuilder::try_sat
(last_change_ty last_change, const TraceOverlay &trace){
  Timing::Guard timing_guard(graph_context);
  DecisionNode *decision;
  if (last_change.which() == LastChangeKind::PREFIX) {
    decision = trace.prefix_at(boost::get<unsigned>(last_change)).decision_ptr();
  } else {
    const BlockedChange &c = boost::get<BlockedChange>(last_change);
    decision = trace.blocking_awaits.at(c.addr).at(c.pid).decision_ptr.get();
  }
  int decision_depth = decision->depth;
  filtered_awaits_ty awaits;
  std::vector<bool> keep = prefix_keep(decision_depth, trace, awaits);

  /* Caching not implemented for blocked awaits */
  SaturatedGraph g; // (get_cached_graph(decision, trace).clone());
  for (unsigned i = 0; i < trace.prefix_size(); ++i) {
    if (keep[i] && (last_change.which() != LastChangeKind::PREFIX
                    || i != boost::get<unsigned>(last_change))
        && !g.has_event(trace.prefix_at(i).iid())) {
      add_event_to_graph(g, trace, i);
    }
  }
  if (last_change.which() == LastChangeKind::PREFIX) {
    add_event_to_graph(g, trace, boost::get<unsigned>(last_change));
  }
  if (!awaits.empty()) {
    /* All awaits happen after all other events. */
    std::vector<IID<IPid>> happens_after;
    happens_after.reserve(threads.size());
    for (IPid p = 0; p < IPid(threads.size()); ++p) {
      const auto &eis = threads[p].event_indices;
      auto lb = std::lower_bound(eis.begin(), eis.end(), keep,
                                 [](unsigned ix, const std::vector<bool> &keep) {
                                   return keep[ix];
                                 });
      if (lb != eis.begin()) {
        assert(keep[lb[-1]]);
        happens_after.emplace_back(trace.prefix_at(lb[-1]).iid());
      }
    }
    for (const auto &await : awaits) {
      IPid pid = await.pid_await.first;
      Option<IID<IPid>> read_from;
      if (await.pid_await.second.read_from != -1) {
        const auto &w = trace.prefix_at(await.pid_await.second.read_from);
        if (conf.debug_print_on_reset) {
          llvm::dbgs() << "Await by " << threads[pid].cpid << " reading "
                       << await.pid_await.second.read_from << "\n";
        }
        read_from = w.iid();
        assert(w.sym().addr() == await.addr);
      }
      IID<IPid> iid(pid, await.pid_await.second.index);
      g.add_event(pid, iid, SaturatedGraph::LOAD, await.addr.addr, read_from,
                  happens_after);
    }
  }
  if (!g.saturate()) {
    if (conf.debug_print_on_reset)
      llvm::dbgs() << ": Saturation yielded cycle\n";
    return Leaf();
  }
  std::vector<IID<int>> current_exec;
  current_exec.reserve(trace.prefix_size());
  for (unsigned i = 0; i < trace.prefix_size(); ++i) {
    if (keep[i]) {
      const TraceOverlay::TraceEventConstRef e = trace.prefix_at(i);
      assert(!e.deleted());
      current_exec.push_back(e.iid());
    }
  }
  /* We need to preserve g */
  if (Option<std::vector<IID<int>>> res
      = try_generate_prefix(std::move(g), std::move(current_exec))) {
    if (conf.debug_print_on_reset) {
      llvm::dbgs() << ": Heuristic found prefix\n";
      llvm::dbgs() << "[";
      for (IID<int> iid : *res) {
        llvm::dbgs() << iid_string(trace, iid) << ",";
      }
      if (!awaits.empty()) {
        llvm::dbgs() << " ";
        for (const auto &aw : awaits) {
          llvm::dbgs() << iid_string(aw.pid_await) << ",";
        }
      }
      llvm::dbgs() << "]\n";
    }
    assert(res->size() == std::size_t(std::count(keep.begin(), keep.end(), true)));
    std::vector<unsigned> order = map(*res, [&trace](IID<int> iid) {
      return trace.find_process_event(iid.get_pid(), iid.get_index());
    });
    return order_to_leaf(decision_depth, trace, std::move(order), awaits);
  }

  assert(awaits.empty());
  std::unique_ptr<SatSolver> sat = conf.get_sat_solver();
  {
    Timing::Guard timing_guard(sat_context);

    // XXX: We're not outputting blocked awaits
    output_formula(*sat, trace, keep);
    //output_formula(std::cerr, writes_by_address, keep);

    if (!sat->check_sat()) {
      if (conf.debug_print_on_reset) llvm::dbgs() << ": UNSAT\n";
      return Leaf();
    }
    if (conf.debug_print_on_reset) llvm::dbgs() << ": SAT\n";

  }
  std::vector<unsigned> model = sat->get_model();

  unsigned no_keep = 0;
  for (unsigned i = 0; i < trace.prefix_size(); ++i) {
    if (keep[i]) no_keep++;
  }
  std::vector<unsigned> order(no_keep);
  for (unsigned i = 0, var = 0; i < trace.prefix_size(); ++i) {
    if (keep[i]) {
      unsigned pos = model[var++];
      order[pos] = i;
    }
  }

  if (conf.debug_print_on_reset) {
    llvm::dbgs() << "[";
    for (unsigned i : order) {
      llvm::dbgs() << i << ",";
    }
    llvm::dbgs() << "]\n";
  }

  /* XXX: Not handling blocked awaits */
  return order_to_leaf(decision_depth, trace, std::move(order), {});
}

Leaf RFSCTraceBuilder::order_to_leaf
(int decision, const TraceOverlay &trace, const std::vector<unsigned> order,
 const filtered_awaits_ty &awaits) const {
  std::vector<Branch> new_prefix;
  new_prefix.reserve(order.size()+awaits.size());
  for (unsigned i : order) {
    bool new_pinned = trace.prefix_at(i).pinned() || (trace.prefix_at(i).decision_depth() > decision);
    int new_decision = trace.prefix_at(i).decision_depth();
    if (new_decision > decision) {
      new_pinned = true;
      new_decision = -1;
    }
    assert(new_decision != decision || trace.prefix_at(i).size() == 1);
    new_prefix.emplace_back(trace.prefix_at(i).iid().get_pid(),
                            trace.prefix_at(i).size(),
                            new_decision,
                            new_pinned,
                            trace.prefix_at(i).sym());
  }
  for (const auto &await : awaits) {
    assert(await.pid_await.second.get_decision_depth() <= decision);
    new_prefix.emplace_back(await.pid_await.first,
                            1,
                            await.pid_await.second.get_decision_depth(),
                            await.pid_await.second.pinned, // Wait, can they even get pinned?
                            SymEv(),
                            /*blocked=*/true);
  }

  return Leaf(new_prefix);
}

static void causal_past_1(std::vector<bool> &acc, unsigned i,
                          const RFSCTraceBuilder::TraceOverlay &trace) {
  if (acc[i] == true) return;
  acc[i] = true;
  const auto &e = trace.prefix_at(i);
  assert(!e.deleted());
  Option<int> rf = e.read_from();
  if (rf && *rf != -1) {
    causal_past_1(acc, *rf, trace);
  }
  for (unsigned j : e.happens_after()) {
    causal_past_1(acc, j, trace);
  }
  if (Option<unsigned> pred = trace.po_predecessor(i)) {
    causal_past_1(acc, *pred, trace);
  }
}

std::vector<bool>
RFSCTraceBuilder::causal_past(int decision, const TraceOverlay &trace,
                              bool include_blocked_awaits,
                              filtered_awaits_ty *awaits_out) const {
  std::vector<bool> acc(trace.prefix_size());
  for (unsigned i = 0; i < trace.prefix_size(); ++i) {
    const TraceOverlay::TraceEventConstRef e = trace.prefix_at(i);
    assert(!((e.decision_depth() != -1)
             && e.pinned()));
    /* Does not hold when called from compute_unfolding() */
    // assert(::is_load(trace, i) == ((e.decision_depth() != -1)
    //                                || e.pinned()));
    if (e.decision_depth() != -1
        && e.decision_depth() <= decision
        && !e.deleted()) {
      causal_past_1(acc, i, trace);
    }
  }
  if (include_blocked_awaits) {
    for (const auto &addr_awaits : trace.blocking_awaits) {
      for (const auto &pid_await : addr_awaits.second) {
        IPid p = pid_await.first;
        const BlockedAwait &await = pid_await.second;
        assert(await.pinned || await.decision_ptr);
        if (!await.pinned && await.get_decision_depth() <= decision) {
          if (await.index > 1) {
            unsigned i = trace.find_process_event(p, await.index-1);
            causal_past_1(acc, i, trace);
          }
          if (await.read_from != -1) {
            causal_past_1(acc, await.read_from, trace);
          }
          if (awaits_out) {
            awaits_out->emplace_back(addr_awaits.first, pid_await);
          }
        }
      }
    }
  } else {
    assert(!awaits_out);
  }
  return acc;
}

static bool prefix_keep_1(std::vector<bool> &acc, std::vector<bool> &del,
                          unsigned i, int decision,
                          const RFSCTraceBuilder::TraceOverlay &trace) {
  if (del[i]) return false;
  const auto &e = trace.prefix_at(i);
  /* When pretending awaits are blocked, we might delete the unblocked
   * event, and then create another, identical, event. */
  assert(e.decision_depth() != decision || e.modified() || e.deleted());
  if (acc[i]) return !e.modified();
  if (e.deleted() || e.decision_depth() > decision) {
    del[i] = true;
    return false;
  } else {
    assert(!e.deleted());
  }
  if (Option<unsigned> pred = trace.po_predecessor(i)) {
    if (!prefix_keep_1(acc, del, *pred, decision, trace)) {
      del[i] = true;
      return false;
    }
  }
  Option<int> rf = e.read_from();
  if (rf && *rf != -1) {
    if (!prefix_keep_1(acc, del, *rf, decision, trace)) {
      del[i] = true;
      return false;
    }
  }
  for (unsigned j : e.happens_after()) {
    if (!prefix_keep_1(acc, del, j, decision, trace)) {
      del[i] = true;
      return false;
    }
  }
  acc[i] = true;
  if (e.decision_depth() != decision) {
    if (Option<unsigned> succ = trace.try_find_process_event
        (e.iid().get_pid(), e.iid().get_index() + e.size())) {
      assert(trace.po_predecessor(*succ) && *trace.po_predecessor(*succ) == i);
      const auto &se = trace.prefix_at(*succ);
      if (!se.deleted() && !is_load(trace, *succ)) {
        assert(se.decision_depth() == -1);
        prefix_keep_1(acc, del, *succ, decision, trace);
      }
    }
  }
  /* Intentionally return false when e.modified(); this is how we
   * exclude successors of those events. */
  return !e.modified();
}

std::vector<bool>
RFSCTraceBuilder::prefix_keep(int decision, const TraceOverlay &trace,
                              filtered_awaits_ty &awaits_out) const {
  std::vector<bool> acc = causal_past(decision, trace, true, &awaits_out);
  std::vector<bool> del(trace.prefix_size());

  for (unsigned i = 0; i < trace.prefix_size(); ++i) {
    const TraceOverlay::TraceEventConstRef e = trace.prefix_at(i);
    assert(!((e.decision_depth() != -1)
             && e.pinned()));
    if (!e.deleted()) {
      prefix_keep_1(acc, del, i, decision, trace);
    }
  }
#ifndef NDEBUG
  for (unsigned i = 0; i < trace.prefix_size(); ++i) {
    /* Does not hold when called from compute_unfolding() */
    const TraceOverlay::TraceEventConstRef e = trace.prefix_at(i);
    assert(!acc[i] ||
           ::is_load(trace, i) == ((e.decision_depth() != -1)
                                   || e.pinned()));
  }
#endif
  return acc;
}

std::vector<int> RFSCTraceBuilder::iid_map_at(int event) const{
  std::vector<int> map(threads.size(), 1);
  for (int i = 0; i < event; ++i) {
    iid_map_step(map, prefix[i]);
  }
  return map;
}

void RFSCTraceBuilder::iid_map_step(std::vector<int> &iid_map, const Event &event) const{
  if (iid_map.size() <= unsigned(event.iid.get_pid())) iid_map.resize(event.iid.get_pid()+1, 1);
  iid_map[event.iid.get_pid()] += event.size;
}

void RFSCTraceBuilder::iid_map_step_rev(std::vector<int> &iid_map, const Event &event) const{
  iid_map[event.iid.get_pid()] -= event.size;
}

inline Option<unsigned> RFSCTraceBuilder::
try_find_process_event(IPid pid, int index) const{
  assert(pid >= 0 && pid < int(threads.size()));
  assert(index >= 1);
  if (index > int(threads[pid].event_indices.size())){
    return nullptr;
  }

  unsigned k = threads[pid].event_indices[index-1];
  assert(k < prefix.size());
  assert(prefix[k].size > 0);
  assert(prefix[k].iid.get_pid() == pid
         && prefix[k].iid.get_index() <= index
         && (prefix[k].iid.get_index() + prefix[k].size) > index);

  return k;
}

inline unsigned RFSCTraceBuilder::find_process_event(IPid pid, int index) const{
  assert(pid >= 0 && pid < int(threads.size()));
  assert(index >= 1 && index <= int(threads[pid].event_indices.size()));
  unsigned k = threads[pid].event_indices[index-1];
  assert(k < prefix.size());
  assert(prefix[k].size > 0);
  assert(prefix[k].iid.get_pid() == pid
         && prefix[k].iid.get_index() <= index
         && (prefix[k].iid.get_index() + prefix[k].size) > index);

  return k;
}

long double RFSCTraceBuilder::estimate_trace_count() const{
  return estimate_trace_count(0);
}

bool RFSCTraceBuilder::check_for_cycles() {
  return false;
}

long double RFSCTraceBuilder::estimate_trace_count(int idx) const{
  if(idx > int(prefix.size())) return 0;
  if(idx == int(prefix.size())) return 1;

  long double count = 42;
  for(int i = int(prefix.size())-1; idx <= i; --i){
    count += prefix[i].sleep_branch_trace_count;
    // count += std::max(0, int(prefix.children_after(i)))
    //   * (count / (1 + prefix[i].sleep.size()));
  }

  return count;
}

unsigned RFSCTraceBuilder::TraceOverlay::
find_process_event(IPid pid, int index) const {
  /* Since we don't have a prefix pop_back, we assume that any events
   * that share indices with events in tb have the same iid */
  for (auto it = prefix_overlay.lower_bound(tb->prefix.size());
       it < prefix_overlay.end(); ++it) {
    const auto &e = it->second;
    if (e.iid.get_pid() != pid) continue;
    if (e.iid.get_index() <= index
        && e.iid.get_index() + e.size > index) {
      return it->first;
    }
  }
  unsigned res = tb->find_process_event(pid, index);
  assert(prefix_at(res).iid().get_pid() == pid
         && prefix_at(res).iid().get_index() <= index
         && (prefix_at(res).iid().get_index() + prefix_at(res).size() > index
             /* prefix_keep might ask for the successor of a modified
              * event. As a hack, allow it. The right thing to do would
              * be to use try_find_process_event(), but then we'd need a
              * maybe_po_prececessor() (or something) */
             || prefix_at(res).modified() || prefix_at(res).deleted()));
  return res;
}

Option<unsigned> RFSCTraceBuilder::TraceOverlay::
try_find_process_event(IPid pid, int index) const {
  /* Since we don't have a prefix pop_back, we assume that any events
   * that share indices with events in tb have the same iid */
  for (auto it = prefix_overlay.lower_bound(tb->prefix.size());
       it < prefix_overlay.end(); ++it) {
    const auto &e = it->second;
    if (e.iid.get_pid() != pid) continue;
    if (e.iid.get_index() <= index
        && e.iid.get_index() + e.size > index) {
      return it->first;
    }
  }
  Option<unsigned> res = tb->try_find_process_event(pid, index);
  /* The event might have been shortened in the overlay */
  if (res && prefix_at(*res).iid().get_index() + prefix_at(*res).size() <= index)
    return nullptr;
  assert(!res || prefix_at(*res).iid().get_pid() == pid
         && prefix_at(*res).iid().get_index() <= index
         && prefix_at(*res).iid().get_index() + prefix_at(*res).size() > index);
  return res;
}

RFSCTraceBuilder::TraceOverlay::TraceEvent::TraceEvent(const Event &e)
  : decision_ptr(e.decision_ptr.get()), happens_after(e.happens_after),
    sym(e.sym), size(e.size), iid(e.iid), read_from(e.read_from),
    pinned(e.pinned), modified(false), underlying(&e) {}

RFSCTraceBuilder::TraceOverlay::TraceEvent::
TraceEvent(const IID<int> &iid, SymEv sym)
  : decision_ptr(nullptr), sym(std::move(sym)), size(1), iid(iid),
    pinned(false), modified(true) {}

void RFSCTraceBuilder::TraceOverlay::TraceEvent::add_happens_after(unsigned event){
  assert(event != ~0u);
  if (happens_after.size() && happens_after.back() == event) return;
  happens_after.push_back(event);
}
void RFSCTraceBuilder::TraceOverlay::TraceEvent::decision_swap(TraceEvent &e) {
  std::swap(decision_ptr, e.decision_ptr);
}
int RFSCTraceBuilder::TraceOverlay::TraceEvent::get_decision_depth() const {
  return decision_ptr ? decision_ptr->depth : -1;
}

RFSCTraceBuilder::TraceOverlay::TraceEventConstRef::
TraceEventConstRef(const Event &e) : overlay(nullptr), event(&e) {}

RFSCTraceBuilder::TraceOverlay::TraceEventConstRef::
TraceEventConstRef(const TraceEvent &e) : overlay(&e), event(nullptr) {}

int RFSCTraceBuilder::TraceOverlay::TraceEventConstRef::size() const {
  return overlay ? overlay->size : event->size;
}
const IID<int> &RFSCTraceBuilder::TraceOverlay::TraceEventConstRef::iid()
  const {
  return overlay ? overlay->iid : event->iid;
}
bool RFSCTraceBuilder::TraceOverlay::TraceEventConstRef::pinned() const {
  return overlay ? overlay->pinned : event->pinned;
}
int RFSCTraceBuilder::TraceOverlay::TraceEventConstRef::decision_depth() const {
  return overlay ? overlay->get_decision_depth() : event->get_decision_depth();
}
DecisionNode *RFSCTraceBuilder::TraceOverlay::TraceEventConstRef::decision_ptr()
  const {
  return overlay ? overlay->decision_ptr : event->decision_ptr.get();
}
const SymEv &RFSCTraceBuilder::TraceOverlay::TraceEventConstRef::sym() const {
  return overlay ? overlay->sym : event->sym;
}
Option<int> RFSCTraceBuilder::TraceOverlay::TraceEventConstRef::read_from()
  const {
  return overlay ? overlay->read_from : event->read_from;
}
const std::vector<unsigned> &
RFSCTraceBuilder::TraceOverlay::TraceEventConstRef::happens_after() const {
  return overlay ? overlay->happens_after : event->happens_after;
}
bool RFSCTraceBuilder::TraceOverlay::TraceEventConstRef::deleted() const {
  return overlay && overlay->deleted;
}

bool RFSCTraceBuilder::TraceOverlay::TraceEventConstRef::modified() const {
  return overlay && overlay->modified;
}

RFSCTraceBuilder::TraceOverlay::
TraceOverlay(const RFSCTraceBuilder *tb, const writes_by_addr_ty &writes,
             std::initializer_list<unsigned> preallocate)
  : TraceOverlay(tb, writes_by_addr_ty(writes), std::move(preallocate)) {}

RFSCTraceBuilder::TraceOverlay::
TraceOverlay(const RFSCTraceBuilder *tb, writes_by_addr_ty &&writes,
             std::initializer_list<unsigned> preallocate)
  : writes_by_addr(std::move(writes)), blocking_awaits(tb->blocking_awaits),
    _prefix_size(tb->prefix.size()), tb(tb) {
  prefix_overlay.reserve(preallocate.size());
  assert(std::is_sorted(preallocate.begin(), preallocate.end()));
  for (unsigned i : preallocate) {
    /* Assume that preallocate is sorted */
    auto it = prefix_overlay.try_emplace(prefix_overlay.end(), i, tb->prefix[i]);
    it->second.size = 1;
    it->second.modified = true;
  }
}

RFSCTraceBuilder::TraceOverlay::
TraceOverlay(const TraceOverlay &other,
             std::initializer_list<unsigned> preallocate)
  : writes_by_addr(other.writes_by_addr),
    blocking_awaits(other.blocking_awaits), _prefix_size(other._prefix_size),
    tb(other.tb), prefix_overlay(other.prefix_overlay) {
  prefix_overlay.reserve(prefix_overlay.size() + preallocate.size());
  assert(std::is_sorted(preallocate.begin(), preallocate.end()));
  auto insertion_hint = prefix_overlay.end();
  for (unsigned i : preallocate) {
    /* Assume that preallocate is sorted */
    auto it = prefix_overlay.try_emplace(insertion_hint, i, tb->prefix[i]);
    it->second.size = 1;
    it->second.modified = true;
    insertion_hint = it + 1;
  }
}

std::size_t RFSCTraceBuilder::TraceOverlay::prefix_size() const {
  return _prefix_size;
}

auto RFSCTraceBuilder::TraceOverlay::prefix_at(unsigned index) const
  -> TraceEventConstRef {
  assert(index < prefix_size());
  auto it = prefix_overlay.find(index);
  if (it != prefix_overlay.end()) {
    return TraceEventConstRef(it->second);
  }
  return TraceEventConstRef(tb->prefix[index]);
}

auto RFSCTraceBuilder::TraceOverlay::prefix_mut(unsigned index)
  -> TraceEvent& {
  assert(index < prefix_size());
  auto ret = prefix_overlay.try_emplace(index, tb->prefix[index]);
  return ret.first->second;
}

Option<unsigned> RFSCTraceBuilder::TraceOverlay::po_predecessor(unsigned index)
  const {
  const auto &iid = prefix_at(index).iid();
  if (iid.get_index() == 1) return nullptr;
  return find_process_event(iid.get_pid(), iid.get_index()-1);
}
