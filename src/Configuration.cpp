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

#include "Configuration.h"

#include <llvm/Support/CommandLine.h>
#include "Debug.h"

extern llvm::cl::list<std::string> cl_program_arguments;

extern llvm::cl::opt<std::string> cl_transform;

static llvm::cl::opt<bool> cl_explore_all("explore-all",llvm::cl::NotHidden,
                                          llvm::cl::desc("Continue exploring all traces, "
                                                         "even after the first error"));

static llvm::cl::opt<bool> cl_malloc_may_fail("malloc-may-fail",llvm::cl::NotHidden,
                                              llvm::cl::desc("If set then the case of malloc failure is also explored."));

static llvm::cl::opt<bool> cl_disable_mutex_init_requirement("disable-mutex-init-requirement",llvm::cl::NotHidden,
                                                             llvm::cl::desc("If set, then allow use of mutexes without a preceding call to pthread_mutex_init.\nThis switch is necessary when using static mutex initialization."));

static llvm::cl::opt<int>
cl_max_search_depth("max-search-depth",
                    llvm::cl::NotHidden,llvm::cl::init(-1),
                    llvm::cl::desc("Bound the length of the analysed computations (# instructions/events per process)"));

static llvm::cl::opt<Configuration::MemoryModel>
cl_memory_model(llvm::cl::NotHidden, llvm::cl::init(Configuration::MM_UNDEF),
                llvm::cl::desc("Select memory model"),
                llvm::cl::values(clEnumValN(Configuration::SC,"sc","Sequential Consistency"),
                                 clEnumValN(Configuration::ARM,"arm","The ARM model"),
                                 clEnumValN(Configuration::POWER,"power","The POWER model"),
                                 clEnumValN(Configuration::PSO,"pso","Partial Store Order"),
                                 clEnumValN(Configuration::TSO,"tso","Total Store Order")
#ifdef LLVM_CL_VALUES_USES_SENTINEL
                                ,clEnumValEnd
#endif
                                 ));

static llvm::cl::opt<Configuration::DPORAlgorithm>
cl_dpor_algorithm(llvm::cl::NotHidden, llvm::cl::init(Configuration::SOURCE),
                  llvm::cl::desc("Select DPOR algorithm"),
                  llvm::cl::values(clEnumValN(Configuration::SOURCE,"source","Source-DPOR (default)"),
                                   clEnumValN(Configuration::OPTIMAL,"optimal","Optimal-DPOR")
#ifdef LLVM_CL_VALUES_USES_SENTINEL
                                  ,clEnumValEnd
#endif
                                 ));

static llvm::cl::opt<Configuration::SchedulingAlgorithm>
cl_scheduling_algorithm(llvm::cl::NotHidden, llvm::cl::init(Configuration::ROUND_ROBIN),
                        llvm::cl::desc("Select DPOR algorithm"),
                        llvm::cl::values(clEnumValN(Configuration::ROUND_ROBIN,"round-robin","Round Robin (default)"),
                                         clEnumValN(Configuration::OLDEST_FIRST,"oldest-first","Oldest first")
#ifdef LLVM_CL_VALUES_USES_SENTINEL
                                        ,clEnumValEnd
#endif
                                         ));

static llvm::cl::opt<bool> cl_check_robustness("robustness",llvm::cl::NotHidden,
                                               llvm::cl::desc("Check for robustness as a correctness criterion."));

static llvm::cl::OptionCategory cl_transformation_cat("Module Transformation Passes");

static llvm::cl::opt<bool> cl_transform_no_spin_assume("no-spin-assume",llvm::cl::NotHidden,llvm::cl::cat(cl_transformation_cat),
                                                       llvm::cl::desc("Disable the spin assume pass in module transformation."));

static llvm::cl::opt<int>
cl_transform_loop_unroll("unroll",
                         llvm::cl::NotHidden,llvm::cl::init(-1),llvm::cl::value_desc("N"),
                         llvm::cl::cat(cl_transformation_cat),
                         llvm::cl::desc("Bound executions by allowing loops to iterate at most N times."));

static llvm::cl::opt<bool> cl_print_progress("print-progress",llvm::cl::NotHidden,
                                             llvm::cl::desc("Continually print analysis progress to stdout."));

static llvm::cl::opt<bool> cl_print_progress_estimate("print-progress-estimate",llvm::cl::NotHidden,
                                                      llvm::cl::desc("Continually print analysis progress and trace "
                                                                     "number estimate to stdout."));

static llvm::cl::list<std::string> cl_extfun_no_race("extfun-no-race",llvm::cl::NotHidden,
                                                         llvm::cl::value_desc("FUN"),
                                                         llvm::cl::desc("Assume that the external function FUN, when called as blackbox,\n"
                                                                        "does not participate in any races. (See manual.)\n"
                                                                        "May be given multiple times."));

static llvm::cl::OptionCategory cl_dump_cat
("Trace Dumping");

static llvm::cl::opt<std::string> cl_dump_traces
("dump-traces",llvm::cl::NotHidden,llvm::cl::cat(cl_dump_cat),
 llvm::cl::value_desc("FILE"),
 llvm::cl::desc("Write graph of explored equivalence classes to FILE."));

static llvm::cl::opt<std::string> cl_dump_tree
("dump-tree",llvm::cl::NotHidden,llvm::cl::cat(cl_dump_cat),
 llvm::cl::value_desc("FILE"),
 llvm::cl::desc("Write graph of exploration tree to FILE."));

static llvm::cl::opt<std::string> cl_dump_spec
("dump-spec",llvm::cl::NotHidden,llvm::cl::cat(cl_dump_cat),
 llvm::cl::value_desc("FILE"),
 llvm::cl::desc("Write minimal trace_set_spec to FILE."));

static llvm::cl::opt<bool> cl_debug_print_on_reset
("debug-print-on-reset",llvm::cl::Hidden,
 llvm::cl::desc("Print debug info after exploring each trace."));

const std::set<std::string> &Configuration::commandline_opts(){
  static std::set<std::string> opts = {
    "explore-all",
    "extfun-no-race",
    "malloc-may-fail",
    "disable-mutex-init-requirement",
    "max-search-depth",
    "sc","tso","pso","power","arm",
    "source","optimal",
    "round-robin","oldest-first",
    "robustness",
    "no-spin-assume",
    "unroll",
    "print-progress",
    "print-progress-estimate",
    "dump-traces",
    "dump-tree",
    "dump-spec",
  };
  return opts;
}

const Configuration Configuration::default_conf;

void Configuration::assign_by_commandline(){
  explore_all_traces = cl_explore_all;
  for(std::string f : cl_extfun_no_race){
    extfun_no_full_memory_conflict.insert(f);
  }
  malloc_may_fail = cl_malloc_may_fail;
  mutex_require_init = !cl_disable_mutex_init_requirement;
  max_search_depth = cl_max_search_depth;
  memory_model = cl_memory_model;
  dpor_algorithm = cl_dpor_algorithm;
  check_robustness = cl_check_robustness;
  transform_spin_assume = !cl_transform_no_spin_assume;
  transform_loop_unroll = cl_transform_loop_unroll;
  print_progress = cl_print_progress || cl_print_progress_estimate;
  print_progress_estimate = cl_print_progress_estimate;
  trace_dump_file = cl_dump_traces;
  debug_collect_all_traces |= !cl_dump_traces.empty();
  tree_dump_file = cl_dump_tree;
  debug_collect_all_traces |= !cl_dump_tree.empty();
  ee_store_trace           |= !cl_dump_tree.empty();
  spec_dump_file = cl_dump_spec;
  debug_collect_all_traces |= !cl_dump_spec.empty();
  scheduling_algorithm = cl_scheduling_algorithm;
  debug_print_on_reset = cl_debug_print_on_reset;
  argv.resize(1);
  argv[0] = get_default_program_name();
  for(std::string a : cl_program_arguments){
    argv.push_back(a);
  }
}

void Configuration::check_commandline(){
  /* Check commandline switch compatibility with --transform. */
  if(cl_transform.getNumOccurrences()){
    if(cl_extfun_no_race.getNumOccurrences()){
      Debug::warn("Configuration::check_commandline:transform:extfun_no_race")
        << "WARNING: --extfun-no-race ignored in presence of --transform.\n";
    }
    if(cl_malloc_may_fail.getNumOccurrences()){
      Debug::warn("Configuration::check_commandline:transform:malloc_may_fail")
        << "WARNING: --malloc_may_fail ignored in presence of --transform.\n";
    }
    if(cl_disable_mutex_init_requirement.getNumOccurrences()){
      Debug::warn("Configuration::check_commandline:transform:disable_mutex_init_requirement")
        << "WARNING: --disable-mutex-init-requirement ignored in presence of --transform.\n";
    }
    if(cl_max_search_depth.getNumOccurrences()){
      Debug::warn("Configuration::check_commandline:transform:max-search-depth")
        << "WARNING: --max-search-depth ignored in presence of --transform.\n";
    }
    if(cl_memory_model.getNumOccurrences()){
      Debug::warn("Configuration::check_commandline:transform:memory_model")
        << "WARNING: Given memory model ignored in presence of --transform.\n";
    }
    if(cl_dpor_algorithm.getNumOccurrences()){
      Debug::warn("Configuration::check_commandline:transform:dpor_algorithm")
        << "WARNING: Given DPOR algorithm ignored in presence of --transform.\n";
    }
    if(cl_print_progress.getNumOccurrences()){
      Debug::warn("Configuration::check_commandline:transform:print-progress")
        << "WARNING: --print-progress ignored in presence of --transform.\n";
    }
    if(cl_print_progress_estimate.getNumOccurrences()){
      Debug::warn("Configuration::check_commandline:transform:print-progress-estimate")
        << "WARNING: --print-progress-estimate ignored in presence of --transform.\n";
    }
    if(cl_check_robustness.getNumOccurrences()){
      Debug::warn("Configuration::check_commandline:transform:check_robustness")
        << "WARNING: --robustness ignored in presence of --transform.\n";
    }
    if(cl_program_arguments.size()){
      Debug::warn("Configuration::check_commandline:transform:program_arguments")
        << "WARNING: Program arguments (argv for test case) ignored in presence of --transform.\n";
    }
  }else{
    if(cl_transform_no_spin_assume.getNumOccurrences()){
      Debug::warn("Configuration::check_commandline:no:transform:transform-no-spin-assume")
        << "WARNING: --no-spin-assume ignored in absence of --transform.\n";
    }
    if(cl_transform_loop_unroll.getNumOccurrences()){
      Debug::warn("Configuration::check_commandline:no:transform:transform_loop_unroll")
        << "WARNING: --unroll ignored in absence of --transform.\n";
    }
  }
  /* Check commandline switch compatibility with memory model. */
  {
    std::string mm;
    if(cl_memory_model == Configuration::SC) mm = "SC";
    if(cl_memory_model == Configuration::TSO) mm = "TSO";
    if(cl_memory_model == Configuration::PSO) mm = "PSO";
    if(cl_memory_model == Configuration::POWER) mm = "POWER";
    if(cl_memory_model == Configuration::ARM) mm = "ARM";
    if(cl_memory_model == Configuration::ARM || cl_memory_model == Configuration::POWER){
      if(cl_extfun_no_race.getNumOccurrences()){
        Debug::warn("Configuration::check_commandline:mm:extfun-no-race")
          << "WARNING: --extfun-no-race ignored under memory model " << mm << ".\n";
      }
      if(cl_malloc_may_fail.getNumOccurrences()){
        Debug::warn("Configuration::check_commandline:mm:malloc-may-fail")
          << "WARNING: --malloc-may-fail ignored under memory model " << mm << ".\n";
      }
      if(cl_max_search_depth.getNumOccurrences()){
        Debug::warn("Configuration::check_commandline:mm:max-search-depth")
          << "WARNING: --max-search-depth ignored under memory model " << mm << ".\n";
      }
      if(cl_check_robustness.getNumOccurrences()){
        Debug::warn("Configuration::check_commandline:mm:robustness")
          << "WARNING: --robustness ignored under memory model " << mm << ".\n";
      }
      if (cl_dump_traces != ""){
        Debug::warn("Configuration::check_commandline:mm:dump-traces")
          << "WARNING: --dump-traces not implemented for memory model " << mm << ".\n";
      }
      if (cl_dump_spec != ""){
        Debug::warn("Configuration::check_commandline:mm:dump-spec")
          << "WARNING: --dump-spec ignored under memory model " << mm << ".\n";
      }
    }
    if (cl_dpor_algorithm == Configuration::OPTIMAL
        && cl_memory_model != Configuration::SC
        && cl_memory_model != Configuration::TSO) {
      Debug::warn("Configuration::check_commandline:dpor:mm")
        << "WARNING: Optimal-DPOR not implemented for memory model " << mm << ".\n";
    }
  }
}
