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

#include "CommandLineOptions.h"

llvm::cl::opt<std::string>
cl_transform("transform",llvm::cl::init(""),
             llvm::cl::desc("Transform the input module and store it (as LLVM assembly) to OUTFILE."),
             llvm::cl::NotHidden,llvm::cl::value_desc("OUTFILE"));

llvm::cl::list<std::string>
cl_program_arguments(llvm::cl::desc("[-- <program arguments>...]"),
                     llvm::cl::Positional,
                     llvm::cl::ZeroOrMore);
