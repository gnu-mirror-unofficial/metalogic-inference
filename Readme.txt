
  MLI compilation, installation, and running


MLI requires: C++14 compiler, and the GMP multiprecision library. If one wants to compile beyond what is in the distribution, Flex is needed to compile lexer.ll, and Bison to compile parser.yy.

Note: Compiles on MacOS 10.12 using g++ (MacPorts gcc6 6.3.0_0) 6.3.0 and Apple LLVM version 8.0.0 (clang-800.0.42.1), Flex 2.5.37, and Bison 3.0.4.


To compile: move to the directory src, and issue the shell command
  ./configure && make
which results in the program 'mli'.

To install: with suitable permissions, type 'make install' to install the programs and any data files and documentation.

After installation, as a first check that the program is properly installed and in the PATH, try say
  mli --help
or
  mli --version


To run the program 'mli' examples:

In a suitable working directory, copy in the installed examples by:
  cp -R /usr/local/share/doc/mli/examples .
Then move to the directory examples:
  cd examples

Run the file main.mli by
  mli main.mli
which interprets it, attempts to verify the parsed statement, and writes the result in a file "main.mlo", where the verifications that failed are marked "unproved". Any earlier file "main.mlo" is overwritten. Also, a file "main.log" is written with more detailed debugging information about the verification process.

The proofs in the file that main.mli includes can then be altered, and mli rerun, to see the difference in verification:
The last statement in the file tests/TK1.mli has a deliberate error in the proof, and the correct proof commented out. So just change this, to include the correct line.

-----

   Copyright (C) 2017 Hans Åberg.

   This file is part of MLI, MetaLogic Inference.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>. 

