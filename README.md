Vergo: A Verification System for Golog Programs
=================================================

Getting Started
-------------------------------------------------

It is required that the environment variable PATH_GOLOG is set to root
directory of this software, e.g. via

    $ export PATH_GOLOG=/home/user/vergo/

Directories
-------------------------------------------------

The code is divided into the following subdirectories:

- agents:

  Contains agents interfaces. These are required for the actual
  execution of and interaction with an agent program.

- examples:

  Example domain definitions for agents.

- projection:

  Code implementing regression and progression methods.

- reasoning:

  Contains different implementations and interfaces for backend
  reasoners (propositional and FOL).

- temp:

  Temporary files are put here.

- tools:

  Conversion tools such as PDDL parser.

- transfinal:

  Contains various definitions for Golog program semantics.

- lib:

  Various libraries (utilities, environment variables).

- verification:

  Contains implementations of different verification methods.

Dependencies
-------------------------------------------------

Vergo uses SWI-Prolog (currently version 7.6.4). Furthermore, there
are the following dependencies to external tools and systems:

1. **The E Theorem Prover**

   To use FOL theorem proving, we require that the 'eprover'
   executable is visible in PATH. The system has been developed and
   tested with the (currently) most recent version "2.0 Turzum". E can
   be downloaded from

   http://www.eprover.org 

   and installed manually. For some distributions such as Fedora,
   there are also prepackaged versions. Installation on Fedora then
   for example is via

       $ sudo yum install E.x86_64
 
2. **The NuSMV Model Checker**

   To use verification based on abstraction and model checking, we
   require that the 'nusmv' executable is visible in PATH. The system
   has been developed and tested with the (currently) most recent
   version 2.5.4, which can be downloaded from

   http://nusmv.fbk.eu

   and installed manually according to the installation instructions
   given there.

3. **Graphviz/dot**

   To visualize some of the graph structures created during
   verification, there are predicates to generate corresponding .dot
   files in the temp directory. An image file can then be generated
   for example using

       $ dot -Tpng prop_trans.dot -o prop_trans.png

4. **JPL (bidirectional Prolog/Java interface)**

   For some purposes, the Prolog->Java interface provided by the JPL
   library is needed. Typically, JPL does not have to be installed
   manually: Under Windows, it is already contained in the SWI-Prolog
   distribution; under some Linuxes such as Ubuntu, it can be
   installed through the package manager via

       $ sudo apt-get install swi-prolog-java

   For JPL to function properly, the LD_LIBRARY_PATH environment
   variable should be modified so that it contains directories that
   contain libjava.so, libjni.so, libjsig.so, and maybe some other
   Java libraries. For example, this can be achieved via

       $ export LD_LIBRARY_PATH=/usr/lib/jvm/java-7-openjdk-amd64/jre/lib/amd64/server/

   (where the specific path and Java version may differ for your
   system).

5. **The Konclude Description Logic (OWL 2) Reasoner**

   To use description logic reasoning, we require that the 'Konclude'
   executable is visible in PATH. The system has been developed and
   tested with the (currently) most recent version
   v0.6.1-527. Konclude can be obtained at

   http://www.derivo.de/products/konclude.html

   as 64-bit binary for Windows, Linux and MacOS X, both in statically
   and dynamically linked form. Its source code is published under the
   LGPL.

6. **FO²-Solver**

   Verification based on abstraction and model checking relies on
   deciding consistency of sets of first-order formulas. As a theorem
   prover is not a decision procedure for this problem, one variant
   uses Tomer Kotek's FO²-Solver

   http://forsyte.at/people/kotek/fo2-solver/

   (version 0.3d), which in turn requires a propositional SAT solver
   such as Glucose

   http://www.labri.fr/perso/lsimon/glucose/

   or Lingeling

   http://fmv.jku.at/lingeling/

   as well as a Java runtime environment. The environment variable
   PATH_FO2SOLVER has to point to the location of the installation of
   FO²-Solver, e.g. using

       $ export PATH_FO2SOLVER=~/local/FO2-Solver/

7. **The Vampire Theorem Prover**

   To use Vampire as alternative FOL theorem prover (instead of E),
   the 'vampire' executable binary (last tested stable version: 4.2.2)
   has to be visible in PATH. Vampire is available under

   https://vprover.github.io/index.html