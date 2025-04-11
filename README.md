# Vergo: A Verification System for GOLOG Programs

Vergo is (yet) an(other) implementation of the high-level agent
control language **GOLOG**, specifically devised as a testbed for
various algorithms for the temporal verification of programs.

This repository is a collection of code whose development was started
during the preparation of the doctoral thesis

> Jens Claßen: <br/>
> **Planning and Verification in the Action Language GOLOG.** <br/>
> PhD Thesis, Department of Computer Science, RWTH Aachen University, 2013.
> [[Fulltext](http://publications.rwth-aachen.de/record/229059/)]

and was continued during the [VERITAS][1] project on Verification of
Non-Terminating Action Programs within the research unit on [Hybrid
Reasoning for Intelligent Systems][2] funded by the [German Science
Foundation][3] (DFG).

While other GOLOG implementations such as [Reiter's original
prototype][4], [IndiGolog][5] or [Readylog][6] make use of Prolog's
evaluation mechanism for reasoning, Vergo supports full first-order
logic (FOL) by relying on an embedded theorem prover. That is to say
Prolog is used only for the *manipulation* of formulas (for syntactic
transformations such as regression), which are represented as terms
with a special syntax. For example. `all(X,some(Y,p(X) + q(Y) *
-r(X,Y)))` expresses that for every `X` there is some `Y` such that
`p(X)` or `q(Y)` and not `r(X,Y)` holds (with the usual syntactical
preference among Boolean connectives). *Inference* tasks, such as
deciding whether an initial theory entails a query formula, are then
delegated to the theorem prover. The reason for this is that for the
purpose of formal verification, it is necessary to adhere strictly to
the formal definition of the underlying logic, and avoid intermingling
Prolog evaluation with GOLOG reasoning. It also means that the full
expressivity of FOL can be utilized to devise agent programs, which,
as always, comes at the price of computational efficiency.

As opposed to many other GOLOG systems, Vergo is not a fully-fledged
agent framework that includes interfaces to an agent's sensors and
actuators and takes care of the full sense-plan-act cycle. Should one
actually decide to use it for controlling an agent, it should rather
be thought of as a *module* to be integrated into a larger agent/robot
framework. The interpreter runs in a single instance of Prolog and
provides an interface for (a) telling the system updates about world
state changes in terms of actions that have been executed and sensing
results that were obtained, and (b) asking it queries about what is
known about the world state or what the next action should be. We thus
follow Levesque's functional view on a knowledge-based system.

The code provided in this repository is in a constant state of 'work
in progress' and comes without any warranty (see also the attached
license). The algorithms implemented herein merely serve as proofs of
concept and are open-sourced for the sake of academic exchange and
reproducibility.

[1]: https://www.hybrid-reasoning.org/en/projects/a1-verification-of-non-terminating-action-programs/
[2]: https://www.hybrid-reasoning.org
[3]: http://www.dfg.de
[4]: http://www.cs.toronto.edu/cogrobo/kia
[5]: https://bitbucket.org/ssardina-research/indigolog/src
[6]: http://robocup.rwth-aachen.de/readylog

## Getting Started

Vergo requires a recent version of
[SWI-Prolog](http://www.swi-prolog.org) as well as at least one FOL
theorem prover being installed (see [dependencies](#dependencies)
below). The environment variable PATH_GOLOG should then point to the
root directory of this software, e.g. via

    $ export PATH_GOLOG=/home/user/vergo/

There currently is no elaborate documentation. Instead, we encourage
the interested reader to study the [sources](#directories) and look at
the provided examples. The underlying algorithms are discussed in the
corresponding [papers](#references).

### Verification by Fixpoint Computation

To get started with verification by fixpoint computation, consider the
`coffee_robot` domain in the `examples` directory. Look at the file
`coffee_bat_fct.pl` and how actions, fluents, programs and temporal
properties are defined in it. From within the directory, call
SWI-Prolog and consult the file:

    ?- [coffee_bat_fct].

Next, construct the characteristic graph via

    ?- construct_characteristic_graph(main).

and observe the output. The actual verification for one of the
properties is initiated e.g. through

    ?- verify(main,prop4,Truth).

### Verification by Abstraction

For the local-effect case, consider the `dish_robot` domain in the
`examples` directory. Look at the file `dish_robot_bat.pl` and how
actions, fluents, programs and temporal properties are defined in
it. From within the directory, call SWI-Prolog, and consult the file
containing the action theory:

    ?- [dish_robot_bat].

Next, start the construction of the abstract transition system via

    ?- compute_abstraction(main).

and observe the output (this may take some time). To actually verify a
property by the model checker, call then e.g.

    ?- verify(main,prop5,Truth).

The abstraction method also supports the more general acyclic
theories, but currently there is no example domain for their
verification. See the `warehouse_robot` domain for an example on
_synthesis_ for acyclic theories.

### Synthesis by Abstraction

For the local-effect case, consider the `dish_robot` domain in the
`examples` directory. Look at the file `dish_robot_bat_syn.pl` and how
actions, fluents, programs and temporal properties are defined in
it. From within the directory, call SWI-Prolog, and consult the file
containing the action theory:

    ?- [dish_robot_bat_syn].

Next, start the construction of the abstract transition system via

    ?- synthesize(main,prop1).

and observe the output. For an example of an acyclic action theory,
consider the `warehouse_robot` domain in the `examples` directory.

## Directories

The code is divided into the following subdirectories:

- agents:

  Contains agents interfaces. These are required for the actual
  execution of and interaction with an agent program.

- examples:

  Example domain definitions for agents.

- golog:

  Contains code related to Golog programs, e.g. transition semantics.

- kbs:

  Modules implementing a knowledge base given a certain base logic,
  most importantly L (FOL with standard names).

- lib:

  Various libraries (utilities, environment variables).

- logic:

  Various modules for representing and manipulating logical formulas,
  e.g. (first-order) BDD representation, and the closed-world and
  unique names assumptions.

- planning:

  Planning related code such as PDDL parser.

- projection:

  Code implementing regression and progression methods.
  
- reasoners:

  Contains different implementations and interfaces for backend
  reasoners (FOL, FO^2, Description Logics, System Z).

- temp:

  Temporary files are put here.

- verification:

  Contains implementations of different verification methods.

## Dependencies

Vergo uses SWI-Prolog (currently version 9.0.4). Furthermore, there
are the following dependencies to external tools and systems:

1. **Theorem Prover** (required)

   In order to be able to use FOL theorem proving, we require that at
   least one theorem prover is available.

   1. E Prover

      By default, the system expects the 'eprover' executable to be
      visible in PATH. The system has been developed and tested with
      the (currently) most recent version "E 3.2 Puttabong
      Moondrop". E can be downloaded from

      http://www.eprover.org 

      and installed manually. For some distributions such as Debian
      and Fedora, there are also prepackaged versions. Installation on
      Debian then for example is via

          $ sudo apt-get install eprover

      and on Fedora via

          $ sudo yum install E.x86_64

   2. Vampire

      Alternatively, Vampire can be used instead of E. This similarly
      requires that the 'vampire' executable binary (last tested
      stable version: 4.9) is visible in PATH. Vampire is available
      under

      https://vprover.github.io/index.html    

      Then call

          ?- fol:set_reasoner(vampire).

   3. FO²-Solver

      Verification based on abstraction and model checking relies on
      deciding consistency of sets of formulas from the two-variable
      fragment of FOL. An FOL theorem prover is generally not a
      decision procedure for this problem. As alternative, we can use
      Tomer Kotek's FO²-Solver

      http://forsyte.at/people/kotek/fo2-solver/

      (version 0.3d), which in turn requires a propositional SAT
      solver such as Glucose

      http://www.labri.fr/perso/lsimon/glucose/

      or Lingeling

      http://fmv.jku.at/lingeling/

      as well as a Java runtime environment. The environment variable
      PATH_FO2SOLVER has to point to the location of the installation
      of FO²-Solver, e.g. using

          $ export PATH_FO2SOLVER=~/local/FO2-Solver/

      Then call

          ?- fol:set_reasoner(fo2solver).

2. **Model Checker**

   For verification based on abstraction, it is possible (though not
   required) to use the NuSMV model checker. By default, an internal
   implementation of a CTL model checking algorithm is utilized. Since
   states of the abstract transition system have to enumerated, there
   is no real performance advantage in using a fast symbolic model
   checker.

   For employing NuSMV, we require that the 'NuSMV' executable is
   visible in PATH. Then set the model checker by calling

          ?- abstraction_acyclic:set_modelchecker(nusmv).

   The system has been developed and tested with the (currently) most
   recent version 2.6.0, which can be downloaded from

   http://nusmv.fbk.eu

   and installed manually according to the installation instructions
   given there.

   So far, NuSMV is the only external model checker supported.

3. **Graphviz/dot**

   To visualize some of the graph structures created during
   verification, there are predicates to generate corresponding .dot
   files in the temp directory. An image file can then be generated
   for example using

       $ dot -Tpng prop_trans.dot -o prop_trans.png

4. **JPL (bidirectional Prolog/Java interface)**

   For some purposes such as the visualization applet for the Wumpus
   world, the Prolog->Java interface provided by the JPL library is
   needed. Typically, JPL does not have to be installed manually:
   Under Windows, it is already contained in the SWI-Prolog
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
   v0.6.2. Konclude can be obtained at

   http://www.derivo.de/products/konclude.html

   as 64-bit binary for Windows, Linux and MacOS X, both in statically
   and dynamically linked form. Its source code is published under the
   LGPL.

6. **The Fast Downward PDDL Planner**

   To use PDDL planning, we require that 'fast-downward.py' is visible
   in PATH and executable (meaning Python and all dependencies are
   installed). Instructions for obtaining and running Fast Downward
   are available at

   http://www.fast-downward.org/

   Fast Downward will be run using the default configuration using
   `--alias lama-first`. So far, Fast Downward is the only PDDL
   planner supported.

## References

1. Till Hofmann and Jens Claßen: <br/>
   **LTLf Synthesis on First-Order Agent Programs in Nondeterministic Environments.** <br/>
   In *Proc. AAAI*, 2025.
   [[PDF]](http://www.jens-classen.net/pub/HofmannClassen2025.pdf)

1. Jens Claßen: <br/>
   **Symbolic Verification of Golog Programs with First-Order BDDs.** <br/>
   In *Proc. KR*, 2018.
   [[PDF]](http://jens-classen.net/pub/Classen2018.pdf)

2. Benjamin Zarrieß and Jens Claßen: <br/>
   **Verifying CTL\* Properties of Golog Programs over Local-Effect
   Actions.** <br/>
   In *Proc. ECAI*, 2014.
   [[PDF]](http://www.jens-classen.net/pub/ZarriessClassen2014b.pdf)

3. Jens Claßen, Martin Liebenberg, Gerhard Lakemeyer, and Benjamin
   Zarrieß: <br/>
   **Exploring the Boundaries of Decidable Verification of
   Non-Terminating Golog Programs.** <br/>
   In *Proc. AAAI*, 2014.
   [[PDF]](http://www.jens-classen.net/pub/ClassenEtAl2014.pdf)

4. Jens Claßen: <br/>
   **Planning and Verification in the Action Language GOLOG.** <br/>
   PhD Thesis, RWTH Aachen University, 2013.
   [[Fulltext](http://publications.rwth-aachen.de/record/229059/)]
   
5. Jens Claßen and Gerhard Lakemeyer: <br/>
   **A Logic for Non-Terminating Golog Programs.** <br/>
   In *Proc. KR*, 2008.
   [[PDF]](http://jens-classen.net/pub/ClassenLakemeyer2008.pdf)

6. Jens Claßen and Gerhard Lakemeyer: <br/>
   **Foundations for Knowledge-Based Programs using ES.** <br/>
   In *Proc. KR*, 2006.
   [[PDF]](http://jens-classen.net/pub/ClassenLakemeyer2006a.pdf)
