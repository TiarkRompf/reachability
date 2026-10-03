# Artifact for "Type, Ability, and Effect Systems: Perspectives on Purity, Semantics, and Expressiveness"

## Overview of Rocq Files by Section
- The systems presented in the main paper share the same syntax and dynamic semantics (Fig. 3),
which are defined in [stlc_tae.v](stlc_tae.v).
   * the terms are defined by [tm](stlc_tae.v#68)
   * the values are defined by [vl](stlc_tae.v#81)
   * the value environment is defined by [venv](stlc_tae.v#87) 
   * the store is defined by [stor](stlc_tae.v#92)
   * the operational semantics is defined by [teval](stlc_tae.v#253)
   

- [stlc_effects.v](stlc_effects.v) includes: 
    * the type is defined by [ty_E](stlc_effects.v#20)
    * the typing environment is defined by [tenv_E](stlc_effects.v#26)
    * the type rules for the effect type system ($\lambda_{e}$) (Fig. 4, Section 4 in the main paper) are defiend by [has_type_E](stlc_effects.v#42). 
    * the subtyping ruels (Fig. 1 in the supplement) are defined by [stp_E](stlc_effects.v#29)
    * context typing rules (Fig. 3 in the supplement) are defined by [ctx_type_E](stlc_effects.v#185) 
    * the translation from $\lambda_e$ to $\lambda_{ae}$ (Fig. 7 in the main paper) is defined 
    by [tty_E](stlc_effects.v#108)
    * the semantic soundness proof of $\lambda_e$ is formalized as theorem [fundamental_E](stlc_effects.v#173)
    * the soundness proof of the translation of context typing rules is formalized as lemma [translate_ctx_E](stlc_effects.v#238)
    * the soundness of contextual equivalence [soundness_E](stlc_effects.v#326) and purity  [soundness_of_purity_E](stlc_effects.v#341)
    * the proof of the reordering rule [reorder_tbin_E](stlc_effects.v#350) with its relevant inversion lemmas:[tbin_inversion1](stlc_effects.v#361) and [tbin_inversion2](stlc_effects.v#403)
- [stlc_ability.v](stlc_ability.v) includes:
    * the type is defined by [ty_A](stlc_ability.v#19)
    * the typing environment is defined by [tenv_A](stlc_ability.v#25)
    * the type rules for the ability type system ($\lambda_{a}$) (Fig. 5, Section 5 in the main paper) is defined by [has_type_A](stlc_ability.v#53)
     * the subtyping rules (Fig. 4 in the supplement) is defined by [stp_A](stlc_ability.v#39) 
    * the semantic soundness proof of $\lambda_a$ is formalized as theorem [fundamental_A](stlc_ability.v#189)
    * the translation from $\lambda_a$ to $\lambda_{ae}$ (Fig. 7 in the main paper) is defiend by [tty_A](stlc_ability.v#30)
    * context typing rules (Fig. 5 in the supplement) is defined by [ctx_type_A](stlc_ability.v#204)and the soundness proof of the translation of context typing rules [translate_ctx_A](stlc_ability.v#256)
    * the soundness of contextual equivalence [soundness_A](stlc_ability.v#336) and purity [soundness_of_purity_A](stlc_ability.v#354)
    * the proof of the reordering rule [reorder_tbin_A](stlc_ability.v#364) with its relevant inversion lemmas: [tbin_inversion1](stlc_ability.v#378) and [tbin_inversion2](stlc_ability.v#408)
- [stlc_tae.v](stlc_tae.v) includes:
    * the type is defined by [ty](stlc_tae.v#62)
    * the typing environment is defined by [tenv](stlc_tae.v#88)
    * the type rules for the type, ability, and effect system ($\lambda_{ae}$) (Fig. 6, Section 6 in the main paper) [has_type](stlc_tae.v#138)
    * the subtyping rules (Fig. 6 in the supplement) [stp](stlc_tae.v#108) 
    * the definition of the binary logical relations (Fig. 9 and 10, Section 6 in the main paper and Fig. 10 in the supplement) [val_type](stlc_tae.v#453)
    * the semantic soundness proof of $\lambda_{ae}$ [fundamental](stlc_tae.v#4224)
    * the proof of the $\beta$-rule [beta_equivalence](stlc_tae.v#7106) 
    * the proof of the reordering rule [reorder_tbin](stlc_tae.v#5054) with its relevant inversion lemmas: [tinb_inversion1](stlc_tae.v#7117) and [tin_inversion2](stlc_tae.v#7166)
- [stlc_tae_ctx.v](stlc_tae_ctx.v) includes:
    * context typing rules (Fig. 9 in the supplement) [ctx_type](stlc_tae_ctx.v#155)
    * the soundness of contextual equivalence [soundness](stlc_tae_ctx.v#691) and purity [soundness_of_purity](stlc_tae_ctx.v#944)
- [example.v](example.v) includes examples shown in Fig. 8 in the main paper.
- [stlc_tae_list.v](stlc_tae_list.v) includes the extensions of list syntax [tm](stlc_tae_list.v#69), values [vl](stlc_tae_list.v#85), types [ty](stlc_tae_list.v#62), and typing rules [has_type](stlc_tae_list.v#147) (Fig. 7, Section 7 in the supplement)  
- [stlc_tae_list_example.v](stlc_tae_list_example.v) includes the encoding of the map function (`Definition ex_map`) and its derived typing rule (`Lemma ty5`) as well as examples: (1) passing a function without effects to map (`Lemma ty5_noeff`, `Lemma ty5_noeff'` and `Lemma ty5_noeff''`);
(2) passing an effectful function to map (`Lemma ty5_eff`).

## Key Lemmas and Theorems

Notation: P: main paper; S: supplement

| System | Item | Mechanization | Paper |
|---------|------|---------------|-------|
| $\lambda_e$ | let-encoding | `Lemma ty_abs_app_E` | Rule T-LET-E |
|             | fundamental property | `Theorem fundamental_E` | Theorem 4.1 |
|             | soundness of contextual equivalence | `Theorem soundness_E` | Theorem 4.2 |
|             | effect safety of effect type system | `Theorem soundness_of_purity_E` | Theorem 4.3 |
|             | reordering | `Theorem reorder_tbin_E` | Theorem 4.4 |
| $\lambda_a$ | let-encoding | `Lemma ty_tabs_app_A` | Rule T-LET-A |
|             | fundamental property | `Theorem fundamental_A` | Theorem 5.1 |
|             | soundness of contextual equivalence | `Theorem soundness_A` | Theorem 5.2 |
|             | effect safety of ability type system | `Theorem soundness_of_purity_A` | Theorem 5.3 |
|             | reordering | `Theorem reorder_tbin_A` | Theorem 5.4 |
| $\lambda_{ae}$ | let-encoding | `Lemma ty_tabs_app` | Rule T-LET-AE |
|                | strengthening | `Lemma hast_strengthen` | Lemma 6.1 |
|                | soundness of translation from $\lambda_e$ to $\lambda_{ae}$ | `Lemma translate_E` | Theorem 6.2 |
|                | pure terms from $\lambda_e$ remain pure in $\lambda_{ae}$ | `Corollary translate_E_pure` | Corollary 6.4 |
|                | soundness of translation from $\lambda_a$ to $\lambda_{ae}$ | `Lemma translate_A` | Theorem 6.3 |
|                | pure terms from $\lambda_a$ remain pure in $\lambda_{ae}$ | `Corollary translate_A_pure` | Corollary 6.4 |
|                | fundamental property | `Theorem fundamental` | Theorem 7.7 |
|                | soundness w.r.t. contextual equivalence | `Theorem soundness` | Theorem 7.8 |
|                | effect safety of ability and effect type system | `Theorem soundness_of_purity` | Theorem 7.9 |
|                | $\beta$-equivalence | `Corollary beta_equivalence` | Theorem 7.10 |
|                | reordering | `Theorem reorder_tbin` | Theorem 7.11 |

## Reusability Guide

The following components are reusable and extensible for future research:

- `env.v`: This file contains the module for general theories of environments as lists of De Bruijn levels, suitable for representing syntax with variable binding. This module is independent of the specific systems presented in the paper, and can be reused in the development of any system involving variable binding.
- `qualifiers.v`: This file provides modular and general reasoning about qualifiers. Extending a system with additional terms or types requires no change to this file.

- `tactics.v`: This file contains general-purpose tactics for relating propositions to Boolean expressions.

The following shows how to experiment with new equational rules using the current systems:
- Proving new equational rules in $\lambda_e$: Create a new Rocq file, and import the files `stlc_tae.v`, `stlc_tae_ctx.v` and `stlc_effects.v`.
    
- Proving new equational rules in $\lambda_a$: Create a new Rocq file, and import the files `stlc_tae.v`, `stlc_tae_ctx.v` and `stlc_ability.v`.

- Proving new equational rules in $\lambda_{ae}$: Create a new Rocq file, and import the files `stlc_tae.v` and `stlc_tae_ctx.v`.

The following shows how to extend the current systems:

- Adding new types: For each system, new types can be introduced by extending the corresponding inductive type definition, such as `ty`, `ty_E`, or `ty_A`. 

- Adding new language constructs: New language constructs can be introduced by extending the inductive type `tm` in `stlc_tae.v` and the corresponding extended syntax files.
- Adding new typing rules: For each system, new typing rules can be introduced by extending the corresponding inductive typing proposition, such as `has_type`, `has_type_E`, or `has_type_A`.

## Coq/Rocq Installation

1. Install opam
On Ubuntu or Debian, install opam using:

&emsp;&emsp; `# Update the system package index`

&emsp;&emsp; `sudo apt update`

&emsp;&emsp; `# Install the opam package manager.`

&emsp;&emsp; `sudo apt install opam`

&emsp;&emsp; On macOS with Homebrew, install opam using:

&emsp;&emsp; `# Install the opam package manager through Homebrew.`

&emsp;&emsp; `brew install opam`

&emsp;&emsp; If opam is already installed, verify that it is available:

&emsp;&emsp; `# Display the installed opam version.`

&emsp;&emsp; `opam --version`

2. Initialize opam

&emsp;&emsp; If opam has not previously been initialized, run:

&emsp;&emsp; `# Initialize opam and configure its default package repositories.`

&emsp;&emsp; `opam init`

&emsp;&emsp; `# Update the current shell environment so that opam-installed executables can be found.`

&emsp;&emsp; `eval "$(opam env)"`

&emsp;&emsp; Follow any instructions printed by opam init. Depending on the shell configuration, it may be necessary to run eval "$(opam env)" again after opening a new terminal.

3. Create an Isolated Coq Environment
Create a separate opam switch containing OCaml 4.14.2:

&emsp;&emsp; `# Create a new opam switch named "coq-8.17.1" using OCaml 4.14.2.`

&emsp;&emsp; `# The switch isolates this artifact's dependencies from other`

&emsp;&emsp; `# OCaml and Coq installations.`

&emsp;&emsp; `opam switch create coq-8.17.1 ocaml-base-compiler.4.14.2`

&emsp;&emsp; `# Configure the current shell to use the newly created switch.`

&emsp;&emsp; `eval "$(opam env --switch=coq-8.17.1)"` 

&emsp;&emsp; Install Coq 8.17.1 in this switch:

&emsp;&emsp; `# Install the exact Coq version used to develop and test the artifact.`

&emsp;&emsp; `opam install coq.8.17.1`

&emsp;&emsp; Verify that the correct Coq compiler is active:

&emsp;&emsp;  `# Display the installed Coq compiler version.`

&emsp;&emsp; `coqc --version`

&emsp;&emsp; The output should report Coq version 8.17.1.


## Compilation

To generate/update the `CoqMakefile` from `_CoqProject`:

`coq_makefile -f _CoqProject -o CoqMakefile`

Then, to compile/check all proof scripts listed in `_CoqProject`:

`make -f CoqMakefile all`

Compatibility tested with Coq `8.17.1`.
