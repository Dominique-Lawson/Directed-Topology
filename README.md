# Directed Topology

## Description
This git repository is created with the goal of obtaining formal proofs in the field of Directed Topology written in the *Lean theorem prover* language.
In particular, it is our main aim to achieve a proof for a Van Kampen Theorem relating to directed topology. 

This is part of a Bachelor's Thesis for Leiden University, The Netherlands.

## Installation
Installing Lean can be done by following the [leanprover community website](https://leanprover-community.github.io/lean3/get_started.html).
Our project uses Lean version 3.50.3.

This repository can then be cloned using `leanproject get git@github.com:Dominique-Lawson/Directed-Topology.git`.
That will also install a local copy of MathLib.

In order to speed up verification, you might want to compile the `.lean` files into `.olean` files.
This is done by running `lean --make src/all.lean` in the root directory of this repository.

## Authors and acknowledgment
Student:  
Dominique Lawson.

Supervisors:  
Dr. H. Basold, Leiden University  
Dr. P. Bruin, Leiden University

## License
See LICENSE.md
