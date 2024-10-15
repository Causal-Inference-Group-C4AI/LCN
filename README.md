![Static Badge](https://img.shields.io/badge/build-passing-brightgreen?style=flat)
[![License](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)


# Logical Credal Networks
Logical Credal Networks (LCNs) is an expressive probabilistic logic that 
generalizes prior formalisms that combine logic and probability. Given imprecise information represented by probability bounds and conditional probability bounds 
on logic formulas, an LCN specifies a set of probability distributions over all 
its interpretations. LCNs allow propositional logic formulas with few 
restrictions, e.g., without requiring acyclicity and are endowed with a 
generalized Markov condition that allows us to identify implicit independence 
relationships between propositions. The package provides novel exact and 
approximate inference algorithms for computing posterior probability bounds on 
given query formulas as well as for generating most probable (partial) explanations of observed evidence in the network. 

An LCN program consists of two types of *probability-labeled sentences*:

$$l \le P(\phi) \le u$$
$$l \le P(\phi|\psi) \le u$$

where $l$ and $u$ are the lower and upper probability bounds, while $\phi$ and 
$\psi$ denote propositional logic formulas. 

For example the following two sentences represent a valid LCN program defined
over propositions `A, B` and `C`.

```
0.3 <= P(A) <= 0.5
0.4 <= P(!B or C | A) <= 0.7
```

### LCN Syntax
The LCN package supports the following basic syntax for LCN programs. An LCN program can be easily specified in a `.lcn` file. 

* An LCN *proposition* can be specified by any string as long as it starts with a letter
and does not contain spaces. For example `A`, `x1` or `Abc12` are valid LCN
propositions. 

* An LCN *formula* can be specified by a set of propositions connected by logical connectors. The following connectors can be used: `and`, `or`, `xor`, `nand`, and `not`. The
connectors can be specified by the following char symbols: `&`, `|`, `^`, `/` and `!`, 
respectively. In addition, it is possible to use paranthesis `()` for a more
readable formula. Furthermore, for increased readability we recommend using the 
long form logical connectors instead of their short form counterparts (i.e., use `and` instead of `&`).

The two types of LCN sentences can be specified as follows:

```
label: lb <= P(formula) <= ub
label: lb <= P(formula | formula) <= ub
```

where `label` is any string that starts with a letter and does not contain spaces. Note that each LCN sentence must have a unique label.

The LCN below encodes the following simple example: *Bronchitis* (`B`) is more likely than *Smoking* (`S`); *Smoking* may cause *Cancer* (`C`) or *Bronchitis*; *Dyspnea* (`D`) or shortness of breadth is a common symptom for *Cancer* and *Bronchitis*; in case of *Cancer* we have either a positive *X-Ray* result (`X`) and *Dyspnea*, or a negative *X-Ray* and no *Dyspnea*. 

```
# This line is a comment
# ... and so is this line :)

s1: 0.05 <= P(B) <= 0.1
s2: 0.3 <= P(S) <= 0.4
s3: 0.1 <= P((B or C) | S) <= 0.2
s4: 0.6 <= P(D | B and C) <= 0.7
s5: 0.7 <= P(!(X xor D) | C) <= 0.8
```

The folder `examples` contains additional LCN examples specified in the `.lcn`
file format described above.

## LCN Exact Inference
Given an LCN file and a query formula $\phi$, *marginal inference* means computing exact posterior lower and upper bounds on $P(\phi)$. An exact marginal inference algorithm is implemented by the `ExactInference` class (located in `lcn.inference.exact.marginal` module) and can be used to compute the probability bounds on the query formula. We give next a small example:

```
import lcn.inference.exact.marginal.ExactInference

# Specify the LCN program
file_name = "examples/asia.lcn"

# Create the LCN instance from the .lcn file
l = LCN()
l.from_lcn(file_name)

# Specify the query formula as a string
query = "(B and !C)"

# Run exact marginal inference
algo = ExactInferece(l)
algo.run(query, debug=True)
```
The output of the exact algorithm is shown below:

```
Parsed LCN format with 5 sentences.
Build the LCN's primal graph.
Build the LCN's structure graph.
Build the LCN's independence assumptions (LMC).
LCN
s2: 0.05 <= P(B) <= 0.1
s3: 0.3 <= P(S) <= 0.4
s4: 0.1 <= P((B or C) | S) <= 0.2
s5: 0.6 <= P(D | B and C) <= 0.7
s6: 0.7 <= P(!(X xor D) | C) <= 0.8

Local Markov Condition yields 2 independencies.
independence: (D ⟂ S | C, B, X)
independence: (X ⟂ B, S | D, C)
Solver status: ok
[Ipopt] objective=1.0, optimal=True
CONSISTENT
[Local Markov Condition: 2 independencies]
(D ⟂ S | C, B, X)
(X ⟂ B, S | D, C)
adding constraints for independence: (D ⟂ S | C, B, X)
adding constraints for independence: (X ⟂ B, S | D, C)
Solver status: ok
[Ipopt] objective=-7.927970481842095e-08, optimal=True
adding constraints for independence: (D ⟂ S | C, B, X)
adding constraints for independence: (X ⟂ B, S | D, C)
Solver status: ok
[Ipopt] objective=0.10000007033870394, optimal=True
[ExactInference] Result for (B and !C) is: [ 7.927970481842095e-08, 0.10000007033870394 ]
[ExactInference] Feasibility: lb=True, ub=True, all=True
[ExactInference] Time elapsed: 0.21419095993041992 sec
```

## LCN Approximate Inference
For approximate marginal inferece, we can use the ARIEL message-passing scheme implemented in the `ApproximateInference` class available in the `lcn.inference.approximate.marginal` module. The algorithm computes approximate lower and upper probability bounds on the posterior probability of the LCN's propositions. As before, we can use the following example:

```
import lcn.inference.approximate.marginal.ApproximateInference

# Specify the LCN program
file_name = "examples/asia.lcn"

# Create the LCN instance from the .lcn file
l = LCN()
l.from_lcn(file_name)

# Run exact marginal inference
algo = ApproximateInferece(l)
algo.run(n_iters=10, threshold=0.000001, debug=False)
```

The output of the approximate inference algorithm is shown below:

```
Parsed LCN format with 5 sentences.
Build the LCN's primal graph.
Build the LCN's structure graph.
Build the LCN's independence assumptions (LMC).
LCN
s2: 0.05 <= P(B) <= 0.1
s3: 0.3 <= P(S) <= 0.4
s4: 0.1 <= P((B or C) | S) <= 0.2
s5: 0.6 <= P(D | B and C) <= 0.7
s6: 0.7 <= P(!(X xor D) | C) <= 0.8

Local Markov Condition yields 2 independencies.
independence: (D ⟂ S | B, X, C)
independence: (X ⟂ S, B | D, C)
Solver status: ok
[Ipopt] objective=1.0, optimal=True
CONSISTENT
[ApproximateInference] Running marginal inference...
Iteration 0 ...
### Variable to factor messages ###
### Factor to variable messages ###
After iteration 0 average change in messages is 0.1156250431563193
Elapsed time per iteration: 0.3842339515686035 sec
Iteration 1 ...
### Variable to factor messages ###
### Factor to variable messages ###
After iteration 1 average change in messages is 0.06238024828227323
Elapsed time per iteration: 0.36359095573425293 sec
Iteration 2 ...
### Variable to factor messages ###
### Factor to variable messages ###
After iteration 2 average change in messages is 0.003005215647402235
Elapsed time per iteration: 0.37595176696777344 sec
Iteration 3 ...
### Variable to factor messages ###
### Factor to variable messages ###
After iteration 3 average change in messages is 5.561350752403057e-11
Elapsed time per iteration: 0.3729119300842285 sec
Converged after 3 iterations with delta=5.561350752403057e-11
[ApproximateInference] Marginals:
B: [0.04999999249186405, 0.10000000738802459]
S: [0.29999999253112253, 0.400000007458209]
C: [7.203050475106924e-08, 0.9541665925512998]
D: [0.0015000852157267832, 0.9992499145950501]
X: [6.919372188563531e-08, 0.9999999356848208]
[ApproximateInference] Time elapsed: 1.4968690872192383 sec
```

## MAP and Marginal MAP Inference for LCNs
In addition to marginal inference, the LCN package implements exact and approximate algorithms for computing complete or partial most probable explanations of evidence (i.e., observed truth values of a set of propositions) in a given LCN. The algorithms are based on depth-first search, limited discrepancy search or simulated annealing. We also provide an extension called AMAP of the ARIEL scheme for computing MAP and Marginal MAP explanations.


## Installation Instructions
For development and running experiments, we need to create a Python 3.10 
environment that contains the required dependencies. This can be done easily by
cloning the `LCN` git repository, creating a conda environment with Python 3.10
and installing the `LCN` package in that environment, as follows:

```
git clone git@github.com:IBM/LCN.git
cd LCN
conda create -n lcn python=3.10
conda activate lcn
pip install -e .
```

The LCN inference algorithms require the non-linear solver `ipopt`. To install 
the solver, follow the instructions below for `Linux` and `MacOS`. Unfortunately,
the LCN package is currently not supported on `Windows` systems.

### Installing ipopt on Linux

To install the `ipopt` solver on Linux, you can use the `coinbrew` tool. Simply download the `coinbrew` script from https://coin-or.github.io/coinbrew/ (make sure to also run `chmod u+x coinbrew`). `coinbrew` automates the download of the source code for ASL, MUMPS, and `Ipopt` and the sequential build and installation of these three packages. The
Linux installation requires the following dependencies before running the `coinbrew` tool.

* Ubuntu: `sudo apt-get install gcc g++ gfortran git cmake liblapack-dev pkg-config --install-recommends`
* Fedora: `sudo yum install gcc gcc-c++ gcc-gfortran git cmake lapack-devel`

After obtaining the `coinbrew` script, run:

```
/path/to/coinbrew fetch Ipopt --no-prompt
/path/to/coinbrew build Ipopt --prefix=/dir/to/install --test --no-prompt --verbosity=3
/path/to/coinbrew install Ipopt --no-prompt
```

Also, add the following to your `.bashrc` file:

```
export LD_LIBRARY_PATH=/dir/to/install/lib
export PATH="/dir/to/install/bin:$PATH"
```

### Installing ipopt on MacOS

Install `ipopt` on MacOS is straightforward by just running `brew install ipopt`


## References

If you found the LCN package useful, please cite the following papers:

```
@inproceedings{ lcn2022neurips,
    title={ Logical Credal Networks },
    author={ Marinescu, Radu and Qian, Haifeng and Gray, Alexander and Bhattacharjya, Debarun and Barahona, Francisco and Gao, Tian and Riegel, Ryan and Sahu, Pravinda },
    year={ 2022 },
    booktitle = { NeurIPS },
    url= {https://proceedings.neurips.cc/paper_files/paper/2022/file/62891522c00cf7323cbacb500e6cfc8d-Paper-Conference.pdf}
}

@inproceedings{ lcn2023ijcai,
    title={ Approximate Inference in Logical Credal Networks },
    author={ Marinescu, Radu and Qian, Haifeng and Gray, Alexander and Bhattacharjya, Debarun and Barahona, Francisco and Gao, Tian and Riegel, Ryan },
    year={ 2023 },
    booktitle = { IJCAI },
    url= {https://proceedings.neurips.cc/paper_files/paper/2022/file/62891522c00cf7323cbacb500e6cfc8d-Paper-Conference.pdf}
}

@article{ lcn2024ijar,
    title = {Markov Conditions and Factorization in Logical Credal Networks},
    journal = {International Journal of Approximate Reasoning},
    volume = {172},
    pages = {109237},
    year = {2024},
    doi = {https://doi.org/10.1016/j.ijar.2024.109237},
    url = {https://www.sciencedirect.com/science/article/pii/S0888613X24001245},
    author = {Fabio G. Cozman and Radu Marinescu and Junkyu Lee and Alexander Gray and Ryan Riegel and Debarun Bhattacharjya}
}

@inproceedings{ lcn2024neurips,
    title={ Abductive Reasoning in Logical Credal Networks },
    author={ Marinescu, Radu and Lee, Junkyu and Bhattacharjya, Debarun and Cozman, Fabio and Gray, Alexander },
    year={ 2024 },
    booktitle = { NeurIPS },
}

```

# Contact

Radu Marinescu (`radu.marinescu at ie dot ibm dot com`)