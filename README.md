# Origin Essentialism // Computational Metaphysics
This repository contains the code for my [GSoC'19 project](https://summerofcode.withgoogle.com/projects/#5151227975827456) with [AOSSIE](http://aossie.org). 

## 1. Summary of Work
I formalised the arguments for origin essentialism given by Nathan Salmon (summarised [here](https://plato.stanford.edu/entries/essential-accidental/origin-essentialism.html)) and by Guy Rohrbaugh & Louis deRosset (in [this](https://doi.org/10.1093/mind/113.452.705) paper) in modal logic K and S5.

## 2. Details
* I used the modal logic formalisations previously created by [AOSSIE](https://gitlab.com/aossie/ComputationalPhilosophy/). [K](https://gitlab.com/aossie/ComputationalPhilosophy/blob/5296e31ff8115ff7ea2d6c900c32f101ec3322c3/Formalizations/Isabelle/QML.thy) and [S5](https://gitlab.com/aossie/ComputationalPhilosophy/blob/5296e31ff8115ff7ea2d6c900c32f101ec3322c3/Formalizations/Isabelle/QML_S5.thy) systems were used as they are.
* Every proof file has the author(s)'s original version mentioned in the beginning. 
* A total of six versions have been formalised using the [Isabelle](http://isabelle.in.tum.de/) theorem prover (v2019). 
* I used leibniz identity to denote *overlapping*. Hence, the arguments do not require *necessity of distinction*. I have also shown that *necessity of distinction* can be proved in K, hence the arguments can be proved in K. 
* Future work may include some other formalisation for *overlapping* instead leibniz identity (possibly mereology axioms), or a formalisation of the Four Worlds Paradox.

## 3. Working Paper
The working papers for different versions of the proofs presented can be viewed at:
* [K](https://drive.google.com/file/d/1KoYt8yCOEv5lXAUVeYvWpK40LoyLHi1k/view?usp=sharing)
* [S5](https://drive.google.com/file/d/10vvm-rPawmxUcBszhSrrpPtIO80sgF0a/view?usp=sharing)
* [S5 abriged](https://drive.google.com/file/d/1Cg8Hc4_QYMlmiFoPNe5EehNxbNqMqCfY/view?usp=sharing)
