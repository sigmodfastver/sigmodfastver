Formal Proof of FastVer Verification protocol
=============================================

This repository contains the [F*](http://www.fstar-lang.org/) code for the mechanized proof of correctness of the verification protocol used in FastVer. The [F* website](http://www.fstar-lang.org/) contains information the language and instructions for installing F*.

### Overview

The following gives a brief overview of the F* files used in the proof:

- *Veritas.Verifier.fst:* contains the main verifier logic including implementation of the core api methods (add, evict, get, and put over records). 
- *Veritas.Key.fsti:* contains definitions of the key domain.
- *Veritas.Record.fsti:* contains definitions of data and merkle records.
- *Veritas.State.fsti:* contains correctness definitions including a formalization of sequential consistency
- *Veritas.Verifier.Correctness.fst:* contains the final lemma stating the correctness of the verification protocol. 

The final correctness lemma (lemma_verifier_correct) states that if all the verification checks pass and the get and put operations are *not* sequentially consistent, we can construct a hash collision. 
