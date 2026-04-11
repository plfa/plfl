Programming Language Foundations in Lean
Philip Wadler

Built using verso by David Thrane Christiansen


You can then build your book with:
```
$ lake exe plfl --output _out/html --depth 2
```

You can read the book with:
```
$ python3 -m http.server 8800 --directory _out/html/html-multi &
```


# Fabrizio Montezi's library

from: Fabrizio Montesi<famontesi@gmail.com>
to: behavioural-types@lists.cent.gla.ac.uk

Dear all,

As part of our recent project on choreographic programming (https://www.chords.dev/), which includes a major formalisation effort in the Lean theorem prover, we made a 'spin-off' general Lean library that already now includes many interesting definitions and theorems about concurrency.

You can find it here: https://github.com/cs-lean/cslib

The library already contains general definitions and theorems about labelled transition systems (LTSs) and their classes, bisimulation, weak bisimulation, simulation, trace equivalence, and many theorems about them. These results abstract from the concrete definition of the LTS, formalising much of the development in the textbook 'Introduction to Bisimulation and Coinduction' [Sangiorgi 2011]. As a demonstrative exercise, there's a formalisation of CCS and a proof that bisimilarity is a congruence.

If you see this as useful (either as a potential user or contributor), please get in touch! The aim of this library is to establish a base of useful definitions and theorems that should be kept API-compatible, in order to accelerate both research and teaching. I've already been contacted by people interested in adding various things (e.g., lambda-calculus). The more, the merrier. :-)

All the best,
Fabrizio

# Other resources

An Introduction to Lean 4: An Introduction to Formal Verification
https://www.uv.es/coslloen/Lean4/

The Hitchhiker's Guide to Lean
https://github.com/lean-forward/logical_verification_2025/blob/main/hitchhikers_guide_2025_desktop.pdf
