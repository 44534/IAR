IAR
===
[![Build Status](https://travis-ci.org/44534/IAR.svg?branch=master)](https://travis-ci.org/44534/IAR)

A module to translate deterministic Rabin automata into deterministic parity automata using Index Appearance Records (IARs).

Features
--------
* Translation using the procedure to translate Streett automata into parity automata with IARs
* Direct IAR translation for Rabin automata
* Optimizations for IAR procedures:
    * SCC decomposition
    * find a small parity automaton for each SCC

Programm
--------
IAR has the executable `IAR-exe` to apply the translations to automata. The automata have to be specified in Hanoi-Omega-Automata format.

The supported options are:
```
> IAR-exe -h
IAR-exe

Usage: IAR-exe [--streett] [--opt]
  translation of Rabin automata to parity automata using Index Appearance
  Records

Available options:
  -h,--help                Show this help text
  --streett                use IAR procedure for Streett automata
  --opt                    Use improvements (SCC decomposition and finding a
                           good initial state for each SCC)

```


Install
-------
Dependency: `omega-automata`

```
stack install
```
