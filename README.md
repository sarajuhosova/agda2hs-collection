# Agda2HS Collection

This repository contains a collection of Haskell programs, rewritten using Agda2HS.
It is meant to be able to showcase the abilities and limitations of Agda2HS, as well as to offer solutions for commonly occuring problems.

The following modules are included:

1. `HLedger`: with code extracted from the open source [hledger](https://github.com/simonmichael/hledger)
2. `git-mediate`: with code extracted from the open source [Git Mediate](https://github.com/Peaker/git-mediate)


## Using Agda2HS

To compile an Agda file to Haskell, run the following:

```bash
agda2hs <pathToFile>/<fileName>.agda -o _haskell
```

This will save the file under `_haskell/<moduleName>.hs`. `_haskell` is a gitignored directory.
