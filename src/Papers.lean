/-
Copyright (c) Philip Wadler. All rights reserved.
Released under Creative Commons CC-BY License as described in file LICENSE.
Author: Philip Wadler
-/

import VersoManual
open Verso.Genre.Manual

/-!
src.Papers: Bibliography
-/

-- Here, `inlines!` is a macro that parses a string constant into Verso inline elements

def someThesis : Thesis where
  title := inlines!"A Great Thesis"
  author := inlines!"A. Great Student"
  year := 2025
  university := inlines!"A University"
  degree := inlines!"Something"

def somePaper : InProceedings where
  title := inlines!"Grommulation of Flying Lambdas"
  authors := #[inlines!"A. Great Student"]
  year := 2025
  booktitle := inlines!"Proceedings of the Best Conference Ever"

def someArXiv : ArXiv where
  title := inlines!"Grommulation of Flying Lambdas"
  authors := #[inlines!"A. Great Student"]
  year := 2025
  id := "...insert arXiv id here..."
