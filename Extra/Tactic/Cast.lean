/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Extra.Cast.DCast

macro "elim_cast" : tactic => `(tactic| simp only [←heq_iff_eq, elim_cast] <;> try apply heq_of_eq)
