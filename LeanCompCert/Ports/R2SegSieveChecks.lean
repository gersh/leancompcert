/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Ports.R2SegSieve

/-! Closed kernel regressions, isolated from the production emitter API. -/

namespace LeanCompCert.Ports.R2SegSieve.Check

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve

def divOut (m p fuel : Nat) : Nat :=
  match fuel with
  | 0 => m
  | fuel + 1 => if 1 < p && m % p = 0 then divOut (m / p) p fuel else m

def tdAux (m d fuel : Nat) (acc : List Nat) : List Nat :=
  match fuel with
  | 0 => if 1 < m then acc ++ [m] else acc
  | fuel + 1 =>
      if m < d * d then (if 1 < m then acc ++ [m] else acc)
      else if m % d = 0 then tdAux (divOut m d m) (d + 1) fuel (acc ++ [d])
      else tdAux m (d + 1) fuel acc

def factorsTD (n : Nat) : List Nat := tdAux n 2 (n + 2) []

def refFold (S lo hi root d0 t0 p0 : Nat) : Nat × Nat :=
  let step := fun (acc : Nat × Nat × Nat) (n : Nat) =>
    let mt := jumpOf S n root (factorsTD n)
    if mt.1 = 4 then acc
    else
      let d := acc.1 + gammaStep S * (n - acc.2.2)
      let d := if mt.1 % 2 = 1 then d + mt.2 else d - mt.2
      (d, acc.2.1 + 1, n)
  let r := ((List.range (hi + 1)).drop lo).foldl step (d0, t0, p0)
  (r.1 + gammaStep S * (hi - r.2.2), r.2.1)

def refHead (S top root : Nat) : Nat × Nat :=
  let step := fun (acc : Nat × Nat) (n : Nat) =>
    let mt := jumpOf S n root (factorsTD n)
    let d := acc.1 + gammaStep S
    if mt.1 = 4 then (d, acc.2)
    else ((if mt.1 % 2 = 1 then d + mt.2 else d - mt.2), acc.2 + 1)
  ((List.range (top + 1)).drop 1).foldl step (biasOf S, 0)

def cfg : R2Cfg :=
  { lo := 6, segLen := 9, segCount := 1, sc := 4
    markSteps := 37, logSteps := 40, streamCap := 12
    table := [packEntry 2 11 1, packEntry 3 17 1] }

def seed : R2Seed :=
  { d := 268435475, err := 128, prev := 5, terms := 4
    sq := 2, sq2 := 9, ex := 2, th := 8, ln := 25, thr := 96, viol := 0 }

example : (seed.d, seed.terms) = refHead 4 5 3 := by decide

example : cfg.table.map (fun e =>
      (e % 2 ^ valBits, e / 2 ^ valBits % 2 ^ wtBits, e / 2 ^ 63)) =
    [(2, 11, 1), (3, 17, 1)] := by decide

end LeanCompCert.Ports.R2SegSieve.Check
