/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Ports.PsiSegSieve

/-!
# Kernel regression checks for the segmented `ψ` emitter

These closed toy evaluations are isolated from the production API because
their elaboration has a multi-gigabyte peak.  Editing a theorem below must not
invalidate `PsiSegSieve` or its production consumers.
-/

namespace LeanCompCert.Ports.PsiSegSieve.Check

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.LogFixed
open LeanCompCert.Ports.ArraySegSieve

def smallestFactorAux (n d fuel : Nat) : Nat :=
  match fuel with
  | 0 => n
  | fuel + 1 => if d * d > n then n else if n % d = 0 then d else
      smallestFactorAux n (d + 1) fuel

def smallestFactor (n : Nat) : Nat := smallestFactorAux n 2 n

def isPowerOf (p m fuel : Nat) : Bool :=
  match fuel with
  | 0 => m == 1
  | fuel + 1 =>
      if m == 1 then true
      else if p < 2 then false
      else if m % p == 0 then isPowerOf p (m / p) fuel else false

def lambdaFix (S n : Nat) : Nat :=
  if n < 2 then 0
  else
    let p := smallestFactor n
    if isPowerOf p n n then lnFix S p else 0

def refWindow (S lo hi : Nat) : Nat × Nat × Nat :=
  ((List.range (hi + 1)).drop lo).foldl (fun acc n =>
    let w := lambdaFix S n
    if w = 0 then acc else (acc.1 + w, acc.2.1 + 1, n)) (0, 0, lo - 1)

def cfg : PsiCfg :=
  { base :=
      { lo := 25, segLen := 8, segCount := 1, rootCount := 1
        bootPrimes := [2], mainCount := 3, rootCap := 5, markSteps := 29 }
    sc := 4
    streamCap := 5
    pp := [(25, 25), (27, 17), (32, 11)] }

def seed : PsiSeed :=
  { dlo := 134217695, dhi := 0, prev := 24, terms := 13
    sq := 4, sq2 := 25, ex := 4, th := 32 }

example : seed.dlo = biasOf 4 + (refWindow 4 2 24).1 - 2 ^ 4 * 24 := by decide

example : seed.terms = (refWindow 4 2 24).2.1 := by decide

example : cfg.pp = [(25, lnFix 4 5), (27, lnFix 4 3), (32, lnFix 4 2)] := by decide

end LeanCompCert.Ports.PsiSegSieve.Check
