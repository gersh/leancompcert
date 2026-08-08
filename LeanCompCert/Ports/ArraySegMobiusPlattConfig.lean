import LeanCompCert.Ports.ArraySegSieve

/-!
# Literal aligned configurations for Platt's finite stronger range

The benchmark emitter may derive a `Cfg` from a range, but a proof receipt
must not depend on rerunning that emit-time prime enumeration.  This module
records the two literal configurations used by the aligned CompCert campaign.
Both root segment lengths divide `87903`, so the root walk stops exactly at
the formal cap.
-/

namespace LeanCompCert.Ports.ArraySegMobiusPlattConfig

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.ArraySegSieve

/-- The bootstrap primes through `293 = floor (sqrt 87903)`. -/
def plattBootPrimes : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
   59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
   127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
   191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
   257, 263, 269, 271, 277, 281, 283, 293]

/-- Opening link `[3, 7727054615]`, with three exactly aligned root windows. -/
def plattAlignedFirst : Cfg where
  lo := 3
  segLen := 29301
  segCount := 263713
  rootCount := 3
  bootPrimes := plattBootPrimes
  mainCount := 8534
  rootCap := 87903
  markSteps := 91684

/-- Tail link `[7727054616, 7727068586]`, with `29301` three-cell root windows. -/
def plattAlignedTail : Cfg where
  lo := 7727054616
  segLen := 3
  segCount := 4657
  rootCount := 29301
  bootPrimes := plattBootPrimes
  mainCount := 8534
  rootCap := 87903
  markSteps := 17086

def plattBootBound : Nat := 296

def plattFirstBootFuel : Nat := 0
def plattFirstLaterFuel : Nat := 1
def plattFirstMainFuel : Nat := 263713
def plattFirstDelta : Nat := 18446744073709463715

def plattTailBootFuel : Nat := 98
def plattTailLaterFuel : Nat := 29201
def plattTailMainFuel : Nat := 4657
def plattTailDelta : Nat := 7726966712

theorem plattAlignedFirst_shape :
    plattAlignedFirst.hi = 7727054615 ∧
    plattAlignedFirst.rootLen = 87903 ∧
    plattAlignedFirst.rootCap = 87903 ∧
    plattAlignedFirst.period = 120985 ∧
    plattAlignedFirst.rootSpan = 362955 ∧
    plattAlignedFirst.tableLen = 8534 ∧
    plattAlignedFirst.arrayLen = 96455 ∧
    plattAlignedFirst.wDelta = plattFirstDelta := by decide

theorem plattAlignedTail_shape :
    plattAlignedTail.hi = 7727068586 ∧
    plattAlignedTail.rootLen = 87903 ∧
    plattAlignedTail.rootCap = 87903 ∧
    plattAlignedTail.period = 17089 ∧
    plattAlignedTail.rootSpan = 500724789 ∧
    plattAlignedTail.tableLen = 8534 ∧
    plattAlignedTail.arrayLen = 8561 ∧
    plattAlignedTail.wDelta = plattTailDelta := by decide

theorem plattAligned_split :
    plattAlignedFirst.lo = 3 ∧
    plattAlignedFirst.hi + 1 = plattAlignedTail.lo ∧
    plattAlignedTail.hi + 1 = 7727068587 := by decide

end LeanCompCert.Ports.ArraySegMobiusPlattConfig
