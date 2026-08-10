import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk573A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360579013073535346, 360579033899863154⟩, ⟨166168085078364601, 166974329669733995⟩, true⟩

def state01 : KState := ⟨⟨360593756936302566, 360593777770165686⟩, ⟨(-678700309979374466), (-677893633576383580)⟩, true⟩

def words00 : List Nat := [360581948140537177, 360581948402239746, 360581948512430996, 360581948622705218, 360581948623373949, 360581948746130906, 360581948984609024, 360581949223230168, 360581949229225228, 360581949436450058]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 57300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 57300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360607000359233151, 360607021200632527⟩, ⟨(-1437757574247958464), (-1436950465904389074)⟩, true⟩

def words01 : List Nat := [360581949877467307, 360581950318711813, 360581950934487891, 360581951246838830, 360581951301809379, 360581951356855461, 360581951501424881, 360581951842297507, 360581952280302371, 360581952718472335]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 57310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 57300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360571426417412874, 360571447266445184⟩, ⟨601289008993683916, 602096554891693976⟩, true⟩

def words02 : List Nat := [360581952924353604, 360581952925152913, 360581952827453254, 360581952623742004, 360581952419824460, 360581952137499745, 360581951551610386, 360581950786670928, 360581950021605049, 360581949561140661]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 57320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 57300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360531443701227370, 360531464557777964⟩, ⟨2893831349390214303, 2894639326350082909⟩, true⟩

def words03 : List Nat := [360581949499689168, 360581949621578965, 360581949622291749, 360581949560763823, 360581949267295383, 360581948896386760, 360581948525267813, 360581948145641146, 360581947462587554, 360581946583002068]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 57330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 57300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360560944281036187, 360560965145135396⟩, ⟨1202020461508861833, 1202828871342866819⟩, true⟩

def words04 : List Nat := [360581945703267500, 360581944924833558, 360581944331932762, 360581943639865733, 360581942947746678, 360581941998867554, 360581940850271502, 360581940006065254, 360581939161644637, 360581938621531959]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 57340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 57300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk573A
