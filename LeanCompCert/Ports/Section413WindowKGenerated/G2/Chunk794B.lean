import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk794A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk794B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk794A

def state06 : KState := ⟨⟨360611005574618518, 360611046677927453⟩, ⟨(-2292958255883486639), (-2290752405045829517)⟩, true⟩

def words05 : List Nat := [360582215732746638, 360582216149225586, 360582216543823172, 360582216780545225, 360582216881797398, 360582216983140544, 360582217080323104, 360582217312197548, 360582217675931982, 360582218039915777]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 79450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 79400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595060964367830, 360595102078503522⟩, ⟨(-1025995207061757667), (-1023788495877417547)⟩, true⟩

def words06 : List Nat := [360582218323201541, 360582218499276236, 360582218800818549, 360582219102717446, 360582219321221516, 360582219381880603, 360582219382892824, 360582219364362862, 360582219373082363, 360582219536496030]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 79460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 79400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360561853505361858, 360561894630205424⟩, ⟨1613163009555362192, 1615370571748162038⟩, true⟩

def words07 : List Nat := [360582219695620216, 360582219854941902, 360582219917860499, 360582219918996656, 360582219865564992, 360582219673898892, 360582219481905943, 360582219299534378, 360582219124452661, 360582218869910359]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 79470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 79400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360597023939999819, 360597065075567396⟩, ⟨(-1182328074821375721), (-1180119660230260201)⟩, true⟩

def words08 : List Nat := [360582218615117019, 360582218521721905, 360582218638075402, 360582218754644219, 360582218755710516, 360582218722456887, 360582218725331532, 360582218786738476, 360582218934496427, 360582219122437731]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 79480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 79400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360576509523175859, 360576550669579931⟩, ⟨448543507501604608, 450752783537838666⟩, true⟩

def words09 : List Nat := [360582219231079269, 360582219339864770, 360582219606390504, 360582219952308391, 360582220210328104, 360582220468524461, 360582220605651262, 360582220606787640, 360582220585935221, 360582220515913741]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 79490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 79400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 79400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk794B
