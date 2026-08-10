import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk636A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk636B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk636A

def state06 : KState := ⟨⟨360602118396579301, 360602144319047075⟩, ⟨(-1239983800159684718), (-1238869035289976828)⟩, true⟩

def words05 : List Nat := [360582682076323399, 360582682126180067, 360582682345232615, 360582682700159892, 360582682942103254, 360582683184184502, 360582683237838971, 360582683297882370, 360582683604308481, 360582683911021911]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 63650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 63600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360586171707340894, 360586197638236443⟩, ⟨(-224814314698261590), (-223699013274679326)⟩, true⟩

def words06 : List Nat := [360582684206250667, 360582684317033663, 360582684317831097, 360582684304557662, 360582684291152585, 360582684052390331, 360582684087988205, 360582684229580208, 360582684230379487, 360582684280298376]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 63660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 63600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360608742125144394, 360608768064500171⟩, ⟨(-1661911827714814085), (-1660795987586785675)⟩, true⟩

def words07 : List Nat := [360582684582696664, 360582684885365072, 360582685333836797, 360582685811086295, 360582686084421251, 360582686357808699, 360582686774432219, 360582687314271410, 360582687724572423, 360582688135045754]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 63670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 63600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360618017974259756, 360618043922145307⟩, ⟨(-2252786920210516885), (-2251670536865421067)⟩, true⟩

def words08 : List Nat := [360582688421393280, 360582688625927124, 360582688985514409, 360582689345362902, 360582689603394473, 360582689867720101, 360582689938028543, 360582690008429377, 360582690324997502, 360582690881105515]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 63680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 63600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360590883012672664, 360590908968999014⟩, ⟨(-524344407870498551), (-523227486888953773)⟩, true⟩

def words09 : List Nat := [360582691683227234, 360582692485495241, 360582693093693452, 360582693456566856, 360582693757050831, 360582694057762634, 360582694604492359, 360582694906010488, 360582695035759790, 360582695165653872]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 63690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 63600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 63600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk636B
