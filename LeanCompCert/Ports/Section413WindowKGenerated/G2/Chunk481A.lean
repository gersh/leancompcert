import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk481A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360531407671998670, 360531422140373394⟩, ⟨2459047724761258290, 2459517988908438372⟩, true⟩

def state01 : KState := ⟨⟨360577889461413542, 360577903936032415⟩, ⟨222982525003052777, 223453089525174451⟩, true⟩

def words00 : List Nat := [360582554507988591, 360582553777598841, 360582553264571772, 360582552818696045, 360582552372781404, 360582551563182153, 360582550464973279, 360582549688065993, 360582548910995481, 360582548564789954]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 48100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 48100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360586002753598683, 360586017234533158⟩, ⟨(-167490474483504891), (-167019606087278283)⟩, true⟩

def words01 : List Nat := [360582548468850696, 360582548010899766, 360582547552843093, 360582547223026563, 360582547219500336, 360582547108250700, 360582546996932654, 360582546621602313, 360582546335895971, 360582546408779594]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 48110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 48100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360558716968867248, 360558731456035685⟩, ⟨1145655102349872992, 1146126270755958974⟩, true⟩

def words02 : List Nat := [360582546911912970, 360582546983689501, 360582546984284982, 360582546837290532, 360582546690208032, 360582546150134817, 360582545883900539, 360582545540839683, 360582545197720655, 360582544592764461]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 48120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 48100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360577310994540680, 360577325487971144⟩, ⟨250725616493187224, 251197086320930392⟩, true⟩

def words03 : List Nat := [360582544098543372, 360582544034896923, 360582544238170453, 360582544267682456, 360582544268293256, 360582543927300835, 360582543586191626, 360582543648441421, 360582543648989774, 360582543541280678]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 48130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 48100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577727573282749, 360577742073026647⟩, ⟨230465838614052050, 230937612401191736⟩, true⟩

def words04 : List Nat := [360582543433485867, 360582543110478399, 360582542356231324, 360582541861782094, 360582541367175972, 360582540764999352, 360582540314127760, 360582539532035224, 360582538749848359, 360582538285122207]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 48140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 48100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk481A
