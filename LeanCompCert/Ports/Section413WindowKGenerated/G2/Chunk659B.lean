import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk659A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk659B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk659A

def state06 : KState := ⟨⟨360609824412780471, 360609852321365245⟩, ⟨(-1776355855411912976), (-1775112355838776854)⟩, true⟩

def words05 : List Nat := [360582939766427123, 360582939682061697, 360582939684910752, 360582939781726049, 360582939782583608, 360582939683568011, 360582939713942603, 360582939959608726, 360582940368371058, 360582940777334094]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 65950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 65900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360604112391734297, 360604140309197986⟩, ⟨(-1399637132423519909), (-1398393047154927503)⟩, true⟩

def words06 : List Nat := [360582941003463664, 360582941260939114, 360582941747699193, 360582942234718699, 360582942629150767, 360582942794494820, 360582942795329075, 360582942784707761, 360582942899500040, 360582943221884547]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 65960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 65900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360571642416879196, 360571670343096110⟩, ⟨742601010546651155, 743845673310697233⟩, true⟩

def words07 : List Nat := [360582943677813182, 360582944133905595, 360582944474906525, 360582944586812501, 360582944587609899, 360582944490091571, 360582944392305545, 360582944372747937, 360582944318297204, 360582944148390301]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 65970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 65900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580338160932895, 360580366095944608⟩, ⟨168967623085080282, 170212866172777956⟩, true⟩

def words08 : List Nat := [360582944036760964, 360582944273479303, 360582944739235237, 360582945205155084, 360582945474907574, 360582945515611045, 360582945540219206, 360582945565112447, 360582945565883008, 360582945469579595]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 65980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 65900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578835439515061, 360578863383381892⟩, ⟨268173665615986354, 269419493096494586⟩, true⟩

def words09 : List Nat := [360582945431321883, 360582945278260827, 360582945200319158, 360582945435770382, 360582945580978537, 360582945726350016, 360582945756120668, 360582945757051106, 360582945557695283, 360582945496913658]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 65990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 65900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 65900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk659B
