import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk980A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk980B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk980A

def state06 : KState := ⟨⟨360618172756028002, 360618236384442483⟩, ⟨(-3514359508837910848), (-3510146452162765222)⟩, true⟩

def words05 : List Nat := [360582438118106233, 360582438372841670, 360582438689697827, 360582438990880433, 360582439203165140, 360582439415572913, 360582439731622695, 360582440111684095, 360582440477887865, 360582440844399421]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 98050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 98000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360597490115080841, 360597553757068069⟩, ⟨(-1486227236182500393), (-1482012848495813895)⟩, true⟩

def words06 : List Nat := [360582441158552479, 360582441369189833, 360582441577129075, 360582441785478591, 360582441926458645, 360582441963999595, 360582441965268568, 360582441938129714, 360582441969460849, 360582442125204462]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 98060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 98000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360580254341957276, 360580317997357025⟩, ⟨204195928547064242, 208411631666631214⟩, true⟩

def words07 : List Nat := [360582442358550822, 360582442592175013, 360582442752689221, 360582442809694660, 360582442840175392, 360582442871042688, 360582442899075866, 360582442930957098, 360582442932226091, 360582442912035519]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 98070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 98000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360594625728783923, 360594689397628791⟩, ⟨(-1205398817024800660), (-1201181795141572834)⟩, true⟩

def words08 : List Nat := [360582442973751071, 360582443110045295, 360582443312542982, 360582443515335362, 360582443629129043, 360582443639396659, 360582443640556700, 360582443632401477, 360582443685117673, 360582443811436974]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 98080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 98000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360604700932841693, 360604764615290713⟩, ⟨(-2193781293044900054), (-2189562936666506820)⟩, true⟩

def words09 : List Nat := [360582443857296659, 360582443903275392, 360582444034800281, 360582444218554054, 360582444345915885, 360582444473506010, 360582444538451025, 360582444681236242, 360582444909910211, 360582445139070629]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 98090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 98000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 98000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk980B
