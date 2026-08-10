import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk458A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk458B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk458A

def state06 : KState := ⟨⟨360604302571296666, 360604315671787683⟩, ⟨(-968538677634054715), (-968132689763801093)⟩, true⟩

def words05 : List Nat := [360583201709598338, 360583202143218974, 360583203051370473, 360583203642217635, 360583203827580758, 360583204012979409, 360583204185998443, 360583204597776713, 360583205058625902, 360583205519593798]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 45850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 45800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360637012571466027, 360637025677946317⟩, ⟨(-2468989800474177410), (-2468583537906903528)⟩, true⟩

def words06 : List Nat := [360583205742486322, 360583205752952717, 360583206237811397, 360583206722855012, 360583207087020342, 360583207556705994, 360583207788456595, 360583208020265692, 360583208726322060, 360583209900267459]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 45860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 45800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360597356155602464, 360597369268006714⟩, ⟨(-649776681759879041), (-649370147431016983)⟩, true⟩

def words07 : List Nat := [360583211061855824, 360583212223505419, 360583213148049520, 360583213598626023, 360583213912713740, 360583214226953534, 360583214679116574, 360583215293355046, 360583215602415371, 360583215911553476]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 45870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 45800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360619865008017845, 360619878126358605⟩, ⟨(-1682722185998284986), (-1682315379273015288)⟩, true⟩

def words08 : List Nat := [360583216101603930, 360583216532237262, 360583217122163580, 360583217712183212, 360583217867353796, 360583217867982941, 360583217704025338, 360583217859491978, 360583218387650898, 360583219187148891]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 45880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 45800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360602036082558797, 360602049206903136⟩, ⟨(-864369576377936224), (-863962494119843272)⟩, true⟩

def words09 : List Nat := [360583219747383055, 360583220307671409, 360583221341689293, 360583222614048295, 360583223678082330, 360583224742172508, 360583225568514478, 360583226083277820, 360583226493885474, 360583226904684888]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 45890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 45800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 45800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk458B
