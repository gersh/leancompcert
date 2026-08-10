import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk721A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360594058528842657, 360594092111964864⟩, ⟨(-848902657557929861), (-847267166365400159)⟩, true⟩

def state01 : KState := ⟨⟨360624892491346114, 360624926084120042⟩, ⟨(-3072143365414592183), (-3070507178284669389)⟩, true⟩

def words00 : List Nat := [360582341352491025, 360582341819341890, 360582342477923186, 360582343136682179, 360582343605313928, 360582343960083410, 360582344310682674, 360582344661568624, 360582345204149352, 360582345795699626]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 72100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 72100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360623941307102441, 360623974909623888⟩, ⟨(-3003545893162665622), (-3001909003091569222)⟩, true⟩

def words01 : List Nat := [360582346257683574, 360582346719761562, 360582347292184482, 360582348045325797, 360582348749363813, 360582349453556213, 360582350060068442, 360582350522887874, 360582351100870443, 360582351679176563]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 72110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 72100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599202650386867, 360599236262563799⟩, ⟨(-1219324696527319164), (-1217687110053666528)⟩, true⟩

def words02 : List Nat := [360582352253210268, 360582352635492530, 360582352897660768, 360582353159939738, 360582353367176680, 360582353671006874, 360582353953070524, 360582354235336256, 360582354421630814, 360582354656734771]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 72120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 72100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360609840755534676, 360609874377372085⟩, ⟨(-1986766333135723272), (-1985128049803276442)⟩, true⟩

def words03 : List Nat := [360582354957539359, 360582355258633777, 360582355691564645, 360582355932824303, 360582355986772573, 360582356040773649, 360582356087032001, 360582356277786696, 360582356660068704, 360582357042572134]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 72130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 72100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360588042422921377, 360588076054527808⟩, ⟨(-414151268334429162), (-412512280218043092)⟩, true⟩

def words04 : List Nat := [360582357320160232, 360582357603227855, 360582357970924970, 360582358338922219, 360582358627686973, 360582358724810538, 360582358726027652, 360582358727359113, 360582358728207332, 360582358707849065]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 72140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 72100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk721A
