import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk721

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

def state06 : KState := ⟨⟨360565586049390354, 360565619690635821⟩, ⟨1206238231324339133, 1207877914946045431⟩, true⟩

def words05 : List Nat := [360582358877395336, 360582359047132732, 360582359120084099, 360582359121108696, 360582359074831915, 360582358980123122, 360582358918122307, 360582358919146628, 360582358806170817, 360582358575266449]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 72150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 72100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360591496595066829, 360591530245990519⟩, ⟨(-663646262371725684), (-662005880321824776)⟩, true⟩

def words06 : List Nat := [360582358344128854, 360582358384809498, 360582358385656345, 360582358370504793, 360582358355276765, 360582358159855090, 360582357772559408, 360582357577267895, 360582357381680347, 360582357505134472]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 72160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 72100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360589811608646844, 360589845269331719⟩, ⟨(-542028051410051501), (-540386964847325949)⟩, true⟩

def words07 : List Nat := [360582357506063048, 360582357489086839, 360582357645586026, 360582357943197327, 360582358192421716, 360582358441810108, 360582358545586840, 360582358546611373, 360582358610285171, 360582358715185236]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 72170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 72100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595124084447581, 360595157754780210⟩, ⟨(-925516616236582103), (-923874833250018151)⟩, true⟩

def words08 : List Nat := [360582358818242388, 360582358987072927, 360582359060073809, 360582359133202191, 360582359157470106, 360582359298521983, 360582359549800511, 360582359801267878, 360582359930845891, 360582360109183806]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 72180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 72100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582037547256064, 360582071227276817⟩, ⟨19223618086599009, 20866100506609015⟩, true⟩

def words09 : List Nat := [360582360283405889, 360582360457909759, 360582360661645007, 360582360674006975, 360582360674952135, 360582360523975975, 360582360372809436, 360582360233545934, 360582360234377478, 360582360231438959]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 72190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 72100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 72100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk721
