import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk721A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk721B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk721A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk721B
