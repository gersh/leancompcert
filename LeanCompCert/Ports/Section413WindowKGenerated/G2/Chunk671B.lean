import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk671A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk671B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk671A

def state06 : KState := ⟨⟨360624384581239618, 360624413556088035⟩, ⟨(-2786511031416465021), (-2785196559382318741)⟩, true⟩

def words05 : List Nat := [360582940173377069, 360582940427789474, 360582940903218457, 360582941157489513, 360582941177118315, 360582941196814003, 360582941437609967, 360582941874305182, 360582942492577282, 360582943111047278]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 67150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 67100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360618956277511041, 360618985261379680⟩, ⟨(-2422086176914629104), (-2420771099037822656)⟩, true⟩

def words06 : List Nat := [360582943595142694, 360582943858041171, 360582944268854397, 360582944679934202, 360582944907635622, 360582945189926039, 360582945316820377, 360582945443804156, 360582945791799930, 360582946329414430]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 67160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 67100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360569048061090314, 360569077053899112⟩, ⟨930579500335517382, 931895178768519038⟩, true⟩

def words07 : List Nat := [360582946932149710, 360582947535061484, 360582948027259991, 360582948298307444, 360582948511691184, 360582948725329607, 360582948910583808, 360582948911532085, 360582948875641455, 360582948670135619]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 67170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 67100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360617684933895928, 360617713935656077⟩, ⟨(-2337105889494999828), (-2335789609664765914)⟩, true⟩

def words08 : List Nat := [360582948479065624, 360582948605986345, 360582948807572848, 360582949009342949, 360582949023048972, 360582949043163361, 360582949284165826, 360582949525446373, 360582949987514708, 360582950505886246]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 67180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 67100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578640943821104, 360578669954624844⟩, ⟨286499050650451605, 287815938165213415⟩, true⟩

def words09 : List Nat := [360582950913602411, 360582951321410415, 360582951652077284, 360582952093987363, 360582952443207317, 360582952792571579, 360582953002655400, 360582953003603902, 360582952992529066, 360582952929895160]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 67190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 67100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 67100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk671B
