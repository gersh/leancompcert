import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk987A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk987B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk987A

def state06 : KState := ⟨⟨360580127019049513, 360580191594611914⟩, ⟨216434922637375621, 220741188492463659⟩, true⟩

def words05 : List Nat := [360582427262117080, 360582427192898145, 360582427123409393, 360582427047291940, 360582427027205512, 360582426981387645, 360582426935401012, 360582426838245128, 360582426743072597, 360582426722077411]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 98750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 98700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585887034320709, 360585951623423042⟩, ⟨(-352501510790416734), (-348193907667952222)⟩, true⟩

def words06 : List Nat := [360582426700611291, 360582426681273424, 360582426667294786, 360582426574539182, 360582426481551285, 360582426362987328, 360582426341834398, 360582426375522270, 360582426376810052, 360582426358844695]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 98760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 98700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360609370080405671, 360609434683044565⟩, ⟨(-2672048162536380702), (-2667739222341289080)⟩, true⟩

def words07 : List Nat := [360582426461526852, 360582426564628125, 360582426769728690, 360582426988150481, 360582427119065011, 360582427250074593, 360582427358291490, 360582427530869491, 360582427805436616, 360582428080334112]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 98770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 98700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595851993891950, 360595916610193690⟩, ⟨(-1336757857716386584), (-1332447567838805634)⟩, true⟩

def words08 : List Nat := [360582428293498241, 360582428404643996, 360582428599577429, 360582428794971738, 360582428935225433, 360582428973544909, 360582428974833259, 360582428933438436, 360582428931990169, 360582429070156250]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 98780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 98700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360577319674492919, 360577384304330124⟩, ⟨494110708972626098, 498422336086900130⟩, true⟩

def words09 : List Nat := [360582429154747286, 360582429239583946, 360582429272823254, 360582429274259335, 360582429237754740, 360582429175673038, 360582429113171762, 360582429113100426, 360582429114379289, 360582429064816834]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 98790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 98700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 98700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk987B
