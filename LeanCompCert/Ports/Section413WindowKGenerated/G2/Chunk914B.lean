import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk914A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk914B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk914A

def state06 : KState := ⟨⟨360609109444405231, 360609164497259885⟩, ⟨(-2489365923009895745), (-2485965837266461489)⟩, true⟩

def words05 : List Nat := [360581982733314334, 360581982746464195, 360581982878652332, 360581982992603308, 360581982993849564, 360581982993441385, 360581983110470230, 360581983289719084, 360581983587979747, 360581983886537649]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 91450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 91400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360610964613635319, 360611019679091929⟩, ⟨(-2659072596384903212), (-2655671358005050160)⟩, true⟩

def words06 : List Nat := [360581984114355500, 360581984371364013, 360581984747501775, 360581985124020575, 360581985423072833, 360581985725382618, 360581985968041112, 360581986210833834, 360581986427796832, 360581986746708933]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 91460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 91400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360582316022712560, 360582371100617850⟩, ⟨(-38429520690167384), (-35027143569060780)⟩, true⟩

def words07 : List Nat := [360581987063203181, 360581987379941948, 360581987636533014, 360581987773958654, 360581987880605853, 360581987987650985, 360581988134392341, 360581988199880760, 360581988205244194, 360581988210798445]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 91470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 91400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588441614203180, 360588496704600872⟩, ⟨(-598884284756166283), (-595480764768675439)⟩, true⟩

def words08 : List Nat := [360581988211873061, 360581988274056733, 360581988334644285, 360581988395465068, 360581988396698649, 360581988360032510, 360581988232986117, 360581988124655945, 360581988015939667, 360581988077907879]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 91480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 91400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360598883232963941, 360598938335954556⟩, ⟨(-1554254140508926715), (-1550849468334961535)⟩, true⟩

def words09 : List Nat := [360581988090266582, 360581988102769492, 360581988234350242, 360581988465874913, 360581988643196245, 360581988820728585, 360581988906369409, 360581988973618624, 360581989159926397, 360581989346672090]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 91490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 91400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 91400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk914B
