import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk469A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk469B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk469A

def state06 : KState := ⟨⟨360551358875773632, 360551372639150300⟩, ⟨1480975269037196314, 1481412022934207368⟩, true⟩

def words05 : List Nat := [360582921295233787, 360582921402592663, 360582921403173504, 360582921193704112, 360582920838293255, 360582920368714915, 360582919898951679, 360582919881583833, 360582919562883419, 360582918891768150]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 46950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 46900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360591664549315603, 360591678318790491⟩, ⟨(-412031257438609715), (-411594217139715895)⟩, true⟩

def words06 : List Nat := [360582918220535433, 360582917898794041, 360582917807085351, 360582917704741778, 360582917602352606, 360582917108991044, 360582916409873045, 360582916029368476, 360582915648691975, 360582915588230365]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 46960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 46900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360582828866929413, 360582842642545926⟩, ⟨3021701777618867, 3459030579108053⟩, true⟩

def words07 : List Nat := [360582915588812040, 360582915455935736, 360582915542654203, 360582915990350561, 360582916320800038, 360582916651340160, 360582916651924911, 360582916630059339, 360582916271095444, 360582916270272174]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 46970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 46900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585718156485175, 360585731938178360⟩, ⟨(-132782541192781229), (-132344926878834137)⟩, true⟩

def words08 : List Nat := [360582916338950969, 360582916339599466, 360582916320090899, 360582916075034379, 360582915829871871, 360582915470834820, 360582915532184906, 360582915663108305, 360582915663689453, 360582915549361803]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 46980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 46900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360616604698858572, 360616618486653953⟩, ⟨(-1584430584117501591), (-1583992683031650287)⟩, true⟩

def words09 : List Nat := [360582915560410732, 360582915571644045, 360582916034098096, 360582916045109789, 360582916045707755, 360582915669223191, 360582915366878430, 360582915796404621, 360582916514005318, 360582917231722534]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 46990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 46900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 46900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk469B
