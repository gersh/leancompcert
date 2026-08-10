import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk578A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360618269747981653, 360618290954107632⟩, ⟨(-2102768416838216290), (-2101940314733217506)⟩, true⟩

def state01 : KState := ⟨⟨360623490389098885, 360623511602896638⟩, ⟨(-2404732509678738128), (-2403903964106455602)⟩, true⟩

def words00 : List Nat := [360581926312753334, 360581926493040049, 360581926972482199, 360581927452144336, 360581927738677239, 360581928032974796, 360581928176314404, 360581928319729757, 360581928762257935, 360581929482467889]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 57800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 57800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360566919580193517, 360566940801601756⟩, ⟨865980888354230028, 866809873926456706⟩, true⟩

def words01 : List Nat := [360581930290316152, 360581931098287994, 360581931678143080, 360581932036154630, 360581932267665633, 360581932499396281, 360581932690140901, 360581932690947799, 360581932583278665, 360581932324845037]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 57810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 57800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591185877206941, 360591207106226509⟩, ⟨(-537175971437285847), (-536346545740220589)⟩, true⟩

def words02 : List Nat := [360581932066222819, 360581932165708690, 360581932519404501, 360581932873246349, 360581932969935829, 360581932970743528, 360581932911206585, 360581932697203208, 360581932567162940, 360581932728371376]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 57820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 57800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360606047363718157, 360606068600426121⟩, ⟨(-1396735619689657604), (-1395905749336581694)⟩, true⟩

def words03 : List Nat := [360581932729090722, 360581932696059286, 360581932862640810, 360581933330819390, 360581933665563468, 360581934000429158, 360581934145677941, 360581934264764644, 360581934682677577, 360581935100843877]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 57830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 57800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360595451302291346, 360595472546609226⟩, ⟨(-783923661703652999), (-783093351154346879)⟩, true⟩

def words04 : List Nat := [360581935510239475, 360581935621543011, 360581935622268854, 360581935584780279, 360581935547162313, 360581935352357514, 360581935601963786, 360581935876711452, 360581935927771115, 360581936162602825]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 57840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 57800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk578A
