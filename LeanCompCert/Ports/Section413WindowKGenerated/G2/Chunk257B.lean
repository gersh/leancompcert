import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk257A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk257B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk257A

def state06 : KState := ⟨⟨360624414800756254, 360624418739609245⟩, ⟨(-1060938286713949856), (-1060869650011881338)⟩, true⟩

def words05 : List Nat := [360583236123998942, 360583237576232521, 360583238405817913, 360583238406155166, 360583238271572088, 360583236618369256, 360583234965230507, 360583234312178045, 360583235911225412, 360583237510231043]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 25750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 25700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360645632845074423, 360645636787138530⟩, ⟨(-1607850013659969153), (-1607781294223385921)⟩, true⟩

def words06 : List Nat := [360583238266038510, 360583238817837085, 360583240872935550, 360583242927973689, 360583244597112736, 360583245851727463, 360583245928565343, 360583246005426062, 360583247136221613, 360583249557530701]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 25760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 25700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360611279786869660, 360611283732111585⟩, ⟨(-722149501677704340), (-722080700332627774)⟩, true⟩

def words07 : List Nat := [360583253480921208, 360583257404072522, 360583260107847102, 360583262927710160, 360583265353102911, 360583267778399529, 360583271291964385, 360583273308234505, 360583274395054324, 360583275481836863]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 25770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 25700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566997359849960, 360567001308283349⟩, ⟨419627135822036636, 419696019458885274⟩, true⟩

def words08 : List Nat := [360583276001646832, 360583277270839927, 360583278277070655, 360583279283288952, 360583279283603443, 360583279009006174, 360583277238149751, 360583276582359597, 360583275926516535, 360583274903454303]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 25780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 25700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360549349807202363, 360549353758850688⟩, ⟨874864912591956787, 874933879158137915⟩, true⟩

def words09 : List Nat := [360583274272775738, 360583272881884906, 360583271600026876, 360583272489672236, 360583272489961930, 360583271930646060, 360583271371336865, 360583270052481269, 360583267238800081, 360583265924709531]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 25790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 25700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 25700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk257B
