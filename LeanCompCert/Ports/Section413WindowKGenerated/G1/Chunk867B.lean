import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk867A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk867B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk867A

def state06 : KState := ⟨⟨362490355526506431, 362490469106787954⟩, ⟨(-463907510617632158), (-457253888356275550)⟩, true⟩

def words05 : List Nat := [371285198457915028, 371285198422563977, 371285198480015473, 371285198526730393, 371285198612916910, 371285198700236861, 371285198759605076, 371285198762675976, 371285198772322065, 371285198836869947]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 86750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 86700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489267194666986, 362489380801820460⟩, ⟨(-369447963564979552), (-362792009754769254)⟩, true⟩

def words06 : List Nat := [371285199015173996, 371285199093755650, 371285199171685719, 371285199250606792, 371285199317594299, 371285199320920792, 371285199452535908, 371285199587011216, 371285199722174025, 371285199773484326]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 86760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 86700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499367183519755, 362499480817960443⟩, ⟨(-1245831854391446877), (-1239173532729508301)⟩, true⟩

def words07 : List Nat := [371285199956395752, 371285200140898348, 371285200421780914, 371285200548875351, 371285200659293177, 371285200770661766, 371285200999932112, 371285201164969244, 371285201331620118, 371285201499529802]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 86770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 86700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494649661084530, 362494763322761754⟩, ⟨(-836466673629359221), (-829805988242596741)⟩, true⟩

def words08 : List Nat := [371285201666465292, 371285201669484331, 371285201779668272, 371285201903711867, 371285202037256571, 371285202061558439, 371285202085163847, 371285202109755912, 371285202240964025, 371285202354594057]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 86780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 86700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481070024713355, 362481183713627381⟩, ⟨342231825008132990, 348894874412152166⟩, true⟩

def words09 : List Nat := [371285202585305844, 371285202817275972, 371285203022661876, 371285203051888119, 371285203120859684, 371285203191324371, 371285203323800974, 371285203326820713, 371285203282638295, 371285203239830286]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 86790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 86700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 86700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk867B
