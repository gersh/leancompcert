import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk792A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk792B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk792A

def state06 : KState := ⟨⟨362484524049966690, 362484618184758370⟩, ⟨41192965134434734, 46231228484031360⟩, true⟩

def words05 : List Nat := [371285201621357123, 371285201566016443, 371285201572580347, 371285201589454265, 371285201608949583, 371285201629504655, 371285201636289175, 371285201639030815, 371285201474505758, 371285201470507601]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 79250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 79200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471440913731846, 362471535072940286⟩, ⟨1078207718068292310, 1083247916817538928⟩, true⟩

def words06 : List Nat := [371285201485338772, 371285201488076587, 371285201298384707, 371285201109233289, 371285200918999037, 371285200774140889, 371285200571758062, 371285200504111837, 371285200435509275, 371285200367715328]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 79260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 79200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490038089480527, 362490132273459813⟩, ⟨(-396087006616400980), (-391044844156756938)⟩, true⟩

def words07 : List Nat := [371285200197190286, 371285200129051036, 371285200146919793, 371285200149671191, 371285200087017154, 371285199981176949, 371285199874262060, 371285199850365919, 371285199817720143, 371285199883049037]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 79270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 79200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480183869467297, 362480278078203790⟩, ⟨385207442463319732, 390251567800074504⟩, true⟩

def words08 : List Nat := [371285199934058244, 371285199936845320, 371285199931975467, 371285200011319467, 371285200119254767, 371285200121995879, 371285200057163518, 371285199990019802, 371285199921742107, 371285199904005280]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 79280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 79200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362474281863727910, 362474376097111891⟩, ⟨853259010706082557, 858305090462741403⟩, true⟩

def words09 : List Nat := [371285199905859538, 371285199970875610, 371285200035030186, 371285200037770324, 371285199917166703, 371285199846904168, 371285199849898036, 371285199852639232, 371285199749957105, 371285199616537651]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 79290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 79200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 79200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk792B
