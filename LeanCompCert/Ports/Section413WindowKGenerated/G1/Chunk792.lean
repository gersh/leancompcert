import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk792

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489538057817936, 362489632044780421⟩, ⟨(-356114849407775378), (-351088298589131218)⟩, true⟩

def state01 : KState := ⟨⟨362483303495896517, 362483397507172013⟩, ⟨137710859685377959, 142739336223457543⟩, true⟩

def words00 : List Nat := [371285199384773297, 371285199398264863, 371285199400315187, 371285199394160880, 371285199387888968, 371285199390904875, 371285199393382658, 371285199467269661, 371285199541155845, 371285199543988368]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 79200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 79200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489363068579416, 362489457104597303⟩, ⟨(-342299486394353976), (-337269049889580452)⟩, true⟩

def words01 : List Nat := [371285199551735879, 371285199583667545, 371285199763596958, 371285199766333050, 371285199734213869, 371285199677038980, 371285199682769379, 371285199685816162, 371285199729034875, 371285199785832209]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 79210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 79200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362496218487230077, 362496312547921656⟩, ⟨(-885450261872464911), (-880417870590054225)⟩, true⟩

def words02 : List Nat := [371285199841640250, 371285199844408433, 371285199903041350, 371285200003829038, 371285200150347272, 371285200165365268, 371285200179207342, 371285200193932268, 371285200366696219, 371285200510075484]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 79220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 79200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477054709875592, 362477148795279654⟩, ⟨633058446822328863, 638092796196783255⟩, true⟩

def words03 : List Nat := [371285200811307230, 371285201113685256, 371285201361088976, 371285201414166366, 371285201466085833, 371285201519349106, 371285201641290166, 371285201644027293, 371285201553974635, 371285201455504248]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 79230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 79200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480486996233154, 362480581106128384⟩, ⟨361144000055214017, 366180290233781531⟩, true⟩

def words04 : List Nat := [371285201413214754, 371285201416232194, 371285201549300333, 371285201690987520, 371285201801828263, 371285201804565693, 371285201703018245, 371285201669029704, 371285201674776465, 371285201677613984]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 79240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 79200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk792
