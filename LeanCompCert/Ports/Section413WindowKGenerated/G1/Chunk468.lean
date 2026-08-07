import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk468

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362471716440774688, 362471747919237438⟩, ⟨636320587976254362, 637315919814626862⟩, true⟩

def state01 : KState := ⟨⟨362462242682679326, 362462274174992159⟩, ⟨1079778145835638907, 1080774125931064585⟩, true⟩

def words00 : List Nat := [371285365491153845, 371285365492735211, 371285365115100630, 371285364738701641, 371285364361748222, 371285363914547111, 371285363291659224, 371285363125017613, 371285362957876877, 371285362705774707]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 46800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 46800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362501893714489124, 362501925220852009⟩, ⟨(-776500082477307360), (-775503444629893998)⟩, true⟩

def words01 : List Nat := [371285362213601363, 371285362177743122, 371285362396008813, 371285362397563963, 371285362104373265, 371285361737302926, 371285361456191476, 371285361457927050, 371285361711119004, 371285362066612888]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 46810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 46800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484037515374301, 362484069035778323⟩, ⟨59527275495075499, 60524570821201067⟩, true⟩

def words02 : List Nat := [371285362422268011, 371285362423823891, 371285362267783505, 371285362286221818, 371285362441599282, 371285362443161976, 371285362163522419, 371285361779870445, 371285361465552481, 371285361467356824]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 46820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 46800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362464359835288116, 362464391369706527⟩, ⟨981224046978474398, 982221998671617364⟩, true⟩

def words03 : List Nat := [371285361868438247, 371285362297751060, 371285362683057086, 371285362684612840, 371285362462703923, 371285362240292798, 371285362017104667, 371285361984588469, 371285361542344341, 371285361096407459]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 46830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 46800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478285605101639, 362478317153442924⟩, ⟨328962234270091654, 329960838179972694⟩, true⟩

def words04 : List Nat := [371285360649785551, 371285360584066617, 371285360441132360, 371285360574461607, 371285360622317779, 371285360623874318, 371285360129608951, 371285360032753937, 371285360072602499, 371285360074215176]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 46840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 46800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362491943877716714, 362491975440245074⟩, ⟨(-311005072069017828), (-310005803423638166)⟩, true⟩

def words05 : List Nat := [371285359925075153, 371285359644554538, 371285359535955134, 371285359537689595, 371285359677698484, 371285359818317254, 371285359959146612, 371285359960730190, 371285359864199212, 371285360007296063]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 46850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 46800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480407916358070, 362480439492732279⟩, ⟨229656262418030888, 230656179952272326⟩, true⟩

def words06 : List Nat := [371285360604070603, 371285360605627469, 371285360596163592, 371285360539224885, 371285360481696140, 371285360418182438, 371285360352415189, 371285360547884121, 371285360681219031, 371285360682831539]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 46860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 46800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499857438792963, 362499889029290740⟩, ⟨(-682028767446876635), (-681028187872553861)⟩, true⟩

def words07 : List Nat := [371285360710177066, 371285360843376604, 371285361312143384, 371285361313703021, 371285361294080743, 371285361202689486, 371285361471847128, 371285361664770227, 371285361975730382, 371285362287372425]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 46870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 46800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362508922907257038, 362508954511804864⟩, ⟨(-1107127671011334918), (-1106126432696415704)⟩, true⟩

def words08 : List Nat := [371285362597006120, 371285362598574273, 371285362809582235, 371285363121787648, 371285363572215126, 371285363738966653, 371285363906136998, 371285364073838889, 371285364694855237, 371285365199725864]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 46880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 46800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482082587932023, 362482114206515815⟩, ⟨151604338200941362, 152606234733088196⟩, true⟩

def words09 : List Nat := [371285366003990531, 371285366808838085, 371285367428385701, 371285367442784686, 371285367591165455, 371285367740329279, 371285368212110143, 371285368213668428, 371285368138408791, 371285368070795839]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 46890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 46800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 46800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk468
