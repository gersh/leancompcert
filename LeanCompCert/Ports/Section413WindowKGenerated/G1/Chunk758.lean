import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk758

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362504388089916372, 362504473889265538⟩, ⟨(-1464305308766526698), (-1459913407894945060)⟩, true⟩

def state01 : KState := ⟨⟨362482523846449057, 362482609669379345⟩, ⟨193047572365667025, 197441260805703251⟩, true⟩

def words00 : List Nat := [371285214293894967, 371285214301573095, 371285214325416782, 371285214350539852, 371285214427267863, 371285214429880414, 371285214318660478, 371285214207457631, 371285214095155385, 371285214091761692]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 75800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 75800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362466941650363565, 362467027496763533⟩, ⟨1374472114659789047, 1378867582453972469⟩, true⟩

def words01 : List Nat := [371285214172960027, 371285214289566962, 371285214392201320, 371285214394811700, 371285214265469217, 371285214166948194, 371285214067036046, 371285214040353744, 371285213800478175, 371285213563532908]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 75810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 75800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362470855594422977, 362470941464178995⟩, ⟨1077747474277904949, 1082144713048691433⟩, true⟩

def words02 : List Nat := [371285213325448136, 371285213262338359, 371285213111233507, 371285213026702448, 371285212941297500, 371285212825873798, 371285212512913000, 371285212360296891, 371285212206371083, 371285212131633152]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 75820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 75800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477979989129912, 362478065882732498⟩, ⟨537463748607231205, 541862795781383433⟩, true⟩

def words03 : List Nat := [371285211945431349, 371285211716303473, 371285211486095388, 371285211430867050, 371285211313481304, 371285211230303336, 371285211146274409, 371285211040327493, 371285210789012508, 371285210698077717]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 75830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 75800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474477444419802, 362474563361254349⟩, ⟨803136339202530139, 807537148408791875⟩, true⟩

def words04 : List Nat := [371285210666234197, 371285210668858116, 371285210565079078, 371285210459264281, 371285210352519757, 371285210230109928, 371285210019749799, 371285209967691221, 371285209914722359, 371285209862881361]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 75840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 75800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362498549047157489, 362498634987624988⟩, ⟨(-1022783780032915639), (-1018381178151534441)⟩, true⟩

def words05 : List Nat := [371285209732771939, 371285209744434286, 371285209928415341, 371285209976383163, 371285210007528961, 371285210039531749, 371285210216826264, 371285210324293514, 371285210503062425, 371285210682934152]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 75850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 75800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362495056913078570, 362495142877123972⟩, ⟨(-757899804759638726), (-753495414138265402)⟩, true⟩

def words06 : List Nat := [371285210861069513, 371285210863682073, 371285210956721839, 371285211083910135, 371285211262544768, 371285211297567418, 371285211299537694, 371285211300718896, 371285211472846096, 371285211606755343]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 75860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 75800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486184093114834, 362486270080731257⟩, ⟨(-84646868210893682), (-80240689133971222)⟩, true⟩

def words07 : List Nat := [371285211849672728, 371285212093679323, 371285212302280023, 371285212304893153, 371285212352858612, 371285212403982302, 371285212576258851, 371285212593584931, 371285212609492424, 371285212626439222]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 75870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 75800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487887569768113, 362487973580766103⟩, ⟨(-213855044784352797), (-209447091395783439)⟩, true⟩

def words08 : List Nat := [371285212755886536, 371285212799675234, 371285213015941600, 371285213233242857, 371285213422334822, 371285213432427815, 371285213491499582, 371285213551968958, 371285213700720193, 371285213739791603]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 75880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 75800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362490976191513038, 362491062226290656⟩, ⟨(-448254179697820279), (-443844421557186667)⟩, true⟩

def words09 : List Nat := [371285213762397099, 371285213785860430, 371285213936700611, 371285214041760359, 371285214183403655, 371285214326068027, 371285214464381611, 371285214466995326, 371285214470462564, 371285214550745444]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 75890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 75800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 75800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk758
