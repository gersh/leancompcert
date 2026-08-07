import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk479

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489112889698912, 362489145927918013⟩, ⟨(-188174507202984950), (-187105317173697192)⟩, true⟩

def state01 : KState := ⟨⟨362468800667735925, 362468833720356798⟩, ⟨784821706207167295, 785891586154925133⟩, true⟩

def words00 : List Nat := [371285239845391826, 371285239839590517, 371285239325000309, 371285239246020173, 371285239166247121, 371285239072905602, 371285238532845743, 371285237991781234, 371285237450076321, 371285237218293658]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 47900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 47900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362467557526015387, 362467590593002336⟩, ⟨844443262025583079, 845513830324464445⟩, true⟩

def words01 : List Nat := [371285236969229291, 371285237063197413, 371285237157792003, 371285237159386527, 371285236673987676, 371285236173621138, 371285235672437722, 371285235606270223, 371285235237997046, 371285234871598423]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 47910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 47900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362467151776012021, 362467184857278653⟩, ⟨864021642410818113, 865092895065931457⟩, true⟩

def words02 : List Nat := [371285234532791845, 371285234534579688, 371285234565040862, 371285234721031258, 371285234805338530, 371285234806934575, 371285234402457047, 371285234223876529, 371285234044484118, 371285233947515790]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 47920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 47900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484326887944425, 362484359983735908⟩, ⟨40737861859918928, 41809810762867748⟩, true⟩

def words03 : List Nat := [371285233572150192, 371285233190655352, 371285232859532991, 371285232861306517, 371285232697829651, 371285232668967807, 371285232639520227, 371285232579057389, 371285232127849861, 371285232111619990]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 47930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 47900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473840666393812, 362473873776403976⟩, ⟨543511490556052111, 544584121176488961⟩, true⟩

def words04 : List Nat := [371285232472130977, 371285232473726407, 371285232273305831, 371285231990180819, 371285231706435912, 371285231499603077, 371285231129774866, 371285231163006996, 371285231164208198, 371285231109483778]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 47940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 47900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362491839752707934, 362491872877159531⟩, ⟨(-319594131706403093), (-318520808548903653)⟩, true⟩

def words05 : List Nat := [371285231070757094, 371285231269742614, 371285231853187782, 371285231858131113, 371285231859368078, 371285231766045876, 371285231672118189, 371285231621458838, 371285231490675427, 371285231630968899]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 47950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 47900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483251194391505, 362483284333249207⟩, ⟨92275715962024933, 93349730109384781⟩, true⟩

def words06 : List Nat := [371285231778297885, 371285231779893996, 371285231349305840, 371285231352209516, 371285231459688159, 371285231461285879, 371285231097681846, 371285230699291623, 371285230333697972, 371285230335544588]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 47960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 47900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475851660643392, 362475884813866521⟩, ⟨447253983838491112, 448328687169628738⟩, true⟩

def words07 : List Nat := [371285230296088508, 371285230291341728, 371285230286071196, 371285230282450780, 371285229868938989, 371285229527186739, 371285229274383412, 371285229276010038, 371285229081189078, 371285228888213533]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 47970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 47900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491166143954984, 362491199311462985⟩, ⟨(-287528178468841555), (-286452789676311105)⟩, true⟩

def words08 : List Nat := [371285228933171842, 371285229023872697, 371285229402075982, 371285229780927676, 371285230061099694, 371285230062696636, 371285229829790222, 371285229897036651, 371285230299814639, 371285230425845342]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 47980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 47900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362477583074545385, 362477616256642734⟩, ⟨364434100040081794, 365510189046594040⟩, true⟩

def words09 : List Nat := [371285230489823023, 371285230554377456, 371285230842659686, 371285230967293432, 371285231160866685, 371285231355035546, 371285231546714954, 371285231548312423, 371285231208888720, 371285231052247872]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 47990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 47900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 47900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk479
