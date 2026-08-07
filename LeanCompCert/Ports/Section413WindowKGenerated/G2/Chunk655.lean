import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk655

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360555183048937681, 360555210554241470⟩, ⟨1812651034051165735, 1813868025883731125⟩, true⟩

def state01 : KState := ⟨⟨360583395022400061, 360583422536417545⟩, ⟨(-35389637419999287), (-34172074796826467)⟩, true⟩

def words00 : List Nat := [360582902773824455, 360582902431299961, 360582902208075167, 360582902125870511, 360582902043600904, 360582901732374654, 360582901427123944, 360582901191267605, 360582900955147482, 360582900912952832]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 65500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 65500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587453619167543, 360587481142003118⟩, ⟨(-301374704960871283), (-300156564622745031)⟩, true⟩

def words01 : List Nat := [360582900913783848, 360582900774186359, 360582900634427652, 360582900472404199, 360582900449309174, 360582900367982904, 360582900286552250, 360582900088682839, 360582899996768124, 360582900067773135]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 65510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 65500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360570751513921486, 360570779045441702⟩, ⟨793062353884527437, 794281063284767723⟩, true⟩

def words02 : List Nat := [360582900370927295, 360582900466069416, 360582900466892126, 360582900445518217, 360582900423995275, 360582900408838807, 360582900409605108, 360582900287522993, 360582900165352392, 360582899922342126]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 65520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 65500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360611215412255435, 360611242952495319⟩, ⟨(-1858832255755016634), (-1857612974912755418)⟩, true⟩

def words03 : List Nat := [360582899738126448, 360582899655122542, 360582899571853554, 360582899529023537, 360582899529877567, 360582899317013874, 360582899122568510, 360582899323715823, 360582899756925710, 360582900190332509]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 65530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 65500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593949521515360, 360593977070563653⟩, ⟨(-727237947928037895), (-726018089739565201)⟩, true⟩

def words04 : List Nat := [360582900443754469, 360582900465145529, 360582900718698441, 360582900972514562, 360582901167759369, 360582901295989185, 360582901307103553, 360582901318326755, 360582901319078946, 360582901448685428]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 65540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 65500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360569145828347719, 360569173386092866⟩, ⟨898861034428996767, 900081462740296687⟩, true⟩

def words05 : List Nat := [360582901850681882, 360582902252845467, 360582902538477857, 360582902656241415, 360582902657028118, 360582902614778523, 360582902761228104, 360582902762152055, 360582902719969531, 360582902511515995]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 65550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 65500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585849378479706, 360585876944951147⟩, ⟨(-196189828914062558), (-194968828464970386)⟩, true⟩

def words06 : List Nat := [360582902302853308, 360582902396996070, 360582902771467118, 360582903146104138, 360582903326502962, 360582903327426951, 360582903411382623, 360582903548013736, 360582903548778290, 360582903544690896]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 65560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 65500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360573736052734546, 360573763628003738⟩, ⟨598116155361955899, 599337732724022069⟩, true⟩

def words07 : List Nat := [360582903545519828, 360582903413075656, 360582903280455233, 360582903351838839, 360582903352613673, 360582903330309565, 360582903307889344, 360582903169234354, 360582902798524858, 360582902660219719]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 65570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 65500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595727032086493, 360595754616073080⟩, ⟨(-844193675753819314), (-842971526661347818)⟩, true⟩

def words08 : List Nat := [360582902614340808, 360582902687382769, 360582902688229140, 360582902575379753, 360582902462386839, 360582902220574503, 360582902292024014, 360582902444322687, 360582902480221518, 360582902677138450]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 65580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 65500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360602630284489461, 360602657877198391⟩, ⟨(-1297077275851699102), (-1295854554617793136)⟩, true⟩

def words09 : List Nat := [360582903056154107, 360582903435438744, 360582903778152943, 360582903889225226, 360582903890077738, 360582903803545689, 360582903716850338, 360582903693955859, 360582903995834207, 360582904297914268]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 65590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 65500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 65500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk655
