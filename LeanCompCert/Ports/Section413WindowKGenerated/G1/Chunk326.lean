import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk326

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362490527539073339, 362490542367787346⟩, ⟨(-189431796858361428), (-189105059731502614)⟩, true⟩

def state01 : KState := ⟨⟨362493447573184436, 362493462411389698⟩, ⟨(-284765438603475172), (-284438392013464676)⟩, true⟩

def words00 : List Nat := [371284741957220838, 371284741958272476, 371284740885935521, 371284740752768273, 371284740772858918, 371284740773931883, 371284740342602798, 371284739910089316, 371284739981732662, 371284740250400662]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 32600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 32600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362470249590078614, 362470264437760469⟩, ⟨471981073979926643, 472308429649432151⟩, true⟩

def words01 : List Nat := [371284741456674075, 371284742663291882, 371284743682657632, 371284743705481269, 371284743740204059, 371284743775460572, 371284744415732716, 371284744416785471, 371284743986206787, 371284743543513058]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 32610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 32600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484119466266910, 362484134323365136⟩, ⟨19547412849981177, 19875075730312509⟩, true⟩

def words02 : List Nat := [371284743594325512, 371284743620211171, 371284743963363960, 371284744306933045, 371284744483912515, 371284744484972321, 371284743820375548, 371284743424986473, 371284743426644507, 371284743427739342]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 32620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 32600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487232765146796, 362487247631850462⟩, ⟨(-81977125837284647), (-81649149485498425)⟩, true⟩

def words03 : List Nat := [371284743409860670, 371284743364519256, 371284744209532362, 371284744767421768, 371284745521586097, 371284746276097443, 371284746786619260, 371284746787672569, 371284746124722612, 371284746202682070]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 32630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 32600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474211525978577, 362474226402074800⟩, ⟨343108792085171803, 343437075058754303⟩, true⟩

def words04 : List Nat := [371284746669910087, 371284746670965713, 371284746170438855, 371284745685658628, 371284745200515223, 371284745003071115, 371284744606054279, 371284744876577528, 371284745147539389, 371284745148630964]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 32640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 32600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362510236511222146, 362510251396829347⟩, ⟨(-833206709920057978), (-832878116364548330)⟩, true⟩

def words05 : List Nat := [371284745326122995, 371284745826285666, 371284747261897854, 371284747684734426, 371284747882904772, 371284748081395446, 371284748845083235, 371284749140842579, 371284749922403648, 371284750704371537]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 32650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 32600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479215945857319, 362479230840990453⟩, ⟨180088449616581693, 180417354337623879⟩, true⟩

def words06 : List Nat := [371284751468752728, 371284751469824895, 371284752247342533, 371284753038823414, 371284754036751808, 371284754037805932, 371284753788015514, 371284753539759053, 371284753291115447, 371284753257713368]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 32660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 32600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362467427145822336, 362467442050451684⟩, ⟨565431340736716240, 565760555747406362⟩, true⟩

def words07 : List Nat := [371284753641313955, 371284754194353934, 371284754748342036, 371284754749399923, 371284754502893704, 371284754520667641, 371284755239896638, 371284755240951045, 371284754713527507, 371284754184960479]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 32670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 32600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476366856500617, 362476381770583330⟩, ⟨273212580007237631, 273542104002346851⟩, true⟩

def words08 : List Nat := [371284753655950368, 371284753613841529, 371284753223950856, 371284752926073971, 371284752627897133, 371284752176155497, 371284750625797936, 371284750010013220, 371284749530378477, 371284749531488878]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 32680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 32600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362469149218915205, 362469164142588385⟩, ⟨509266937192823383, 509596774749527047⟩, true⟩

def words09 : List Nat := [371284749276314746, 371284748900181573, 371284749079993726, 371284749170093774, 371284749435620291, 371284749701539897, 371284749781470440, 371284749782525576, 371284748617110541, 371284748141816200]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 32690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 32600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 32600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk326
