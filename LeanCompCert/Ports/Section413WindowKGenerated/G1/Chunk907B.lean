import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk907A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk907B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk907A

def state06 : KState := ⟨⟨362475913671065088, 362476038398279001⟩, ⟨816793044724632792, 824436250068527548⟩, true⟩

def words05 : List Nat := [371285122284242654, 371285122373991494, 371285122461709392, 371285122464877552, 371285122390697535, 371285122323223511, 371285122285311142, 371285122288484015, 371285122190788355, 371285122094291215]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 90750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 90700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477008650370547, 362477133405987982⟩, ⟨717413431819286155, 725059215210804825⟩, true⟩

def words06 : List Nat := [371285121996371968, 371285121935866007, 371285121829790517, 371285121776261659, 371285121721799172, 371285121648504771, 371285121457742886, 371285121381996220, 371285121304598530, 371285121278800705]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 90760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 90700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477017238520098, 362477142022974331⟩, ⟨716658703524505707, 724307104577775215⟩, true⟩

def words07 : List Nat := [371285121193169360, 371285121107562170, 371285121031975702, 371285121035505917, 371285120993886305, 371285120990284801, 371285120985524392, 371285120981551994, 371285120814879626, 371285120730889927]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 90770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 90700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472938210694672, 362473063023398208⟩, ⟨1086969754342075301, 1094620720015711947⟩, true⟩

def words08 : List Nat := [371285120645152513, 371285120647940455, 371285120524476677, 371285120362621805, 371285120199511709, 371285120065992520, 371285119870542651, 371285119797582382, 371285119723582489, 371285119645493326]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 90780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 90700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362484349169101962, 362484474010487991⟩, ⟨50948473860924283, 58602043759300879⟩, true⟩

def words09 : List Nat := [371285119514847422, 371285119491766465, 371285119561210767, 371285119564402097, 371285119552445084, 371285119521878163, 371285119490094587, 371285119478939457, 371285119410944881, 371285119407445693]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 90790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 90700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 90700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk907B
