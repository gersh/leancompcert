import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk586A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362475626310994950, 362475676565798514⟩, ⟨545647270940222564, 547636564993724390⟩, true⟩

def state01 : KState := ⟨⟨362488464567443909, 362488514839979347⟩, ⟨(-206650143838319605), (-204659810609714565)⟩, true⟩

def words00 : List Nat := [371285021873530929, 371285021875712086, 371285022142410842, 371285022422987169, 371285022658082228, 371285022660061892, 371285022602069879, 371285022699824681, 371285022945580602, 371285023007207176]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 58600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 58600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362493397915636049, 362493448206197534⟩, ⟨(-495801714065600919), (-493810324237006261)⟩, true⟩

def words01 : List Nat := [371285023014386193, 371285023022189331, 371285023320580141, 371285023474867706, 371285023695517773, 371285023916938533, 371285024127159152, 371285024136425921, 371285024281484924, 371285024427615849]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 58610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 58600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483040324604070, 362483090632797988⟩, ⟨111393153925339870, 113385577458098588⟩, true⟩

def words02 : List Nat := [371285024781487546, 371285024783467818, 371285024749445684, 371285024715184387, 371285024680164159, 371285024646542488, 371285024493018565, 371285024521341711, 371285024548128616, 371285024550203039]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 58620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 58600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362505957496279088, 362506007822402784⟩, ⟨(-1232322652748933398), (-1230329177902296162)⟩, true⟩

def words03 : List Nat := [371285024776765422, 371285025037388261, 371285025477955008, 371285025618765828, 371285025711731037, 371285025805277494, 371285026163368007, 371285026404061816, 371285026763229520, 371285027123269033]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 58630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 58600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362495482208821642, 362495532552813228⟩, ⟨(-618083931252425637), (-616089408543219683)⟩, true⟩

def words04 : List Nat := [371285027428634213, 371285027430615404, 371285027524700713, 371285027663385807, 371285027852997704, 371285027855014074, 371285027836715623, 371285027822597702, 371285028042297160, 371285028223670618]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 58640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 58600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk586A
