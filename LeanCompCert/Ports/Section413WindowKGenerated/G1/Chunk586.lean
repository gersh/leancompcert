import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk586

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

def state06 : KState := ⟨⟨362485736933521271, 362485787295367583⟩, ⟨(-46416245555417905), (-44420675578549025)⟩, true⟩

def words05 : List Nat := [371285028662294938, 371285029101708775, 371285029481959815, 371285029483941308, 371285029554876310, 371285029635682949, 371285030006320513, 371285030022073254, 371285030036464050, 371285030051618269]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 58650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 58600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478475241529028, 362478525621084376⟩, ⟨379680980003671886, 381677588886914146⟩, true⟩

def words06 : List Nat := [371285030356741279, 371285030517702770, 371285030825976587, 371285031135054216, 371285031398744240, 371285031400726063, 371285031276836515, 371285031160845760, 371285031117394751, 371285031119446178]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 58660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 58600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484304514746159, 362484354912394663⟩, ⟨37660926092360410, 39658596590918132⟩, true⟩

def words07 : List Nat := [371285031010062969, 371285030873303995, 371285030803961229, 371285030806198154, 371285030890950303, 371285030978968670, 371285031065490730, 371285031067473088, 371285030766621030, 371285030757599008]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 58670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 58600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473966656599529, 362474017071928934⟩, ⟨644348390243894366, 646347098348575898⟩, true⟩

def words08 : List Nat := [371285030827670776, 371285030829664142, 371285030690201704, 371285030554669107, 371285030418404040, 371285030270623601, 371285029977399830, 371285029975672780, 371285029973224354, 371285029971883758]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 58680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 58600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502587417749590, 362502637850973650⟩, ⟨(-1035560242475294909), (-1033560484044322525)⟩, true⟩

def words09 : List Nat := [371285029811223786, 371285029839208199, 371285030156746436, 371285030158729394, 371285030089433912, 371285029984421835, 371285030031796917, 371285030043467480, 371285030344775394, 371285030646938893]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 58690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 58600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 58600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk586
