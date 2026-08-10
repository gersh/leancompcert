import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk896A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk896B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk896A

def state06 : KState := ⟨⟨362500142306515622, 362500263914379367⟩, ⟨(-1363557072186910731), (-1356195267352349375)⟩, true⟩

def words05 : List Nat := [371285137562017302, 371285137563169050, 371285137684481564, 371285137687613505, 371285137677415237, 371285137649550227, 371285137713283449, 371285137761177664, 371285137932004017, 371285138104190407]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 89650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 89600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485935855485019, 362486057491604422⟩, ⟨(-89794331802443954), (-82429993426123764)⟩, true⟩

def words06 : List Nat := [371285138255067559, 371285138258195338, 371285138304206615, 371285138355726405, 371285138432981760, 371285138436109731, 371285138361571228, 371285138277337557, 371285138228538201, 371285138242422121]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 89660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 89600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474073791629201, 362474195455940639⟩, ⟨974007794345520753, 981374660840933893⟩, true⟩

def words07 : List Nat := [371285138379071196, 371285138517042119, 371285138649060416, 371285138662790071, 371285138684081548, 371285138706914814, 371285138757654861, 371285138760782929, 371285138645997407, 371285138527537885]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 89670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 89600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478854060769711, 362478975753050264⟩, ⟨545314706424104981, 552684081335774899⟩, true⟩

def words08 : List Nat := [371285138409875643, 371285138413323170, 371285138355683817, 371285138349389202, 371285138342112783, 371285138314506157, 371285138120226802, 371285138010299984, 371285137909264496, 371285137912503222]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 89680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 89600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485627219991597, 362485748940813365⟩, ⟨(-62205761074744615), (-54833826162161167)⟩, true⟩

def words09 : List Nat := [371285137846177986, 371285137757116016, 371285137686457419, 371285137689964819, 371285137682077991, 371285137699436087, 371285137706927960, 371285137710112601, 371285137634533685, 371285137645218421]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 89690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 89600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 89600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk896B
