import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk823A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk823B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk823A

def state06 : KState := ⟨⟨362484899843970808, 362485001785966123⟩, ⟨16221340168922598, 21890588184698886⟩, true⟩

def words05 : List Nat := [371285266377801572, 371285266704498306, 371285267019028123, 371285267137710402, 371285267258210333, 371285267380043095, 371285267575493680, 371285267578347307, 371285267577460690, 371285267577469095]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 82350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 82300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488313803437879, 362488415771049237⟩, ⟨(-264894255070253023), (-259222897196953283)⟩, true⟩

def words06 : List Nat := [371285267720455438, 371285267819763097, 371285268022766519, 371285268226898661, 371285268400970096, 371285268403824121, 371285268478361323, 371285268579141752, 371285268713375682, 371285268754536181]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 82360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 82300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488483898921143, 362488585892466723⟩, ⟨(-278866510538186978), (-273193016326371316)⟩, true⟩

def words07 : List Nat := [371285268794662145, 371285268835725183, 371285269023108711, 371285269138157887, 371285269298879491, 371285269460768149, 371285269624564135, 371285269627418406, 371285269634819213, 371285269678578492]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 82370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 82300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488770087758989, 362488872106782469⟩, ⟨(-302456399740597256), (-296780806528893176)⟩, true⟩

def words08 : List Nat := [371285269818693692, 371285269821555972, 371285269811352216, 371285269774250744, 371285269740870055, 371285269744050152, 371285269781785797, 371285269876459958, 371285269957784257, 371285270004531873]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 82380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 82300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362501568311772704, 362501670356599428⟩, ⟨(-1356926995236302529), (-1351249275964582779)⟩, true⟩

def words09 : List Nat := [371285270175481148, 371285270347931905, 371285270666260301, 371285270844460760, 371285270998913328, 371285271154204539, 371285271356880489, 371285271496125994, 371285271697084150, 371285271899348126]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 82390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 82300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 82300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk823B
