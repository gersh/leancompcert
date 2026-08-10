import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk921A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk921B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk921A

def state06 : KState := ⟨⟨362487312182021887, 362487440939502960⟩, ⟨(-223751195433382880), (-215739373547084728)⟩, true⟩

def words05 : List Nat := [371285100014812648, 371285099971003965, 371285099996202950, 371285100011339276, 371285100029860848, 371285100049547972, 371285100061405624, 371285100064650606, 371285100013401040, 371285100042881319]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 92150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 92100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483576668572620, 362483705454777717⟩, ⟨120571350912808997, 128585820154282495⟩, true⟩

def words06 : List Nat := [371285100155008687, 371285100191287142, 371285100227134655, 371285100264039013, 371285100335839625, 371285100350181081, 371285100427804202, 371285100506765601, 371285100545492518, 371285100548844705]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 92160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 92100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362507068557829663, 362507197373130785⟩, ⟨(-2044797465466324960), (-2036780314294597906)⟩, true⟩

def words07 : List Nat := [371285100620976455, 371285100709878691, 371285100914765724, 371285101000260383, 371285101066096568, 371285101133036281, 371285101316175735, 371285101441856373, 371285101683745672, 371285101927059528]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 92170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 92100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491729349764065, 362491858194142830⟩, ⟨(-630810996458014494), (-622791164759317552)⟩, true⟩

def words08 : List Nat := [371285102168992112, 371285102254941208, 371285102367519575, 371285102481753148, 371285102621249705, 371285102624472693, 371285102607353227, 371285102591570960, 371285102672831524, 371285102749850445]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 92180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 92100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362473913187738964, 362474042061160023⟩, ⟨1011773049787446733, 1019795559041949185⟩, true⟩

def words09 : List Nat := [371285102836420700, 371285102924326187, 371285103010726924, 371285103013952853, 371285102966879774, 371285102957500720, 371285102982203743, 371285102985427260, 371285102866830221, 371285102750520565]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 92190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 92100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 92100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk921B
