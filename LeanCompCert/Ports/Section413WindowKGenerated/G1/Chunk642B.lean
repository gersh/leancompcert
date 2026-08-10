import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk642A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk642B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk642A

def state06 : KState := ⟨⟨362478851099343132, 362478911973067498⟩, ⟨421179579343262904, 423821690445646562⟩, true⟩

def words05 : List Nat := [371285507940004929, 371285507907856843, 371285507908805242, 371285507911213005, 371285507825995227, 371285507802216015, 371285507777668723, 371285507752986298, 371285507492961297, 371285507393086883]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 64250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 64200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475217231148530, 362475278124302943⟩, ⟨654784088870528160, 657427448650812832⟩, true⟩

def words06 : List Nat := [371285507407972476, 371285507410175774, 371285507366098372, 371285507329690728, 371285507326983459, 371285507329391627, 371285507258705992, 371285507274958999, 371285507276609284, 371285507273962984]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 64260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 64200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497943873743494, 362498004786679775⟩, ⟨(-805959536751269703), (-803314905489684599)⟩, true⟩

def words07 : List Nat := [371285507199330696, 371285507285026979, 371285507493453773, 371285507501755921, 371285507503449513, 371285507472009833, 371285507513100555, 371285507515531604, 371285507663708537, 371285507860597579]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 64270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 64200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478613006563475, 362478673939247100⟩, ⟨436668884622961896, 439314785344331012⟩, true⟩

def words08 : List Nat := [371285508010217225, 371285508012403054, 371285507906911225, 371285507977094503, 371285508051711683, 371285508053897754, 371285507806154084, 371285507558866877, 371285507310624343, 371285507269241568]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 64280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 64200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476155306671527, 362476216259015651⟩, ⟨594743052861456742, 597390217655647250⟩, true⟩

def words09 : List Nat := [371285507274377859, 371285507386667513, 371285507481627053, 371285507483821488, 371285507387990947, 371285507257739325, 371285507213183906, 371285507215380996, 371285507073194276, 371285506931140934]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 64290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 64200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 64200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk642B
