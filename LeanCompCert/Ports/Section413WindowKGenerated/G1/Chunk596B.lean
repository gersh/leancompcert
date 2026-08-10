import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk596A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk596B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk596A

def state06 : KState := ⟨⟨362505951158927290, 362506003322406987⟩, ⟨(-1248959657739649497), (-1246857500229336391)⟩, true⟩

def words05 : List Nat := [371285102510845402, 371285102824478553, 371285103163547609, 371285103270898349, 371285103291209994, 371285103312166093, 371285103509251643, 371285103580266896, 371285103931950464, 371285104284505690]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 59650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 59600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362497801270849452, 362497853452597798⟩, ⟨(-762762960083069885), (-760659712576111419)⟩, true⟩

def words06 : List Nat := [371285104576767166, 371285104578788766, 371285104840287181, 371285105113553389, 371285105469906373, 371285105471925152, 371285105453710239, 371285105434883720, 371285105675617609, 371285105891595367]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 59660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 59600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485287223398570, 362485339423314845⟩, ⟨(-15910617223225738), (-13806285541183256)⟩, true⟩

def words07 : List Nat := [371285106388017790, 371285106885262373, 371285107380492785, 371285107501665953, 371285107601866718, 371285107703002629, 371285108056011116, 371285108077050144, 371285108082453419, 371285108088626399]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 59670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 59600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494191267883719, 362494243485899239⟩, ⟨(-547280649494559226), (-545175237557961336)⟩, true⟩

def words08 : List Nat := [371285108313407578, 371285108457147351, 371285108784964945, 371285109113568646, 371285109371455799, 371285109379110325, 371285109561049135, 371285109744064716, 371285110040391286, 371285110195494355]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 59680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 59600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502629652904048, 362502681889295994⟩, ⟨(-1050994107590656260), (-1048887598672859214)⟩, true⟩

def words09 : List Nat := [371285110344585250, 371285110494334214, 371285110924453583, 371285111215710598, 371285111590300042, 371285111965726508, 371285112269447177, 371285112284635995, 371285112580304426, 371285112877073873]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 59690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 59600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 59600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk596B
