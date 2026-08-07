import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk596

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362505735138813568, 362505787193314006⟩, ⟨(-1235542516297255170), (-1233446857232691466)⟩, true⟩

def state01 : KState := ⟨⟨362480637270674119, 362480689343334991⟩, ⟨260400983537921577, 262497725060851779⟩, true⟩

def words00 : List Nat := [371285092470815760, 371285092532118821, 371285092797941804, 371285093064775416, 371285093325618328, 371285093327634846, 371285093213165851, 371285093070928183, 371285092927866988, 371285092928724370]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 59600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 59600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478529463160299, 362478581554005927⟩, ⟨386142004578043696, 388239830183692676⟩, true⟩

def words01 : List Nat := [371285093064283482, 371285093274546955, 371285093487829124, 371285093489846831, 371285093378464372, 371285093352336329, 371285093578399637, 371285093580426180, 371285093566877029, 371285093459913068]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 59610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 59600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362512156834117155, 362512208942984355⟩, ⟨(-1618855729838759543), (-1616756829693606271)⟩, true⟩

def words02 : List Nat := [371285093524703778, 371285093590731037, 371285093908343084, 371285094226784362, 371285094501114856, 371285094543300208, 371285094866606745, 371285095190925475, 371285095796007269, 371285096252778026]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 59620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 59600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502375285976258, 362502427413274227⟩, ⟨(-1035519938019211203), (-1033419938755488101)⟩, true⟩

def words03 : List Nat := [371285096662776105, 371285097073449973, 371285097599246393, 371285097985518327, 371285098455148094, 371285098925521966, 371285099393689975, 371285099487365849, 371285099779278762, 371285100072371904]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 59630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 59600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486817653792195, 362486869799057085⟩, ⟨(-107540226789191839), (-105439155885362427)⟩, true⟩

def words04 : List Nat := [371285100524440687, 371285100726153250, 371285100916647649, 371285101107795459, 371285101367265642, 371285101487663809, 371285101721733395, 371285101956620784, 371285102166523346, 371285102198247621]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 59640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 59600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk596
