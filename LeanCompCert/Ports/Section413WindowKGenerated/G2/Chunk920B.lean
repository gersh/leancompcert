import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk920A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk920B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk920A

def state06 : KState := ⟨⟨360593735262012494, 360593791068076101⟩, ⟨(-1091445818053904117), (-1087976617663719959)⟩, true⟩

def words05 : List Nat := [360581971901349432, 360581972170984930, 360581972436660919, 360581972584852195, 360581972624151472, 360581972663548129, 360581972700089808, 360581972811911319, 360581972941370263, 360581973071121216]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 92050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 92000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589753448317250, 360589809267071774⟩, ⟨(-724954623841294712), (-721484255065533990)⟩, true⟩

def words06 : List Nat := [360581973132278220, 360581973133609528, 360581973145952009, 360581973191138298, 360581973206457328, 360581973207795011, 360581973188567711, 360581973110297115, 360581973031774586, 360581973094389111]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 92060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 92000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360577199393270320, 360577255224571995⟩, ⟨430945679882270463, 434417203937951963⟩, true⟩

def words07 : List Nat := [360581973176729613, 360581973259308089, 360581973275220778, 360581973276555086, 360581973240350727, 360581973145375870, 360581973071364927, 360581973096901688, 360581973098104685, 360581973048246387]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 92070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 92000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593608366953605, 360593664210811315⟩, ⟨(-1080066291052514318), (-1076593610773276796)⟩, true⟩

def words08 : List Nat := [360581972998094393, 360581973000092025, 360581973154716671, 360581973309593248, 360581973352785321, 360581973354117487, 360581973384451407, 360581973443260995, 360581973541490782, 360581973669816286]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 92080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 92000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360570127386982691, 360570183243540002⟩, ⟨1082453426420276780, 1085927276266008162⟩, true⟩

def words09 : List Nat := [360581973738801360, 360581973807971196, 360581973877830110, 360581974007013690, 360581974093037983, 360581974179277675, 360581974203507618, 360581974204839406, 360581974111368829, 360581973984867538]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 92090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 92000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 92000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk920B
