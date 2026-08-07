import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk920

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360603330728650825, 360603386459142765⟩, ⟨(-1974049672101722409), (-1970587426563738253)⟩, true⟩

def state01 : KState := ⟨⟨360600011326932429, 360600067070111119⟩, ⟨(-1668759590818383204), (-1665296178038569374)⟩, true⟩

def words00 : List Nat := [360581967399767584, 360581967442758100, 360581967603482354, 360581967764608563, 360581967895833449, 360581967934212276, 360581967935408664, 360581967914982231, 360581967990470876, 360581968188694348]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 92000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 92000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360574187099680598, 360574242855383939⟩, ⟨707526918706589028, 710991483942468762⟩, true⟩

def words01 : List Nat := [360581968475145626, 360581968761845737, 360581968989130236, 360581969181971637, 360581969264248602, 360581969346865121, 360581969431448455, 360581969432779197, 360581969426604185, 360581969344016220]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 92010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 92000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589770445088681, 360589826213371560⟩, ⟨(-726502688704823951), (-723036965838052629)⟩, true⟩

def words02 : List Nat := [360581969261130392, 360581969265754505, 360581969369640315, 360581969473777458, 360581969477279768, 360581969501117381, 360581969560306311, 360581969619879793, 360581969676452802, 360581969763198922]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 92020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 92000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360591223053687270, 360591278834644805⟩, ⟨(-860188641555918333), (-856721752178279955)⟩, true⟩

def words03 : List Nat := [360581969790516877, 360581969817979549, 360581969963088939, 360581970168028092, 360581970326463453, 360581970485138625, 360581970554830532, 360581970584971030, 360581970687180333, 360581970789836750]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 92030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 92000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360595750914840152, 360595806708345113⟩, ⟨(-1277000646559276597), (-1273532602254899543)⟩, true⟩

def words04 : List Nat := [360581971009926727, 360581971112512751, 360581971125283509, 360581971138166158, 360581971139280488, 360581971139154049, 360581971275883567, 360581971412874252, 360581971480409576, 360581971632112863]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 92040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 92000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk920
