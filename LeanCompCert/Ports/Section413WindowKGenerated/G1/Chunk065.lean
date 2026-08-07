import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk065

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362764179953665951, 362764180464026467⟩, ⟨(-1835712772205786959), (-1835710525412283207)⟩, true⟩

def state01 : KState := ⟨⟨362513772095049863, 362513772607058977⟩, ⟨(-207470838850821143), (-207468581332897573)⟩, true⟩

def words00 : List Nat := [371281846577091108, 371281854823661916, 371281872443898459, 371281890058810683, 371281914695605668, 371281914695788458, 371281907955732434, 371281900909840483, 371281903393124877, 371281908288009231]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 6500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 6500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362267417613116998, 362267418126776522⟩, ⟨1398271565899152017, 1398273834169720711⟩, true⟩

def words01 : List Nat := [371281927484916762, 371281946676006675, 371281965008843842, 371281965009027062, 371281952049738742, 371281946136458376, 371281940835007319, 371281940835190598, 371281910201146722, 371281877303796418]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 6510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 6500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362424510553573052, 362424511068874996⟩, ⟨373544951547136709, 373547230534692497⟩, true⟩

def words02 : List Nat := [371281844416453462, 371281835003955009, 371281813951399180, 371281804139798584, 371281794331148466, 371281780370124335, 371281744537827315, 371281727167490705, 371281715851309099, 371281715851498992]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 6520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 6500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483437919493920, 362483438436469602⟩, ⟨(-11494262752372360), (-11491972826761124)⟩, true⟩

def words03 : List Nat := [371281707092676502, 371281693850389461, 371281686127707973, 371281686127913327, 371281687591509859, 371281691825153630, 371281695933920175, 371281695934107117, 371281681253855343, 371281681522721435]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 6530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 6500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362323187938071777, 362323188456685191⟩, ⟨1037540738107587587, 1037543038752632295⟩, true⟩

def words04 : List Nat := [371281700404572026, 371281700404756071, 371281688279621050, 371281676061092075, 371281663846227908, 371281645476276646, 371281615544423356, 371281608884622224, 371281602226794849, 371281591974052006]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 6540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 6500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362558403095216357, 362558403615501985⟩, ⟨(-503806312288772607), (-503804000682614365)⟩, true⟩

def words05 : List Nat := [371281567794125896, 371281566868346468, 371281588256887173, 371281588257071688, 371281587057677339, 371281581551354929, 371281590040832688, 371281592515807618, 371281604224944420, 371281615930593799]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 6550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 6500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362557292721935749, 362557293243887833⟩, ⟨(-496941185730712073), (-496938863183930681)⟩, true⟩

def words06 : List Nat := [371281627632605468, 371281627632790612, 371281628183103512, 371281640042161323, 371281654671878564, 371281654672066556, 371281651733033066, 371281645327868484, 371281655669370714, 371281667180399182]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 6560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 6500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362627704653204200, 362627705176823744⟩, ⟨(-959483474513083916), (-959481141002654020)⟩, true⟩

def words07 : List Nat := [371281701827059563, 371281736463251031, 371281766807369817, 371281774398784533, 371281788441446352, 371281802479930651, 371281839627135216, 371281865209761346, 371281887374030297, 371281909531632641]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 6570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 6500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362657002178749300, 362657002704025254⟩, ⟨(-1151589721860723946), (-1151587377442417582)⟩, true⟩

def words08 : List Nat := [371281954770619971, 371281988597065767, 371282037916475961, 371282087220983217, 371282133119943262, 371282153970239330, 371282183962551478, 371282213945853042, 371282254998606848, 371282281511878021]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 6580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 6500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362701133962569799, 362701134489539442⟩, ⟨(-1442491909075804050), (-1442489553487609350)⟩, true⟩

def words09 : List Nat := [371282307819032920, 371282334118271731, 371282376233568924, 371282410098514117, 371282450797539476, 371282491484295742, 371282532168946527, 371282542345903025, 371282575466051190, 371282608576270603]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 6590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 6500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 6500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk065
