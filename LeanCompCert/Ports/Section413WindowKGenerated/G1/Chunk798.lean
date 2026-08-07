import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk798

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362472619074467723, 362472714546102054⟩, ⟨989922532953910678, 995067116025919046⟩, true⟩

def state01 : KState := ⟨⟨362459124288833696, 362459219785007778⟩, ⟨2066907993925344287, 2072054535395798349⟩, true⟩

def words00 : List Nat := [371285183905083837, 371285183907841696, 371285183701361452, 371285183495608114, 371285183288841128, 371285183088594045, 371285182823052840, 371285182596467506, 371285182368913912, 371285182127263082]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 79800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 79800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362486741005703666, 362486836526785161⟩, ⟨(-137302652321962778), (-132154122864491414)⟩, true⟩

def words01 : List Nat := [371285181803836011, 371285181638708946, 371285181472151832, 371285181463388349, 371285181323636751, 371285181145318556, 371285180965836975, 371285180944371778, 371285180871944730, 371285180895774970]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 79810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 79800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473928059416238, 362474023605432934⟩, ⟨885448759864092746, 890599279777448384⟩, true⟩

def words02 : List Nat := [371285180897893658, 371285180892537574, 371285180694231323, 371285180654217514, 371285180612806477, 371285180606709842, 371285180406845531, 371285180153738886, 371285179899488865, 371285179803350728]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 79820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 79800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362469386431580771, 362469482002456973⟩, ⟨1248057294518202416, 1253209799093800960⟩, true⟩

def words03 : List Nat := [371285179665474389, 371285179659171969, 371285179651918179, 371285179630193153, 371285179414117721, 371285179206266800, 371285178997021849, 371285178906787140, 371285178711438159, 371285178517976685]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 79830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 79800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481295266509548, 362481390862118053⟩, ⟨297285858037898578, 302440337369275772⟩, true⟩

def words04 : List Nat := [371285178323251047, 371285178286502127, 371285178250869637, 371285178313459006, 371285178349889871, 371285178352664648, 371285178338265668, 371285178411854432, 371285178465235763, 371285178468096379]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 79840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 79800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362480623833240071, 362480719453967043⟩, ⟨350931847886474825, 356088333053597079⟩, true⟩

def words05 : List Nat := [371285178422727016, 371285178373344508, 371285178404177076, 371285178410183992, 371285178463234143, 371285178517436324, 371285178568721349, 371285178571481530, 371285178413641062, 371285178361217902]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 79850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 79800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482732977962986, 362482828623282766⟩, ⟨182488611906591613, 187647061179516471⟩, true⟩

def words06 : List Nat := [371285178408094111, 371285178410854730, 371285178326929974, 371285178213645250, 371285178099280826, 371285178034218080, 371285177951551887, 371285177990581106, 371285178026423900, 371285178029332341]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 79860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 79800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488528237660661, 362488623907946570⟩, ⟨(-280406341845708106), (-275245898403871934)⟩, true⟩

def words07 : List Nat := [371285178033448478, 371285178068454434, 371285178258609201, 371285178261369740, 371285178242963476, 371285178199739825, 371285178174077213, 371285178177119531, 371285178162476014, 371285178208738951]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 79870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 79800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479122475183275, 362479218170383837⟩, ⟨470927801241032482, 476090234993698864⟩, true⟩

def words08 : List Nat := [371285178253832207, 371285178256611699, 371285178160959116, 371285178129952206, 371285178097531738, 371285178094695896, 371285177902898482, 371285177714209155, 371285177524364556, 371285177492389016]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 79880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 79800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362472251753848180, 362472347473912348⟩, ⟨1019857358604222607, 1025021778837527749⟩, true⟩

def words09 : List Nat := [371285177419701627, 371285177398225365, 371285177375877969, 371285177322341001, 371285177085721321, 371285176875786512, 371285176664400650, 371285176598023875, 371285176439631457, 371285176282158125]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 79890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 79800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 79800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk798
