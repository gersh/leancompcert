import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk903

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483865395732534, 362483988813758649⟩, ⟨94447479560725323, 101972163713664767⟩, true⟩

def state01 : KState := ⟨⟨362477149935959522, 362477273382039271⟩, ⟨700906096888479184, 708433314427972704⟩, true⟩

def words00 : List Nat := [371285118161259552, 371285118164410801, 371285118115196376, 371285118067527323, 371285118018596966, 371285118008462588, 371285117950872279, 371285117915501732, 371285117879096023, 371285117843498999]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 90300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 90300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362497526999900847, 362497650474462643⟩, ⟨(-1139451014105440750), (-1131921224207512212)⟩, true⟩

def words01 : List Nat := [371285117758785820, 371285117757193508, 371285117871092065, 371285117889547340, 371285117892011747, 371285117884012568, 371285117959682130, 371285117986935968, 371285118127829688, 371285118270166771]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 90310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 90300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484634710340609, 362484758213381925⟩, ⟨24986095823292130, 32518458137123646⟩, true⟩

def words02 : List Nat := [371285118360766772, 371285118363918700, 371285118308205875, 371285118329338284, 371285118385757283, 371285118388916116, 371285118318633709, 371285118249386884, 371285118206000819, 371285118209597326]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 90320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 90300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362478624827983253, 362478748359363585⟩, ⟨567933775222754571, 575468697547628877⟩, true⟩

def words03 : List Nat := [371285118311951789, 371285118419566904, 371285118526389750, 371285118529545524, 371285118515549627, 371285118492817449, 371285118523327982, 371285118526489055, 371285118458437661, 371285118391437391]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 90330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 90300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482814025307829, 362482937584940890⟩, ⟨189491613223344119, 197029088042328443⟩, true⟩

def words04 : List Nat := [371285118356024722, 371285118359596475, 371285118382885897, 371285118419716925, 371285118443564542, 371285118446717393, 371285118318749007, 371285118301689871, 371285118313124125, 371285118316407878]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 90340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 90300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362487382913787412, 362487506502195065⟩, ⟨(-223314468947100264), (-215774394198893124)⟩, true⟩

def words05 : List Nat := [371285118294650695, 371285118274227750, 371285118351016587, 371285118411018430, 371285118480583701, 371285118551380964, 371285118620981673, 371285118624134654, 371285118556719488, 371285118587118883]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 90350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 90300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479080554628701, 362479204171162463⟩, ⟨526931986476913990, 534474602845553404⟩, true⟩

def words06 : List Nat := [371285118728497968, 371285118731651015, 371285118710089825, 371285118669322371, 371285118627382047, 371285118591336830, 371285118492861759, 371285118483884613, 371285118473821753, 371285118463547608]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 90360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 90300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362496291990367349, 362496415635355034⟩, ⟨(-1028537728458146556), (-1020992540563111328)⟩, true⟩

def words07 : List Nat := [371285118457163918, 371285118517835357, 371285118699256400, 371285118735803518, 371285118751329860, 371285118767903402, 371285118834024396, 371285118840176626, 371285118967307514, 371285119095810627]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 90370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 90300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477723916965988, 362477847590414925⟩, ⟨649711831510945947, 657259591876748551⟩, true⟩

def words08 : List Nat := [371285119217715974, 371285119220869881, 371285119203159556, 371285119230781742, 371285119294216124, 371285119297371380, 371285119218114000, 371285119117942345, 371285119016533055, 371285118965477175]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 90380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 90300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362472053374713338, 362472177076628840⟩, ⟨1162288961935332890, 1169839295536063038⟩, true⟩

def words09 : List Nat := [371285118887211405, 371285118839979272, 371285118791656904, 371285118736226281, 371285118516758837, 371285118323477191, 371285118128555781, 371285118057043838, 371285117916356752, 371285117776800700]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 90390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 90300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 90300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk903
