import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk752

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360577007947906717, 360577044602922692⟩, ⟨390914545782321421, 392776317510497865⟩, true⟩

def state01 : KState := ⟨⟨360569994063758546, 360570030728990913⟩, ⟨918273293226190358, 920135833275870434⟩, true⟩

def words00 : List Nat := [360582267623766997, 360582267418930034, 360582267138838393, 360582267001935449, 360582266864745868, 360582266619057539, 360582266269362131, 360582265771057276, 360582265272539022, 360582264950946450]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 75200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 75200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360563634029205831, 360563670704514601⟩, ⟨1396652040089569531, 1398515338037214045⟩, true⟩

def words01 : List Nat := [360582264803036396, 360582264817996318, 360582264818959807, 360582264724722003, 360582264453640624, 360582264057726847, 360582263661509410, 360582263442046783, 360582263284243687, 360582263038176357]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 75210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 75200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576101849002828, 360576138534436752⟩, ⟨458807549060885260, 460671608671257248⟩, true⟩

def words02 : List Nat := [360582262791875301, 360582262547823731, 360582262496661974, 360582262559971110, 360582262560963115, 360582262445358658, 360582262235610901, 360582262202673091, 360582262169443014, 360582262043790352]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 75220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 75200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360566556019554161, 360566592715199295⟩, ⟨1176974656253293437, 1178839484102538009⟩, true⟩

def words03 : List Nat := [360582261963362286, 360582261771617554, 360582261579674132, 360582261469988938, 360582261448948316, 360582261342618783, 360582261236157525, 360582261029096873, 360582260645268521, 360582260438273492]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 75230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 75200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574775777175300, 360574812482919486⟩, ⟨558434192964255743, 560299780716032583⟩, true⟩

def words04 : List Nat := [360582260230906020, 360582260150839384, 360582260012618039, 360582259738290151, 360582259463789998, 360582259111166470, 360582258847107185, 360582258704121444, 360582258561032745, 360582258327181494]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 75240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 75200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360569172231320547, 360569208947177180⟩, ⟨980145321866609255, 982011670629465777⟩, true⟩

def words05 : List Nat := [360582258229106955, 360582258158679449, 360582258192712523, 360582258193784063, 360582258160827381, 360582257972923615, 360582257784837542, 360582257523091339, 360582257374436466, 360582257202168271]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 75250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 75200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360572318151686887, 360572354877746642⟩, ⟨743273146174842968, 745140262876469794⟩, true⟩

def words06 : List Nat := [360582257029749891, 360582256769126843, 360582256490098241, 360582256343451317, 360582256196503614, 360582256005062205, 360582255637097155, 360582255180241709, 360582254723192488, 360582254442817407]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 75260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 75200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360558694606046315, 360558731342214708⟩, ⟨1768748076113249805, 1770615953741507939⟩, true⟩

def words07 : List Nat := [360582254312180204, 360582254177620676, 360582254042954408, 360582253774131289, 360582253384160238, 360582252949793379, 360582252515107774, 360582252256926567, 360582252056759343, 360582251745425940]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 75270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 75200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580006764942384, 360580043511222788⟩, ⟨164253539889599519, 166122178801045563⟩, true⟩

def words08 : List Nat := [360582251433858027, 360582251258064273, 360582251170677625, 360582251135834543, 360582251100927453, 360582250896158908, 360582250514867935, 360582250265323779, 360582250015471743, 360582249942074177]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 75280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 75200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360545246391342183, 360545283147849490⟩, ⟨2781585298556102983, 2783454707501354025⟩, true⟩

def words09 : List Nat := [360582249913724146, 360582249797226050, 360582249680509952, 360582249553716775, 360582249533890869, 360582249374730348, 360582249215454298, 360582248949695583, 360582248507486390, 360582248017803028]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 75290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 75200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 75200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk752
