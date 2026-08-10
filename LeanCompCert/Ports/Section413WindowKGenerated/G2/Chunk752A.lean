import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk752A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk752A
