import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk629A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362513598431530282, 362513656657691490⟩, ⟨(-1779716905434758846), (-1777243133550540298)⟩, true⟩

def state01 : KState := ⟨⟨362492533277115572, 362492591522579748⟩, ⟨(-454584903972329214), (-452109917831460606)⟩, true⟩

def words00 : List Nat := [371285402477657996, 371285402696993470, 371285403168298881, 371285403640715157, 371285404138086252, 371285404332936038, 371285404527417150, 371285404722586256, 371285404905623827, 371285405022320152]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 62900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 62900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362481587949811328, 362481646214536948⟩, ⟨234110305849650993, 236586503823371201⟩, true⟩

def words01 : List Nat := [371285405354921546, 371285405688411595, 371285406004233875, 371285406017156458, 371285406106246819, 371285406196412028, 371285406445382441, 371285406447519178, 371285406387931725, 371285406330618057]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 62910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 62900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362499817014522171, 362499875298391860⟩, ⟨(-912960594738217276), (-910483192125014358)⟩, true⟩

def words02 : List Nat := [371285406465120988, 371285406534459790, 371285406671260144, 371285406808880378, 371285406905125331, 371285406907262480, 371285406752883748, 371285406803863434, 371285407106210278, 371285407338370170]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 62920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 62900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490999777929551, 362491058081221293⟩, ⟨(-358043458043622038), (-355564833099365072)⟩, true⟩

def words03 : List Nat := [371285407522597962, 371285407707511138, 371285408016118134, 371285408222409499, 371285408463871908, 371285408706163313, 371285408881486244, 371285408883623774, 371285408812104729, 371285408904482771]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 62930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 62900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491758267109779, 362491816589450463⟩, ⟨(-405739724068394793), (-403259900084925077)⟩, true⟩

def words04 : List Nat := [371285409225467260, 371285409320989876, 371285409415104849, 371285409510009357, 371285409680723278, 371285409761873789, 371285410025297639, 371285410289560110, 371285410552285256, 371285410656262986]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 62940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 62900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk629A
