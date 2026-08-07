import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk629

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

def state06 : KState := ⟨⟨362488223948267287, 362488282289973850⟩, ⟨(-183284333013875031), (-180803289850768813)⟩, true⟩

def words05 : List Nat := [371285410776801972, 371285410898433670, 371285411085710902, 371285411087848819, 371285410939112544, 371285410746678520, 371285410583461658, 371285410585858523, 371285410570741399, 371285410618782942]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 62950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 62900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477268114674010, 362477326475654075⟩, ⟨506489209856553604, 508971466577654472⟩, true⟩

def words06 : List Nat := [371285410673728362, 371285410675866600, 371285410394526368, 371285410338894691, 371285410282214109, 371285410234330543, 371285409926217902, 371285409612581487, 371285409298060083, 371285409236755833]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 62960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 62900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362467907595594066, 362467965975839926⟩, ⟨1096063449232491888, 1098546919215985470⟩, true⟩

def words07 : List Nat := [371285409233704564, 371285409359907874, 371285409486855177, 371285409488998057, 371285409377158424, 371285409268193790, 371285409265398144, 371285409267536830, 371285409040498215, 371285408765919571]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 62970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 62900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362503445579726020, 362503503979110718⟩, ⟨(-1142262294165743789), (-1139777618719140635)⟩, true⟩

def words08 : List Nat := [371285408490417316, 371285408467979230, 371285408418760411, 371285408521824413, 371285408605700527, 371285408607891619, 371285408748847058, 371285408947180122, 371285409396507013, 371285409685978062]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 62980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 62900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362501437702232958, 362501496121183555⟩, ⟨(-1015776897122915737), (-1013290989127113321)⟩, true⟩

def words09 : List Nat := [371285409972513654, 371285410259775703, 371285410650353361, 371285410916332624, 371285411245193037, 371285411574842228, 371285411846169111, 371285411877727575, 371285412134484771, 371285412392526437]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 62990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 62900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 62900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk629
