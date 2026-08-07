import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk504

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362481186121907847, 362481222849880576⟩, ⟨190339844324224526, 191590428081764002⟩, true⟩

def state01 : KState := ⟨⟨362467474298373297, 362467511041322542⟩, ⟨881552459820920891, 882803798473503879⟩, true⟩

def words00 : List Nat := [371285024358314708, 371285024360010873, 371285024288590205, 371285024212135853, 371285024135059429, 371285024081154388, 371285023860416190, 371285023745752009, 371285023630522981, 371285023515007794]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 50400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 50400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362510209465501105, 362510246223647316⟩, ⟨(-1272932809406046976), (-1271680704595332980)⟩, true⟩

def words01 : List Nat := [371285023214563725, 371285023262364573, 371285023511087733, 371285023537204887, 371285023538508180, 371285023499214830, 371285023811169537, 371285023969006129, 371285024470391955, 371285024972490153]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 50410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 50400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362504242893297873, 362504279666655860⟩, ⟨(-972132904890183126), (-970880033024241260)⟩, true⟩

def words02 : List Nat := [371285025396945674, 371285025419020812, 371285025833562346, 371285026248987274, 371285026781104094, 371285026909445307, 371285027033054702, 371285027157225408, 371285027631559404, 371285028015230661]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 50420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 50400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362473321515852957, 362473358304389139⟩, ⟨587458555481972575, 588712192860759353⟩, true⟩

def words03 : List Nat := [371285028575796581, 371285029137046602, 371285029697827397, 371285029783756402, 371285029819085840, 371285029855218630, 371285030222650352, 371285030224334710, 371285030068226997, 371285029838744032]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 50430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 50400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494935080761838, 362494971884391243⟩, ⟨(-502731266764277935), (-501476868004977997)⟩, true⟩

def words04 : List Nat := [371285029769825996, 371285029789375690, 371285030164148742, 371285030539575906, 371285030842691007, 371285030844387051, 371285031077028034, 371285031360382324, 371285031805975286, 371285032004745548]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 50440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 50400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362492387833449867, 362492424652404537⟩, ⟨(-374194213884719304), (-372939041888001974)⟩, true⟩

def words05 : List Nat := [371285032168237422, 371285032332275344, 371285032756170175, 371285032985110495, 371285033333605119, 371285033682782512, 371285033961341303, 371285033963026194, 371285033864725528, 371285034013259693]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 50450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 50400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362495545775112497, 362495582609105524⟩, ⟨(-533541743827865739), (-532285812919872517)⟩, true⟩

def words06 : List Nat := [371285034553223973, 371285034672264151, 371285034708592633, 371285034745480240, 371285034901952138, 371285034912083952, 371285035284009826, 371285035656604835, 371285036028909010, 371285036239647422]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 50460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 50400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499577640693234, 362499614489925888⟩, ⟨(-737005841178654757), (-735749141048997479)⟩, true⟩

def words07 : List Nat := [371285036747205204, 371285037255648148, 371285038013560150, 371285038249143523, 371285038429242052, 371285038609840614, 371285038952846002, 371285039135894338, 371285039425786736, 371285039716425978]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 50470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 50400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479208585066553, 362479245449519446⟩, ⟨291262169748647419, 292519638272370221⟩, true⟩

def words08 : List Nat := [371285039997865144, 371285039999551420, 371285039935909319, 371285040047881545, 371285040209667765, 371285040211353605, 371285039850621425, 371285039490921254, 371285039130536660, 371285039064854609]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 50480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 50400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470980506488722, 362471017386114327⟩, ⟨706752691716631805, 708010926388837611⟩, true⟩

def words09 : List Nat := [371285038999634695, 371285039049816702, 371285039099937485, 371285039101623487, 371285038629279543, 371285038278111246, 371285037964531923, 371285037966247279, 371285037680208278, 371285037404458661]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 50490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 50400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 50400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk504
