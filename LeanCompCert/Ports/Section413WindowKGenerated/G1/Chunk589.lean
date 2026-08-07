import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk589

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362464595329793054, 362464646121013801⟩, ⟨1199266997091508992, 1201287805778787248⟩, true⟩

def state01 : KState := ⟨⟨362474334273724790, 362474385082736223⟩, ⟨625617847810883399, 627639704461635647⟩, true⟩

def words00 : List Nat := [371285041154804559, 371285041099231579, 371285040899315718, 371285040825181561, 371285040750468119, 371285040536367237, 371285039937383662, 371285039627875547, 371285039317368379, 371285039296018546]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 58900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 58900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471142093693728, 362471192920892924⟩, ⟨813755449948069467, 815778378131008679⟩, true⟩

def words01 : List Nat := [371285039116654292, 371285038941363351, 371285038876106071, 371285038878322315, 371285038901902722, 371285038958178133, 371285038992924224, 371285038994915544, 371285038679167705, 371285038446658895]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 58910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 58900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362470442837357424, 362470493682292039⟩, ⟨855008383774652323, 857032357019826381⟩, true⟩

def words02 : List Nat := [371285038266401635, 371285038268398312, 371285038030082611, 371285037793005950, 371285037555194685, 371285037406743199, 371285037173302587, 371285037086353666, 371285036998714714, 371285036909120816]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 58920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 58900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492589853603720, 362492640716540346⟩, ⟨(-450242347192643124), (-448217312997423622)⟩, true⟩

def words03 : List Nat := [371285036663688973, 371285036659658242, 371285036766032957, 371285036768025055, 371285036535341925, 371285036260158244, 371285035995023943, 371285035997239194, 371285036077143671, 371285036208422102]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 58930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 58900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362470362325935162, 362470413206854288⟩, ⟨859963894503629973, 861989988678214671⟩, true⟩

def words04 : List Nat := [371285036294531144, 371285036296533046, 371285036205784161, 371285036306229318, 371285036491561934, 371285036493554422, 371285036295235495, 371285036035362474, 371285035774717179, 371285035598519737]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 58940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 58900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362463109477326570, 362463160376202926⟩, ⟨1287640807240798699, 1289667960085281721⟩, true⟩

def words05 : List Nat := [371285035356900596, 371285035364152343, 371285035365642404, 371285035366747480, 371285035129178619, 371285034946460505, 371285034762735877, 371285034723800471, 371285034353469008, 371285033984752541]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 58950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 58900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476086320718269, 362476137237447498⟩, ⟨522480905300803104, 524509110838632956⟩, true⟩

def words06 : List Nat := [371285033615143660, 371285033364111349, 371285032987405240, 371285032899489979, 371285032810975513, 371285032679954869, 371285032164776040, 371285031938699228, 371285031742944855, 371285031745007930]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 58960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 58900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472914964899110, 362472965899746932⟩, ⟨709501503115337460, 711530777200209064⟩, true⟩

def words07 : List Nat := [371285031595679515, 371285031394543139, 371285031192621746, 371285031170965214, 371285031005544133, 371285030845691299, 371285030685152333, 371285030526060994, 371285030034997455, 371285029832897156]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 58970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 58900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474516255607547, 362474567208231922⟩, ⟨615093730789943419, 617124053428330845⟩, true⟩

def words08 : List Nat := [371285029629716657, 371285029606663585, 371285029422155417, 371285029237012543, 371285029051095187, 371285028933362864, 371285028726767834, 371285028744968152, 371285028746484918, 371285028711087124]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 58980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 58900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362500288520629785, 362500339491298530⟩, ⟨(-905335850353206865), (-903304463188068847)⟩, true⟩

def words09 : List Nat := [371285028645490698, 371285028758290894, 371285028987107627, 371285028989111238, 371285028944043127, 371285028846412098, 371285028935836331, 371285028983045444, 371285029243898876, 371285029505651032]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 58990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 58900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 58900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk589
