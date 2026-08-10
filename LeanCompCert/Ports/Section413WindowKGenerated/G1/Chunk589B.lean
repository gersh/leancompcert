import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk589A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk589B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk589A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk589B
