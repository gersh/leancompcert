import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk639A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362499081361276012, 362499141528301496⟩, ⟨(-877070697120610352), (-874473871506872588)⟩, true⟩

def state01 : KState := ⟨⟨362499817082272637, 362499877268677811⟩, ⟨(-924095722778762523), (-921497658702018451)⟩, true⟩

def words00 : List Nat := [371285457166178780, 371285457331521640, 371285457423194773, 371285457515596000, 371285457681048614, 371285457725482226, 371285458014156894, 371285458303697634, 371285458589191935, 371285458817101369]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 63900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 63900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362515229306904167, 362515289512950423⟩, ⟨(-1909138850432394833), (-1906539530996023979)⟩, true⟩

def words01 : List Nat := [371285459261011182, 371285459706051978, 371285460395053793, 371285460758406469, 371285461084445575, 371285461411138295, 371285461795146509, 371285462078484175, 371285462546596085, 371285463015696062]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 63910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 63900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362503011064836786, 362503071290471799⟩, ⟨(-1128150786972500252), (-1125550215321102126)⟩, true⟩

def words02 : List Nat := [371285463429246843, 371285463568743302, 371285463914672876, 371285464261738654, 371285464682366377, 371285464777428170, 371285464872880370, 371285464969067741, 371285465309339262, 371285465587208577]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 63920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 63900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362494353419982673, 362494413665215106⟩, ⟨(-574597174907290463), (-571995350295874229)⟩, true⟩

def words03 : List Nat := [371285465964834797, 371285466343303582, 371285466705862985, 371285466836044681, 371285467026885378, 371285467218851872, 371285467564080105, 371285467707204068, 371285467848741143, 371285467991073384]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 63930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 63900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362498136838297061, 362498197102956835⟩, ⟨(-816497944899805294), (-813894878003014728)⟩, true⟩

def words04 : List Nat := [371285468332677579, 371285468553453135, 371285468898099788, 371285469243629278, 371285469520692934, 371285469522867165, 371285469582914485, 371285469694713591, 371285470050226693, 371285470251492386]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 63940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 63900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk639A
