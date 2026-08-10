import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk743A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360604384718853280, 360604420467747727⟩, ⟨(-1643660277241030642), (-1641866238912192880)⟩, true⟩

def state01 : KState := ⟨⟨360583726981590867, 360583762740547965⟩, ⟨(-108774751127619329), (-106979965094050285)⟩, true⟩

def words00 : List Nat := [360582323177018895, 360582323258538976, 360582323470489023, 360582323682755866, 360582323728392804, 360582323729449957, 360582323652649549, 360582323440625587, 360582323228401771, 360582323115659402]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 74300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 74300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360562780602584847, 360562816371503260⟩, ⟨1447936250411176478, 1449731776720713412⟩, true⟩

def words01 : List Nat := [360582323316681980, 360582323517920013, 360582323601763457, 360582323602820635, 360582323554689700, 360582323433475916, 360582323370342249, 360582323371399355, 360582323249897654, 360582322988520493]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 74310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 74300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587240088950894, 360587275867848858⟩, ⟨(-370008256918417464), (-368211988878643908)⟩, true⟩

def words02 : List Nat := [360582322726914887, 360582322519482646, 360582322464438429, 360582322527923559, 360582322528899817, 360582322437071953, 360582322350286274, 360582322225281282, 360582322120099268, 360582322187838114]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 74320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 74300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583095033315358, 360583130822309154⟩, ⟨(-61947426932816496), (-60150408422486534)⟩, true⟩

def words03 : List Nat := [360582322188789893, 360582322166433487, 360582322143891237, 360582322037487652, 360582322038372561, 360582321997936393, 360582321957384693, 360582321807783536, 360582321695318109, 360582321707440879]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 74330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 74300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360554847060160517, 360554882859106629⟩, ⟨2038147147317861729, 2039944905734800351⟩, true⟩

def words04 : List Nat := [360582321780921494, 360582321781978935, 360582321674797439, 360582321477323802, 360582321279683081, 360582321036746480, 360582320884744432, 360582320606272330, 360582320327707751, 360582319912310864]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 74340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 74300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk743A
