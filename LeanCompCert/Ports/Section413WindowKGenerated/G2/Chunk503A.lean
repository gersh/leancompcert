import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk503A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360621516610641449, 360621532490585214⟩, ⟨(-1991039154858956242), (-1990499429115018416)⟩, true⟩

def state01 : KState := ⟨⟨360581611710931158, 360581627597503638⟩, ⟨16276317649399856, 16816376849422300⟩, true⟩

def words00 : List Nat := [360581961262100474, 360581961811475607, 360581962221304980, 360581962631316366, 360581962942083847, 360581962942778458, 360581962859474448, 360581962527160495, 360581962194736496, 360581961852658666]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 50300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 50300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360566306376472164, 360566322269584479⟩, ⟨786474510290899770, 787014898543004372⟩, true⟩

def words01 : List Nat := [360581962234224146, 360581962622552467, 360581962781858894, 360581962884119845, 360581962884701805, 360581962794758299, 360581962891307858, 360581962892002708, 360581962780370487, 360581962470270946]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 50310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 50300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593105181765471, 360593121081444468⟩, ⟨(-562239588774858030), (-561698870054562974)⟩, true⟩

def words02 : List Nat := [360581962243386501, 360581962526614730, 360581962620735529, 360581962714973978, 360581962715619716, 360581962405286806, 360581961701101544, 360581961256840041, 360581960812384827, 360581960983889193]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 50320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 50300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360582322009867713, 360582337916160769⟩, ⟨(-19428799446714438), (-18887747807805290)⟩, true⟩

def words03 : List Nat := [360581960984509471, 360581960967046966, 360581961325293965, 360581961900841819, 360581962377172299, 360581962853605206, 360581962975454131, 360581962976149111, 360581962711796512, 360581962720042142]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 50330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 50300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360568777423606811, 360568793336444999⟩, ⟨662463512223729791, 663004893377048081⟩, true⟩

def words04 : List Nat := [360581963121916836, 360581963130365081, 360581963130984254, 360581962896437901, 360581962661774399, 360581962328408547, 360581962190889287, 360581961963584373, 360581961736215244, 360581961258855666]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 50340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 50300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk503A
