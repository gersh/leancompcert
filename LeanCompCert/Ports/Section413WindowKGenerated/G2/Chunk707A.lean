import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk707A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360574239653733968, 360574271895004666⟩, ⟨575244933318650543, 576784613069558941⟩, true⟩

def state01 : KState := ⟨⟨360567131654242309, 360567163905052838⟩, ⟨1077723540293381945, 1079263894557605581⟩, true⟩

def words00 : List Nat := [360582429978711972, 360582429764341583, 360582429568064545, 360582429440722254, 360582429313107925, 360582429107401438, 360582428701855832, 360582428117313131, 360582427532588442, 360582427147798668]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 70700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 70700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360561401184905947, 360561433445152581⟩, ⟨1483003557911532248, 1484544579450116104⟩, true⟩

def words01 : List Nat := [360582426932755597, 360582426838605987, 360582426744359295, 360582426531221846, 360582426323364393, 360582426065379083, 360582425807106836, 360582425748571876, 360582425604339601, 360582425308549783]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 70710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 70700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586566275581343, 360586598545297469⟩, ⟨(-296866057847614088), (-295324366579335232)⟩, true⟩

def words02 : List Nat := [360582425012547744, 360582424712558912, 360582424511946027, 360582424477819589, 360582424443619164, 360582424212014011, 360582423780582372, 360582423510352501, 360582423239817070, 360582423228016796]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 70720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 70700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360566633780764782, 360566666060026532⟩, ⟨1113049399917396481, 1114591766394232151⟩, true⟩

def words03 : List Nat := [360582423228919026, 360582423163304697, 360582423097504252, 360582423184505776, 360582423185359930, 360582423118933185, 360582423052403698, 360582422832385117, 360582422455857351, 360582422234275815]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 70730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 70700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360571427670831588, 360571459959547458⟩, ⟨773888226125907584, 775431261433659584⟩, true⟩

def words04 : List Nat := [360582422012361646, 360582421760999848, 360582421569552179, 360582421278393921, 360582420987080003, 360582420645736068, 360582420431405834, 360582420378044722, 360582420324598595, 360582420118719666]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 70740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 70700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk707A
