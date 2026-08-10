import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk951A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360584084528812118, 360584144232242687⟩, ⟨(-193095447699256794), (-189261497747198208)⟩, true⟩

def state01 : KState := ⟨⟨360597218971647956, 360597278688073086⟩, ⟨(-1442225593043191808), (-1438390407242970938)⟩, true⟩

def words00 : List Nat := [360582154254350423, 360582154389758622, 360582154469835794, 360582154550050461, 360582154571121922, 360582154678456265, 360582154895921361, 360582155113654274, 360582155246342873, 360582155406778147]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 95100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 95100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360616592951864720, 360616652681294376⟩, ⟨(-3284981082946528893), (-3281144660222086493)⟩, true⟩

def words01 : List Nat := [360582155677438513, 360582155948512500, 360582156307372332, 360582156618178436, 360582156820776217, 360582157023498523, 360582157242583764, 360582157523627290, 360582157887390334, 360582158251460564]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 95110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 95100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360597903261403990, 360597963003993740⟩, ⟨(-1507243570324713162), (-1503405895749783172)⟩, true⟩

def words02 : List Nat := [360582158544546471, 360582158748004701, 360582158928931656, 360582159110240369, 360582159261539294, 360582159302913087, 360582159304141658, 360582159274094534, 360582159303274659, 360582159471015534]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 95120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 95100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360576110724754577, 360576170480319954⟩, ⟨566078232828677368, 569917141840838974⟩, true⟩

def words03 : List Nat := [360582159748742504, 360582160026731899, 360582160238629945, 360582160417918619, 360582160552356553, 360582160687157237, 360582160818819145, 360582160840605056, 360582160841854084, 360582160780318282]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 95130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 95100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593041312917972, 360593101081497843⟩, ⟨(-1044740491852276259), (-1040900344577330355)⟩, true⟩

def words04 : List Nat := [360582160740466237, 360582160832448176, 360582161034487180, 360582161236810556, 360582161345578199, 360582161367022878, 360582161416298790, 360582161465989202, 360582161507336007, 360582161623745667]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 95140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 95100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk951A
