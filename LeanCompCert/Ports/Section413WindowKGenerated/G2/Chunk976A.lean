import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk976A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360585883562989015, 360585946572917562⟩, ⟨(-349156814310445901), (-345004264176668509)⟩, true⟩

def state01 : KState := ⟨⟨360596984842800396, 360597047866124441⟩, ⟨(-1432776808765005939), (-1428622951165346081)⟩, true⟩

def words00 : List Nat := [360582411743412298, 360582411810073375, 360582411852363265, 360582411894920490, 360582411896241222, 360582411848821321, 360582411740375562, 360582411737293940, 360582411834012503, 360582411985422826]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 97600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 97600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360590174512568174, 360590237549388150⟩, ⟨(-767941497542241651), (-763786322539755355)⟩, true⟩

def words01 : List Nat := [360582412084007800, 360582412182747569, 360582412386119050, 360582412691751301, 360582412925410779, 360582413159276084, 360582413326981622, 360582413390234714, 360582413471531058, 360582413553295714]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 97610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 97600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599576150879629, 360599639201065554⟩, ⟨(-1685772207917213850), (-1681615728063983328)⟩, true⟩

def words02 : List Nat := [360582413697406848, 360582413879122768, 360582414008116150, 360582414137249795, 360582414190171381, 360582414304634206, 360582414504801614, 360582414705236717, 360582414824623512, 360582415002521404]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 97620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 97600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360613121380603208, 360613184444165092⟩, ⟨(-3008307973562845152), (-3004150187747239680)⟩, true⟩

def words03 : List Nat := [360582415215842093, 360582415429587984, 360582415723941525, 360582415913982984, 360582416008350157, 360582416102858430, 360582416279506928, 360582416508780944, 360582416825043108, 360582417141620595]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 97630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 97600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585085606286175, 360585148683389850⟩, ⟨(-270888380476315501), (-266729272378976065)⟩, true⟩

def words04 : List Nat := [360582417392619823, 360582417539192349, 360582417604748181, 360582417670692204, 360582417687903356, 360582417689321412, 360582417602059828, 360582417433381037, 360582417264430025, 360582417228797691]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 97640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 97600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk976A
