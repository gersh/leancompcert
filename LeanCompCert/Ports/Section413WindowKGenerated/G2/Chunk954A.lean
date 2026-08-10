import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk954A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360585830170330920, 360585890265697437⟩, ⟨(-357723673567935071), (-353852391695478299)⟩, true⟩

def state01 : KState := ⟨⟨360580998477396974, 360581058585805568⟩, ⟨103206207822297623, 107078733972421719⟩, true⟩

def words00 : List Nat := [360582181309886818, 360582181350488844, 360582181351751294, 360582181284544184, 360582181217106669, 360582181122087658, 360582181081355465, 360582181034782081, 360582180988069824, 360582180886759058]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 95400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 95400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360603231230757999, 360603291352216615⟩, ⟨(-2018138406668575384), (-2014264635352010138)⟩, true⟩

def words01 : List Nat := [360582180947124282, 360582181019657117, 360582181201635127, 360582181366916455, 360582181439266818, 360582181511723463, 360582181555896353, 360582181668827502, 360582181891174473, 360582182113837726]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 95410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 95400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586708325260066, 360586768459881789⟩, ⟨(-441552846845046020), (-437677819438221410)⟩, true⟩

def words02 : List Nat := [360582182259999834, 360582182296821869, 360582182396861054, 360582182497330828, 360582182521911616, 360582182523294882, 360582182438473744, 360582182283836321, 360582182128936832, 360582182132384035]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 95420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 95400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360569732173953959, 360569792321622443⟩, ⟨1178542475426987695, 1182418747951906661⟩, true⟩

def words03 : List Nat := [360582182178876330, 360582182225613660, 360582182226851723, 360582182205065594, 360582182073584645, 360582181914571244, 360582181755132378, 360582181644349435, 360582181581896109, 360582181453516323]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 95430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 95400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360596453516196964, 360596513676918061⟩, ⟨(-1371854064979747114), (-1367976546649987516)⟩, true⟩

def words04 : List Nat := [360582181324825098, 360582181340977358, 360582181486526636, 360582181632338378, 360582181670622760, 360582181676604753, 360582181698814304, 360582181721423136, 360582181810142393, 360582181961727545]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 95440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 95400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk954A
