import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk844A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360560558056963064, 360560604647819767⟩, ⟨1840898067421268023, 1843553658803139295⟩, true⟩

def state01 : KState := ⟨⟨360586969423482064, 360587016025776075⟩, ⟨(-388339674020487444), (-385683117272526344)⟩, true⟩

def words00 : List Nat := [360582447442827874, 360582447325636349, 360582447280696063, 360582447257662622, 360582447234538678, 360582447073775932, 360582446916540371, 360582446899896745, 360582446882902743, 360582446916095198]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 84400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 84400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360565091345238198, 360565137959099423⟩, ⟨1458524108674863213, 1461181641866091963⟩, true⟩

def words01 : List Nat := [360582446917185298, 360582446897811944, 360582446878224325, 360582446877435022, 360582446895673962, 360582446914110231, 360582446915192455, 360582446847714722, 360582446639870008, 360582446436259647]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 84410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 84400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360565995880873168, 360566042506142957⟩, ⟨1382209997571912570, 1384868493931588016⟩, true⟩

def words02 : List Nat := [360582446232213809, 360582446168611839, 360582446135661932, 360582446025084344, 360582445914319485, 360582445709845059, 360582445575346390, 360582445437347645, 360582445299231602, 360582445070325494]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 84420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 84400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360599117473986487, 360599164110701148⟩, ⟨(-1414407664156139947), (-1411748201449334535)⟩, true⟩

def words03 : List Nat := [360582444877033617, 360582444824272546, 360582444782920049, 360582444844631828, 360582444845755301, 360582444786860086, 360582444807755778, 360582444959711491, 360582445158694596, 360582445357945386]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 84430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 84400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360588277846594797, 360588324494869134⟩, ⟨(-499173283688943228), (-496512844825097120)⟩, true⟩

def words04 : List Nat := [360582445449579982, 360582445450792466, 360582445492840167, 360582445584775094, 360582445641031517, 360582445642244040, 360582445558523208, 360582445367111422, 360582445175443749, 360582445193915622]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 84440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 84400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk844A
