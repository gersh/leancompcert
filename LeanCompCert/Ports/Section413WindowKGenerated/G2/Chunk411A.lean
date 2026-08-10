import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk411A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360583834265765311, 360583844693684518⟩, ⟨(-61211489061396844), (-60921830319539286)⟩, true⟩

def state01 : KState := ⟨⟨360556121980981704, 360556132414156510⟩, ⟨1077871798581819927, 1078161673354996899⟩, true⟩

def words00 : List Nat := [360582362759951840, 360582362760509981, 360582362484082862, 360582361910743356, 360582361337331251, 360582360613180333, 360582360338225877, 360582359901010143, 360582359463754741, 360582358677191174]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 41100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 41100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360596959502035074, 360596969940487745⟩, ⟨(-601280186833113970), (-600990095061066086)⟩, true⟩

def words01 : List Nat := [360582358039712810, 360582357373174511, 360582356706499540, 360582356630012066, 360582356170400178, 360582355210508229, 360582354250555047, 360582354066135618, 360582354422033779, 360582354778038849]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 41110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 41100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360537842320550529, 360537852764322595⟩, ⟨1829748187184750132, 1830038497716118476⟩, true⟩

def words02 : List Nat := [360582354833790353, 360582354834349311, 360582354582554193, 360582354224736094, 360582353866795592, 360582353078154904, 360582351700712029, 360582350027181683, 360582348353628759, 360582346771074750]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 41120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 41100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360501123599317388, 360501134048358019⟩, ⟨3340321212410032987, 3340611739663548713⟩, true⟩

def words03 : List Nat := [360582345689763183, 360582345198182161, 360582344706551845, 360582343918961652, 360582342715269507, 360582341226717967, 360582339738075608, 360582338606205797, 360582337084787046, 360582335111548675]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 41130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 41100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583458821701786, 360583469276012215⟩, ⟨(-47333611985725378), (-47042867906211328)⟩, true⟩

def words04 : List Nat := [360582333138274469, 360582331754534094, 360582330666112349, 360582330167096428, 360582329668063407, 360582328653521619, 360582327653138121, 360582326929590268, 360582326205907664, 360582326099226567]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 41140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 41100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk411A
