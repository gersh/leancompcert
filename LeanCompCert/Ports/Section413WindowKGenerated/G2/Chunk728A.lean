import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk728A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360593674979352768, 360593709243987329⟩, ⟨(-825595493593675712), (-823910626455981308)⟩, true⟩

def state01 : KState := ⟨⟨360576860013794429, 360576894288276944⟩, ⟨398540682556025122, 400226266674996040⟩, true⟩

def words00 : List Nat := [360582392006742278, 360582392007776583, 360582391980959382, 360582392032520686, 360582392036143294, 360582392037177769, 360582391917427241, 360582391650817917, 360582391384021413, 360582391146767193]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 72800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 72800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360568408102501443, 360568442386726072⟩, ⟨1013995024062828215, 1015681317553406961⟩, true⟩

def words01 : List Nat := [360582391072110945, 360582391062643567, 360582391053068172, 360582390923362935, 360582390801189395, 360582390631672204, 360582390479444617, 360582390480480549, 360582390411816438, 360582390221353282]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 72810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 72800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590188900650439, 360590223194652131⟩, ⟨(-572219450381553461), (-570532444877505907)⟩, true⟩

def words02 : List Nat := [360582390030668582, 360582389790129201, 360582389721974432, 360582389782621862, 360582389783577223, 360582389682713490, 360582389525508817, 360582389451912016, 360582389437644423, 360582389546276062]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 72820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 72800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360575613180538243, 360575647484382124⟩, ⟨489420581652695236, 491108304013051454⟩, true⟩

def words03 : List Nat := [360582389547204230, 360582389511534827, 360582389591565607, 360582389816077922, 360582389909944892, 360582390003962932, 360582390004893593, 360582390003656010, 360582389864398987, 360582389773014923]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 72830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 72800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591232723354766, 360591267036961452⟩, ⟨(-648367223045290346), (-646678789516051136)⟩, true⟩

def words04 : List Nat := [360582389681291084, 360582389796846675, 360582389823523231, 360582389850311778, 360582389851180296, 360582389802283277, 360582389977710453, 360582390153331791, 360582390182222535, 360582390305145609]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 72840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 72800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk728A
