import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk794A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360622443131930239, 360622484170767601⟩, ⟨(-3200488511915040036), (-3198287782049443582)⟩, true⟩

def state01 : KState := ⟨⟨360608756728176040, 360608797777838022⟩, ⟨(-2113777210278793267), (-2111575620885513047)⟩, true⟩

def words00 : List Nat := [360582204361215382, 360582204714441414, 360582205200764223, 360582205687413799, 360582206134237545, 360582206422976917, 360582206598487308, 360582206774123410, 360582206974114340, 360582207310259406]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 79400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 79400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360575264873792233, 360575305934139274⟩, ⟨546076873409822824, 548279311357390080⟩, true⟩

def words01 : List Nat := [360582207804332516, 360582208298610516, 360582208701400753, 360582208998310935, 360582209185859039, 360582209373698399, 360582209546321900, 360582209560938201, 360582209561951215, 360582209476211264]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 79410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 79400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360605556004596930, 360605597075670561⟩, ⟨(-1859762846771228929), (-1857559556865977967)⟩, true⟩

def words02 : List Nat := [360582209404435022, 360582209547119284, 360582209847721993, 360582210148537747, 360582210311740527, 360582210354649482, 360582210555606108, 360582210756890877, 360582210953919442, 360582211249521250]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 79420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 79400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360592273552160715, 360592314634039952⟩, ⟨(-804633677570447418), (-802429529321338216)⟩, true⟩

def words03 : List Nat := [360582211411730762, 360582211574052091, 360582211894395581, 360582212296209501, 360582212658212340, 360582213020410902, 360582213303220521, 360582213428015855, 360582213556091589, 360582213684538796]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 79430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 79400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360602598234602663, 360602639327192511⟩, ⟨(-1624913064561405252), (-1622708065408018642)⟩, true⟩

def words04 : List Nat := [360582213866442435, 360582214093131212, 360582214180329344, 360582214267616673, 360582214315261969, 360582214442415849, 360582214679250061, 360582214916295529, 360582215058337315, 360582215316602235]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 79440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 79400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk794A
