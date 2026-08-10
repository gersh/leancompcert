import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk754A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk754B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk754A

def state06 : KState := ⟨⟨360567143713319867, 360567180632354974⟩, ⟨1132237489639304567, 1134119149926880207⟩, true⟩

def words05 : List Nat := [360582210594821448, 360582210737103007, 360582210743832887, 360582210744908399, 360582210648016820, 360582210507054564, 360582210365769885, 360582210349028081, 360582210238683090, 360582210040649791]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 75450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 75400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360574063342731961, 360574100271903219⟩, ⟨610049689449721117, 611932114661449097⟩, true⟩

def words06 : List Nat := [360582209842351149, 360582209768614664, 360582209769487407, 360582209755272171, 360582209740989294, 360582209577341166, 360582209289510817, 360582208997907905, 360582208705994946, 360582208554858850]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 75460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 75400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360582938597596994, 360582975537007164⟩, ⟨(-59848773002191787), (-57965575009749637)⟩, true⟩

def words07 : List Nat := [360582208448387446, 360582208208310678, 360582207968034330, 360582207879613831, 360582207880514718, 360582207861594237, 360582207842557295, 360582207730472061, 360582207576383647, 360582207587788027]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 75470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 75400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360574058693366582, 360574095642911021⟩, ⟨610426745914266022, 612310708891981248⟩, true⟩

def words08 : List Nat := [360582207588672883, 360582207542285692, 360582207524786005, 360582207418903836, 360582207312849967, 360582207134190245, 360582207070612189, 360582207007338263, 360582206943930235, 360582206792849980]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 75480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 75400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360575539166855027, 360575576126546845⟩, ⟨498594811399428734, 500479540453897614⟩, true⟩

def words09 : List Nat := [360582206686278344, 360582206632158707, 360582206577718730, 360582206550743734, 360582206348399352, 360582205979959273, 360582205611325543, 360582205302438441, 360582205081318437, 360582204994632328]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 75490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 75400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 75400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk754B
