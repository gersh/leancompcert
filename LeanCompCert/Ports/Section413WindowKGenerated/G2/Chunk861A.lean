import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk861A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360545341860359150, 360545390422013217⟩, ⟨3173481422127840348, 3176305029839297318⟩, true⟩

def state01 : KState := ⟨⟨360531953873462946, 360532002446766150⟩, ⟨4326227622532016174, 4329052233293126940⟩, true⟩

def words00 : List Nat := [360582280877595376, 360582280524450902, 360582280036286786, 360582279480610066, 360582278924746644, 360582278289127952, 360582277726187555, 360582277160012445, 360582276593704155, 360582275960101340]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 86100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 86100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360565336150694617, 360565384735682142⟩, ⟨1451532237281444167, 1454357854238466365⟩, true⟩

def words01 : List Nat := [360582275377279976, 360582274929537020, 360582274481419362, 360582274168247752, 360582273858562294, 360582273434267307, 360582273009744755, 360582272720266141, 360582272504279436, 360582272309465683]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 86110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 86100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360554923659727169, 360554972256541975⟩, ⟨2348218239272077656, 2351044874847830384⟩, true⟩

def words02 : List Nat := [360582272114507379, 360582271814426103, 360582271484396522, 360582271251340092, 360582271017967043, 360582270699452624, 360582270245968737, 360582269710589849, 360582269174964754, 360582268725540557]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 86120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 86100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360539133018138464, 360539181626601959⟩, ⟨3708387282250699841, 3711214921186858301⟩, true⟩

def words03 : List Nat := [360582268409623523, 360582268228573299, 360582268047391852, 360582267798896896, 360582267415400019, 360582266916861699, 360582266417970287, 360582266053935483, 360582265651383952, 360582265152503827]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 86130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 86100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360552047925451532, 360552096545619222⟩, ⟨2595854798822149806, 2598683446015448364⟩, true⟩

def words04 : List Nat := [360582264653361041, 360582264128054017, 360582263704622363, 360582263416026823, 360582263127341694, 360582262724159126, 360582262262802198, 360582261914087395, 360582261565022289, 360582261182253180]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 86140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 86100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk861A
