import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk152

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362506528878678801, 362506531897581051⟩, ⟨(-340813195000315842), (-340782154018453288)⟩, true⟩

def state01 : KState := ⟨⟨362458116968582925, 362458119991644563⟩, ⟨395163742216348627, 395194846442230219⟩, true⟩

def words00 : List Nat := [371284114862324272, 371284114862788024, 371284113062947853, 371284113721472673, 371284115699654622, 371284115700115507, 371284111926451256, 371284107674422975, 371284103422763619, 371284102558800529]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 15200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 15200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362382802414227239, 362382805441438197⟩, ⟨1541054759905538274, 1541085927264310646⟩, true⟩

def words01 : List Nat := [371284100850976138, 371284099905272070, 371284098959544011, 371284097221610247, 371284089737728332, 371284082563066616, 371284075389104738, 371284072523040876, 371284066097161712, 371284059444543606]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 15210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 15200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362438872877108374, 362438875908447025⟩, ⟨687540432044858482, 687571662248030088⟩, true⟩

def words02 : List Nat := [371284052792600404, 371284049716066326, 371284044753810830, 371284042626335442, 371284040498996128, 371284037175988285, 371284029252220927, 371284025630789453, 371284022009595496, 371284021782527658]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 15220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 15200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362434045090516722, 362434048126071000⟩, ⟨761285414697614971, 761316709125901919⟩, true⟩

def words03 : List Nat := [371284018818794964, 371284015855762488, 371284014227713766, 371284014228221990, 371284013416759742, 371284012792546955, 371284012168266119, 371284011552650061, 371284006568250158, 371284003290711808]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 15230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 15200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362426197677568415, 362426200717239922⟩, ⟨881043885453073667, 881075242649259931⟩, true⟩

def words04 : List Nat := [371284001030783195, 371284001031245117, 371283996323225102, 371283991614253423, 371283986905727479, 371283983504934885, 371283978946076402, 371283978186689450, 371283977427244175, 371283976142987415]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 15240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 15200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481891105473001, 362481894149318958⟩, ⟨31428807144824855, 31460228022767969⟩, true⟩

def words05 : List Nat := [371283972354997491, 371283971997214909, 371283973044118781, 371283973044581494, 371283969893631883, 371283966243433811, 371283962593526135, 371283960316205352, 371283955897797796, 371283955763212980]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 15250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 15200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362468255003100386, 362468258051120073⟩, ⟨239441975134512136, 239473459724976712⟩, true⟩

def words06 : List Nat := [371283955628468673, 371283955494622820, 371283951402506677, 371283951497756725, 371283952444566394, 371283952445030358, 371283949067353934, 371283944838335462, 371283940660921971, 371283940661449149]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 15260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 15200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362456530524674572, 362456533576865475⟩, ⟨418918629766487160, 418950178072814132⟩, true⟩

def words07 : List Nat := [371283942886846922, 371283946138964575, 371283949404767312, 371283949405238230, 371283949534337707, 371283949930698723, 371283954603157122, 371283954603620343, 371283953576213645, 371283951782236733]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 15270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 15200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362468366041110691, 362468369097456040⟩, ⟨237832360162109108, 237863971969386424⟩, true⟩

def words08 : List Nat := [371283949988289383, 371283949000979995, 371283945961787585, 371283944409111551, 371283942856499139, 371283940607952322, 371283932665094809, 371283928995833803, 371283925929672332, 371283925930155150]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 15280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 15200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362458277101559921, 362458280162122979⟩, ⟨392207951277905713, 392239627595213245⟩, true⟩

def words09 : List Nat := [371283924913120238, 371283923920339896, 371283925079841511, 371283925107163430, 371283925107496257, 371283924859348753, 371283924611071495, 371283924355393685, 371283918414217546, 371283916739089987]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 15290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 15200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 15200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk152
