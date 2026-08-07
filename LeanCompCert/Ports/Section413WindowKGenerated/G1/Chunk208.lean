import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk208

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362441836170240871, 362441841982358950⟩, ⟨888153976416637707, 888235734755903797⟩, true⟩

def state01 : KState := ⟨⟨362481037668662115, 362481043486572121⟩, ⟨72565826910570071, 72647705751614977⟩, true⟩

def words00 : List Nat := [371284543570934921, 371284542279915645, 371284539832555437, 371284539409744469, 371284538986768144, 371284538451852402, 371284535160913667, 371284534169809097, 371284534485697802, 371284534486367970]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 20800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 20800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362486815833410457, 362486821657219333⟩, ⟨(-47759184969014634), (-47677183341926012)⟩, true⟩

def words01 : List Nat := [371284534319112847, 371284533664978253, 371284533887858689, 371284533888572024, 371284533611346967, 371284533599453875, 371284533587340637, 371284533541239305, 371284531686044170, 371284531796821566]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 20810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 20800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362449152768077066, 362449158597655675⟩, ⟨736664610780105412, 736746732562835978⟩, true⟩

def words02 : List Nat := [371284533859364313, 371284533860013102, 371284533461311570, 371284532600267903, 371284531739062198, 371284530599890132, 371284528627229994, 371284528476543715, 371284528325659438, 371284528099939057]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 20820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 20800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362506888920100421, 362506894755554431⟩, ⟨(-466140303503792282), (-466058059307314136)⟩, true⟩

def words03 : List Nat := [371284526432983878, 371284526464309303, 371284528516871376, 371284528517524232, 371284528515098675, 371284528180547929, 371284529422034042, 371284530050723194, 371284531124335831, 371284532198128813]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 20830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 20800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491017833912967, 362491023675218141⟩, ⟨(-135471204779886759), (-135388838614812943)⟩, true⟩

def words04 : List Nat := [371284533279704618, 371284533280355247, 371284532486638305, 371284532944153173, 371284533463667388, 371284533464327543, 371284532070350693, 371284530685356382, 371284530204999976, 371284530517162662]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 20840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 20800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362437268711284115, 362437274558434043⟩, ⟨985646546142936410, 985729034201077910⟩, true⟩

def words05 : List Nat := [371284532527112013, 371284534537128660, 371284536075896016, 371284536076545208, 371284534558307127, 371284533371286889, 371284533284954903, 371284533285604188, 371284531330996158, 371284529066305620]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 20850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 20800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362436832925797649, 362436838778757153⟩, ⟨994965134658703286, 995047743933948702⟩, true⟩

def words06 : List Nat := [371284526801539071, 371284526158167555, 371284525139570916, 371284525599843180, 371284525874728738, 371284525875378341, 371284523096880910, 371284520535835452, 371284517974707086, 371284517156521118]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 20860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 20800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501887133612116, 362501892992505343⟩, ⟨(-363075970781708524), (-362993237640739680)⟩, true⟩

def words07 : List Nat := [371284514872580097, 371284512580401735, 371284510288174070, 371284510281060414, 371284509472869961, 371284509270760194, 371284509068455094, 371284508875721549, 371284508258081456, 371284509091464170]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 20870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 20800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362457203890308542, 362457209754992776⟩, ⟨570128827847242724, 570211681934987222⟩, true⟩

def words08 : List Nat := [371284510438674241, 371284510439324572, 371284509137534738, 371284507845801858, 371284506553949424, 371284505971646752, 371284504904937993, 371284505512944942, 371284505670161725, 371284505670834566]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 20880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 20800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362529852996573157, 362529858867129864⟩, ⟨(-947960547005648393), (-947877570212521793)⟩, true⟩

def words09 : List Nat := [371284504582593037, 371284504801244231, 371284506457568330, 371284506458219316, 371284505552663145, 371284504212319198, 371284503810473079, 371284503811196992, 371284505872608824, 371284508043235672]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 20890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 20800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 20800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk208
