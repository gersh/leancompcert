import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk175

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360593017622227343, 360593019378449528⟩, ⟨(-157439643058323848), (-157418838587755550)⟩, true⟩

def state01 : KState := ⟨⟨360594153089344386, 360594154847659308⟩, ⟨(-177571160840669105), (-177550319736621453)⟩, true⟩

def words00 : List Nat := [360584024530416803, 360584024961066677, 360584027447784987, 360584029934261293, 360584029934467673, 360584029660814734, 360584026153223937, 360584021320557014, 360584016488377535, 360584015488414455]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 17500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 17500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360622733894325460, 360622735654755397⟩, ⟨(-678285526972183114), (-678264648823776998)⟩, true⟩

def words01 : List Nat := [360584015488613194, 360584013990947870, 360584013296028919, 360584016606079726, 360584018531927935, 360584020457592510, 360584020748050900, 360584020748273595, 360584021918838987, 360584024128653932]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 17510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 17500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360543964882920309, 360543966645445773⟩, ⟨701836008273724230, 701856923146299788⟩, true⟩

def words02 : List Nat := [360584026235284251, 360584026235506528, 360584025113268960, 360584021264165256, 360584017415463854, 360584012704387055, 360584010176681364, 360584008701311420, 360584007226081768, 360584004119669750]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 17520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 17500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360641133396169819, 360641135160793651⟩, ⟨(-1002113248584472434), (-1002092296917043952)⟩, true⟩

def words03 : List Nat := [360584001836039694, 360584001617871154, 360584003478464189, 360584005137644730, 360584005137853152, 360584003697894981, 360584002258059861, 360584000073039820, 360584003330636565, 360584006587912000]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 17530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 17500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576310167014941, 360576311933763430⟩, ⟨135109002060571971, 135129991004465877⟩, true⟩

def words04 : List Nat := [360584008185169511, 360584010067866420, 360584013995064971, 360584017921881303, 360584019347248307, 360584019347471071, 360584018937523485, 360584016900989784, 360584014864648995, 360584011648350580]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 17540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 17500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360508311327615931, 360508313096459912⟩, ⟨1329174309030088053, 1329195334760470231⟩, true⟩

def words05 : List Nat := [360584014007309958, 360584016804698221, 360584017976799292, 360584017977022038, 360584017213933755, 360584015607155407, 360584014558431245, 360584014558654000, 360584011902241249, 360584007591605725]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 17550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 17500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360530777786714664, 360530779557663802⟩, ⟨934268530966804198, 934289593674511834⟩, true⟩

def words06 : List Nat := [360584003281411503, 360584000027320847, 360583998383410966, 360583995311623852, 360583992240169020, 360583986402347376, 360583977353399947, 360583968769504925, 360583960186520032, 360583954833342488]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 17560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 17500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360599965181548474, 360599966954620318⟩, ⟨(-281876869505896966), (-281855769492041348)⟩, true⟩

def words07 : List Nat := [360583951807232044, 360583947159746518, 360583942512747134, 360583941865644734, 360583941865832098, 360583940599324018, 360583939332940166, 360583935604540415, 360583934202973354, 360583935115163402]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 17570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 17500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360609020067708270, 360609021842879169⟩, ⟨(-440998411084948862), (-440977274159004724)⟩, true⟩

def words08 : List Nat := [360583939252374941, 360583941598693459, 360583942325464914, 360583943052181951, 360583943052368691, 360583944490681606, 360583947976679039, 360583951462322615, 360583952071519295, 360583953496897758]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 17580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 17500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360719840988414366, 360719842765694507⟩, ⟨(-2391327527656601696), (-2391306353618708714)⟩, true⟩

def words09 : List Nat := [360583954712369503, 360583955927764909, 360583959350790183, 360583961441671491, 360583961441879824, 360583960175984197, 360583960862533531, 360583965365791445, 360583973086278909, 360583980805941158]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 17590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 17500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 17500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk175
