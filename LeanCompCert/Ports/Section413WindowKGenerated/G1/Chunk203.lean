import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk203

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362506547582280584, 362506553106688514⟩, ⟨(-437929857278245814), (-437854011728487214)⟩, true⟩

def state01 : KState := ⟨⟨362472487508330433, 362472493038425935⟩, ⟨253495368056846930, 253571329093161808⟩, true⟩

def words00 : List Nat := [371284985762553782, 371284985763184304, 371284983292416266, 371284982927770136, 371284982733747807, 371284982734385703, 371284981533132474, 371284979813972779, 371284978094733242, 371284978086633378]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 20300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 20300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362422778264430261, 362422783800209762⟩, ⟨1263579086513275726, 1263655163021253596⟩, true⟩

def words01 : List Nat := [371284978643049938, 371284979814305266, 371284980656995576, 371284980657637422, 371284979487504517, 371284978456203330, 371284977629805099, 371284977630436293, 371284974614149903, 371284971554295454]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 20310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 20300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362458287168450640, 362458292709886655⟩, ⟨541902450171300785, 541978641648208563⟩, true⟩

def words02 : List Nat := [371284968494461261, 371284966455577809, 371284963219491181, 371284962396352282, 371284961573104834, 371284960381597950, 371284955970553542, 371284953971801430, 371284951972897499, 371284951767518146]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 20320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 20300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362439359584416459, 362439365131601959⟩, ⟨926983784620746390, 927060093013591812⟩, true⟩

def words03 : List Nat := [371284950456743690, 371284949106025559, 371284948814017234, 371284948814712709, 371284948686368085, 371284948707324581, 371284948734923136, 371284948735554863, 371284945547410583, 371284943307266345]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 20330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 20300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362449231739114969, 362449237291932974⟩, ⟨726278317177135419, 726354740164831081⟩, true⟩

def words04 : List Nat := [371284941234601105, 371284941235243716, 371284939394624121, 371284937561814186, 371284935728940138, 371284934329851645, 371284931723529021, 371284931524887434, 371284931326073407, 371284930399557782]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 20340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 20300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362542651917139844, 362542657475675293⟩, ⟨(-1175343372195991783), (-1175266832829888133)⟩, true⟩

def words05 : List Nat := [371284928897420362, 371284929149468082, 371284931806917072, 371284931807549104, 371284931253827913, 371284930002325789, 371284929903492426, 371284930335043254, 371284933170793907, 371284936006551484]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 20350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 20300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362493815577232863, 362493821141476809⟩, ⟨(-181080516683127542), (-181003861062570324)⟩, true⟩

def words06 : List Nat := [371284938364131958, 371284938364764228, 371284937678731353, 371284937844899737, 371284938753235488, 371284938753869585, 371284937222061890, 371284935792537823, 371284935335095096, 371284935772026975]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 20360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 20300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362438543268207149, 362438548838137430⟩, ⟨945305431150923199, 945382202631657311⟩, true⟩

def words07 : List Nat := [371284937794052560, 371284939816132719, 371284941844826961, 371284941845459956, 371284941099612510, 371284940978962983, 371284941139419408, 371284941140053276, 371284938856699623, 371284936581151741]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 20370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 20300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362431244637014511, 362431250212612984⟩, ⟨1094197765867101487, 1094274652894519487⟩, true⟩

def words08 : List Nat := [371284934305552998, 371284934015630598, 371284932707268381, 371284931936008540, 371284931164608881, 371284929946715414, 371284925527892613, 371284922030668574, 371284918533468048, 371284917434432235]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 20380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 20300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486472471047172, 362486478052432662⟩, ⟨(-32238832651558332), (-32161827598327704)⟩, true⟩

def words09 : List Nat := [371284914803006915, 371284911666212489, 371284908529463721, 371284907790478372, 371284906229898135, 371284905409186229, 371284904588349818, 371284903732526032, 371284901491461339, 371284901569534847]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 20390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 20300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 20300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk203
