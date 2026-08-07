import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk502

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362472150010931610, 362472186436201760⟩, ⟨642859243578361510, 644094601343580354⟩, true⟩

def state01 : KState := ⟨⟨362484874864889331, 362484911305172341⟩, ⟨4070663844205454, 5306775332010188⟩, true⟩

def words00 : List Nat := [371285016751506355, 371285016750566082, 371285016683652964, 371285016817965810, 371285016885175949, 371285016886860120, 371285016657726289, 371285016742769100, 371285016995039043, 371285016996774254]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 50200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 50200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488914314981163, 362488950770549036⟩, ⟨(-198777306226688893), (-197540427209430399)⟩, true⟩

def words01 : List Nat := [371285016995956552, 371285016915282490, 371285017090886372, 371285017151487666, 371285017228706431, 371285017306569583, 371285017370964293, 371285017372674650, 371285017267330336, 371285017347733692]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 50210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 50200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480798344328076, 362480834814812473⟩, ⟨208877548786923011, 210115176990384031⟩, true⟩

def words02 : List Nat := [371285017823283874, 371285017824960619, 371285017772509401, 371285017720991986, 371285017668835766, 371285017583839802, 371285017530806162, 371285017703515001, 371285017874533720, 371285017876269578]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 50220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 50200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362496618914342339, 362496655400036063⟩, ⟨(-585804104871510120), (-584565712630505444)⟩, true⟩

def words03 : List Nat := [371285018106802639, 371285018421529550, 371285019095381699, 371285019241897019, 371285019303988418, 371285019366583808, 371285019632332374, 371285019701342198, 371285019934102630, 371285020167603777]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 50230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 50200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490513143429172, 362490549644242970⟩, ⟨(-279103339650598215), (-277864187699370469)⟩, true⟩

def words04 : List Nat := [371285020400897489, 371285020402574812, 371285020148055523, 371285020190002286, 371285020302765847, 371285020304473543, 371285020140077087, 371285019974894508, 371285020006751205, 371285020118707173]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 50240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 50200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362470388815955275, 362470425331893475⟩, ⟨732319993304005301, 733559905334088729⟩, true⟩

def words05 : List Nat := [371285020564663108, 371285021011271578, 371285021380252211, 371285021381930001, 371285021223422526, 371285021095067463, 371285021132133011, 371285021133818816, 371285020922927837, 371285020634426983]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 50250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 50200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484833203436343, 362484869734366957⟩, ⟨6360758089811201, 7601423716673051⟩, true⟩

def words06 : List Nat := [371285020450161033, 371285020452009768, 371285020662875945, 371285020967243257, 371285021214628110, 371285021216306985, 371285021006394366, 371285020902497276, 371285020944547854, 371285020946296869]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 50260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 50200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500877766989781, 362500914313225599⟩, ⟨(-800253750006005815), (-799012314909758999)⟩, true⟩

def words07 : List Nat := [371285020944550004, 371285020937182802, 371285021315126043, 371285021591384086, 371285021983945572, 371285022377116721, 371285022770109425, 371285022771790447, 371285023055863574, 371285023374005819]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 50270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 50200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486568848114712, 362486605409324480⟩, ⟨(-80776845469189641), (-79534657406112163)⟩, true⟩

def words08 : List Nat := [371285023738164279, 371285023739844338, 371285023657042692, 371285023527412003, 371285023397151416, 371285023364536716, 371285023427173400, 371285023657311639, 371285023887255716, 371285023920441656]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 50280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 50200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362508809471545079, 362508846047904696⟩, ⟨(-1199353011838567828), (-1198110061813141510)⟩, true⟩

def words09 : List Nat := [371285024348000307, 371285024776424500, 371285025491371695, 371285025680249319, 371285025777778325, 371285025875817771, 371285026171204529, 371285026285815486, 371285026760509238, 371285027235916602]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 50290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 50200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 50200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk502
