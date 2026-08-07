import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk612

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489980541765252, 362490035544120713⟩, ⟨(-290411837745236706), (-288138116737898726)⟩, true⟩

def state01 : KState := ⟨⟨362475911753092176, 362475966773939513⟩, ⟨570666473970282809, 572941326776715023⟩, true⟩

def words00 : List Nat := [371285327670197741, 371285327672272619, 371285327541064377, 371285327391634544, 371285327241408081, 371285327172288522, 371285326989436385, 371285327010603672, 371285327028723381, 371285327030871007]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 61200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 61200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492325560659694, 362492380600234244⟩, ⟨(-434079442998355546), (-431803443803016704)⟩, true⟩

def words01 : List Nat := [371285326993555084, 371285327110205800, 371285327427747683, 371285327429822783, 371285327422720288, 371285327331356789, 371285327254798401, 371285327257111398, 371285327291098331, 371285327408620207]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 61210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 61200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490896480653176, 362490951538962071⟩, ⟨(-346593111968126865), (-344315965759238745)⟩, true⟩

def words02 : List Nat := [371285327524633920, 371285327526745443, 371285327581873140, 371285327744736377, 371285327970160538, 371285328003737317, 371285328037510849, 371285328071950682, 371285328215241771, 371285328309458075]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 61220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 61200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362478516631924914, 362478571708942788⟩, ⟨411585038195099464, 413863330048420202⟩, true⟩

def words03 : List Nat := [371285328669646332, 371285329030695449, 371285329390241852, 371285329477933044, 371285329607480962, 371285329738095981, 371285329962039453, 371285329964115772, 371285329872630923, 371285329764626140]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 61230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 61200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485921355872522, 362485976451502446⟩, ⟨(-41897692719528236), (-39618260972808544)⟩, true⟩

def words04 : List Nat := [371285329769399608, 371285329771687718, 371285329830278043, 371285329895710768, 371285329914680438, 371285329916756922, 371285329617136517, 371285329556845952, 371285329620561936, 371285329633312167]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 61240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 61200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362484133427876295, 362484188542385417⟩, ⟨67670029666099896, 69950617860147612⟩, true⟩

def words05 : List Nat := [371285329634868512, 371285329616015144, 371285329842027812, 371285329977764863, 371285330192729642, 371285330408518430, 371285330574054463, 371285330576131215, 371285330422954121, 371285330406862403]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 61250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 61200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484149501531116, 362484204634535369⟩, ⟨66693896521266882, 68975617823580706⟩, true⟩

def words06 : List Nat := [371285330637705664, 371285330639782463, 371285330534248190, 371285330427318907, 371285330319531153, 371285330292673928, 371285330219858027, 371285330309820743, 371285330397310134, 371285330399474550]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 61260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 61200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362502610700163745, 362502665851979083⟩, ⟨(-1064548311023197579), (-1062265437072715305)⟩, true⟩

def words07 : List Nat := [371285330473612649, 371285330567219543, 371285330891058674, 371285330893135854, 371285330862156490, 371285330809643939, 371285330899287379, 371285330946575278, 371285331230864637, 371285331516098913]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 61270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 61200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486661965276899, 362486717135826622⟩, ⟨(-87174452419719884), (-84890430329318136)⟩, true⟩

def words08 : List Nat := [371285331749051417, 371285331751138747, 371285331973659984, 371285332219909748, 371285332421851762, 371285332423929386, 371285332271067143, 371285332127262394, 371285332071753296, 371285332096745366]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 61280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 61200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476647727942989, 362476702917210464⟩, ⟨526739541952517438, 529024711349952980⟩, true⟩

def words09 : List Nat := [371285332387154042, 371285332678433844, 371285332968178026, 371285332984130535, 371285332985599279, 371285332982534704, 371285333239138715, 371285333241216741, 371285333148850711, 371285333010380937]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 61290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 61200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 61200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk612
