import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk612A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk612A
