import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk945A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360595554683936442, 360595613607471687⟩, ⟨(-1280694691781687327), (-1276934676150755221)⟩, true⟩

def state01 : KState := ⟨⟨360576090006206129, 360576148942625925⟩, ⟨558758758959766448, 562519992246264298⟩, true⟩

def words00 : List Nat := [360582101356254367, 360582101386990767, 360582101388213591, 360582101341734948, 360582101295034314, 360582101196186905, 360582101166099835, 360582101097794234, 360582101029351998, 360582100905299148]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 94500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 94500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360607001535774862, 360607060485112554⟩, ⟨(-2362858525328831432), (-2359096071108192314)⟩, true⟩

def words01 : List Nat := [360582100843430271, 360582100842455025, 360582100950472092, 360582101096027652, 360582101146564326, 360582101197206624, 360582101323612836, 360582101521199092, 360582101786366702, 360582102051842612]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 94510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 94500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589056306027151, 360589115268419846⟩, ⟨(-666725132321955252), (-662961444078613800)⟩, true⟩

def words02 : List Nat := [360582102230956283, 360582102320168702, 360582102374614337, 360582102429448301, 360582102430630851, 360582102432000218, 360582102346258151, 360582102203529401, 360582102060517163, 360582102104017919]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 94520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 94500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360567953764705241, 360568012739988632⟩, ⟨1328284935137419612, 1332049842002428178⟩, true⟩

def words03 : List Nat := [360582102291172885, 360582102478586585, 360582102609648650, 360582102723203506, 360582102741281260, 360582102759722767, 360582102779458295, 360582102780827858, 360582102689193064, 360582102541575288]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 94530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 94500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360592258795483966, 360592317783712096⟩, ⟨(-969571372003034279), (-965805241279200351)⟩, true⟩

def words04 : List Nat := [360582102393648424, 360582102407722336, 360582102570394750, 360582102733329424, 360582102786588960, 360582102787959180, 360582102872947746, 360582102972309137, 360582103025640895, 360582103135096226]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 94540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 94500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk945A
