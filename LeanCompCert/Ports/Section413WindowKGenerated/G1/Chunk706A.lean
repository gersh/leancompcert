import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk706A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362471667301981719, 362471741323003353⟩, ⟨953749602286518101, 957278939424892155⟩, true⟩

def state01 : KState := ⟨⟨362474882912734064, 362474956955436105⟩, ⟨726768179717532122, 730299047603389320⟩, true⟩

def words00 : List Nat := [371285300324371005, 371285300262815203, 371285300131524381, 371285300133526447, 371285300134811153, 371285300105319147, 371285299840315920, 371285299776884403, 371285299712208876, 371285299669606951]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 70600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 70600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362486842776523815, 362486916841240212⟩, ⟨(-117782905984140134), (-114250483554418694)⟩, true⟩

def words01 : List Nat := [371285299524940551, 371285299381349068, 371285299278917064, 371285299281607394, 371285299225320163, 371285299207336717, 371285299188456369, 371285299170498182, 371285299017753013, 371285299043650906]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 70610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 70600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484495910631229, 362484569996906487⟩, ⟨47964196324893135, 51498141354174295⟩, true⟩

def words02 : List Nat := [371285299268393222, 371285299270812457, 371285299228714857, 371285299135860932, 371285299042050833, 371285299011803316, 371285298965100985, 371285299043612028, 371285299119961460, 371285299122509690]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 70620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 70600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489915853642383, 362489989961793527⟩, ⟨(-334899681255699529), (-331364191023235433)⟩, true⟩

def words03 : List Nat := [371285299207417059, 371285299303940013, 371285299496926633, 371285299499346335, 371285299425590383, 371285299302309084, 371285299178097214, 371285299138617975, 371285299072985806, 371285299142141721]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 70630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 70600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482994983735006, 362483069113741026⟩, ⟨154024388281864372, 157561422452131268⟩, true⟩

def words04 : List Nat := [371285299196592817, 371285299199046171, 371285299269910912, 371285299384277403, 371285299552669791, 371285299555089877, 371285299456710059, 371285299359512967, 371285299279705073, 371285299282494772]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 70640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 70600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk706A
