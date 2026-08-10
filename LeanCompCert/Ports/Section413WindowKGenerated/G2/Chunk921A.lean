import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk921A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360570127386982691, 360570183243540002⟩, ⟨1082453426420276780, 1085927276266008162⟩, true⟩

def state01 : KState := ⟨⟨360572106329108200, 360572162198208804⟩, ⟨900126118386698742, 903601123531315878⟩, true⟩

def words00 : List Nat := [360581973857925221, 360581973803548911, 360581973631444892, 360581973370860759, 360581973110069207, 360581972785170230, 360581972570243906, 360581972473294544, 360581972376201966, 360581972220177443]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 92100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 92100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360600969729272771, 360601025610964346⟩, ⟨(-1758664424206616848), (-1755188259246986364)⟩, true⟩

def words01 : List Nat := [360581972125959411, 360581972138637821, 360581972148326061, 360581972177488445, 360581972178730319, 360581972097316663, 360581972029877993, 360581972120503574, 360581972328413620, 360581972536646363]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 92110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 92100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360582377485524563, 360582433379892099⟩, ⟨(-45962191373178944), (-42484858642238150)⟩, true⟩

def words02 : List Nat := [360581972685549012, 360581972717035880, 360581972788104289, 360581972859574731, 360581972860698583, 360581972847346054, 360581972747475588, 360581972544999458, 360581972342272379, 360581972244566940]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 92120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 92100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360570554875700007, 360570610782614655⟩, ⟨1043311342609032397, 1046789831368853671⟩, true⟩

def words03 : List Nat := [360581972245651318, 360581972236184891, 360581972226584464, 360581972142271333, 360581972060518702, 360581971949711957, 360581971838506274, 360581971829661109, 360581971766605445, 360581971644687250]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 92130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 92100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581414818768377, 360581470738278401⟩, ⟨42606342703806073, 46085992064643211⟩, true⟩

def words04 : List Nat := [360581971522484370, 360581971398098635, 360581971383495018, 360581971435798599, 360581971437027463, 360581971389163070, 360581971223567235, 360581971076370070, 360581970928759507, 360581970857562879]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 92140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 92100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk921A
