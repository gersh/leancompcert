import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk852A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362474634849431966, 362474744228706400⟩, ⟨892636745691336120, 898929154175848880⟩, true⟩

def state01 : KState := ⟨⟨362480886805055366, 362480996210687345⟩, ⟨359978687002228061, 366273341288034933⟩, true⟩

def words00 : List Nat := [371285294932361942, 371285294935339309, 371285294854032949, 371285294774058762, 371285294692914503, 371285294655215951, 371285294605646850, 371285294646375980, 371285294685984943, 371285294689050073]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 85200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 85200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488825016354800, 362488934448765759⟩, ⟨(-316494465769113798), (-310197529511270490)⟩, true⟩

def words01 : List Nat := [371285294640650223, 371285294622689584, 371285294719281493, 371285294722242464, 371285294670255809, 371285294601716105, 371285294531944951, 371285294512419402, 371285294483843668, 371285294529854795]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 85210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 85200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478858293725569, 362478967752855466⟩, ⟨532868245335388563, 539167458716689141⟩, true⟩

def words02 : List Nat := [371285294554022111, 371285294556983450, 371285294397419730, 371285294376994348, 371285294355115453, 371285294341146816, 371285294166512869, 371285293992809019, 371285293817893362, 371285293781938145]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 85220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 85200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362476802995036670, 362476912480889904⟩, ⟨708096354855796231, 714397846003640081⟩, true⟩

def words03 : List Nat := [371285293739280481, 371285293772143832, 371285293803831213, 371285293806799271, 371285293695840401, 371285293628534255, 371285293626435905, 371285293629410328, 371285293592353323, 371285293497384551]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 85230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 85200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362495834689388442, 362495944201763332⟩, ⟨(-914267979860066132), (-907964227875938110)⟩, true⟩

def words04 : List Nat := [371285293401081744, 371285293380938144, 371285293336329939, 371285293384965485, 371285293410377895, 371285293413391694, 371285293370760989, 371285293420819466, 371285293591891093, 371285293719917067]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 85240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 85200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk852A
