import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk571A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362479932671889965, 362479980288505405⟩, ⟨282633611699309680, 284470277155611152⟩, true⟩

def state01 : KState := ⟨⟨362484887725633915, 362484935359476255⟩, ⟨(-299249565287463), 1538399636136841⟩, true⟩

def words00 : List Nat := [371284962175168930, 371284962177292182, 371284962116790874, 371284962183500208, 371284962199113191, 371284962201072258, 371284962029837862, 371284962099323618, 371284962294965717, 371284962296958940]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 57100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 57100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482365119681028, 362482412771120408⟩, ⟨143780936594601051, 145619590844545757⟩, true⟩

def words01 : List Nat := [371284962297927073, 371284962298218761, 371284962376003521, 371284962378150051, 371284962404669954, 371284962465514224, 371284962524121116, 371284962526047092, 371284962175875648, 371284962133705222]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 57110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 57100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473389038333243, 362473436706899688⟩, ⟨656584066071355115, 658423698709907195⟩, true⟩

def words02 : List Nat := [371284962334764052, 371284962336699262, 371284962288007203, 371284962173913900, 371284962059106724, 371284962037856798, 371284961863418130, 371284961815240313, 371284961766396578, 371284961714753879]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 57120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 57100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362510388967335021, 362510436653303203⟩, ⟨(-1457396345605767643), (-1455555718718743111)⟩, true⟩

def words03 : List Nat := [371284961619322219, 371284961726619725, 371284961993799777, 371284962106067349, 371284962194923061, 371284962284392880, 371284962563963865, 371284962705281803, 371284963152405301, 371284963600351405]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 57130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 57100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491449521071578, 362491497224452570⟩, ⟨(-375177325052404437), (-373335703108770157)⟩, true⟩

def words04 : List Nat := [371284963983805237, 371284963985731921, 371284964240917694, 371284964523463072, 371284964820329996, 371284964822256770, 371284964710921031, 371284964594071856, 371284964663997199, 371284964780521427]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 57140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 57100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk571A
