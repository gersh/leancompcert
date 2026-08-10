import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk769A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360562980228817699, 360563018627483684⟩, ⟨1470688967874925676, 1472683349942498270⟩, true⟩

def state01 : KState := ⟨⟨360575994100670908, 360576032509703109⟩, ⟨469884325418021810, 471879504699109646⟩, true⟩

def words00 : List Nat := [360582169008084553, 360582168787098457, 360582168720093147, 360582168745225648, 360582168746246638, 360582168628744334, 360582168342370232, 360582168225099244, 360582168107514878, 360582167986295219]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 76900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 76900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360578320471521058, 360578358890992860⟩, ⟨290953615047168428, 292949597290349622⟩, true⟩

def words01 : List Nat := [360582167907499505, 360582167732902204, 360582167558088058, 360582167629517043, 360582167665283685, 360582167701248004, 360582167702225329, 360582167653703629, 360582167436359472, 360582167388097519]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 76910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 76900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360561752565000229, 360561790994816891⟩, ⟨1565326524987766207, 1567323303008003463⟩, true⟩

def words02 : List Nat := [360582167339477029, 360582167281171629, 360582167054177853, 360582166659579481, 360582166264816134, 360582165768447941, 360582165356453880, 360582165053842202, 360582164751118885, 360582164364152755]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 76920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 76900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360581022313531242, 360581060753700018⟩, ⟨82808939595955163, 84806514055739249⟩, true⟩

def words03 : List Nat := [360582164100215077, 360582163911331808, 360582163722120331, 360582163672120082, 360582163673133457, 360582163513666621, 360582163354009914, 360582163139385123, 360582163009079848, 360582162995889461]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 76930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 76900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360584852439798276, 360584890890430478⟩, ⟨(-211980636760448186), (-209982257196300486)⟩, true⟩

def words04 : List Nat := [360582162982550647, 360582162872687425, 360582162849948566, 360582162923663107, 360582162924587697, 360582162885620786, 360582162722259403, 360582162450709194, 360582162178955938, 360582162111633630]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 76940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 76900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk769A
