import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk378A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360604162128583662, 360604170889310198⟩, ⟨(-851496948108353274), (-851273101508275346)⟩, true⟩

def state01 : KState := ⟨⟨360587626359455374, 360587635124979855⟩, ⟨(-226352157441397126), (-226128129454485632)⟩, true⟩

def words00 : List Nat := [360581652142964535, 360581652857028042, 360581653220025066, 360581653583060955, 360581653768272758, 360581654303637806, 360581654479492091, 360581654655426110, 360581654655884575, 360581654639685775]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 37800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 37800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360673410791567759, 360673419561905277⟩, ⟨(-3470268519243145652), (-3470044309251877908)⟩, true⟩

def words01 : List Nat := [360581655496784540, 360581656353988109, 360581657909482066, 360581659726995960, 360581660947949217, 360581662168878251, 360581663597644390, 360581665566695575, 360581667993178830, 360581670419649603]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 37810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 37800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360607958898505343, 360607967673707223⟩, ⟨(-994712332328274244), (-994487938343294336)⟩, true⟩

def words02 : List Nat := [360581672310501139, 360581673505727077, 360581675235818529, 360581676965967876, 360581678236746112, 360581678812038381, 360581679044045444, 360581679276100242, 360581679332167529, 360581680027640683]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 37820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 37800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360552326460087366, 360552335240089201⟩, ⟨1110285363518501168, 1110509939110581840⟩, true⟩

def words03 : List Nat := [360581681420735892, 360581682813855148, 360581683856241080, 360581684203390026, 360581684203825250, 360581683943883631, 360581683953704169, 360581683954214575, 360581683529393412, 360581682754336310]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 37830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 37800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583110478993444, 360583119263818423⟩, ⟨(-54662498236582385), (-54437740113475619)⟩, true⟩

def words04 : List Nat := [360581681979201047, 360581682084070162, 360581682344056957, 360581682604125626, 360581682604600994, 360581682254862571, 360581681427015330, 360581681296519592, 360581681165887199, 360581681052407537]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 37840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 37800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk378A
