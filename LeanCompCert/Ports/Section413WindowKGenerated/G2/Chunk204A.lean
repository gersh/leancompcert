import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk204A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360581191195400012, 360581193615212221⟩, ⟨17029758489459698, 17063164471714242⟩, true⟩

def state01 : KState := ⟨⟨360577245418045539, 360577247840321564⟩, ⟨97293025518533215, 97326481775064403⟩, true⟩

def words00 : List Nat := [360582031050208135, 360582031050469964, 360582030203770489, 360582028139054965, 360582026074504422, 360582021776050837, 360582018940800725, 360582018497246756, 360582018053707658, 360582016408757383]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 20400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 20400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360634785213849833, 360634787638601606⟩, ⟨(-1077268118965853855), (-1077234612167140685)⟩, true⟩

def words01 : List Nat := [360582018332227365, 360582020489197649, 360582024303230679, 360582026708315172, 360582027052913905, 360582027397501440, 360582028516397932, 360582031155810701, 360582033739595508, 360582036323182815]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 20410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 20400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360584675462156129, 360584677889405508⟩, ⟨(-54255676706830409), (-54222118894722791)⟩, true⟩

def words02 : List Nat := [360582037692526157, 360582037692788298, 360582036671107903, 360582036335836466, 360582036000528976, 360582034297633007, 360582032698426104, 360582029276701769, 360582025855262515, 360582023975309540]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 20420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 20400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360562262042804215, 360562264472526487⟩, ⟨403915487597317723, 403949095942894175⟩, true⟩

def words03 : List Nat := [360582026490663592, 360582029005821551, 360582029678615868, 360582029678878803, 360582029643351708, 360582028473551799, 360582027861364801, 360582028114851372, 360582028115087354, 360582027148453244]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 20430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 20400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360572668599587739, 360572671031785265⟩, ⟨191597898359746331, 191631557311908413⟩, true⟩

def words04 : List Nat := [360582027598240331, 360582030233462468, 360582035251229411, 360582040268556178, 360582043181635041, 360582043710353851, 360582043710570108, 360582043300864328, 360582042891121799, 360582041768084136]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 20440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 20400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk204A
