import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk863A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360601379156994515, 360601427953171400⟩, ⟨(-1660512273139295094), (-1657668449564951206)⟩, true⟩

def state01 : KState := ⟨⟨360582400395600383, 360582449203625837⟩, ⟨(-22671389864553245), (-19826543701753753)⟩, true⟩

def words00 : List Nat := [360582220103961958, 360582220107157878, 360582220108178485, 360582220108007472, 360582220107505512, 360582220042262288, 360582219956606828, 360582219786044075, 360582219615250082, 360582219493117307]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 86300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 86300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360546817500391555, 360546866320097068⟩, ⟨3048774983049216691, 3051620837376718041⟩, true⟩

def words01 : List Nat := [360582219630879520, 360582219768876526, 360582219839555775, 360582219840797062, 360582219813287450, 360582219735829850, 360582219658036364, 360582219470046278, 360582219147700594, 360582218739436465]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 86310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 86300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581671597189295, 360581720428606910⟩, ⟨39981473372096309, 42828338746272335⟩, true⟩

def words02 : List Nat := [360582218330894389, 360582218000248849, 360582217736970851, 360582217608016907, 360582217478949137, 360582217236013007, 360582216948602367, 360582216772817477, 360582216596649809, 360582216528905141]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 86320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 86300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360564967442256219, 360565016285510201⟩, ⟨1482119092615345256, 1484966979881908504⟩, true⟩

def words03 : List Nat := [360582216524283895, 360582216416950459, 360582216309387153, 360582216188921074, 360582216135815787, 360582216024784733, 360582215913628570, 360582215726357938, 360582215544913021, 360582215347125697]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 86330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 86300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574034090732687, 360574082945680389⟩, ⟨699231834014213075, 702080730973663723⟩, true⟩

def words04 : List Nat := [360582215148930101, 360582215084988388, 360582214959038165, 360582214740250138, 360582214521282262, 360582214211483052, 360582213997235154, 360582213884766536, 360582213772165106, 360582213585297919]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 86340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 86300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk863A
