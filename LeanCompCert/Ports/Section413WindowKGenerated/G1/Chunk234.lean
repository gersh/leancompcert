import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk234

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362518258874398357, 362518266304746609⟩, ⟨(-790425775340307929), (-790308209481321451)⟩, true⟩

def state01 : KState := ⟨⟨362471751192407183, 362471758629312090⟩, ⟨298079086724327575, 298196806042667263⟩, true⟩

def words00 : List Nat := [371284496074237618, 371284496074972628, 371284495824477233, 371284495432204803, 371284495055178236, 371284495055988159, 371284495185226675, 371284496023194902, 371284496638207063, 371284496638967907]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 23400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 23400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362515964250727083, 362515971694263352⟩, ⟨(-737142851538619392), (-737024976945130810)⟩, true⟩

def words01 : List Nat := [371284496881518789, 371284497668476893, 371284499658145183, 371284499705774829, 371284499706354228, 371284499206529312, 371284500029954875, 371284500452626390, 371284501796905843, 371284503141385801]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 23410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 23400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362504604316525351, 362504611766711701⟩, ⟨(-471100407361387671), (-470982376989917071)⟩, true⟩

def words02 : List Nat := [371284504299851170, 371284504300599802, 371284505082072247, 371284506190553994, 371284507825816176, 371284508265262065, 371284508625692003, 371284508986325457, 371284510085244673, 371284510943998633]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 23420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 23400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472634275862658, 362472641732683591⟩, ⟨278346410236861023, 278464596089808079⟩, true⟩

def words03 : List Nat := [371284513624018323, 371284516304114422, 371284518985640891, 371284519242203247, 371284519929585145, 371284520617286791, 371284522584172498, 371284522584908900, 371284522127602140, 371284521621595273]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 23430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 23400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494328550609796, 362494336014026304⟩, ⟨(-230345859446695448), (-230227518959121490)⟩, true⟩

def words04 : List Nat := [371284521529885422, 371284521530696478, 371284521038889372, 371284520899896051, 371284520760698418, 371284520331439653, 371284518038921692, 371284517566490694, 371284518208603437, 371284518628031715]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 23440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 23400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362508139792230251, 362508147262352581⟩, ⟨(-554248264125464374), (-554129766352940656)⟩, true⟩

def words05 : List Nat := [371284519043986809, 371284519460156516, 371284521396346103, 371284522435123085, 371284524023117047, 371284525611266637, 371284526869341693, 371284526870079050, 371284527066801758, 371284528074493882]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 23450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 23400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362467825972018934, 362467833448703177⟩, ⟨391739788019139017, 391858439768862525⟩, true⟩

def words06 : List Nat := [371284530402840129, 371284530403577380, 371284530312793714, 371284529886573508, 371284529460091876, 371284529311556031, 371284528701956052, 371284529147264214, 371284529589387448, 371284529590150509]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 23460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 23400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362537973761774237, 362537981245144080⟩, ⟨(-1255025994968527177), (-1254907186274405123)⟩, true⟩

def words07 : List Nat := [371284528925878484, 371284528973343681, 371284530835491078, 371284531166029148, 371284531219578706, 371284531273345035, 371284532449942683, 371284533175906194, 371284535452730729, 371284537729694381]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 23470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 23400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484612341975250, 362484619832002510⟩, ⟨(-1981557981127602), (-1862592937160198)⟩, true⟩

def words08 : List Nat := [371284539994829958, 371284540131420084, 371284541546142438, 371284542961117955, 371284544082495364, 371284544083233500, 371284542790924272, 371284541496183912, 371284540538136456, 371284540542362344]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 23480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 23400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362457655551695830, 362457663048372003⟩, ⟨631516697893025566, 631635819153841474⟩, true⟩

def words09 : List Nat := [371284541672139675, 371284542802124428, 371284543796074250, 371284543796814551, 371284542958061407, 371284542394241069, 371284543076568862, 371284543077307859, 371284542311311567, 371284541168335997]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 23490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 23400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 23400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk234
