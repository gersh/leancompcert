import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk980A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496245617051734, 362496391901537409⟩, ⟨(-1091560677667158976), (-1081881825837498618)⟩, true⟩

def state01 : KState := ⟨⟨362487425990202775, 362487572305741189⟩, ⟨(-227229583590380601), (-217547688433906123)⟩, true⟩

def words00 : List Nat := [371285352519089658, 371285352527532081, 371285352609901122, 371285352694013895, 371285352786240365, 371285352789682207, 371285352743339466, 371285352680528732, 371285352653868994, 371285352680511022]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 98000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 98000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487937879606664, 362488084226074811⟩, ⟨(-277354623947691676), (-267669697209328384)⟩, true⟩

def words01 : List Nat := [371285352809645467, 371285352940148414, 371285353060115834, 371285353094461950, 371285353159192888, 371285353225677023, 371285353394467862, 371285353425620016, 371285353456076088, 371285353487792103]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 98010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 98000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362491721058087212, 362491867435398070⟩, ⟨(-648207332097521337), (-638519381998753385)⟩, true⟩

def words02 : List Nat := [371285353514576632, 371285353518383674, 371285353589562892, 371285353675136010, 371285353742526281, 371285353745973632, 371285353741453673, 371285353786804042, 371285353921867857, 371285353991875116]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 98020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 98000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484605545041513, 362484751953728125⟩, ⟨49383317648430110, 59074343669038874⟩, true⟩

def words03 : List Nat := [371285354051041617, 371285354111440423, 371285354238979983, 371285354316042452, 371285354397877206, 371285354480956593, 371285354562753550, 371285354566196264, 371285354509050535, 371285354507213122]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 98030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 98000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487205599059834, 362487352038463648⟩, ⟨(-205504980958169164), (-195810943267689464)⟩, true⟩

def words04 : List Nat := [371285354601347494, 371285354630586637, 371285354639816243, 371285354650160887, 371285354690671622, 371285354694520176, 371285354799930730, 371285354907293206, 371285354982946504, 371285355006885514]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 98040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 98000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk980A
