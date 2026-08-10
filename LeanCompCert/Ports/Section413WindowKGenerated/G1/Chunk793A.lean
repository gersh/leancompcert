import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk793A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362474281863727910, 362474376097111891⟩, ⟨853259010706082557, 858305090462741403⟩, true⟩

def state01 : KState := ⟨⟨362490060725988760, 362490154983912122⟩, ⟨(-398087149959981245), (-393039124104171063)⟩, true⟩

def words00 : List Nat := [371285199504276303, 371285199507294908, 371285199460909280, 371285199472790933, 371285199474916460, 371285199446269121, 371285199251736777, 371285199199372533, 371285199248764885, 371285199314155037]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 79300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 79300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487487520214647, 362487581803077721⟩, ⟨(-193979888476522373), (-188929884522389787)⟩, true⟩

def words01 : List Nat := [371285199378739183, 371285199444283397, 371285199614053040, 371285199705453961, 371285199821839151, 371285199939245014, 371285200024337010, 371285200027076943, 371285199930210911, 371285199963659126]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 79310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 79300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480251898130930, 362480346205419638⟩, ⟨379997421856240134, 385049363376854398⟩, true⟩

def words02 : List Nat := [371285200077351220, 371285200080098717, 371285200031226157, 371285199982322780, 371285199932350784, 371285199916228722, 371285199884815718, 371285199927447910, 371285199969926467, 371285199972763353]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 79320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 79300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491518785423644, 362491613117473839⟩, ⟨(-513864935518620723), (-508811029541983979)⟩, true⟩

def words03 : List Nat := [371285199919026006, 371285199927852662, 371285200093995778, 371285200096736171, 371285200051500427, 371285199971316900, 371285199965530523, 371285199986222180, 371285200068925751, 371285200152808131]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 79330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 79300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475964793448027, 362476059150210146⟩, ⟨720205501462149196, 725261368205052644⟩, true⟩

def words04 : List Nat := [371285200233356506, 371285200236097218, 371285200104843004, 371285200056859140, 371285200007475700, 371285199965356758, 371285199728886097, 371285199493347829, 371285199256724170, 371285199180055201]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 79340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 79300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk793A
