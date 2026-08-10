import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk269A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360669994067517452, 360669998378975845⟩, ⟨(-2352125019726470393), (-2352046570691989639)⟩, true⟩

def state01 : KState := ⟨⟨360666314213051249, 360666318527884813⟩, ⟨(-2253507761265338214), (-2253429221422862206)⟩, true⟩

def words00 : List Nat := [360582567081262074, 360582567832588387, 360582569963195566, 360582572093748445, 360582573865845403, 360582575450196020, 360582576339087343, 360582577227957368, 360582579054364717, 360582582166492711]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 26900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 26900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360562069243542201, 360562073561702454⟩, ⟨552350624801539183, 552429254182416217⟩, true⟩

def words01 : List Nat := [360582585733679090, 360582589300667387, 360582592172817137, 360582593669992436, 360582594217305441, 360582594764666019, 360582595521901392, 360582595522255230, 360582595469809407, 360582594707845932]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 26910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 26900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598786248494159, 360598790569999756⟩, ⟨(-436112263766920148), (-436033544312805842)⟩, true⟩

def words02 : List Nat := [360582594560849784, 360582596243708250, 360582597721371788, 360582599198991235, 360582599480071245, 360582599480425039, 360582598671614576, 360582598955874881, 360582599201482439, 360582599803065264]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 26920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 26900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360537249656926017, 360537253981799957⟩, ⟨1221533933302129777, 1221612743482626239⟩, true⟩

def words03 : List Nat := [360582599803380730, 360582599594464789, 360582599797910096, 360582601026306834, 360582601897715826, 360582602769125566, 360582602769444054, 360582602745657470, 360582601349282774, 360582599666413270]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 26930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 26900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360556739641599685, 360556743969814643⟩, ⟨696181005782276737, 696259905986098669⟩, true⟩

def words04 : List Nat := [360582597983552208, 360582597016854393, 360582595479895692, 360582592878345528, 360582590276931741, 360582586851007045, 360582584126901698, 360582582777850637, 360582581428862721, 360582579216790009]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 26940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 26900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk269A
