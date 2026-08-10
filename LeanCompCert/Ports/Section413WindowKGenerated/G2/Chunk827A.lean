import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk827A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360600485622591552, 360600530284929237⟩, ⟨(-1503238168353879860), (-1500743710514148512)⟩, true⟩

def state01 : KState := ⟨⟨360578894975885563, 360578939649524097⟩, ⟨282346763500214453, 284842155974944085⟩, true⟩

def words00 : List Nat := [360582383810169104, 360582383811354753, 360582383930337948, 360582384050253665, 360582384051266016, 360582384035447031, 360582383977167354, 360582383829288918, 360582383681189899, 360582383515513397]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 82700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 82700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360556407636764963, 360556452321583642⟩, ⟨2142443675019014580, 2144939992258468700⟩, true⟩

def words01 : List Nat := [360582383549774537, 360582383625919411, 360582383626976099, 360582383619264411, 360582383465558235, 360582383252299187, 360582383038696796, 360582382947462921, 360582382759451364, 360582382447215394]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 82710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 82700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360610588461526663, 360610633157530245⟩, ⟨(-2339660075118118573), (-2337162832607047433)⟩, true⟩

def words02 : List Nat := [360582382134709325, 360582381968648197, 360582381987851335, 360582382071199337, 360582382072294509, 360582382044870142, 360582382204034517, 360582382363556875, 360582382668781449, 360582383011483334]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 82720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 82700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585620567038961, 360585665274357311⟩, ⟨(-273944995784002865), (-271446817148037263)⟩, true⟩

def words03 : List Nat := [360582383233219759, 360582383455078255, 360582383638868907, 360582383896034912, 360582384116169170, 360582384336491668, 360582384466447637, 360582384511830586, 360582384552444418, 360582384593471801]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 82730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 82700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580967879219458, 360581012597704014⟩, ⟨111058536184448446, 113557638769289436⟩, true⟩

def words04 : List Nat := [360582384739699862, 360582384863772646, 360582384914421528, 360582384965198601, 360582384966198549, 360582384926895015, 360582384940326936, 360582384953969230, 360582384955026385, 360582384895453492]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 82740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 82700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk827A
