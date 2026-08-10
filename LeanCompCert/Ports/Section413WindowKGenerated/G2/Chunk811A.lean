import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk811A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360599941570833750, 360599984456523784⟩, ⟨(-1445942786833427773), (-1443593841275766571)⟩, true⟩

def state01 : KState := ⟨⟨360600532821545435, 360600575718209385⟩, ⟨(-1493822833954344350), (-1491472998357147586)⟩, true⟩

def words00 : List Nat := [360582184877633950, 360582185368039704, 360582185836679237, 360582186305523765, 360582186644241373, 360582186866556455, 360582187059531300, 360582187252848386, 360582187441845862, 360582187669752861]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 81100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 81100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360599755417165019, 360599798324883049⟩, ⟨(-1430772371480388250), (-1428421639230672026)⟩, true⟩

def words01 : List Nat := [360582187802691859, 360582187935751982, 360582188151929953, 360582188484455935, 360582188778717743, 360582189073181916, 360582189291107606, 360582189357522190, 360582189575533987, 360582189793932609]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 81110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 81100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595633730787086, 360595676649457092⟩, ⟨(-1096468268071365649), (-1094116647343223647)⟩, true⟩

def words02 : List Nat := [360582190082692125, 360582190269892004, 360582190340403444, 360582190411024927, 360582190412004786, 360582190393436392, 360582190514000981, 360582190634784362, 360582190679448391, 360582190846898968]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 81120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 81100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360599710778560872, 360599753708182938⟩, ⟨(-1427258897246281024), (-1424906387921764658)⟩, true⟩

def words03 : List Nat := [360582191165830881, 360582191485095929, 360582191825430593, 360582192046403216, 360582192135533838, 360582192224749346, 360582192276807760, 360582192405212807, 360582192622584242, 360582192840213333]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 81130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 81100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591446464231524, 360591489404921693⟩, ⟨(-756750097260841976), (-754396689817990262)⟩, true⟩

def words04 : List Nat := [360582192926965880, 360582192934517134, 360582193046867890, 360582193159593401, 360582193234084306, 360582193264522815, 360582193265564785, 360582193181523697, 360582193097264188, 360582193195511853]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 81140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 81100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk811A
