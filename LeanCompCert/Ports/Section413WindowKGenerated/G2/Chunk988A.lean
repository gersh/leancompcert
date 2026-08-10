import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk988A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360577319674492919, 360577384304330124⟩, ⟨494110708972626098, 498422336086900130⟩, true⟩

def state01 : KState := ⟨⟨360608285168719622, 360608349812102136⟩, ⟨(-2565439686613582198), (-2561126721156394440)⟩, true⟩

def words00 : List Nat := [360582429066223527, 360582429196921506, 360582429382487760, 360582429568328458, 360582429656315048, 360582429664695990, 360582429775152811, 360582429886031536, 360582430098833245, 360582430362636425]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 98800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 98800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360585043671650070, 360585108328733579⟩, ⟨(-268799223186045131), (-264484903866620583)⟩, true⟩

def words01 : List Nat := [360582430574966400, 360582430787461988, 360582430967281887, 360582431209299923, 360582431424998516, 360582431640927203, 360582431805377205, 360582431867886694, 360582431896154411, 360582431924893640]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 98810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 98800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360578807011483810, 360578871682090631⟩, ⟨347501361573415733, 351817017333742633⟩, true⟩

def words02 : List Nat := [360582431988055864, 360582431989491925, 360582431950678267, 360582431860727221, 360582431770535673, 360582431627706964, 360582431566157773, 360582431564167454, 360582431562031393, 360582431502158766]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 98820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 98800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583866516639729, 360583931200826341⟩, ⟨(-152603184268491388), (-148286186352082092)⟩, true⟩

def words03 : List Nat := [360582431479969199, 360582431494220544, 360582431504472461, 360582431505908645, 360582431414249029, 360582431219930218, 360582431025339937, 360582430933483164, 360582430934376669, 360582430951068123]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 98830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 98800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583040138120187, 360583104835969054⟩, ⟨(-71017500565341649), (-66699152203315769)⟩, true⟩

def words04 : List Nat := [360582430952347967, 360582430910285243, 360582430791367140, 360582430748137908, 360582430704528865, 360582430620411739, 360582430520515405, 360582430341212790, 360582430161638377, 360582430091634619]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 98840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 98800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk988A
