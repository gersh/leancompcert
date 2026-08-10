import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk463A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360515997911260902, 360516011274895129⟩, ⟨3103595489417504112, 3104013603006458788⟩, true⟩

def state01 : KState := ⟨⟨360590989422918059, 360591002792546811⟩, ⟨(-368946467940301447), (-368528076775930813)⟩, true⟩

def words00 : List Nat := [360583051157981626, 360583050176095327, 360583049427780905, 360583048884939263, 360583048342087862, 360583047358190298, 360583046288735024, 360583045684691436, 360583045080485988, 360583045113447333]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 46300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 46300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360550185612154553, 360550198987835265⟩, ⟨1520987100331468525, 1521405771792456213⟩, true⟩

def words01 : List Nat := [360583045114013479, 360583045003819737, 360583045033125490, 360583045439177205, 360583045622879882, 360583045806678166, 360583045807244199, 360583045758265205, 360583045243977169, 360583044535585534]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 46310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 46300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360570353456575227, 360570366838238101⟩, ⟨586643776493597877, 587062725078154313⟩, true⟩

def words02 : List Nat := [360583043827017373, 360583043190585740, 360583042620869066, 360583041816087985, 360583041011239751, 360583039925766215, 360583039195859570, 360583038930916761, 360583038665916004, 360583038168371453]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 46320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 46300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360595316528293921, 360595329915963933⟩, ⟨(-570116897876656689), (-569697670952041725)⟩, true⟩

def words03 : List Nat := [360583037983275291, 360583038071872495, 360583038148763810, 360583038149399443, 360583037761335998, 360583036976786546, 360583036192149275, 360583035872322316, 360583036051009944, 360583036316970557]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 46330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 46300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360572599847573637, 360572613241302884⟩, ⟨482525117654304087, 482944625393127357⟩, true⟩

def words04 : List Nat := [360583036317543324, 360583036359583994, 360583036473437573, 360583036587469085, 360583036588004846, 360583036317842202, 360583035582811724, 360583034486576458, 360583033390266786, 360583032758571345]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 46340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 46300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk463A
