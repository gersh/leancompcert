import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk382A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360577043393220309, 360577052347985645⟩, ⟨185132680631385384, 185363900775474862⟩, true⟩

def state01 : KState := ⟨⟨360613424253634914, 360613433213266185⟩, ⟨(-1204763413712543871), (-1204532007664911221)⟩, true⟩

def words00 : List Nat := [360581905236177388, 360581906134044301, 360581906839498599, 360581907545011338, 360581907684253331, 360581907840674340, 360581908200532114, 360581908560520117, 360581909213578512, 360581910039110447]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 38200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 38200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360599177765096550, 360599186729649226⟩, ⟨(-660414980638094721), (-660183386520402595)⟩, true⟩

def words01 : List Nat := [360581910463443436, 360581910887810777, 360581911117408331, 360581911869525261, 360581912448389682, 360581913027309404, 360581913263233196, 360581913263749330, 360581913485026097, 360581913937557957]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 38210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 38200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360569177970180786, 360569186939588685⟩, ⟨486333408327311333, 486565188036097839⟩, true⟩

def words02 : List Nat := [360581914782215680, 360581915265827987, 360581915343801689, 360581915421823184, 360581915422258518, 360581915080066846, 360581915080491616, 360581914918811149, 360581914757081619, 360581914252903781]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 38220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 38200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360633010592475658, 360633019566755051⟩, ⟨(-1954409098538662759), (-1954177132567954137)⟩, true⟩

def words03 : List Nat := [360581914270140487, 360581914620421480, 360581914820286953, 360581915036680959, 360581915037156822, 360581914669578768, 360581914616346336, 360581915270906072, 360581916607733011, 360581917944606887]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 38230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 38200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360606916396977529, 360606925376186966⟩, ⟨(-956679262706916201), (-956447108187978875)⟩, true⟩

def words04 : List Nat := [360581918744607615, 360581918865308721, 360581919501863624, 360581920138536387, 360581920602356133, 360581920874193505, 360581920874657631, 360581920550954528, 360581920227161245, 360581920876744129]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 38240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 38200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk382A
