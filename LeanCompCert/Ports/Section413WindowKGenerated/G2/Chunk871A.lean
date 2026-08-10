import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk871A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360576614474092574, 360576664214558865⟩, ⟨476465124471012913, 479390818491567713⟩, true⟩

def state01 : KState := ⟨⟨360589886371742054, 360589936124056581⟩, ⟨(-679605168810694666), (-676678442751250170)⟩, true⟩

def words00 : List Nat := [360582168065357655, 360582167958832704, 360582168007228563, 360582168097986973, 360582168099143216, 360582168077776672, 360582167977847243, 360582167994598099, 360582168031347274, 360582168121820914]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 87100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 87100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360581686494598186, 360581736258858278⟩, ⟨34704877581107527, 37632644277298325⟩, true⟩

def words01 : List Nat := [360582168146224941, 360582168170754835, 360582168234356824, 360582168364703513, 360582168388805220, 360582168413091527, 360582168414208773, 360582168361212950, 360582168225680923, 360582168222176429]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 87110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 87100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590270358858032, 360590320134938459⟩, ⟨(-713132643026152678), (-710203846483794366)⟩, true⟩

def words02 : List Nat := [360582168344854913, 360582168488288837, 360582168561504019, 360582168634856192, 360582168635910207, 360582168666798753, 360582168828217727, 360582168989873442, 360582169050815811, 360582169145663875]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 87120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 87100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360605069774250684, 360605119562165087⟩, ⟨(-2002714091322743048), (-1999784263627528860)⟩, true⟩

def words03 : List Nat := [360582169242644114, 360582169339983974, 360582169568500004, 360582169740319617, 360582169785095910, 360582169829990029, 360582169974605526, 360582170200047736, 360582170464428358, 360582170729082755]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 87130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 87100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360597363628507547, 360597413428381894⟩, ⟨(-1331254661610489604), (-1328323791668502672)⟩, true⟩

def words04 : List Nat := [360582170918982893, 360582171154598717, 360582171357520165, 360582171560787549, 360582171702080217, 360582171712010833, 360582171713140480, 360582171637539164, 360582171616348372, 360582171792695918]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 87140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 87100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk871A
