import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk598A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360602896168230947, 360602918928985430⟩, ⟨(-1242639902675449714), (-1241720379186125228)⟩, true⟩

def state01 : KState := ⟨⟨360626583332169956, 360626606100824562⟩, ⟨(-2659290824928577926), (-2658370828971630478)⟩, true⟩

def words00 : List Nat := [360582155061048995, 360582155539799605, 360582156225091843, 360582156910521532, 360582157357169582, 360582157709512506, 360582158103314189, 360582158497359793, 360582159170867063, 360582159914855901]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 59800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 59800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360612329393967100, 360612352170582144⟩, ⟨(-1806729717611109220), (-1805809245499837246)⟩, true⟩

def words01 : List Nat := [360582160517984214, 360582161121185698, 360582161716306269, 360582162454847656, 360582163004114067, 360582163553486665, 360582163938826609, 360582164281398952, 360582164786720913, 360582165292303616]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 59810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 59800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360619434791677797, 360619457576184302⟩, ⟨(-2231784129201082086), (-2230863184985021738)⟩, true⟩

def words02 : List Nat := [360582166013817309, 360582166741392827, 360582167245947525, 360582167750566856, 360582168184393677, 360582168815305656, 360582169594746809, 360582170374321804, 360582170876588022, 360582171500655145]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 59820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 59800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360630756640520454, 360630779432925685⟩, ⟨(-2909275928547322303), (-2908354511710681409)⟩, true⟩

def words03 : List Nat := [360582172134601042, 360582172768779122, 360582173682198627, 360582174317550549, 360582174715974389, 360582175114464895, 360582175706866594, 360582176438144516, 360582177251040001, 360582178064103128]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 59830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 59800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360606927813363928, 360606950613750447⟩, ⟨(-1483433668293500172), (-1482511773819478886)⟩, true⟩

def words04 : List Nat := [360582178713109722, 360582179084051231, 360582179393257493, 360582179702687286, 360582179940424461, 360582180049901313, 360582180050646815, 360582180019579714, 360582180157064199, 360582180571916235]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 59840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 59800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk598A
