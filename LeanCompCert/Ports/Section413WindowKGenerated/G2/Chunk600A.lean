import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk600A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360602415087370459, 360602438006732812⟩, ⟨(-1214891155669101161), (-1213962131564738441)⟩, true⟩

def state01 : KState := ⟨⟨360601782633496210, 360601805560763430⟩, ⟨(-1176986667017274858), (-1176057168581509680)⟩, true⟩

def words00 : List Nat := [360582206128307520, 360582206495296566, 360582206695627823, 360582206896051689, 360582206916720135, 360582207098166153, 360582207407320908, 360582207716629384, 360582207873363322, 360582208200803065]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 60000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 60000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360635461443618295, 360635484378817698⟩, ⟨(-3198316254464527272), (-3197386279978258074)⟩, true⟩

def words01 : List Nat := [360582208519806304, 360582208839042169, 360582209435715187, 360582209877322574, 360582210083374480, 360582210289491511, 360582210773115203, 360582211475688536, 360582212363953413, 360582213252378981]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 60010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 60000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360610338532173477, 360610361475377804⟩, ⟨(-1690483527023593067), (-1689553072044914367)⟩, true⟩

def words02 : List Nat := [360582213948251987, 360582214367639429, 360582215009741947, 360582215652070148, 360582216105083624, 360582216281682972, 360582216282438137, 360582216205809800, 360582216329114065, 360582216798926556]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 60020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 60000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360607106155185279, 360607129106308517⟩, ⟨(-1496370968317532816), (-1495440037926000090)⟩, true⟩

def words03 : List Nat := [360582217487136341, 360582218175498971, 360582218724234319, 360582219192472350, 360582219589671896, 360582219987080948, 360582220661696630, 360582221294113499, 360582221709735397, 360582222125446673]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 60030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 60000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360630944567793320, 360630967526844964⟩, ⟨(-2927643009790488676), (-2926711603337346138)⟩, true⟩

def words04 : List Nat := [360582222818390340, 360582223649801122, 360582224681268842, 360582225712865538, 360582226509166619, 360582227311491422, 360582228093351152, 360582228875437213, 360582229614178422, 360582230426657834]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 60040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 60000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk600A
