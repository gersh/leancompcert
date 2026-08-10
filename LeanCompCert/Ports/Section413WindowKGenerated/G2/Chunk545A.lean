import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk545A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360584158833799346, 360584177598495674⟩, ⟨(-132738413369221548), (-132047439605274134)⟩, true⟩

def state01 : KState := ⟨⟨360569212097820047, 360569230869737024⟩, ⟨681930826648986580, 682622193974052306⟩, true⟩

def words00 : List Nat := [360581754754826473, 360581754585096412, 360581754898048667, 360581755223041147, 360581755326867939, 360581755327625299, 360581755095785057, 360581754695751592, 360581754295601477, 360581753749831944]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 54500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 54500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360535927392170338, 360535946171218472⟩, ⟨2496507843906821578, 2497199599985958480⟩, true⟩

def words01 : List Nat := [360581753520714480, 360581753400864715, 360581753280943668, 360581752993118303, 360581752470539911, 360581751863511659, 360581751256263343, 360581750985006328, 360581750378140600, 360581749538789748]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 54510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 54500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360566397333230603, 360566416119440209⟩, ⟨835123821751824510, 835815968309556380⟩, true⟩

def words02 : List Nat := [360581748699297244, 360581748195865122, 360581747911383843, 360581747618780316, 360581747326129040, 360581746746109601, 360581745909028092, 360581745123007085, 360581744336793201, 360581743755022633]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 54520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 54500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360575166014922767, 360575184808353226⟩, ⟨356850650806474924, 357543191152008442⟩, true⟩

def words03 : List Nat := [360581743474622914, 360581743005991396, 360581742537232885, 360581742225086814, 360581742124693211, 360581741837096332, 360581741549437329, 360581740996901307, 360581740541746633, 360581740422419087]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 54530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 54500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577925926776752, 360577944727340745⟩, ⟨206304250931771919, 206997180376677751⟩, true⟩

def words04 : List Nat := [360581740518181947, 360581740518939788, 360581740399687199, 360581740112492162, 360581739825170912, 360581739453504614, 360581739382433682, 360581739515080662, 360581739515768723, 360581739359428311]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 54540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 54500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk545A
