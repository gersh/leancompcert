import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk385A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360562717827081566, 360562726928869264⟩, ⟨748304620881621449, 748541479358128043⟩, true⟩

def state01 : KState := ⟨⟨360617564312385443, 360617573419078541⟩, ⟨(-1363460307453453607), (-1363223260094854513)⟩, true⟩

def words00 : List Nat := [360582169228066356, 360582169845569572, 360582170989347025, 360582172133164666, 360582172617815577, 360582172913146216, 360582173190180375, 360582173467345219, 360582174216771788, 360582175136507462]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 38500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 38500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587277058600460, 360587286170251873⟩, ⟨(-196902308459104256), (-196665070131545158)⟩, true⟩

def words01 : List Nat := [360582175539742224, 360582175943006068, 360582176636144782, 360582177860634195, 360582178915576503, 360582179970548969, 360582180572766100, 360582180573286578, 360582180638237547, 360582180771375117]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 38510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 38500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591975470071416, 360591984586628724⟩, ⟨(-377931256451203181), (-377693829123686707)⟩, true⟩

def words02 : List Nat := [360582180886497914, 360582181281512584, 360582181339100318, 360582181396742011, 360582181397178831, 360582181049469672, 360582181473342557, 360582181910032572, 360582181995144630, 360582182250091295]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 38520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 38500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360595932477718676, 360595941599189859⟩, ⟨(-530489860511376115), (-530252243828172361)⟩, true⟩

def words03 : List Nat := [360582182960224506, 360582183670477059, 360582184280878351, 360582184281399036, 360582184222629795, 360582183522136053, 360582182821579069, 360582182750208583, 360582183107632633, 360582183465155243]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 38530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 38500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574227638442798, 360574236764878694⟩, ⟨306054636455575433, 306292444503512393⟩, true⟩

def words04 : List Nat := [360582183465619561, 360582183403717861, 360582183981357566, 360582184606076950, 360582184843018349, 360582184843539281, 360582184411703605, 360582183644954220, 360582182878151502, 360582182094178397]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 38540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 38500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk385A
