import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk986A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk986B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk986A

def state06 : KState := ⟨⟨360593561960198585, 360593626399968979⟩, ⟨(-1109093389617853837), (-1104800527787657517)⟩, true⟩

def words05 : List Nat := [360582427852129981, 360582427931431030, 360582428080783694, 360582428149640998, 360582428150962767, 360582428132704748, 360582428125220914, 360582428224543879, 360582428339212987, 360582428454197219]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 98650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 98600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585744105013749, 360585808558430862⟩, ⟨(-337846335784442105), (-333552127503184419)⟩, true⟩

def words06 : List Nat := [360582428517476552, 360582428518909921, 360582428541918671, 360582428605748387, 360582428606968832, 360582428600802844, 360582428492097042, 360582428319449835, 360582428146527435, 360582428111009602]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 98660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 98600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360566155651220980, 360566220118139622⟩, ⟨1595105361605245816, 1599400902151071708⟩, true⟩

def words07 : List Nat := [360582428224060616, 360582428337409165, 360582428393755251, 360582428395188941, 360582428373235128, 360582428325872475, 360582428306318164, 360582428307751791, 360582428234919120, 360582428072154125]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 98670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 98600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585595743879056, 360585660224329678⟩, ⟨(-323382449771507180), (-319085573823684982)⟩, true⟩

def words08 : List Nat := [360582427909074905, 360582427762234969, 360582427666190612, 360582427601165362, 360582427536047704, 360582427370582440, 360582427249479214, 360582427136800240, 360582427023702330, 360582427046290914]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 98680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 98600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360574580199967338, 360574644694093970⟩, ⟨763768368850542765, 768066594549368127⟩, true⟩

def words09 : List Nat := [360582427047568377, 360582427021027923, 360582426994225332, 360582426933265041, 360582426923667805, 360582426888282985, 360582426852735288, 360582426762432481, 360582426601003044, 360582426523825980]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 98690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 98600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 98600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk986B
