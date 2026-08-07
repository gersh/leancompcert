import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk986

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360599103603472859, 360599167961857498⟩, ⟨(-1655038598914338113), (-1650753764151971491)⟩, true⟩

def state01 : KState := ⟨⟨360588660547103141, 360588724919150758⟩, ⟨(-625335126887082169), (-621048944890240661)⟩, true⟩

def words00 : List Nat := [360582426311396176, 360582426417999068, 360582426608238840, 360582426798922794, 360582426903315690, 360582426938192675, 360582426939468894, 360582426922802652, 360582426905882417, 360582426950923175]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 98600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 98600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567124618231277, 360567189003765790⟩, ⟨1498458721605815930, 1502746233614718444⟩, true⟩

def words01 : List Nat := [360582427078022764, 360582427205393696, 360582427281182761, 360582427282615456, 360582427255820884, 360582427157217102, 360582427058170146, 360582426994442223, 360582426899985931, 360582426746957990]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 98610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 98600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587621686465326, 360587686085539332⟩, ⟨(-523070146450293063), (-518781299109116919)⟩, true⟩

def words02 : List Nat := [360582426593607990, 360582426543546113, 360582426544724664, 360582426525073710, 360582426505311094, 360582426397067749, 360582426272787510, 360582426251656169, 360582426230107979, 360582426265613456]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 98620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 98600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585535444405835, 360585599857132494⟩, ⟨(-317297276046303488), (-313007082077395988)⟩, true⟩

def words03 : List Nat := [360582426266909315, 360582426256855435, 360582426306282636, 360582426440582098, 360582426548460761, 360582426656571122, 360582426664548926, 360582426665981964, 360582426628778347, 360582426662597997]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 98630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 98600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594372969355231, 360594437395577365⟩, ⟨(-1189052779919966738), (-1184761254691953472)⟩, true⟩

def words04 : List Nat := [360582426798623643, 360582426934677161, 360582427011688709, 360582427088887182, 360582427132273490, 360582427240654738, 360582427397505280, 360582427554638941, 360582427649999765, 360582427773224911]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 98640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 98600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk986
