import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk986

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494420158923269, 362494568309308773⟩, ⟨(-918734856786607767), (-908872586285235349)⟩, true⟩

def state01 : KState := ⟨⟨362484867911058694, 362485016092738326⟩, ⟨23154225246240754, 33019581505442950⟩, true⟩

def words00 : List Nat := [371285350715070655, 371285350718594397, 371285350812092763, 371285350908571254, 371285351000448373, 371285351003912916, 371285350977560439, 371285350952249663, 371285350939011057, 371285350942971624]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 98600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 98600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476371078255557, 362476519291072093⟩, ⟨861103629961317154, 870972056792993154⟩, true⟩

def words01 : List Nat := [371285351024172177, 371285351110144869, 371285351195145814, 371285351198609674, 371285351146394481, 371285351096391124, 371285351055138876, 371285351058619440, 371285350973366146, 371285350887673118]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 98610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 98600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485440316016887, 362485588559874616⟩, ⟨(-33330638059247832), (-23459149784948022)⟩, true⟩

def words02 : List Nat := [371285350813765074, 371285350817618758, 371285350781912069, 371285350785203737, 371285350787363118, 371285350773511637, 371285350666387812, 371285350663862831, 371285350706181937, 371285350712242686]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 98620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 98600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486494907226176, 362486643182691668⟩, ⟨(-137335072084796517), (-127460466181025899)⟩, true⟩

def words03 : List Nat := [371285350716614374, 371285350722148649, 371285350814085908, 371285350865500651, 371285350946491384, 371285351028777483, 371285351070821089, 371285351074285867, 371285351000022342, 371285351017504971]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 98630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 98600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485970741610316, 362486119047934956⟩, ⟨(-85593743611854505), (-75716093605240269)⟩, true⟩

def words04 : List Nat := [371285351135761965, 371285351164188382, 371285351188836191, 371285351214706694, 371285351268972402, 371285351279210813, 371285351361848335, 371285351445958262, 371285351521853577, 371285351533225473]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 98640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 98600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362491274818636245, 362491423156292001⟩, ⟨(-608884127158244245), (-599003386179275017)⟩, true⟩

def words05 : List Nat := [371285351561291617, 371285351591070548, 371285351705751276, 371285351709216834, 371285351698454634, 371285351673112309, 371285351685202948, 371285351698031755, 371285351761936316, 371285351827335481]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 98650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 98600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483820171130809, 362483968540026933⟩, ⟨126583120064720289, 136466943376428761⟩, true⟩

def words06 : List Nat := [371285351891283366, 371285351894748920, 371285351848734252, 371285351880111335, 371285351915831369, 371285351919297015, 371285351818250306, 371285351713027925, 371285351606417036, 371285351604214391]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 98660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 98600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476124108708861, 362476272508854996⟩, ⟨886048021040125359, 895934927952838967⟩, true⟩

def words07 : List Nat := [371285351670979971, 371285351753284820, 371285351836270652, 371285351839737268, 371285351796406117, 371285351786673152, 371285351848749844, 371285351852216305, 371285351791584227, 371285351703503890]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 98670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 98600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483763269923073, 362483911701099122⟩, ⟨132177601555801532, 142067570656877712⟩, true⟩

def words08 : List Nat := [371285351613864585, 371285351578332475, 371285351490083890, 371285351471245961, 371285351451395800, 371285351406197297, 371285351299132072, 371285351244238563, 371285351231106006, 371285351234695808]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 98680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 98600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480496736727024, 362480645199496509⟩, ⟨454562769519260540, 464455856731677152⟩, true⟩

def words09 : List Nat := [371285351222700666, 371285351205232664, 371285351190998704, 371285351194855667, 371285351150585166, 371285351138621908, 371285351125437372, 371285351112919651, 371285350975933649, 371285350932594095]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 98690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 98600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 98600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk986
