import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk170A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk170B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk170A

def state06 : KState := ⟨⟨360715845074784653, 360715846739866229⟩, ⟨(-2261745711276189707), (-2261726481807536083)⟩, true⟩

def words05 : List Nat := [360583216455818064, 360583223679692665, 360583234329343373, 360583241575993025, 360583245847925874, 360583250119374057, 360583256278854894, 360583264144834611, 360583271916559381, 360583279687418686]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 17050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 17000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360727413547517394, 360727415214653561⟩, ⟨(-2459588936529298971), (-2459569671999100683)⟩, true⟩

def words06 : List Nat := [360583284730048135, 360583288378450644, 360583294495279790, 360583300611457178, 360583305832448960, 360583312540618636, 360583317521894849, 360583322502611557, 360583327945983831, 360583336386699774]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 17060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 17000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360614521116997020, 360614522786167245⟩, ⟨(-531785850545063856), (-531766551283134204)⟩, true⟩

def words07 : List Nat := [360583346868398745, 360583357348912403, 360583365149568466, 360583369554898525, 360583373080078895, 360583376604903021, 360583383544553650, 360583387089788758, 360583388912914125, 360583390735860874]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 17070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 17000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575955220613949, 360575956891822742⟩, ⟨127095460877229574, 127114794968014900⟩, true⟩

def words08 : List Nat := [360583392125545918, 360583395723584107, 360583399814273067, 360583403904523214, 360583404553902906, 360583404554119009, 360583401812131949, 360583398981733151, 360583396151603003, 360583394855249777]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 17080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 17000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360612284213167066, 360612285886436582⟩, ⟨(-493945512069322215), (-493926142751143517)⟩, true⟩

def words09 : List Nat := [360583394420246597, 360583392185982217, 360583391126014890, 360583395695876949, 360583398303814139, 360583400911480655, 360583401344378104, 360583401344594445, 360583401316435888, 360583403005742404]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 17090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 17000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 17000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk170B
