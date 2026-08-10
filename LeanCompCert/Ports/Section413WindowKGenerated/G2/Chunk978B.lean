import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk978A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk978B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk978A

def state06 : KState := ⟨⟨360599187370957028, 360599250730188088⟩, ⟨(-1651901736975915374), (-1647715049506310870)⟩, true⟩

def words05 : List Nat := [360582411843391287, 360582412023252890, 360582412198621640, 360582412437319980, 360582412649220582, 360582412861358583, 360582413013813882, 360582413082926913, 360582413256134039, 360582413429838549]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 97850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 97800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580604576739433, 360580667949350626⟩, ⟨166739377669642428, 170927374586499984⟩, true⟩

def words06 : List Nat := [360582413707404576, 360582413901288799, 360582414042677840, 360582414184226056, 360582414255098492, 360582414379154289, 360582414421508464, 360582414464105423, 360582414465377807, 360582414422984902]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 97860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 97800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360610637187400152, 360610700573422364⟩, ⟨(-2772718083614063335), (-2768528774093736025)⟩, true⟩

def words07 : List Nat := [360582414492786913, 360582414580849389, 360582414744829695, 360582414911233710, 360582414986342875, 360582415061544817, 360582415167367863, 360582415353604205, 360582415643731624, 360582415934175792]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 97870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 97800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360602191049522163, 360602254449105126⟩, ⟨(-1946040604158145380), (-1941849967245838368)⟩, true⟩

def words08 : List Nat := [360582416138229169, 360582416258929717, 360582416483670509, 360582416708839071, 360582416907222214, 360582417070086735, 360582417170926622, 360582417271949591, 360582417385801711, 360582417590075738]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 97880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 97800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583135703011425, 360583199115965512⟩, ⟨(-80590176604656473), (-76398230724895575)⟩, true⟩

def words09 : List Nat := [360582417866248912, 360582418142688822, 360582418357777768, 360582418468991620, 360582418509033077, 360582418549430167, 360582418673490993, 360582418735165100, 360582418744402810, 360582418753857619]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 97890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 97800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 97800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk978B
