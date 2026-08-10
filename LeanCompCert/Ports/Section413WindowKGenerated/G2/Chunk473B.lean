import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk473A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk473B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk473A

def state06 : KState := ⟨⟨360558433757090643, 360558447765731992⟩, ⟨1154549393952839399, 1154997714590008971⟩, true⟩

def words05 : List Nat := [360582840009369559, 360582839669054976, 360582839431999038, 360582839432649826, 360582839091740449, 360582838256291336, 360582837420754179, 360582836547594742, 360582835900672790, 360582835386394788]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 47350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 47300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360568030353609216, 360568044368455097⟩, ⟨699998401503923135, 700447016019120005⟩, true⟩

def words06 : List Nat := [360582834872044291, 360582834135991342, 360582833587924057, 360582833484334365, 360582833380576761, 360582833165795333, 360582832885221582, 360582832333438955, 360582831781563721, 360582831090346994]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 47360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 47300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360506364287423756, 360506378308402719⟩, ⟨3621582279911704202, 3622031184981882504⟩, true⟩

def words07 : List Nat := [360582830808754648, 360582830839435913, 360582830840016000, 360582830649093033, 360582830013435862, 360582829250381929, 360582828487153785, 360582827634457503, 360582826337128408, 360582824724295119]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 47370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 47300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580038235044118, 360580052262179561⟩, ⟨130462686393916610, 130911883187860856⟩, true⟩

def words08 : List Nat := [360582823111381453, 360582821942669611, 360582821045441186, 360582820127343154, 360582819209242066, 360582817910210929, 360582816663422155, 360582815860730763, 360582815057877576, 360582814699047843]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 47380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 47300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360562724275933521, 360562738309270655⟩, ⟨951126990666460606, 951576481389041708⟩, true⟩

def words09 : List Nat := [360582814641337764, 360582814362218114, 360582814137577897, 360582814419495600, 360582814590287224, 360582814761179978, 360582814761770773, 360582814537345511, 360582814185262381, 360582813762464517]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 47390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 47300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 47300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk473B
