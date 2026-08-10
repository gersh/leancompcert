import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk313A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk313B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk313A

def state06 : KState := ⟨⟨360533504727282843, 360533510664760773⟩, ⟨1548179902790902363, 1548305817820244995⟩, true⟩

def words05 : List Nat := [360582887820078488, 360582888449410541, 360582888449788372, 360582888291803038, 360582887483534863, 360582886418422269, 360582885353249276, 360582885302076953, 360582884235475815, 360582882661502490]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 31350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 31300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360514133320862655, 360514139262274458⟩, ⟨2155894867879197759, 2156020906294810911⟩, true⟩

def words06 : List Nat := [360582881087530152, 360582879671415823, 360582878770430646, 360582878597409546, 360582878424371590, 360582877210305657, 360582874981342076, 360582872725273770, 360582870469229663, 360582868012873592]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 31360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 31300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360536368352804299, 360536374298187906⟩, ⟨1458230317856941669, 1458356480887196387⟩, true⟩

def words07 : List Nat := [360582865822408203, 360582863125186828, 360582860428054055, 360582858475824393, 360582857299089673, 360582855817165584, 360582854335290171, 360582852347046336, 360582849854004471, 360582848373423317]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 31370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 31300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360559897310197799, 360559903259516197⟩, ⟨719656789789825659, 719783076313480929⟩, true⟩

def words08 : List Nat := [360582846892804445, 360582845385506004, 360582844169284827, 360582842185490003, 360582840201753574, 360582837962272315, 360582836236803350, 360582835523134446, 360582834809457411, 360582833590077315]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 31380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 31300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360647224604920947, 360647230558179642⟩, ⟨(-2021951026479207090), (-2021824616250033580)⟩, true⟩

def words09 : List Nat := [360582833140872711, 360582833422251225, 360582834714781877, 360582835879258432, 360582836072537080, 360582836265827358, 360582837470160186, 360582839187738820, 360582841238758128, 360582843289740738]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 31390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 31300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 31300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk313B
