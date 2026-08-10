import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk868A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk868B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk868A

def state06 : KState := ⟨⟨360560148492815521, 360560197949004024⟩, ⟨1907065512797860527, 1909966480336991367⟩, true⟩

def words05 : List Nat := [360582188006563750, 360582188089438272, 360582188090559894, 360582188070942956, 360582187918645698, 360582187704390682, 360582187489739625, 360582187407723046, 360582187223205992, 360582186971342696]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 86850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 86800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585790292067037, 360585839760071907⟩, ⟨(-320340643561352069), (-317438649595916157)⟩, true⟩

def words06 : List Nat := [360582186719201018, 360582186599814094, 360582186551532181, 360582186500045752, 360582186448463046, 360582186284253558, 360582186088697114, 360582185875055426, 360582185661035599, 360582185621756521]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 86860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 86800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360579070376455070, 360579119856355379⟩, ⟨263470967721259671, 266373995102143677⟩, true⟩

def words07 : List Nat := [360582185622871628, 360582185581444972, 360582185604661438, 360582185737664129, 360582185828349626, 360582185919236391, 360582185920380350, 360582185911733983, 360582185889242520, 360582185855378194]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 86870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 86800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360567026713405599, 360567076205072447⟩, ⟨1309894203132004204, 1312798252849789072⟩, true⟩

def words08 : List Nat := [360582185897820569, 360582185899070657, 360582185844515860, 360582185723842100, 360582185602944165, 360582185449022163, 360582185361079676, 360582185255503080, 360582185149800047, 360582184943164861]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 86880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 86800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360585152505848762, 360585202009334097⟩, ⟨(-265218429443054363), (-262313352758273647)⟩, true⟩

def words09 : List Nat := [360582184770311589, 360582184594408325, 360582184418136132, 360582184323360191, 360582184166957056, 360582183897331028, 360582183627471607, 360582183466723293, 360582183442404865, 360582183478445405]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 86890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 86800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 86800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk868B
