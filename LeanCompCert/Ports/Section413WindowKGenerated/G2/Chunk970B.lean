import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk970A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk970B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk970A

def state06 : KState := ⟨⟨360578261880532378, 360578324168391245⟩, ⟨389718604925257619, 393800875881603339⟩, true⟩

def words05 : List Nat := [360582381028537943, 360582381287849945, 360582381450165543, 360582381506798980, 360582381507999176, 360582381476499509, 360582381487694135, 360582381500656077, 360582381501911162, 360582381461569502]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 97050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 97000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360591480672072663, 360591542973244533⟩, ⟨(-893347877242813542), (-889264314060222954)⟩, true⟩

def words06 : List Nat := [360582381425314645, 360582381513555069, 360582381658589834, 360582381803900281, 360582381858496003, 360582381859904934, 360582381842954880, 360582381878933682, 360582381909516969, 360582382005354430]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 97060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 97000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585683584316607, 360585745898901154⟩, ⟨(-330594566526628547), (-326509701307961913)⟩, true⟩

def words07 : List Nat := [360582382023377093, 360582382041544500, 360582382165573535, 360582382343911757, 360582382449899675, 360582382556130506, 360582382608865959, 360582382610275059, 360582382591758930, 360582382628010785]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 97070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 97000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588378073114796, 360588440400993388⟩, ⟨(-592233333797322040), (-588147177927963274)⟩, true⟩

def words08 : List Nat := [360582382769906371, 360582382806294177, 360582382807585511, 360582382749836015, 360582382691851095, 360582382607223637, 360582382635027965, 360582382667806130, 360582382669061524, 360582382711012567]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 97080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 97000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360593356293041498, 360593418634215845⟩, ⟨(-1075583314374627503), (-1071495867555339589)⟩, true⟩

def words09 : List Nat := [360582382854267296, 360582382997951550, 360582383226928675, 360582383388064728, 360582383459302325, 360582383530648485, 360582383531821257, 360582383545079602, 360582383659865613, 360582383774970778]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 97090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 97000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 97000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk970B
