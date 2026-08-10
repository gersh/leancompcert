import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk449A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk449B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk449A

def state06 : KState := ⟨⟨360652603048345738, 360652615619168238⟩, ⟨(-3120507640827322611), (-3120125706027509685)⟩, true⟩

def words05 : List Nat := [360583209964161441, 360583210478033775, 360583211485904752, 360583212790822564, 360583213631590310, 360583214472362483, 360583215210514533, 360583216260707791, 360583217804785336, 360583219348933424]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 44950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 44900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360618122556510988, 360618135133200381⟩, ⟨(-1570297705860043642), (-1569915507255191738)⟩, true⟩

def words06 : List Nat := [360583220511939364, 360583221181449555, 360583222344872067, 360583223508429258, 360583224279275512, 360583224556727703, 360583224557278458, 360583224524367483, 360583224847703384, 360583225624689226]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 44960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 44900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360573938859688265, 360573951442169352⟩, ⟨416998287523793572, 417380746609952710⟩, true⟩

def words07 : List Nat := [360583226895336247, 360583228166044501, 360583229128881335, 360583229706692263, 360583229933677132, 360583230160805180, 360583230680277515, 360583230899092871, 360583230899645518, 360583230693983713]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 44970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 44900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360630725733010915, 360630738321310423⟩, ⟨(-2137502787768166812), (-2137120066941241940)⟩, true⟩

def words08 : List Nat := [360583230573355530, 360583231101413052, 360583232122847211, 360583233144353719, 360583233746902826, 360583233994941807, 360583234736400916, 360583235478008288, 360583236207600715, 360583237264055834]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 44980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 44900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360610921484120039, 360610934078283703⟩, ⟨(-1246389582550405141), (-1246006597865473623)⟩, true⟩

def words09 : List Nat := [360583238071819379, 360583238879610734, 360583239829329974, 360583241028511802, 360583242101803701, 360583243175158851, 360583243972893446, 360583244426241395, 360583245042066295, 360583245658073809]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 44990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 44900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 44900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk449B
