import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk814A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk814B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk814A

def state06 : KState := ⟨⟨360585205692786002, 360585248974961619⟩, ⟨(-247968440154571699), (-245587268217575111)⟩, true⟩

def words05 : List Nat := [360582232935581525, 360582233288617465, 360582233547790736, 360582233687294737, 360582233727681772, 360582233768370492, 360582233959267435, 360582234115294586, 360582234153373232, 360582234191590220]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 81450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 81400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360625960204255048, 360626003497439254⟩, ⟨(-3568056263113052441), (-3565674194362393739)⟩, true⟩

def words06 : List Nat := [360582234277317015, 360582234438897708, 360582234750665178, 360582235062651704, 360582235245868529, 360582235532528142, 360582235907310191, 360582236282438348, 360582236782172812, 360582237320586603]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 81460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 81400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360607199100466810, 360607242404776600⟩, ⟨(-2039501369311095166), (-2037118394104853574)⟩, true⟩

def words07 : List Nat := [360582237763396364, 360582238206320269, 360582238619441413, 360582239132201551, 360582239605252715, 360582240078481453, 360582240435605208, 360582240642588571, 360582240950377405, 360582241258569450]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 81470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 81400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593208281141466, 360593251596437914⟩, ⟨(-899487453100752254), (-897103582647201264)⟩, true⟩

def words08 : List Nat := [360582241617194154, 360582241861692489, 360582242019857451, 360582242178151340, 360582242270499153, 360582242439727210, 360582242604599505, 360582242769682482, 360582242838539033, 360582242974839858]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 81480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 81400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360609395783553177, 360609439109864346⟩, ⟨(-2218674808788726832), (-2216290040691452446)⟩, true⟩

def words09 : List Nat := [360582243177904418, 360582243381304587, 360582243704851567, 360582244032365143, 360582244232078945, 360582244431868706, 360582244676212860, 360582245031203763, 360582245365824090, 360582245700695239]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 81490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 81400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 81400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk814B
