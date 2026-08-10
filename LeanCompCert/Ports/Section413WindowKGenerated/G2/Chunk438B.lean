import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk438A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk438B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk438A

def state06 : KState := ⟨⟨360583493216388748, 360583505155336926⟩, ⟨(-13767584467339129), (-13413712726939541)⟩, true⟩

def words05 : List Nat := [360583196629333779, 360583196779080781, 360583197448171427, 360583198378708139, 360583198941022524, 360583199503400104, 360583199669304768, 360583199669903706, 360583199324448548, 360583199332106108]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 43850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 43800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360611663445628183, 360611675390224928⟩, ⟨(-1249449617442886754), (-1249095497927650116)⟩, true⟩

def words06 : List Nat := [360583199580378069, 360583200058638919, 360583200275405146, 360583200492226866, 360583200500929325, 360583200769569584, 360583201557129860, 360583202344772870, 360583202731799060, 360583203381428055]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 43860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 43800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360610061559966997, 360610073510218578⟩, ⟨(-1179167273207493197), (-1178812905586551181)⟩, true⟩

def words07 : List Nat := [360583204256019705, 360583205130745965, 360583206378477996, 360583207108254225, 360583207393546777, 360583207678874455, 360583207892615525, 360583208427737033, 360583209040464660, 360583209653296755]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 43870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 43800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586389652227645, 360586401608196434⟩, ⟨(-140564688552695539), (-140210070033947419)⟩, true⟩

def words08 : List Nat := [360583210004846135, 360583210077811440, 360583210137144360, 360583210196648955, 360583210197150707, 360583210030652773, 360583209346330766, 360583208401083151, 360583207455761122, 360583207102032666]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 43880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 43800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360557230707064552, 360557242668668779⟩, ⟨1139519985573239501, 1139874851460588065⟩, true⟩

def words09 : List Nat := [360583207693824532, 360583208285704238, 360583208615196970, 360583208776249492, 360583208804438225, 360583208832784994, 360583208847588745, 360583208848188512, 360583208518100138, 360583207927244192]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 43890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 43800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 43800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk438B
