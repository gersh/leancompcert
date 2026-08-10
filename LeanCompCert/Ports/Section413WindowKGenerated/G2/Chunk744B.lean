import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk744A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk744B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk744A

def state06 : KState := ⟨⟨360568436929853698, 360568472839026486⟩, ⟨1028753825899339381, 1030559785728113787⟩, true⟩

def words05 : List Nat := [360582313266801743, 360582313160833552, 360582313127727536, 360582313292949308, 360582313412464541, 360582313532149750, 360582313560774178, 360582313561833536, 360582313472066345, 360582313287397801]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 74450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 74400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576617441555182, 360576653360704832⟩, ⟨419533440324969599, 421340143080070303⟩, true⟩

def words06 : List Nat := [360582313102380886, 360582312997230203, 360582312785411750, 360582312483582276, 360582312181583405, 360582311810786674, 360582311575139907, 360582311488359585, 360582311401466285, 360582311211424318]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 74460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 74400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585411994686539, 360585447923846729⟩, ⟨(-235448355067454215), (-233640906778509667)⟩, true⟩

def words07 : List Nat := [360582311240367830, 360582311345594414, 360582311446568628, 360582311463456012, 360582311464443445, 360582311324227108, 360582311183817720, 360582311006084477, 360582310961036780, 360582311004272898]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 74470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 74400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360571916539832241, 360571952479076802⟩, ⟨769625437437926419, 771433636861407091⟩, true⟩

def words08 : List Nat := [360582311005224058, 360582310882632757, 360582310627168999, 360582310518925122, 360582310410392457, 360582310256662422, 360582309922771996, 360582309449568628, 360582308976175087, 360582308683088904]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 74480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 74400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360554963076745381, 360554999025968463⟩, ⟨2032673719472885119, 2034482662245847531⟩, true⟩

def words09 : List Nat := [360582308548636921, 360582308553421182, 360582308554375992, 360582308452012960, 360582308428406657, 360582308332296321, 360582308235879177, 360582308139860872, 360582307883542497, 360582307518079146]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 74490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 74400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 74400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk744B
