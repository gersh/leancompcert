import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk556A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk556B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk556A

def state06 : KState := ⟨⟨360499136291599009, 360499155897031539⟩, ⟨4601416249608724208, 4602153532912712096⟩, true⟩

def words05 : List Nat := [360581848774677708, 360581848180133474, 360581847585529365, 360581846781115002, 360581845654612686, 360581844447183077, 360581843239572769, 360581842024734464, 360581840700709869, 360581839215984337]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 55650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 55600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360564208911300994, 360564228524035342⟩, ⟨979152713820646962, 979890403580838754⟩, true⟩

def words06 : List Nat := [360581837731130188, 360581836568459615, 360581835567647144, 360581834888924280, 360581834210158303, 360581833257088650, 360581832209691895, 360581831484416828, 360581830758940709, 360581830291658494]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 55660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 55600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360565018901259936, 360565038521382455⟩, ⟨934011088851481131, 934749189947712379⟩, true⟩

def words07 : List Nat := [360581829976190404, 360581829358862231, 360581828741407895, 360581828445992311, 360581828313335478, 360581827974368337, 360581827635328369, 360581827100636655, 360581826702576752, 360581826401949045]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 55670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 55600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360569573590996028, 360569593218406521⟩, ⟨680407229540049463, 681145736468248177⟩, true⟩

def words08 : List Nat := [360581826121281686, 360581826122061652, 360581826095941798, 360581825860093748, 360581825624139682, 360581825104738787, 360581824746959984, 360581824645227431, 360581824543415454, 360581824242584439]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 55680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 55600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360574073628161445, 360574093262899587⟩, ⟨429778498818542786, 430517413858254434⟩, true⟩

def words09 : List Nat := [360581824125555239, 360581824228401937, 360581824280888183, 360581824281663205, 360581824012760966, 360581823462995208, 360581822913100644, 360581822684981129, 360581822618347935, 360581822480383578]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 55690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 55600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 55600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk556B
