import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk333A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk333B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk333A

def state06 : KState := ⟨⟨360582235355814355, 360582242109540119⟩, ⟨(-34056021675063065), (-33903683859009381)⟩, true⟩

def words05 : List Nat := [360581229413563209, 360581228353861890, 360581227294136036, 360581227588793288, 360581227589172625, 360581227425466574, 360581227261721456, 360581226647219197, 360581225811554546, 360581225842525971]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 33350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 33300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360602281126806115, 360602287884731584⟩, ⟨(-702873570039330584), (-702721092100316430)⟩, true⟩

def words06 : List Nat := [360581226521046233, 360581227225841538, 360581227231538261, 360581227237277873, 360581227237650905, 360581227345200791, 360581228277723189, 360581229210275047, 360581229415822458, 360581230047324845]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 33360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 33300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360654924339563696, 360654931101697437⟩, ⟨(-2459998859504697810), (-2459846241115193694)⟩, true⟩

def words07 : List Nat := [360581230471813908, 360581230896410325, 360581231726110847, 360581232889130253, 360581233274910051, 360581233660708757, 360581234942226988, 360581236675005156, 360581238883108012, 360581241091179023]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 33370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 33300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583208799115053, 360583215565505600⟩, ⟨(-66116884641862504), (-65964124139911676)⟩, true⟩

def words08 : List Nat := [360581242848076328, 360581243710366253, 360581244238665794, 360581244767059473, 360581244767435168, 360581244698688706, 360581243735457746, 360581242259542395, 360581240783629059, 360581240059406954]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 33380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 33300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360513564649843699, 360513571420431815⟩, ⟨2259895477250419000, 2260048377930445886⟩, true⟩

def words09 : List Nat := [360581241014086350, 360581241968793854, 360581242473554676, 360581242474000831, 360581242406554164, 360581242111139334, 360581241815615737, 360581241137240654, 360581239565061722, 360581237539531529]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 33390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 33300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 33300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk333B
