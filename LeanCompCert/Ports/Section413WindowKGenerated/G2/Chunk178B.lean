import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk178A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk178B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk178A

def state06 : KState := ⟨⟨360500753982810719, 360500755815434541⟩, ⟨1484687403135900847, 1484709558433291509⟩, true⟩

def words05 : List Nat := [360583884426173381, 360583889853029134, 360583892825136659, 360583893743674395, 360583893859903729, 360583893976182183, 360583893994503399, 360583893994730155, 360583890904422394, 360583886249837301]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 17850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 17800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598648239623857, 360598650074387253⟩, ⟨(-264039469599617015), (-264017276078747557)⟩, true⟩

def words06 : List Nat := [360583881595721833, 360583878922584027, 360583880898845306, 360583883446642943, 360583883446853740, 360583883331025129, 360583880108119675, 360583877910874675, 360583875744209718, 360583876571165344]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 17860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 17800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360558949641172922, 360558951478100158⟩, ⟨445453008640344169, 445475240839410559⟩, true⟩

def words07 : List Nat := [360583876571371196, 360583874622738135, 360583872830699737, 360583874646066448, 360583874646258782, 360583873889199487, 360583873132200022, 360583870298471989, 360583867594002544, 360583866200742184]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 17870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 17800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360543076543786039, 360543078382850178⟩, ⟨729306286410528865, 729328556828186955⟩, true⟩

def words08 : List Nat := [360583866526679013, 360583866526906104, 360583865145038979, 360583862154591705, 360583859164444530, 360583853877628515, 360583851014129929, 360583849927181021, 360583848840327715, 360583845770040127]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 17880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 17800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360598949863675666, 360598951704886473⟩, ⟨(-270410528014988792), (-270388219182930308)⟩, true⟩

def words09 : List Nat := [360583844322283735, 360583845153160544, 360583847590808473, 360583848686283918, 360583848686493239, 360583847111203880, 360583845536048394, 360583845373429712, 360583846217545853, 360583847061616101]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 17890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 17800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 17800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk178B
