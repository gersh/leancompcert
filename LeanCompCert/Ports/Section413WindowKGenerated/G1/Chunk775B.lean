import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk775A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk775B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk775A

def state06 : KState := ⟨⟨362486915065234678, 362487005054861402⟩, ⟨(-144503412552152148), (-139790185586925860)⟩, true⟩

def words05 : List Nat := [371285202358834890, 371285202494312657, 371285202596563535, 371285202599246055, 371285202531065255, 371285202515049880, 371285202644602992, 371285202677576591, 371285202702815098, 371285202729136013]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 77550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 77500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491307935240632, 362491397948786865⟩, ⟨(-485207635402650729), (-480492553117805391)⟩, true⟩

def words06 : List Nat := [371285202836306304, 371285202872497329, 371285203073624668, 371285203275811504, 371285203450441175, 371285203453116815, 371285203425998430, 371285203449156264, 371285203636965482, 371285203719588869]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 77560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 77500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493943875164471, 362494033913088175⟩, ⟨(-689663836433973274), (-684946863066719482)⟩, true⟩

def words07 : List Nat := [371285203790634955, 371285203862544546, 371285204099434635, 371285204277191528, 371285204481831252, 371285204687510629, 371285204885325168, 371285204888001529, 371285204999446878, 371285205116564971]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 77570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 77500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479264267833451, 362479354329622012⟩, ⟨449243106846660679, 453961931773020487⟩, true⟩

def words08 : List Nat := [371285205301252624, 371285205303928782, 371285205267431585, 371285205199301031, 371285205130098408, 371285205089074126, 371285205021680509, 371285205073020237, 371285205105711502, 371285205108482343]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 77580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 77500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362499874614615603, 362499964700625066⟩, ⟨(-1149997493997677529), (-1145276789651763695)⟩, true⟩

def words09 : List Nat := [371285205125489243, 371285205219312188, 371285205450576603, 371285205533417316, 371285205575153303, 371285205617667566, 371285205740842516, 371285205784050860, 371285205976058778, 371285206169296195]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 77590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 77500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 77500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk775B
