import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk775

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362468570031917014, 362468659876941780⟩, ⟨1277509989723964802, 1282212005688743882⟩, true⟩

def state01 : KState := ⟨⟨362485170361620348, 362485260230590349⟩, ⟨(-9105452465914791), (-4401580624039665)⟩, true⟩

def words00 : List Nat := [371285204336323144, 371285204248877419, 371285204077023789, 371285203973380654, 371285203868818301, 371285203738088409, 371285203507626573, 371285203431365605, 371285203440557095, 371285203444061676]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 77500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 77500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484237504493525, 362484327397884850⟩, ⟨63223606291209299, 67929371148442903⟩, true⟩

def words01 : List Nat := [371285203446095340, 371285203417164869, 371285203521550649, 371285203575682376, 371285203655716645, 371285203736747769, 371285203774997545, 371285203777719108, 371285203687700359, 371285203679762410]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 77510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 77500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480783862346161, 362480873779518482⟩, ⟨330994196904420072, 335701805389691128⟩, true⟩

def words02 : List Nat := [371285203825229933, 371285203827904300, 371285203784854053, 371285203742752036, 371285203699686325, 371285203668055323, 371285203622191630, 371285203684418037, 371285203736835013, 371285203739603478]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 77520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 77500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479587022836978, 362479676964197710⟩, ⟨423819623068087614, 428529107002814158⟩, true⟩

def words03 : List Nat := [371285203717495433, 371285203752660418, 371285203904447689, 371285203907122266, 371285203837568107, 371285203743807346, 371285203657606804, 371285203660554178, 371285203587909107, 371285203519614306]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 77530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 77500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482506299901181, 362482596265389992⟩, ⟨197383378380138007, 202094733327664953⟩, true⟩

def words04 : List Nat := [371285203450341079, 371285203381809757, 371285203108921014, 371285203003655194, 371285202897021367, 371285202822497344, 371285202639353203, 371285202457164308, 371285202273915775, 371285202258082806]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 77540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 77500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk775
