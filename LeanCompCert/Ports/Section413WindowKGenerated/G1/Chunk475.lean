import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk475

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362462166035793535, 362462198502311571⟩, ⟨1096463939026413805, 1097505858703183051⟩, true⟩

def state01 : KState := ⟨⟨362474877479502888, 362474909960178357⟩, ⟨492757373172379749, 493799965398665429⟩, true⟩

def words00 : List Nat := [371285303403463871, 371285303360799410, 371285303467719140, 371285303710293974, 371285303877301895, 371285303878881581, 371285303473840641, 371285303493577977, 371285303559161905, 371285303560797147]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 47500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 47500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471642540016467, 362471675035127231⟩, ⟨646529099608407499, 647572377724246963⟩, true⟩

def words01 : List Nat := [371285303343227780, 371285303123949873, 371285303124796350, 371285303126537073, 371285303146434259, 371285303168399572, 371285303169581757, 371285303165061337, 371285302684742345, 371285302399978331]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 47510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 47500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362470797340991124, 362470829850179109⟩, ⟨686703773485671111, 687747720624847093⟩, true⟩

def words02 : List Nat := [371285302269198763, 371285302270779087, 371285301837471134, 371285301356173933, 371285300874308647, 371285300525806063, 371285299966031048, 371285299848492110, 371285299730414810, 371285299610764526]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 47520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 47500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484574033207133, 362484606556653090⟩, ⟨31796306967529578, 32840931861518902⟩, true⟩

def words03 : List Nat := [371285299307417788, 371285299115485737, 371285299170434988, 371285299172015601, 371285298831759074, 371285298417581302, 371285298002777514, 371285297773837896, 371285297375731991, 371285297362960653]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 47530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 47500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362467659146652074, 362467691684359518⟩, ⟨835993178305688482, 837038481263820122⟩, true⟩

def words04 : List Nat := [371285297349619854, 371285297294555473, 371285296842381583, 371285296832360193, 371285296881260325, 371285296882841325, 371285296354930808, 371285295814563270, 371285295273593864, 371285295017298821]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 47540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 47500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362464514096628130, 362464546648609012⟩, ⟨985578360747238906, 986624342479312162⟩, true⟩

def words05 : List Nat := [371285294648191748, 371285294464957428, 371285294281183979, 371285294013889584, 371285293415622227, 371285292954470410, 371285292492522368, 371285292356015132, 371285291917795482, 371285291483396214]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 47550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 47500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491208806540260, 362491241372673115⟩, ⟨(-284103316294249913), (-283056661422104907)⟩, true⟩

def words06 : List Nat := [371285291048296591, 371285291026042641, 371285290976554056, 371285291173403480, 371285291247630606, 371285291249216565, 371285290870006158, 371285290784777791, 371285291052317266, 371285291179037873]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 47560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 47500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362479263518502342, 362479296099047181⟩, ⟨284263957201990586, 285311297725205234⟩, true⟩

def words07 : List Nat := [371285291266522992, 371285291354552508, 371285291847670122, 371285292120275416, 371285292405377678, 371285292691081287, 371285292977542987, 371285292979125024, 371285292677473258, 371285292553391974]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 47570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 47500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472306649859246, 362472339244497108⟩, ⟨615363503867338463, 616411515010084579⟩, true⟩

def words08 : List Nat := [371285292742911308, 371285292744494429, 371285292551937160, 371285292307135791, 371285292061718789, 371285291923088544, 371285291718724939, 371285291774488800, 371285291785725230, 371285291787363469]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 47580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 47500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492302229767049, 362492334838754364⟩, ⟨(-336331632736234039), (-335282938632964959)⟩, true⟩

def words09 : List Nat := [371285291684488156, 371285291854619717, 371285292128346412, 371285292129929699, 371285291884318739, 371285291587514611, 371285291290101564, 371285291220922950, 371285291077702457, 371285291227514412]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 47590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 47500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 47500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk475
