import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk384A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk384B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk384A

def state06 : KState := ⟨⟨362522387673085238, 362522408595884307⟩, ⟨(-1435053430559393151), (-1434509640303804037)⟩, true⟩
def words05 : List Nat := [371285105046136396, 371285105082200350, 371285105793802725, 371285106336869527, 371285107085365157, 371285107834327868, 371285108585762502, 371285108881059561, 371285109851744497, 371285110823067589]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 38450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 38400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491650116490016, 362491671050480220⟩, ⟨(-252651973048550353), (-252107752322679583)⟩, true⟩
def words06 : List Nat := [371285112469446143, 371285113215938630, 371285113960811966, 371285114706088649, 371285115462451067, 371285115880453859, 371285116483639505, 371285117087283930, 371285117689357018, 371285117861004442]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 38460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 38400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362510812658820049, 362510833604217386⟩, ⟨(-989915204570527965), (-989370544956696711)⟩, true⟩
def words07 : List Nat := [371285118353517275, 371285118846689102, 371285119942917547, 371285120139867185, 371285120267100760, 371285120394694596, 371285121126174123, 371285121640971832, 371285122310032032, 371285122979624556]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 38470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 38400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488235079095856, 362488256035832062⟩, ⟨(-121076856373220354), (-120531760380299108)⟩, true⟩
def words08 : List Nat := [371285123598345656, 371285123599604144, 371285123741903304, 371285124064833532, 371285124536872707, 371285124538152874, 371285124450757814, 371285124362663328, 371285124525943858, 371285124608735331]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 38480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 38400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362473578845621287, 362473599813698220⟩, ⟨443232946237777788, 443778478791975370⟩, true⟩
def words09 : List Nat := [371285125258304433, 371285125908339568, 371285126451271313, 371285126452532732, 371285126355828936, 371285126411344356, 371285127066920795, 371285127068179630, 371285126825398952, 371285126527433077]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 38490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 38400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 38400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk384B
