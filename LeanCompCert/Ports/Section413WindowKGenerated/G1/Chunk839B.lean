import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk839A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk839B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk839A

def state06 : KState := ⟨⟨362492399304050181, 362492505402486376⟩, ⟨(-608502858689178506), (-602487949270664216)⟩, true⟩

def words05 : List Nat := [371285329833329238, 371285329773452817, 371285329758272992, 371285329761200332, 371285329673950346, 371285329567266061, 371285329463380791, 371285329466647558, 371285329506507679, 371285329595275044]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 83950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 83900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472746611158767, 362472852735887326⟩, ⟨1041574315630774181, 1047591432690286325⟩, true⟩

def words06 : List Nat := [371285329679729561, 371285329682643327, 371285329577842506, 371285329510253581, 371285329441292450, 371285329380662670, 371285329130278190, 371285328879313153, 371285328627124470, 371285328518103479]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 83960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 83900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362469744425834454, 362469850576816460⟩, ⟨1293741675871555641, 1299760997565567119⟩, true⟩

def words07 : List Nat := [371285328371507258, 371285328354535776, 371285328336555373, 371285328308148484, 371285328153828356, 371285328042877982, 371285327944009446, 371285327946923704, 371285327788050862, 371285327607032769]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 83970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 83900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488582158432996, 362488688335482363⟩, ⟨(-288320860472023506), (-282299349505755168)⟩, true⟩

def words08 : List Nat := [371285327424717147, 371285327370838697, 371285327258734314, 371285327275765173, 371285327278035760, 371285327253240981, 371285327110124488, 371285327110243431, 371285327225789799, 371285327268826344]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 83980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 83900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478696773972461, 362478802977660902⟩, ⟨542015375046298731, 548039123554262285⟩, true⟩

def words09 : List Nat := [371285327310989433, 371285327354162252, 371285327425030530, 371285327428242654, 371285327460105551, 371285327495047705, 371285327504067515, 371285327506982521, 371285327326888545, 371285327252941310]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 83990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 83900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 83900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk839B
