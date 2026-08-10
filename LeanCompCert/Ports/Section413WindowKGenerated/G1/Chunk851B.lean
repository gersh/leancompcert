import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk851A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk851B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk851A

def state06 : KState := ⟨⟨362488501251128915, 362488610523561192⟩, ⟨(-288379971112112922), (-282096663448366778)⟩, true⟩

def words05 : List Nat := [371285298283776696, 371285298297087807, 371285298395965034, 371285298398923545, 371285298314319276, 371285298195281680, 371285298075071420, 371285298029301264, 371285297971320113, 371285298013568962]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 85150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 85100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480297727915891, 362480407027066939⟩, ⟨410281918273023855, 416567501443256621⟩, true⟩

def words06 : List Nat := [371285298054582726, 371285298057614723, 371285298087716091, 371285298151013678, 371285298255166747, 371285298258125876, 371285298193513789, 371285298130198158, 371285298065678545, 371285298039177345]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 85160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 85100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362470313766790942, 362470423092566738⟩, ⟨1260714160874014410, 1267002011807287332⟩, true⟩

def words07 : List Nat := [371285298045308951, 371285298110042606, 371285298138751071, 371285298141712071, 371285298010640152, 371285297921859898, 371285297840548080, 371285297843507570, 371285297671171239, 371285297499843180]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 85170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 85100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472342856303455, 362472452208601711⟩, ⟨1087888935558286858, 1094179045809665908⟩, true⟩

def words08 : List Nat := [371285297327229093, 371285297277663623, 371285297158121943, 371285297083180329, 371285297007277665, 371285296910407195, 371285296642233090, 371285296462677631, 371285296281630289, 371285296193175132]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 85180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 85100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362474634849431966, 362474744228706400⟩, ⟨892636745691336120, 898929154175848880⟩, true⟩

def words09 : List Nat := [371285296044620898, 371285295898515873, 371285295751178058, 371285295742787091, 371285295664185144, 371285295591973542, 371285295518821636, 371285295419982798, 371285295160498455, 371285295040375131]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 85190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 85100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 85100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk851B
