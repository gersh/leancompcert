import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk493A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk493B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk493A

def state06 : KState := ⟨⟨360545538221071168, 360545553489532674⟩, ⟨1792540841788446750, 1793050096436732452⟩, true⟩

def words05 : List Nat := [360581881951354983, 360581882278655442, 360581882401162886, 360581882401843162, 360581882114417178, 360581881725547106, 360581881336499062, 360581880729949028, 360581880199183943, 360581879463933743]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 49350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 49300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360592543026265529, 360592558301148303⟩, ⟨(-527877094889075491), (-527367523255161073)⟩, true⟩

def words06 : List Nat := [360581878728561807, 360581878115541685, 360581877800174420, 360581877847436231, 360581877848069327, 360581877550724812, 360581876843482528, 360581876545470421, 360581876357497786, 360581876574562754]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 49360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 49300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360586758900011505, 360586774181381007⟩, ⟨(-242284529380558923), (-241774637464494161)⟩, true⟩

def words07 : List Nat := [360581876575179309, 360581876474041342, 360581876566934015, 360581877029435974, 360581877350227063, 360581877671115501, 360581877766278298, 360581877875195452, 360581877974905078, 360581878074832649]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 49370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 49300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360542813200504784, 360542828488281951⟩, ⟨1927861811116637146, 1928372019474799446⟩, true⟩

def words08 : List Nat := [360581878152539085, 360581878153219725, 360581877821493356, 360581877227472791, 360581876633376720, 360581875676023492, 360581874925652977, 360581874123272882, 360581873320850973, 360581872262719587]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 49380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 49300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360567510632730633, 360567525926940670⟩, ⟨707976170691806700, 708486696800993770⟩, true⟩

def words09 : List Nat := [360581871472766210, 360581871091732898, 360581870737374405, 360581870738055286, 360581870356236326, 360581869589260531, 360581868822185404, 360581868333947952, 360581868052524250, 360581867762908302]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 49390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 49300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 49300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk493B
