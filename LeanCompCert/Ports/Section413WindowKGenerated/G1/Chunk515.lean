import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk515

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486225625751754, 362486264040872155⟩, ⟨(-66609930476701484), (-65273382699824068)⟩, true⟩

def state01 : KState := ⟨⟨362490087364708803, 362490125795376450⟩, ⟨(-265541021934108245), (-264203673396454423)⟩, true⟩

def words00 : List Nat := [371284996647544743, 371284996649279120, 371284996402036150, 371284996468137069, 371284996649703341, 371284996651464460, 371284996618269928, 371284996527402681, 371284996620946327, 371284996722491116]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 51500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 51500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478726692626674, 362478765138854772⟩, ⟨319783089506965351, 321121239639160417⟩, true⟩

def words01 : List Nat := [371284997199534381, 371284997677274894, 371284998009009131, 371284998010733286, 371284997915065204, 371284997926863312, 371284998313985238, 371284998315708810, 371284998201156721, 371284998082170750]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 51510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 51500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485240912938258, 362485279374575922⟩, ⟨(-15766553637585819), (-14427609524718457)⟩, true⟩

def words02 : List Nat := [371284998217563316, 371284998317049431, 371284998734687018, 371284999153005198, 371284999494451003, 371284999496174876, 371284999335817049, 371284999239276944, 371284999388131627, 371284999395349346]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 51520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 51500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487772930955216, 362487811408279907⟩, ⟨(-146238297447492929), (-144898544901138703)⟩, true⟩

def words03 : List Nat := [371284999398396358, 371284999402017350, 371284999686600359, 371284999839279238, 371285000001953491, 371285000165294790, 371285000289747248, 371285000291471716, 371285000025782436, 371285000082444143]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 51530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 51500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362464939434061314, 362464977926765846⟩, ⟨1030694879563477183, 1032035424865199777⟩, true⟩

def words04 : List Nat := [371285000250726915, 371285000252451360, 371284999919478649, 371284999559506507, 371284999198874883, 371284998894964930, 371284998465684654, 371284998314738029, 371284998163199088, 371284998012602223]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 51540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 51500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488633906107983, 362488672414411798⟩, ⟨(-190845735953187750), (-189504386429529950)⟩, true⟩

def words05 : List Nat := [371284997625417697, 371284997614946649, 371284997907647990, 371284997909372642, 371284997758204740, 371284997519177198, 371284997279482592, 371284997174379300, 371284996997672100, 371284997070907415]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 51550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 51500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485722075641109, 362485760599542921⟩, ⟨(-40692990807120498), (-39350836972073672)⟩, true⟩

def words06 : List Nat := [371284997092369781, 371284997094126308, 371284997036871432, 371284997197487641, 371284997473404937, 371284997475136690, 371284997460913993, 371284997447884730, 371284997540798043, 371284997557581895]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 51560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 51500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480903831258095, 362480942370673359⟩, ⟨207857942164625006, 209200896108584168⟩, true⟩

def words07 : List Nat := [371284997823719474, 371284998090526289, 371284998357377790, 371284998359103371, 371284998168789333, 371284998089375514, 371284998302847894, 371284998304579823, 371284998300354017, 371284998223641731]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 51570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 51500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362498068500260195, 362498107055151330⟩, ⟨(-677559554974821614), (-676215802708192342)⟩, true⟩

def words08 : List Nat := [371284998442851410, 371284998553577415, 371284998819257310, 371284999085642548, 371284999322737475, 371284999324463380, 371284999135945522, 371284999213047700, 371284999555691709, 371284999811587372]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 51580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 51500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497755809191346, 362497794379806442⟩, ⟨(-661399721390857406), (-660055157846126536)⟩, true⟩

def words09 : List Nat := [371285000029782328, 371285000248564580, 371285000841723990, 371285001247836988, 371285001680048989, 371285002112885262, 371285002487347348, 371285002489073803, 371285002611017166, 371285002861079167]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 51590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 51500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 51500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk515
