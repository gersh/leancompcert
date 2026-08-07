import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk859

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362469525429008641, 362469636683093242⟩, ⟨1335540394363121337, 1341993194025778917⟩, true⟩

def state01 : KState := ⟨⟨362481245688499757, 362481356969318531⟩, ⟨328704924119866523, 335160020381832827⟩, true⟩

def words00 : List Nat := [371285259241254598, 371285259123689639, 371285258941374780, 371285258895735495, 371285258849079606, 371285258773626938, 371285258516646923, 371285258387171255, 371285258258491867, 371285258261605597]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 85900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 85900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491676784463361, 362491788092558618⟩, ⟨(-567501474463964308), (-561044034745773822)⟩, true⟩

def words01 : List Nat := [371285258218466369, 371285258150368660, 371285258127332183, 371285258130660991, 371285258148366206, 371285258180153883, 371285258208431220, 371285258211485322, 371285258246695031, 371285258326439209]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 85910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 85900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479325575839016, 362479436910499556⟩, ⟨493761151619502833, 500220873968201695⟩, true⟩

def words02 : List Nat := [371285258460550878, 371285258463538001, 371285258417361060, 371285258372429100, 371285258326420104, 371285258288568804, 371285258181832038, 371285258178442646, 371285258174013059, 371285258170524789]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 85920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 85900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491483681663543, 362491595043343528⟩, ⟨(-551012796960650392), (-544550752697345944)⟩, true⟩

def words03 : List Nat := [371285258172311329, 371285258243479610, 371285258448249184, 371285258473525890, 371285258475844138, 371285258464392006, 371285258536994170, 371285258557976980, 371285258633770008, 371285258710828229]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 85930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 85900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481266510683950, 362481377899320043⟩, ⟨327048152706470893, 333512513716527791⟩, true⟩

def words04 : List Nat := [371285258787055208, 371285258790043189, 371285258699772957, 371285258648512136, 371285258595747874, 371285258585483771, 371285258462152785, 371285258339884695, 371285258216430700, 371285258207798421]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 85940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 85900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362471434937894357, 362471546353520515⟩, ⟨1172151665254884395, 1178618346194409427⟩, true⟩

def words05 : List Nat := [371285258179523654, 371285258197658543, 371285258199931083, 371285258191883959, 371285258061563381, 371285257974280117, 371285257905975004, 371285257908963331, 371285257751398131, 371285257595332921]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 85950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 85900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362466900549165392, 362467011991528293⟩, ⟨1562005998716157540, 1568474978083362270⟩, true⟩

def words06 : List Nat := [371285257437854338, 371285257396599528, 371285257286503217, 371285257254810317, 371285257222230448, 371285257149886511, 371285256915313124, 371285256738365361, 371285256559809055, 371285256437010245]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 85960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 85900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362470212338730380, 362470323808268548⟩, ⟨1277295855149176596, 1283767170914537380⟩, true⟩

def words07 : List Nat := [371285256227028005, 371285256018107848, 371285255808003040, 371285255716794078, 371285255584457204, 371285255485439974, 371285255385388648, 371285255271212220, 371285254975825606, 371285254805836757]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 85970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 85900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362458640794804495, 362458752291012109⟩, ⟨2272283892520436843, 2278757501463233849⟩, true⟩

def words08 : List Nat := [371285254634245110, 371285254506744580, 371285254249029466, 371285253992460981, 371285253734712766, 371285253499515760, 371285253209950039, 371285252991233203, 371285252771480627, 371285252552687458]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 85980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 85900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486103435342265, 362486214958597911⟩, ⟨(-89360137335722623), (-82884202399275891)⟩, true⟩

def words09 : List Nat := [371285252246540022, 371285252077023746, 371285251905934140, 371285251862666005, 371285251711920232, 371285251541214574, 371285251369325756, 371285251295974035, 371285251185397252, 371285251200009066]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 85990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 85900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 85900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk859
