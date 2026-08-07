import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk014

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362571592714672918, 362571592734813560⟩, ⟨(-164344572206758716), (-164344553021962774)⟩, true⟩

def state01 : KState := ⟨⟨362015732462534276, 362015732482983016⟩, ⟨613742822331155019, 613742841948854791⟩, true⟩

def words00 : List Nat := [371254379437969767, 371254379438003819, 371253807295511943, 371253549584205433, 371253292239731276, 371253190751402292, 371252624158407414, 371251922020875074, 371251220879975251, 371251011094294261]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 1400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 1400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361434336261793126, 361434336282551906⟩, ⟨1439987021386609598, 1439987041443091668⟩, true⟩

def words01 : List Nat := [371250702604869762, 371250691856801397, 371250681123935458, 371250654195806687, 371250224662873870, 371249953160223571, 371249728050997135, 371249728051031687, 371249126304672215, 371248411663849858]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 1410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 1400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362427304127758406, 362427304148828908⟩, ⟨23490178812654165, 23490199313374009⟩, true⟩

def words02 : List Nat := [371247698028841425, 371247104613423815, 371246282625449610, 371245941504050818, 371245600861408129, 371245210112942477, 371244361041551872, 371243991301214740, 371243730861599034, 371243730861635464]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 1420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 1400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362468621470615452, 362468621492005454⟩, ⟨(-34833796960630825), (-34833776001378277)⟩, true⟩

def words03 : List Nat := [371243719382477623, 371243699843622383, 371244136034828181, 371244349505912469, 371244521668858005, 371244693592201618, 371244870152921677, 371244870152956870, 371244431369738346, 371244448156820598]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 1430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 1400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362081924893151515, 362081924914856726⟩, ⟨524789359649104757, 524789381063919651⟩, true⟩

def words04 : List Nat := [371244694322561782, 371244694322597600, 371244558950764708, 371244375821806914, 371244192946301966, 371244053750764945, 371243769102397974, 371243860806461477, 371243860806488767, 371243848625935292]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 1440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 1400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨363196652684903655, 363196652706929301⟩, ⟨(-1096638342374850727), (-1096638320493773899)⟩, true⟩

def words05 : List Nat := [371243815978817126, 371244032463860702, 371244713891812876, 371244774654266065, 371244774654293629, 371244723979045014, 371244962283694668, 371245015749707412, 371245530569565448, 371246044684688525]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 1450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 1400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362178605031710406, 362178605054058788⟩, ⟨392917385723008909, 392917408076951143⟩, true⟩

def words06 : List Nat := [371246560177038825, 371246649141849558, 371246751220562430, 371246853159936336, 371247101318395607, 371247101318431388, 371246739565048877, 371246358913937675, 371245978781058006, 371245895807852633]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 1460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 1400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨361676211634617382, 361676211657289484⟩, ⟨1138710560879769721, 1138710583711241919⟩, true⟩

def words07 : List Nat := [371245986080809001, 371246257691327831, 371246531473192529, 371246531473228656, 371246429889916790, 371246415255421523, 371246565434142549, 371246565434178529, 371246130916012490, 371245610700337621]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 1470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 1400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362631155714411981, 362631155737408552⟩, ⟨(-276988598022872103), (-276988574709525089)⟩, true⟩

def words08 : List Nat := [371245091187166496, 371245019716457397, 371245065149347503, 371245310908840477, 371245419586084462, 371245419586120724, 371244934363441216, 371244894077415614, 371245257365082771, 371245382045450454]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 1480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 1400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362999574416107072, 362999574439435922⟩, ⟨(-828416754885515861), (-828416731075358939)⟩, true⟩

def words09 : List Nat := [371245409433623383, 371245436785118776, 371245906746170030, 371246167835909473, 371246445259783499, 371246722313031859, 371246999897843997, 371246999897881122, 371247296618674551, 371247664558639547]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 1490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 1400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 1400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk014
