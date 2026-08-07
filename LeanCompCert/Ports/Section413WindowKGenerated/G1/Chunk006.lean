import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk006

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362326835476725994, 362326835480046804⟩, ⟨21073918244351609, 21073919604345229⟩, true⟩

def state01 : KState := ⟨⟨362048942582481907, 362048942585920865⟩, ⟨195757485453838119, 195757486885343727⟩, true⟩

def words00 : List Nat := [371164505349753076, 371165046177952562, 371165387717226349, 371165728127448821, 371166192528370779, 371166192528385281, 371167067835373285, 371168815943130355, 371169856498833846, 371169856498847658]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨364473735116060212, 364473735119621209⟩, ⟨(-1297951609462979688), (-1297951607956401794)⟩, true⟩

def words01 : List Nat := [371170302096940885, 371171269754937533, 371174823726619215, 371174937550546756, 371174937550557266, 371174454852601343, 371176058225383434, 371176882764255248, 371180264784192607, 371183635911961947]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨361330279293268156, 361330279296953456⟩, ⟨662526330256463850, 662526331840741178⟩, true⟩

def words02 : List Nat := [371186802551829707, 371186802551843385, 371187311428249609, 371188017219588519, 371189501728662344, 371189501728676081, 371187673196103293, 371185353367659788, 371183040915454144, 371181908395113363]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360442400589437702, 360442400593248488⟩, ⟨1233242768878329446, 1233242770542318764⟩, true⟩

def words03 : List Nat := [371181032573289414, 371181820860067868, 371182573639402378, 371182573639416266, 371180098568436041, 371178291647465787, 371176490399710238, 371175309779487710, 371172357980622863, 371169342422220862]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362687516965767069, 362687516969705026⟩, ⟨(-208582476213745179), (-208582474467709277)⟩, true⟩

def words04 : List Nat := [371166336272731313, 371165710795523398, 371164535117869394, 371165132088797504, 371165359415276843, 371165359415291155, 371164365258020578, 371165046149710756, 371166620855124482, 371167113783118684]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨364123899507951558, 364123899512021266⟩, ⟨(-1150761291249124157), (-1150761289416762161)⟩, true⟩

def words05 : List Nat := [371167272605346608, 371167430941140280, 371169906008972279, 371171295395999626, 371173293775475557, 371175286071610088, 371177313046155210, 371177676007567415, 371180321800765964, 371182959588546588]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362715378605690142, 362715378609891482⟩, ⟨(-210367903913585880), (-210367901993651402)⟩, true⟩

def words06 : List Nat := [371187866463672394, 371189777808126997, 371191535209872967, 371193287326205086, 371195130007135534, 371195903878067530, 371197782890087635, 371199656284738232, 371201396666601983, 371201864597978440]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨363855922409361901, 363855922413699333⟩, ⟨(-979513067345619170), (-979513065333808602)⟩, true⟩

def words07 : List Nat := [371203220353752118, 371204572080541787, 371208114268004902, 371208771163870700, 371209078252658679, 371209384434246347, 371211860512659919, 371213340579601408, 371215462023485583, 371217577236997706]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨363693398733622496, 363693398738097510⟩, ⟨(-869152153156279525), (-869152151050198383)⟩, true⟩

def words08 : List Nat := [371219569155024259, 371219933193196521, 371222432022851585, 371224923556661249, 371227943445063052, 371229186315420460, 371230325362274833, 371231461102757430, 371233757939456635, 371235580863929351]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨361886568871321764, 361886568875936484⟩, ⟨393946441437792200, 393946443640996452⟩, true⟩

def words09 : List Nat := [371239473822531750, 371243355546050308, 371246520505604821, 371246968953068454, 371247986857014636, 371249001840153584, 371250915814417937, 371250915814433492, 371250154632200809, 371249349509709337]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk006
