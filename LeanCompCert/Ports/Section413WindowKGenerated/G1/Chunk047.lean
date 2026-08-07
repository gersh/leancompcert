import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk047

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362574533330830068, 362574533589482300⟩, ⟨(-422350179719015902), (-422349355699086470)⟩, true⟩

def state01 : KState := ⟨⟨362445719660923517, 362445719920733824⟩, ⟨183237065855975265, 183237895324733513⟩, true⟩

def words00 : List Nat := [371284710126844415, 371284710126972684, 371284673184311495, 371284677208176947, 371284694403820215, 371284694403949134, 371284670044794361, 371284645492877342, 371284623932333889, 371284623932480052]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 4700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 4700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362208374592177708, 362208374853149237⟩, ⟨1302734970173062624, 1302735805117117488⟩, true⟩

def words01 : List Nat := [371284626378088369, 371284637077327988, 371284647722545390, 371284647722674048, 371284598751603048, 371284550096158349, 371284501461277812, 371284487525260189, 371284436689222244, 371284378201691000]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 4710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 4700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362544755947902734, 362544756210026993⟩, ⟨(-286275793885514875), (-286274953494614087)⟩, true⟩

def words02 : List Nat := [371284319738879237, 371284305887751019, 371284278300636713, 371284286800002392, 371284286800105062, 371284284212604137, 371284237602439718, 371284221223705025, 371284232963910666, 371284245756952672]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 4720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 4700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362581346387949363, 362581346651250693⟩, ⟨(-458942627566863479), (-458941781602423199)⟩, true⟩

def words03 : List Nat := [371284257463639827, 371284269165424854, 371284325286952114, 371284359540732834, 371284406867253852, 371284454173843964, 371284501376324683, 371284503059189895, 371284523490417033, 371284543913093675]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 4730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 4700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362407078758973882, 362407079023429166⟩, ⟨367774656567709352, 367775508007946258⟩, true⟩

def words04 : List Nat := [371284586323427092, 371284586323556583, 371284569803558939, 371284549108196177, 371284528421506779, 371284515837966526, 371284494248164453, 371284499812492943, 371284505446033087, 371284505446167682]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 4740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 4700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362661072863259256, 362661073128892071⟩, ⟨(-840213923111609453), (-840213066072356043)⟩, true⟩

def words05 : List Nat := [371284516877347231, 371284544593798235, 371284585493317248, 371284585493447041, 371284567759715859, 371284543159971768, 371284527461026185, 371284527461169823, 371284557778727292, 371284594854144675]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 4750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 4700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362301845972332745, 362301846239139549⟩, ⟨870854757695393964, 870855620328953706⟩, true⟩

def words06 : List Nat := [371284628614744490, 371284628614874589, 371284603933907301, 371284601297554810, 371284608988277538, 371284608988407758, 371284561002337758, 371284502224325692, 371284443470909776, 371284415551577485]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 4760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 4700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362209024107843442, 362209024375823218⟩, ⟨1315097560400003225, 1315098428634747989⟩, true⟩

def words07 : List Nat := [371284377285199970, 371284366975857150, 371284356670792013, 371284341070588443, 371284304678282414, 371284281301099724, 371284261536123944, 371284261536254515, 371284207139569044, 371284149570098270]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 4770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 4700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362342041034622074, 362342041303774663⟩, ⟨678757889979854898, 678758763826624384⟩, true⟩

def words08 : List Nat := [371284092024655506, 371284053111574570, 371283992509915885, 371283975262885690, 371283958023022367, 371283926933704317, 371283838058442779, 371283792473231215, 371283746906987403, 371283744594761433]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 4780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 4700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362394075186240685, 362394075456588285⟩, ⟨429630469870563631, 429631349447455531⟩, true⟩

def words09 : List Nat := [371283715017883835, 371283685512492598, 371283669715886981, 371283669716031577, 371283668242546670, 371283667425285115, 371283666608322225, 371283662395702389, 371283600638638953, 371283581987723172]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 4790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 4700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 4700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk047
