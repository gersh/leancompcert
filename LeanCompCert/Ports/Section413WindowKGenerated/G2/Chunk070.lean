import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk070

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360759255267367512, 360759255524363723⟩, ⟨(-1239922292618437086), (-1239921072491879848)⟩, true⟩

def state01 : KState := ⟨⟨360868055763052737, 360868056020818095⟩, ⟨(-2001323167897191884), (-2001321942382761546)⟩, true⟩

def words00 : List Nat := [360582194863175844, 360582250883955616, 360582318154127970, 360582385405109694, 360582435747899555, 360582475785646215, 360582500595258032, 360582525397812258, 360582560736513624, 360582601457648396]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 7000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 7000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361027980615746069, 361027980874289644⟩, ⟨(-3123688594863822422), (-3123687363890312160)⟩, true⟩

def words01 : List Nat := [360582627799694123, 360582654134235651, 360582700715865338, 360582763377803518, 360582813917728455, 360582864443261616, 360582904587728049, 360582947769144162, 360583011164239576, 360583074541304270]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 7010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 7000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360888438194480322, 360888438453794712⟩, ⟨(-2144621058226127772), (-2144619821837595634)⟩, true⟩

def words02 : List Nat := [360583126868235820, 360583159252295121, 360583181287630082, 360583203316700630, 360583219940360942, 360583246834061221, 360583293906190886, 360583340964943772, 360583371622723029, 360583415011633200]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 7020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 7000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨361052823278137872, 361052823538225421⟩, ⟨(-3301855115191980838), (-3301853873364264956)⟩, true⟩

def words03 : List Nat := [360583470244057720, 360583525460799294, 360583585706230382, 360583626062749170, 360583646327318050, 360583666586132804, 360583697032663309, 360583743573112086, 360583810203855385, 360583876815691085]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 7030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 7000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361030129582262747, 361030129843132000⟩, ⟨(-3142124595947547647), (-3142123348612706355)⟩, true⟩

def words04 : List Nat := [360583933166828822, 360583990415340929, 360584067729729373, 360584145022192832, 360584216705706924, 360584283600130380, 360584338195673537, 360584392775734627, 360584438587916160, 360584501797661471]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 7040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 7000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360661783639816174, 360661783901459436⟩, ⟨(-543166012640192828), (-543164759844607262)⟩, true⟩

def words05 : List Nat := [360584567439930089, 360584633063599966, 360584688478505322, 360584724127521207, 360584747411186627, 360584770688276959, 360584813961845451, 360584837483983168, 360584848382982752, 360584859278906738]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 7050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 7000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360874833676742853, 360874833939164173⟩, ⟨(-2048920017284333393), (-2048918758991816753)⟩, true⟩

def words06 : List Nat := [360584878226852788, 360584912673910564, 360584946165653854, 360584979647930664, 360584995525360494, 360584995525442873, 360584997583660063, 360585003480956654, 360585029305556775, 360585070290600771]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 7060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 7000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360751156593226652, 360751156856432909⟩, ⟨(-1174001736578968694), (-1174000472732984434)⟩, true⟩

def words07 : List Nat := [360585101137602079, 360585131975890537, 360585165307061239, 360585209475803211, 360585248432655292, 360585287378511351, 360585310603830294, 360585314156352307, 360585337580529350, 360585360998117278]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 7070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 7000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605418754766904, 360605419018750873⟩, ⟨(-141670465341084613), (-141669195984985981)⟩, true⟩

def words08 : List Nat := [360585395453144061, 360585410243162427, 360585414850371276, 360585419456289948, 360585419456359462, 360585416990936156, 360585428486847855, 360585439979531815, 360585439979605658, 360585440285711107]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 7080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 7000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360654669541508465, 360654669806275105⟩, ⟨(-491920398054764558), (-491919123145691678)⟩, true⟩

def words09 : List Nat := [360585442179994371, 360585444073767112, 360585455964149020, 360585455964231780, 360585448268924112, 360585420459033836, 360585392656965000, 360585376111789598, 360585385422647643, 360585395179723114]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 7090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 7000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 7000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk070
