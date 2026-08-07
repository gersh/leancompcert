import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk603

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588904117829615, 360588927276161632⟩, ⟨(-399777106548701636), (-398833708394500074)⟩, true⟩

def state01 : KState := ⟨⟨360594821600635715, 360594844766910349⟩, ⟨(-756642136824005963), (-755698259689689893)⟩, true⟩

def words00 : List Nat := [360582313523852165, 360582313777404340, 360582313892495552, 360582314007675265, 360582314008393793, 360582314060400262, 360582314264233666, 360582314468218893, 360582314534570569, 360582314743205060]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 60300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 60300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360606283058697884, 360606306232952942⟩, ⟨(-1447963257058931270), (-1447018898585841686)⟩, true⟩

def words01 : List Nat := [360582315111769703, 360582315480585716, 360582315890528183, 360582316119773616, 360582316120551906, 360582316117504876, 360582316385336351, 360582316793580896, 360582317191978295, 360582317590546718]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 60310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 60300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360596780032064458, 360596803214353306⟩, ⟨(-874810968083932148), (-873866124972823794)⟩, true⟩

def words02 : List Nat := [360582317850694635, 360582317851538922, 360582318040798463, 360582318244758175, 360582318303482434, 360582318440280202, 360582318441039222, 360582318440436226, 360582318444204738, 360582318685255947]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 60320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 60300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360568434031456543, 360568457221706501⟩, ⟨835519921600022787, 836465245045125795⟩, true⟩

def words03 : List Nat := [360582319200828689, 360582319716546246, 360582319989617539, 360582320074213022, 360582320074924310, 360582319983276482, 360582320073565722, 360582320074410204, 360582319983624786, 360582319754769894]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 60330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 60300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360612620249866166, 360612643448086241⟩, ⟨(-1830872746792269051), (-1829926942392594533)⟩, true⟩

def words04 : List Nat := [360582319525716031, 360582319637156629, 360582320043253448, 360582320449500558, 360582320612674253, 360582320873631885, 360582321047717390, 360582321222033141, 360582321542612118, 360582322045915729]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 60340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 60300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360607882247541515, 360607905453802385⟩, ⟨(-1544853603772942820), (-1543907314071875160)⟩, true⟩

def words05 : List Nat := [360582322410950552, 360582322776067265, 360582323415628491, 360582324263217991, 360582325040142908, 360582325817180176, 360582326365579159, 360582326709727225, 360582327134183099, 360582327558902171]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 60350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 60300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360579430999440978, 360579454213662936⟩, ⟨172539234517046218, 173486004790281610⟩, true⟩

def words06 : List Nat := [360582327975105203, 360582328117911135, 360582328118672231, 360582328089731550, 360582328060653883, 360582327998351260, 360582328019798724, 360582328041426054, 360582328042178600, 360582327925850948]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 60360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 60300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360601212228395985, 360601235450591112⟩, ⟨(-1142504353057037553), (-1141557101405766027)⟩, true⟩

def words07 : List Nat := [360582328032680777, 360582328187368588, 360582328616191314, 360582328771747752, 360582328772542320, 360582328657370216, 360582328643794890, 360582328923557919, 360582329237371231, 360582329551361127]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 60370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 60300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360602085752029129, 360602108982291059⟩, ⟨(-1195286588881528346), (-1194338850118130084)⟩, true⟩

def words08 : List Nat := [360582329728015420, 360582330011439052, 360582330568986291, 360582331126766098, 360582331533287790, 360582331726715552, 360582331782164837, 360582331837705406, 360582331884936140, 360582332213399699]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 60380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 60300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360593528899795849, 360593552138009830⟩, ⟨(-678491387129500391), (-677543168101867025)⟩, true⟩

def words09 : List Nat := [360582332757611653, 360582333301967624, 360582333677389778, 360582333779630248, 360582333780337701, 360582333770050858, 360582334022457336, 360582334348527420, 360582334535012963, 360582334721607753]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 60390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 60300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 60300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk603
