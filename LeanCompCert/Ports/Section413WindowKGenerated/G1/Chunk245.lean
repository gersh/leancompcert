import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk245

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362517600903464839, 362517609080551658⟩, ⟨(-784372223278615169), (-784236769540231307)⟩, true⟩

def state01 : KState := ⟨⟨362473140883845902, 362473149067892967⟩, ⟨304966132845422319, 305101757145982541⟩, true⟩

def words00 : List Nat := [371285602018844111, 371285602019616460, 371285601575303706, 371285602056216666, 371285602716197017, 371285602716969419, 371285601157689352, 371285599255743008, 371285597353640391, 371285597120000107]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 24500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 24500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362501024941637726, 362501033132653425⟩, ⟨(-378462393539506668), (-378326598402461566)⟩, true⟩

def words01 : List Nat := [371285597573580891, 371285598535262948, 371285599486262552, 371285599487050872, 371285599797050384, 371285600198429398, 371285602266002241, 371285603195293624, 371285603825155597, 371285604455258439]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 24510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 24500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362528418311777428, 362528426509723880⟩, ⟨(-1050275808214555599), (-1050139843100260003)⟩, true⟩

def words02 : List Nat := [371285605679902580, 371285606190124009, 371285608137726143, 371285610085475786, 371285611816887800, 371285611817661209, 371285612513532338, 371285613694700173, 371285616079113772, 371285617825075873]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 24520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 24500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362531939046346044, 362531947251321018⟩, ⟨(-1136588586973468158), (-1136452449413007946)⟩, true⟩

def words03 : List Nat := [371285619323372575, 371285620821795702, 371285623984068974, 371285626586435086, 371285629287521608, 371285631988680422, 371285634679541469, 371285635156875877, 371285637044610108, 371285638932613019]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 24530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 24500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362503198880081978, 362503207091964391⟩, ⟨(-431126847513730610), (-430990540409316830)⟩, true⟩

def words04 : List Nat := [371285641190786584, 371285642081661318, 371285642884049204, 371285643686640771, 371285644979745396, 371285645449119476, 371285647580570633, 371285649712158760, 371285651468335108, 371285652184204654]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 24540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 24500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362552599674133974, 362552607893023457⟩, ⟨(-1644101742822745725), (-1643965263659804749)⟩, true⟩

def words05 : List Nat := [371285654561775238, 371285656939573667, 371285660633957099, 371285662117661934, 371285663365343399, 371285664613170611, 371285666952801150, 371285668469668280, 371285671195741090, 371285673921944926]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 24550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 24500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482056592567355, 362482064818460357⟩, ⟨88563589968525942, 88700241172646862⟩, true⟩

def words06 : List Nat := [371285676656643722, 371285677182238377, 371285677661331747, 371285678140765439, 371285678770151918, 371285678770926599, 371285677482454670, 371285676146564051, 371285674920974899, 371285674921886188]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 24560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 24500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362461129751089582, 362461137983941832⟩, ⟨603095718153292384, 603232540382675070⟩, true⟩

def words07 : List Nat := [371285676287674293, 371285677800571564, 371285679302411636, 371285679337221563, 371285679864577974, 371285680392283474, 371285681589866698, 371285681590641530, 371285680582061691, 371285679584445603]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 24570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 24500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477849543776862, 362477857783567025⟩, ⟨192140780679328689, 192277773478311523⟩, true⟩

def words08 : List Nat := [371285678960680984, 371285678961536794, 371285679121671966, 371285679592907882, 371285679593512130, 371285679477105566, 371285677667356745, 371285677035895249, 371285677131015133, 371285677131817465]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 24580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 24500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494406384042030, 362494414630915482⟩, ⟨(-215044358213541612), (-214907191201663612)⟩, true⟩

def words09 : List Nat := [371285676814431674, 371285676187553797, 371285676588651299, 371285676797408488, 371285677494864934, 371285678192563252, 371285678872812566, 371285678873601716, 371285678565264874, 371285678921342633]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 24590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 24500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 24500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk245
