import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk010

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360180254299426255, 360180254303583333⟩, ⟨264412881285758852, 264412884121670420⟩, true⟩

def state01 : KState := ⟨⟨359792193886536327, 359792193890782560⟩, ⟨648132409553334656, 648132412478853782⟩, true⟩

def words00 : List Nat := [360444403038977407, 360443394437273926, 360442923039871318, 360442563757644150, 360442205190405762, 360440964854234467, 360438790422789597, 360436844759887211, 360434902953598181, 360433909150662614]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 1000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 1000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨359570715940038524, 359570715944375684⟩, ⟨873359867687410730, 873359870705226996⟩, true⟩

def words01 : List Nat := [360433274417476353, 360432123904967211, 360430975663951814, 360431169242684936, 360431169242693087, 360430796328774845, 360430424148216359, 360429564567519401, 360427791381759541, 360426951111733750]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 1010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 1000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨359800826389707891, 359800826394136102⟩, ⟨640701612657526984, 640701615768675714⟩, true⟩

def words02 : List Nat := [360426203184925509, 360426437276523364, 360426437276532008, 360425950537812930, 360425464748826415, 360424550584930477, 360424210035277481, 360424003663663255, 360423797693159146, 360422866797795011]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 1020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 1000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362386501070065394, 362386501074585381⟩, ⟨(-2035300461085669284), (-2035300457879524744)⟩, true⟩

def words03 : List Nat := [360422572456560614, 360422880854037714, 360424098107887172, 360425350119531867, 360425729666013893, 360426108480488130, 360426611500809793, 360427597842729490, 360429481403537265, 360431361345594484]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 1030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 1000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360530939569525450, 360530939574139310⟩, ⟨(-107530160379379357), (-107530157075138509)⟩, true⟩

def words04 : List Nat := [360432743147436140, 360433256939778247, 360433657291691271, 360434056877383327, 360434056877391653, 360433751499136771, 360432584455595981, 360430936145572629, 360429290978178571, 360428627340956496]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 1040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 1000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨359459553530981770, 359459553535689300⟩, ⟨1028788181373537640, 1028788184776615270⟩, true⟩

def words05 : List Nat := [360429603925247000, 360430578654678414, 360430985208248767, 360431336010008135, 360431415397705154, 360431494635191566, 360431494635199795, 360431474276102939, 360431024909405720, 360430108426987994]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 1050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 1000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362195649720707946, 362195649725510307⟩, ⟨(-1883038470395784686), (-1883038466891705706)⟩, true⟩

def words06 : List Nat := [360429193672150425, 360429617032033951, 360430950959683039, 360432282382305715, 360432838462619079, 360433379226313447, 360433903892439592, 360434427576966811, 360435800691021656, 360437443874070806]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 1060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 1000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨361795641237635683, 361795641242534832⟩, ⟨(-1456550440392127782), (-1456550436784005782)⟩, true⟩

def words07 : List Nat := [360438304667635739, 360439163856740087, 360440199552845409, 360441681739553590, 360442813850580904, 360443943859268102, 360444621706719589, 360445733516116364, 360446983430686161, 360448231032743893]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 1070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 1000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360850854801631067, 360850854806626655⟩, ⟨(-435100894850563427), (-435100891137791913)⟩, true⟩

def words08 : List Nat := [360449680160226539, 360450328361810334, 360450462116184568, 360450595624008040, 360450595624016780, 360450102759507399, 360450801796742124, 360451559781115279, 360451679677131833, 360452045557187799]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 1080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 1000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362320482072683734, 362320482077777031⟩, ⟨(-2042808103971108737), (-2042808100151345143)⟩, true⟩

def words09 : List Nat := [360453225922223986, 360454404127400477, 360456393884878323, 360457600906775478, 360458100430938101, 360458599044392068, 360459906985712376, 360461693997547152, 360463383804901382, 360465070542671359]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 1090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 1000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 1000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk010
