import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk822

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360591795744618791, 360591839847813906⟩, ⟨(-784672604560250259), (-782224248135711681)⟩, true⟩

def state01 : KState := ⟨⟨360584148907565758, 360584193021863370⟩, ⟨(-156120024704268946), (-153670755597520758)⟩, true⟩

def words00 : List Nat := [360582323966210129, 360582324009955775, 360582324011013188, 360582323934213184, 360582323857223343, 360582323710739618, 360582323712515113, 360582323788076987, 360582323789126979, 360582323798090426]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 82200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 82200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360622462125085720, 360622506250507864⟩, ⟨(-3306083197625111040), (-3303633013918662452)⟩, true⟩

def words01 : List Nat := [360582323941378215, 360582324085019210, 360582324293642573, 360582324543088345, 360582324649839347, 360582324756648391, 360582325011096997, 360582325353239140, 360582325842891538, 360582326332799266]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 82210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 82200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604273409305312, 360604317545963881⟩, ⟨(-1810521983466915809), (-1808070875845806065)⟩, true⟩

def words02 : List Nat := [360582326748380957, 360582327171415060, 360582327742043511, 360582328313016285, 360582328739893605, 360582329019424909, 360582329224695652, 360582329430090139, 360582329573369997, 360582329842107115]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 82220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 82200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360596742193669533, 360596786341424321⟩, ⟨(-1191154721142413538), (-1188702701023512370)⟩, true⟩

def words03 : List Nat := [360582330258272421, 360582330674655969, 360582331016586782, 360582331211131134, 360582331368355309, 360582331525919826, 360582331830908233, 360582332093588974, 360582332270396058, 360582332447368759]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 82230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 82200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360624568029374147, 360624612188270418⟩, ⟨(-3479720157979745028), (-3477267221532274632)⟩, true⟩

def words04 : List Nat := [360582332771867155, 360582333171758285, 360582333535386191, 360582333899214771, 360582334137017206, 360582334401459285, 360582334687883834, 360582334974643003, 360582335381902017, 360582335897142867]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 82240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 82200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360623851763882862, 360623895934010312⟩, ⟨(-3420825715927764786), (-3418371855660718796)⟩, true⟩

def words05 : List Nat := [360582336293853321, 360582336690664903, 360582337201124707, 360582337785972993, 360582338333391748, 360582338880989883, 360582339315201679, 360582339726838450, 360582340232973057, 360582340739499418]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 82250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 82200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360627254859758009, 360627299040986040⟩, ⟨(-3700809389784106016), (-3698354616326885126)⟩, true⟩

def words06 : List Nat := [360582341393328833, 360582341899976755, 360582342304560105, 360582342709285636, 360582343076702819, 360582343518435822, 360582344107513241, 360582344696802318, 360582345173027433, 360582345720662635]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 82260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 82200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360636343759552904, 360636387951931537⟩, ⟨(-4448697718864288138), (-4446242027992762578)⟩, true⟩

def words07 : List Nat := [360582346206002872, 360582346691659120, 360582347257875517, 360582347735154679, 360582348088276861, 360582348441480989, 360582348838577500, 360582349349033975, 360582350006751889, 360582350664732880]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 82270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 82200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360610363777389406, 360610407980982093⟩, ⟨(-2311004006067284069), (-2308547392447443455)⟩, true⟩

def words08 : List Nat := [360582351248446361, 360582351684953871, 360582352238925556, 360582352793230011, 360582353246170900, 360582353551962725, 360582353758095918, 360582353964343009, 360582354177316046, 360582354519577475]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 82280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 82200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360574391813001553, 360574436027713668⟩, ⟨649371340712288132, 651828869405658892⟩, true⟩

def words09 : List Nat := [360582354883674011, 360582355248001782, 360582355538142617, 360582355759251459, 360582355926924366, 360582356094919464, 360582356259998554, 360582356278030274, 360582356279099474, 360582356184085548]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 82290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 82200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 82200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk822
