import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk003

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362110168845939316, 362110168846248088⟩, ⟨(-538778626190320698), (-538778626126448086)⟩, true⟩

def state01 : KState := ⟨⟨360199222209044545, 360199222209376325⟩, ⟨21381158428760715, 21381158499655219⟩, true⟩

def words00 : List Nat := [360323675106744093, 360323675106746488, 360317797774713595, 360305794748426553, 360293870430508250, 360278091315572754, 360271176459485363, 360272557862473885, 360272557862476100, 360268193688407471]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨364557350821009628, 364557350821365234⟩, ⟨(-1345770744525441239), (-1345770744447036765)⟩, true⟩

def words01 : List Nat := [360277164542730803, 360286298431464992, 360304732400063300, 360314397125970521, 360314498784790948, 360314599802230965, 360323887082299455, 360338633754128413, 360351817244965618, 360364918595673531]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360280840039390885, 360280840039771511⟩, ⟨32801817210856086, 32801817297393026⟩, true⟩

def words02 : List Nat := [360372803894602077, 360383563864039403, 360393616183139215, 360403606641814541, 360408449550713645, 360408449550716260, 360405300692795051, 360397429976713073, 360389607106929045, 360380239486127248]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨357734461344162848, 357734461344569054⟩, ⟨893640598247400058, 893640598342511666⟩, true⟩

def words03 : List Nat := [360387893681134673, 360395800401837327, 360397928791628705, 360397928791631402, 360392288783298789, 360383468998995894, 360374701557625769, 360373957928094158, 360370569304278634, 360362816045576442]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361156813173489064, 361156813173921915⟩, ⟨(-305651885948629599), (-305651885844323679)⟩, true⟩

def words04 : List Nat := [360355108260531779, 360346823098915359, 360343722750216392, 360340463861158173, 360337223864210261, 360326187249749441, 360307888087539040, 360297212053840636, 360286597200850347, 360286010080348344]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360227453435442526, 360227453435903023⟩, ⟨26118844560324855, 26118844674449847⟩, true⟩

def words05 : List Nat := [360286010080350938, 360283396669559588, 360285570486773090, 360295063448954858, 360301612003115066, 360308123870697812, 360308123870700471, 360307598505840774, 360300207877889783, 360300005782220940]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨359628529247456927, 359628529247945565⟩, ⟨232101510132252482, 232101510256652442⟩, true⟩

def words06 : List Nat := [360303045377428230, 360303045377431184, 360299466606030977, 360290187715197434, 360280959667600856, 360269192779624549, 360261815202001880, 360261325124084562, 360260837702415843, 360255830627017599]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨364567845712768704, 364567845713286291⟩, ⟨(-1632124978990453550), (-1632124978855195432)⟩, true⟩

def words07 : List Nat := [360254139787723419, 360251161160117069, 360251886596896922, 360257615034002572, 360257615034005386, 360257286742679958, 360256960192952544, 360261447352185081, 360272779979453649, 360284053117865831]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361694853639564111, 361694853640111564⟩, ⟨(-549021722276896727), (-549021722130134939)⟩, true⟩

def words08 : List Nat := [360291557583648450, 360293016971367084, 360300775295535607, 360308493316722300, 360310043986412033, 360310043986415188, 360305635093898074, 360297359237394734, 360289125930281608, 360290706013180273]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨355026784850885841, 355026784851464029⟩, ⟨2089435310107011003, 2089435310265917909⟩, true⟩

def words09 : List Nat := [360293901440468954, 360297080606041803, 360297080606044686, 360296737639998224, 360290579909034675, 360282247844640714, 360273957755381314, 360271587139148990, 360263464827064424, 360250373127128824]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk003
