import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk285

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360587947025071689, 360587951888875733⟩, ⟨(-161910523689746296), (-161816770123624394)⟩, true⟩

def state01 : KState := ⟨⟨360549109039950059, 360549113907294961⟩, ⟨945056014750930164, 945149869249911932⟩, true⟩

def words00 : List Nat := [360582274684111185, 360582274684487402, 360582273838004275, 360582272364075193, 360582270890181785, 360582269105094181, 360582267938960147, 360582267419113648, 360582266899265225, 360582265428489276]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 28500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 28500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360605672638138572, 360605677509041124⟩, ⟨(-668008211300568886), (-667914255355512352)⟩, true⟩

def words01 : List Nat := [360582264266036494, 360582263074016220, 360582261914805127, 360582261915181644, 360582261180629836, 360582259395328772, 360582257610081004, 360582257533754734, 360582258355237196, 360582259176747183]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 28510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 28500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575578006446157, 360575582880935147⟩, ⟨190166369129026030, 190260427377203750⟩, true⟩

def words02 : List Nat := [360582259372160611, 360582259372538854, 360582259232549181, 360582259252146054, 360582259252466983, 360582258374411846, 360582257109085756, 360582255027434786, 360582252945857907, 360582251665631159]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 28520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 28500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360551538238571881, 360551543116612313⟩, ⟨876289534794857085, 876383694383589389⟩, true⟩

def words03 : List Nat := [360582252096127792, 360582252760394481, 360582252812591424, 360582252812970547, 360582252690280595, 360582251884269369, 360582251494990252, 360582251495367753, 360582251399427411, 360582250323843694]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 28530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 28500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360648711446243374, 360648716327840571⟩, ⟨(-1897586337003656905), (-1897492075887421491)⟩, true⟩

def words04 : List Nat := [360582249395270662, 360582250353608685, 360582251051709985, 360582251749833150, 360582251750182837, 360582251241733321, 360582251527439975, 360582252281746738, 360582254258242191, 360582256586469431]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 28540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 28500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360624631282605825, 360624636167796723⟩, ⟨(-1210063202170470860), (-1209968838436446008)⟩, true⟩

def words05 : List Nat := [360582258210414580, 360582259834287024, 360582261428490360, 360582263638382070, 360582265537929349, 360582267437407622, 360582268565573257, 360582268827915882, 360582270311671144, 360582271795455543]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 28550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 28500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360556573374301285, 360556578263040897⟩, ⟨733970754371003289, 734065219474114731⟩, true⟩

def words06 : List Nat := [360582273651138064, 360582274289212361, 360582274316577586, 360582274343982203, 360582274344298124, 360582274035500157, 360582274035812670, 360582273535631954, 360582273035445261, 360582271830400860]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 28560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 28500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360675532776888518, 360675537669188352⟩, ⟨(-2665291229621813301), (-2665196662785512447)⟩, true⟩

def words07 : List Nat := [360582271252822645, 360582271574620526, 360582273116830943, 360582275234124392, 360582276292459321, 360582277350746961, 360582278454980842, 360582280498445474, 360582283761772666, 360582287024956677]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 28570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 28500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360608587554123291, 360608592450019770⟩, ⟨(-751815678747004833), (-751721009100502153)⟩, true⟩

def words08 : List Nat := [360582289332784152, 360582290936639239, 360582293427658609, 360582295918617819, 360582298099615053, 360582299064896995, 360582299251035024, 360582299437206097, 360582299437513855, 360582300224875477]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 28580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 28500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589855369129298, 360589860268580156⟩, ⟨(-215994156497538028), (-215899385213747242)⟩, true⟩

def words09 : List Nat := [360582302363961174, 360582304502969405, 360582305999281267, 360582307500681764, 360582307994262729, 360582308487902764, 360582310200128615, 360582311074337464, 360582311338631722, 360582311602966585]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 28590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 28500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 28500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk285
