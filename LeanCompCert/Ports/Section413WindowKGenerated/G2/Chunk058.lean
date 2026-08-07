import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk058

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360209787700641091, 360209787873695792⟩, ⟨2092791068440093062, 2092791749611300308⟩, true⟩

def state01 : KState := ⟨⟨360513033804727862, 360513033978410062⟩, ⟨332285801741461123, 332286486555323695⟩, true⟩

def words00 : List Nat := [360570551836792514, 360570519107072944, 360570501756338154, 360570483064666056, 360570464379429245, 360570419770280697, 360570345814389689, 360570301273904586, 360570256748735096, 360570226144770703]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 5800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 5800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360318502395330502, 360318502569646289⟩, ⟨1464403246292312235, 1464403934790450125⟩, true⟩

def words01 : List Nat := [360570216302777884, 360570186628284821, 360570156963988983, 360570178870029735, 360570193260661418, 360570207646356020, 360570207646416373, 360570199262973448, 360570161606310776, 360570118366002037]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 5810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 5800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360547668074481622, 360547668249424958⟩, ⟨129262239076209822, 129262931229877050⟩, true⟩

def words02 : List Nat := [360570075140528503, 360570061194336457, 360570035953935855, 360569995908564071, 360569955876929763, 360569907113169529, 360569873532748180, 360569869178166706, 360569864825072161, 360569840278795435]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 5820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 5800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360573290214212766, 360573290389786980⟩, ⟨(-21727976739250753), (-21727280904363607)⟩, true⟩

def words03 : List Nat := [360569836476410345, 360569820663797913, 360569804856587596, 360569800098456462, 360569766225449321, 360569707528286390, 360569648851223272, 360569597799308867, 360569569964905505, 360569570601924566]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 5830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 5800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580497327465571, 360580497503677077⟩, ⟨(-65428036857587622), (-65427337297815976)⟩, true⟩

def words04 : List Nat := [360569570601985058, 360569546698438418, 360569512892923581, 360569508168243970, 360569503445164650, 360569477932025163, 360569440708243155, 360569388562354500, 360569336434283784, 360569315254950737]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 5840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 5800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360425328991835643, 360425329168678727⟩, ⟨843785408920121992, 843786112177809472⟩, true⟩

def words05 : List Nat := [360569346175394413, 360569377085286690, 360569393095305553, 360569393095372529, 360569380187177487, 360569359459065010, 360569346968331705, 360569346968398778, 360569344548738791, 360569319972804634]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 5850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 5800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360820030674037046, 360820030851513797⟩, ⟨(-1471646042896339169), (-1471645335922149085)⟩, true⟩

def words06 : List Nat := [360569299760805107, 360569319086518818, 360569323739622609, 360569328391151728, 360569328391213842, 360569302835741173, 360569284883962180, 360569290344364126, 360569324661338332, 360569367363875891]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 5860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 5800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360687565295489849, 360687565473608246⟩, ⟨(-693731900203635219), (-693731189459812947)⟩, true⟩

def words07 : List Nat := [360569391554092498, 360569415736078531, 360569438476672934, 360569483781655408, 360569518230162427, 360569552666957346, 360569572613545493, 360569572613612805, 360569583978724470, 360569604040270411]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 5870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 5800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360603541357154506, 360603541535907881⟩, ⟨(-198947178351521776), (-198946463870851058)⟩, true⟩

def words08 : List Nat := [360569652853809777, 360569694451793082, 360569716364360262, 360569738269487816, 360569740624081959, 360569757653046369, 360569766220643946, 360569774785343669, 360569774785404097, 360569770280794853]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 5880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 5800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360950999461000827, 360950999640391511⟩, ⟨(-2247439647277304429), (-2247438929039655823)⟩, true⟩

def words09 : List Nat := [360569790848805590, 360569811409855185, 360569848279890076, 360569887125164514, 360569900659574484, 360569914189399380, 360569956329578715, 360570013213916390, 360570077787941959, 360570142340096705]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 5890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 5800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 5800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk058
