import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk125

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360626261270113890, 360626262138621385⟩, ⟨(-561644749498614599), (-561637395088938433)⟩, true⟩

def state01 : KState := ⟨⟨360660291432351775, 360660292302326572⟩, ⟨(-987298075874591432), (-987290703116520108)⟩, true⟩

def words00 : List Nat := [360581335137008826, 360581338309095677, 360581347835910655, 360581357361246571, 360581363331204340, 360581369320648373, 360581370334419420, 360581371348044323, 360581372181996779, 360581378490231894]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 12500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 12500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360605312642246675, 360605313513670782⟩, ⟨(-299036111191061025), (-299028720294733775)⟩, true⟩

def words01 : List Nat := [360581391146196337, 360581403800167765, 360581412130334913, 360581414126803433, 360581414482819435, 360581414838821762, 360581421538335073, 360581427522455082, 360581429430420936, 360581431338102159]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 12510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 12500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360629900720566310, 360629901593445871⟩, ⟨(-606972288942149935), (-606964879816304529)⟩, true⟩

def words02 : List Nat := [360581435932005891, 360581443754503370, 360581451402909260, 360581459050121131, 360581461186328715, 360581461186482718, 360581459153568917, 360581461303538829, 360581461303664757, 360581464526985389]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 12520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 12500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360581325710017973, 360581326584364563⟩, ⟨1941918384974190, 1949345900031014⟩, true⟩

def words03 : List Nat := [360581465216758905, 360581465906439811, 360581470856914315, 360581479026285082, 360581483717180546, 360581488407352532, 360581488407493529, 360581488381565897, 360581482046816271, 360581482034595826]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 12530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 12500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360602635695543779, 360602636571342318⟩, ⟨(-265561932507465204), (-265554486777636396)⟩, true⟩

def words04 : List Nat := [360581488330396723, 360581488330815548, 360581488330953097, 360581484249023501, 360581480167717671, 360581472472121548, 360581473434144778, 360581477073354920, 360581477073492554, 360581478537179492]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 12540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 12500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360631887040072936, 360631887917331430⟩, ⟨(-633337587437123759), (-633330123377866185)⟩, true⟩

def words05 : List Nat := [360581478537307504, 360581476511447903, 360581478773943966, 360581478774098371, 360581476764863821, 360581469515972057, 360581462268205618, 360581459529166803, 360581463544291239, 360581467558810782]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 12550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 12500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594165912019359, 360594166790748538⟩, ⟨(-160051558605334639), (-160044076066888717)⟩, true⟩

def words06 : List Nat := [360581467746815287, 360581467746970825, 360581468651508008, 360581470094657613, 360581470094789333, 360581467068951692, 360581460534742452, 360581449777252908, 360581439021445776, 360581435577951872]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 12560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 12500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360440841977697902, 360440842857886395⟩, ⟨1768063556126722568, 1768071057016145176⟩, true⟩

def words07 : List Nat := [360581438308768463, 360581441039182098, 360581441039322151, 360581438890544785, 360581430467036607, 360581420344512743, 360581410223553704, 360581406394023708, 360581400219759051, 360581389046838394]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 12570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 12500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360705536167503918, 360705537049154145⟩, ⟨(-1563236337802672846), (-1563228818517342148)⟩, true⟩

def words08 : List Nat := [360581377875658912, 360581369378908769, 360581365329928164, 360581366448012056, 360581366448154818, 360581362161155740, 360581362620590832, 360581364534206978, 360581372726633517, 360581382588148876]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 12580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 12500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360549988807294046, 360549989690423904⟩, ⟨395915831376096825, 395923369297201927⟩, true⟩

def words09 : List Nat := [360581389181089253, 360581395772998160, 360581401851662924, 360581411110317098, 360581416040589649, 360581420970103838, 360581420970243293, 360581420946963844, 360581414673915769, 360581412180050667]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 12590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 12500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 12500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk125
