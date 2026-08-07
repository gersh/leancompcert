import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk300

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362481869298604048, 362481881769353699⟩, ⟨111125067140203866, 111377954221540658⟩, true⟩

def state01 : KState := ⟨⟨362461317626621926, 362461330105950593⟩, ⟨727891566262205953, 728144710758754621⟩, true⟩

def words00 : List Nat := [371285594934910764, 371285594935888926, 371285594701831763, 371285594461185196, 371285594220193136, 371285594053285008, 371285593472749965, 371285593608230541, 371285593608962588, 371285593508508366]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 30000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 30000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362502675216834016, 362502687704848618⟩, ⟨(-513358247018530410), (-513104841813748712)⟩, true⟩

def words01 : List Nat := [371285593000266693, 371285593300975671, 371285594709122398, 371285594837866589, 371285594838620025, 371285594661735983, 371285595036490801, 371285595037550594, 371285595603781444, 371285596174192953]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 30010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 30000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479554309795252, 362479566806507799⟩, ⟨180695149614467142, 180948815975268302⟩, true⟩

def words02 : List Nat := [371285596746903788, 371285596747868722, 371285596188552030, 371285596093471436, 371285596236625267, 371285596237587719, 371285595001055737, 371285593767883239, 371285592534411260, 371285592408105378]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 30020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 30000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362445181029663103, 362445193535040201⟩, ⟨1213249555019088740, 1213503481621843026⟩, true⟩

def words03 : List Nat := [371285592911697542, 371285593616291676, 371285594258023009, 371285594258986139, 371285593425488428, 371285592929244277, 371285592432557748, 371285592377444392, 371285591133125457, 371285589789421754]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 30030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 30000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362465701360098100, 362465713874100371⟩, ⟨596736029442136446, 596990215189024268⟩, true⟩

def words04 : List Nat := [371285588445376346, 371285587675522820, 371285586359271765, 371285585773863264, 371285585188184075, 371285584418963282, 371285582342841860, 371285581372478575, 371285580436003524, 371285580437001837]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 30040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 30000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362489504511095269, 362489517033888620⟩, ⟨(-118728850808808420), (-118474400845854126)⟩, true⟩

def words05 : List Nat := [371285579776648054, 371285578910412866, 371285578043846580, 371285578011775476, 371285577424234169, 371285577173800891, 371285576923044140, 371285576609848425, 371285575768529460, 371285575900830976]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 30050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 30000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362458825046426233, 362458837577797068⟩, ⟨803642701039897631, 803897408887605669⟩, true⟩

def words06 : List Nat := [371285576819973934, 371285576820938001, 371285576267884278, 371285575490374458, 371285574712547621, 371285573981035470, 371285572694795363, 371285572393736951, 371285572092393018, 371285571778292167]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 30060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 30000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489291827298583, 362489304367412654⟩, ⟨(-112575738468055133), (-112320767667838405)⟩, true⟩

def words07 : List Nat := [371285571104180560, 371285571319616996, 371285571896191868, 371285571897162858, 371285571483705085, 371285570888797819, 371285570510572261, 371285570511645580, 371285570298241594, 371285570423472365]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 30070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 30000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483893909915916, 362483906458727246⟩, ⟨49706658773399206, 49961891231744812⟩, true⟩

def words08 : List Nat := [371285570438882498, 371285570439851817, 371285569470933567, 371285569440116152, 371285569408838785, 371285569401369822, 371285568502589303, 371285567592396868, 371285566872753279, 371285566873856251]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 30080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 30000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470277976000778, 362470290533513640⟩, ⟨459616212430076168, 459871706760113410⟩, true⟩

def words09 : List Nat := [371285567866125297, 371285568913887275, 371285569727427076, 371285569728392750, 371285569274676833, 371285569033572211, 371285569651446857, 371285569652412338, 371285569169807578, 371285568663306335]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 30090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 30000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 30000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk300
