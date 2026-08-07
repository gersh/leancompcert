import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk444

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360572909631898630, 360572921878942873⟩, ⟨458099039339868138, 458466507533698848⟩, true⟩

def state01 : KState := ⟨⟨360536041870224698, 360536054122991958⟩, ⟨2095125402368763139, 2095493124693308967⟩, true⟩

def words00 : List Nat := [360583247469125488, 360583247224841550, 360583246554515404, 360583245526051375, 360583244497533209, 360583243277136555, 360583242309219675, 360583241393997589, 360583240478737043, 360583239286799509]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 44400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 44400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360581345997477686, 360581358255969141⟩, ⟨82863044896875037, 83231021461269049⟩, true⟩

def words01 : List Nat := [360583238224824685, 360583237541116190, 360583236857261387, 360583236406384234, 360583235629354611, 360583234380377697, 360583233131340833, 360583232388812133, 360583232026057373, 360583231984502714]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 44410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 44400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360557180428847298, 360557192693129565⟩, ⟨1156391512692579990, 1156759746512969982⟩, true⟩

def words02 : List Nat := [360583231942866497, 360583231488513948, 360583231254102016, 360583231285821835, 360583231286330657, 360583231189085904, 360583230759612659, 360583230013334465, 360583229266984944, 360583228248981759]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 44420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 44400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360545421766636423, 360545434036638094⟩, ⟨1678971031439713005, 1679339519401668169⟩, true⟩

def words03 : List Nat := [360583227663495617, 360583227478379558, 360583227293210516, 360583226852437999, 360583226263956107, 360583225546738523, 360583224829363092, 360583224400149122, 360583223804438272, 360583222954716440]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 44430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 44400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360575648135464572, 360575660411204333⟩, ⟨335464405090704834, 335833148081864946⟩, true⟩

def words04 : List Nat := [360583222104892110, 360583221473497248, 360583221104449543, 360583220711509698, 360583220318539891, 360583219497512372, 360583218335580847, 360583217292799918, 360583216249887941, 360583215712623498]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 44440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 44400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360549400126036495, 360549412407567423⟩, ⟨1502373110132893998, 1502742110568789140⟩, true⟩

def words05 : List Nat := [360583215543204178, 360583214988956461, 360583214434617382, 360583214628426215, 360583214628936097, 360583214572049355, 360583214515108733, 360583214027357710, 360583213034645604, 360583212275101584]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 44450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 44400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575074052983484, 360575086340232032⟩, ⟨360828673993751416, 361197928664297318⟩, true⟩

def words06 : List Nat := [360583211515379190, 360583211152268913, 360583210919192694, 360583210432465518, 360583209945650657, 360583209330254084, 360583208970191390, 360583208952505831, 360583208934760362, 360583208623314207]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 44460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 44400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360578671004760907, 360578683297756690⟩, ⟨200699720966310169, 201069231244841805⟩, true⟩

def words07 : List Nat := [360583208441171972, 360583208247029627, 360583208052721785, 360583207685948923, 360583207044979477, 360583205961720654, 360583204878394220, 360583204159586447, 360583203840108202, 360583203739106619]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 44470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 44400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580366590427030, 360580378889210736⟩, ⟨125133358801002551, 125503126555095051⟩, true⟩

def words08 : List Nat := [360583203638021884, 360583203283608497, 360583202704532084, 360583202630228315, 360583202555771996, 360583202039882980, 360583201634056661, 360583200973118342, 360583200312094500, 360583199818106108]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 44480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 44400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360548159437647598, 360548171742167216⟩, ⟨1558294949171269776, 1558664972144754084⟩, true⟩

def words09 : List Nat := [360583200196159909, 360583200637725495, 360583200825941088, 360583200826549343, 360583200510682267, 360583199861000620, 360583199211163143, 360583199065727792, 360583198707808863, 360583197921316537]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 44490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 44400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 44400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk444
