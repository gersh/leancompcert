import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk284

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360573583576336861, 360573588404594035⟩, ⟨246529187234098461, 246621929492253989⟩, true⟩

def state01 : KState := ⟨⟨360597227697021621, 360597232528847677⟩, ⟨(-425338693753474062), (-425245850121373126)⟩, true⟩

def words00 : List Nat := [360582271969925358, 360582271046814780, 360582270087755759, 360582270225979715, 360582270226295999, 360582269308382790, 360582268433016471, 360582266661699640, 360582264890435810, 360582264880749357]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 28400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 28400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360551697244582919, 360551702079943710⟩, ⟨868490187422722147, 868583131494464733⟩, true⟩

def words01 : List Nat := [360582266642257873, 360582268403714017, 360582268911206018, 360582268911580938, 360582268187159916, 360582267147678790, 360582266108161078, 360582266003222216, 360582265545240436, 360582264470214452]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 28410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 28400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360597121137301324, 360597125976200641⟩, ⟨(-422628321815637188), (-422535277161426124)⟩, true⟩

def words02 : List Nat := [360582263395172513, 360582263617398296, 360582264821746223, 360582266026085195, 360582266159694528, 360582266160069655, 360582265502926877, 360582264482090916, 360582263672711542, 360582264195849566]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 28420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 28400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360607397958401090, 360607402800874287⟩, ⟨(-714882110016933968), (-714788963739794406)⟩, true⟩

def words03 : List Nat := [360582264196188809, 360582263941713072, 360582264664709740, 360582266584587079, 360582267607668596, 360582268630737126, 360582269037540119, 360582269037915375, 360582269573869762, 360582270457998165]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 28430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 28400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576355055134019, 360576359901146198⟩, ⟨167856492483330394, 167949739426903068⟩, true⟩

def words04 : List Nat := [360582270760810017, 360582270761185262, 360582269834938626, 360582268151799386, 360582266468715640, 360582264471944879, 360582263609901385, 360582263794782420, 360582263795120214, 360582263231178779]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 28440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 28400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360599669026235511, 360599673875790688⟩, ⟨(-495611895143215937), (-495518547383783527)⟩, true⟩

def words05 : List Nat := [360582263383486841, 360582263743370054, 360582264798162805, 360582265197650390, 360582265198002435, 360582264430784795, 360582263663552831, 360582262492972638, 360582262823139890, 360582263435279681]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 28450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 28400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360606339672314345, 360606344525450198⟩, ⟨(-685538317040796032), (-685444867357690362)⟩, true⟩

def words06 : List Nat := [360582263435614450, 360582263706305137, 360582265308955992, 360582266911604030, 360582268201243320, 360582268780536653, 360582268780874472, 360582268730099509, 360582268679259250, 360582269330783426]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 28460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 28400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564171866913016, 360564176723586079⟩, ⟨515327778486542563, 515421328891794787⟩, true⟩

def words07 : List Nat := [360582271029642508, 360582272728454042, 360582273812508373, 360582274349684851, 360582274350000589, 360582274061938677, 360582274713822906, 360582275017354068, 360582275017691100, 360582274382606157]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 28470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 28400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360600890264253285, 360600895124478676⟩, ⟨(-530770806664888150), (-530677155072134668)⟩, true⟩

def words08 : List Nat := [360582273747481620, 360582274314242662, 360582274452646952, 360582274591106737, 360582274591456765, 360582273662422138, 360582271508320576, 360582270210565570, 360582268912792019, 360582268991486780]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 28480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 28400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360587947025071689, 360587951888875733⟩, ⟨(-161910523689746296), (-161816770123624394)⟩, true⟩

def words09 : List Nat := [360582269031825565, 360582269072203579, 360582270339519863, 360582272226079191, 360582273481839784, 360582274737575229, 360582274934574892, 360582274934951077, 360582274107037927, 360582274306681297]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 28490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 28400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 28400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk284
