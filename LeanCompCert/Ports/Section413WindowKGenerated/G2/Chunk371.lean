import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk371

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360587501301597833, 360587509727942470⟩, ⟨(-220971498469911142), (-220760174845042258)⟩, true⟩

def state01 : KState := ⟨⟨360547827639675295, 360547836070774986⟩, ⟨1250929869917813542, 1251141369978915062⟩, true⟩

def words00 : List Nat := [360581559479746245, 360581559221439386, 360581558767556848, 360581558419800508, 360581558071930926, 360581557375558750, 360581555954143536, 360581553974939221, 360581551995746116, 360581550470397162]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 37100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 37100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360522863629997103, 360522872065803748⟩, ⟨2177488434472310398, 2177700109232513848⟩, true⟩

def words01 : List Nat := [360581549562328184, 360581548526341473, 360581547490356100, 360581546047488783, 360581544999321950, 360581543541029477, 360581542082664139, 360581541349787026, 360581540135795058, 360581538555815400]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 37110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 37100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581512413209157, 360581520853745029⟩, ⟨83862591732879, 295712922851243⟩, true⟩

def words02 : List Nat := [360581536975814335, 360581535374548925, 360581534245282602, 360581533841227854, 360581533437164112, 360581532319057773, 360581530898644585, 360581530024575751, 360581529150394070, 360581528818003657]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 37120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 37100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360580202883412041, 360580211328704903⟩, ⟨48674782775825040, 48886809758446934⟩, true⟩

def words03 : List Nat := [360581528818234718, 360581528452802935, 360581528226073861, 360581528734140727, 360581528746910390, 360581528759757176, 360581528760202821, 360581528407571257, 360581527648169102, 360581527613297215]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 37130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 37100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360555500476049477, 360555508926061665⟩, ⟨966292309056697191, 966504511338277323⟩, true⟩

def words04 : List Nat := [360581527757954815, 360581527981028598, 360581527981478415, 360581527842727929, 360581527703905911, 360581526910270433, 360581526588838105, 360581526339884349, 360581526090897277, 360581525198237662]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 37140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 37100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360629828561927533, 360629837016663432⟩, ⟨(-1795472848783558860), (-1795260470992320526)⟩, true⟩

def words05 : List Nat := [360581524498357906, 360581524304258539, 360581524405277168, 360581524505191651, 360581524505653146, 360581523994812998, 360581523500214080, 360581524077529117, 360581525378066908, 360581526678647978]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 37150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 37100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360578476986674276, 360578485446190678⟩, ⟨112871144797739535, 113083700254887683⟩, true⟩

def words06 : List Nat := [360581527617988635, 360581528321810467, 360581529004488634, 360581529687270858, 360581530183834885, 360581530184335659, 360581529958155896, 360581529268714596, 360581528579216891, 360581527784104450]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 37160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 37100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360519320288826921, 360519328753057631⟩, ⟨2312202855252534665, 2312415585963993665⟩, true⟩

def words07 : List Nat := [360581528343790541, 360581528985385056, 360581529262027164, 360581529262528063, 360581528816615733, 360581528181017703, 360581527545314415, 360581526744473136, 360581525572941751, 360581523900609111]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 37170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 37100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360563654815270274, 360563663284222892⟩, ⟨663641284253246069, 663854190549300339⟩, true⟩

def words08 : List Nat := [360581522228247276, 360581521278746843, 360581520694225347, 360581520323755048, 360581519953257213, 360581518871270731, 360581517067255581, 360581515679214734, 360581514291096801, 360581513625458421]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 37180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 37100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360562312283234079, 360562320756964964⟩, ⟨713420900154333206, 713633984177522980⟩, true⟩

def words09 : List Nat := [360581513145952308, 360581511983912360, 360581510821840939, 360581509874703306, 360581509292098922, 360581508387626787, 360581507483151374, 360581506218653453, 360581504981349719, 360581504466217048]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 37190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 37100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 37100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk371
