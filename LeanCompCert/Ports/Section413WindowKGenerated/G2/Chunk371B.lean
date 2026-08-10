import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk371A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk371B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk371A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk371B
