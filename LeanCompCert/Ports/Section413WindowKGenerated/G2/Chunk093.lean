import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk093

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360496413771018249, 360496414238102035⟩, ⟨742004460905188188, 742007405797758354⟩, true⟩

def state01 : KState := ⟨⟨360496290086606182, 360496290554742780⟩, ⟨742598686162667131, 742601640851518177⟩, true⟩

def words00 : List Nat := [360576191402561629, 360576189785664478, 360576176744952501, 360576154751567362, 360576132762891356, 360576107750915753, 360576091910555752, 360576081847629538, 360576071786852748, 360576054425940581]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 9300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 9300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360568557419959576, 360568557889149640⟩, ⟨69400154553502878, 69403119055465074⟩, true⟩

def words01 : List Nat := [360576048749840050, 360576051639778840, 360576061570422504, 360576061570534251, 360576060099369897, 360576047877970174, 360576035659174575, 360576017611956729, 360576005374714493, 360576004575743575]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 9310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 9300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360497117610007676, 360497118080262338⟩, ⟨734926505379222391, 734929479808497327⟩, true⟩

def words02 : List Nat := [360576003776928647, 360575995487477559, 360575981430686335, 360575978806936029, 360575976183716128, 360575970310113449, 360575953070937067, 360575930019611993, 360575906973207065, 360575888656876325]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 9320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 9300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360403100717632047, 360403101188942438⟩, ⟨1612147621078685745, 1612150605363242921⟩, true⟩

def words03 : List Nat := [360575880215153552, 360575867237294191, 360575854262204862, 360575832534845271, 360575807978107776, 360575780416841556, 360575752861446659, 360575736705993196, 360575726802421557, 360575708320137647]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 9330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 9300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360692705359783731, 360692705832152591⟩, ⟨(-1094247115139641523), (-1094244120963804883)⟩, true⟩

def words04 : List Nat := [360575689841785983, 360575682755819732, 360575691940985035, 360575702224537299, 360575702224642302, 360575701573242157, 360575689596337014, 360575680730723460, 360575674375247880, 360575686890759820]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 9340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 9300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360562198215054103, 360562198688492966⟩, ⟨127087678823349677, 127090683009175191⟩, true⟩

def words05 : List Nat := [360575693671774759, 360575700451352892, 360575714412536755, 360575734133190122, 360575750867101079, 360575767597453496, 360575778550551623, 360575778550663924, 360575778203590608, 360575776752917024]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 9350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 9300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360405584665495874, 360405585139992883⟩, ⟨1593398977023021534, 1593401991118470224⟩, true⟩

def words06 : List Nat := [360575775302515875, 360575769050974439, 360575757193231198, 360575739577506072, 360575721965524789, 360575701394676999, 360575690133607609, 360575675027459740, 360575659924525321, 360575638714285143]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 9360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 9300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360545321328754651, 360545321804314926⟩, ⟨282964889161032472, 282967913224542550⟩, true⟩

def words07 : List Nat := [360575620567585748, 360575613738241498, 360575606910323179, 360575594521188859, 360575576078026928, 360575547972114168, 360575519872174747, 360575503081617089, 360575492175582102, 360575488959242916]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 9370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 9300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360424993018118168, 360424993494750596⟩, ⟨1411171254534183881, 1411174288659844317⟩, true⟩

def words08 : List Nat := [360575485743571528, 360575475161808086, 360575453347557435, 360575432964391161, 360575412585538768, 360575389268047182, 360575366952367787, 360575335472196312, 360575303998709323, 360575278296524808]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 9380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 9300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360492783426638209, 360492783904332803⟩, ⟨774846167388435303, 774849211493095139⟩, true⟩

def words09 : List Nat := [360575262293549219, 360575257558910972, 360575252825268690, 360575241165288163, 360575236485828595, 360575228881205228, 360575224929320488, 360575224929433388, 360575223441559628, 360575214671512920]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 9390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 9300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 9300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk093
