import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk626A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk626B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk626A

def state06 : KState := ⟨⟨360574817564235667, 360574842646954210⟩, ⟨490116047546505016, 491177772695208664⟩, true⟩

def words05 : List Nat := [360582684488371905, 360582684179052165, 360582683869482918, 360582683814671522, 360582683505892693, 360582682981931388, 360582682457824759, 360582681927174988, 360582681548235206, 360582681424047974]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 62650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 62600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360570997317952641, 360571022409045506⟩, ⟨729453243388675112, 730515493313911762⟩, true⟩

def words06 : List Nat := [360582681299733548, 360582681047337649, 360582680860449364, 360582680868542862, 360582680869279276, 360582680778819440, 360582680434445685, 360582679894158835, 360582679353721357, 360582678951144021]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 62660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 62600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360548051809520133, 360548076908911857⟩, ⟨2167510898488766886, 2168573668544967374⟩, true⟩

def words07 : List Nat := [360582678765872251, 360582678570583144, 360582678375207941, 360582678020347233, 360582677411560527, 360582676663939310, 360582675916074886, 360582675371453471, 360582674997768567, 360582674446699748]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 62670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 62600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360577684967726384, 360577710075419887⟩, ⟨310008559139594686, 311071849592912896⟩, true⟩

def words08 : List Nat := [360582673895450676, 360582673453877093, 360582673159740143, 360582673120111495, 360582673080437315, 360582672810574454, 360582672465065952, 360582672374132660, 360582672282949262, 360582672140336029]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 62680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 62600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571599998459027, 360571625114551805⟩, ⟨691549407547534276, 692613224590044056⟩, true⟩

def words09 : List Nat := [360582672061968989, 360582671855619381, 360582671649092579, 360582671746786297, 360582671805617364, 360582671864592574, 360582671865376752, 360582671796313486, 360582671752632491, 360582671577463927]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 62690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 62600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 62600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk626B
