import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk626

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360617935869499570, 360617960902282047⟩, ⟨(-2209297725857863525), (-2208239128199928323)⟩, true⟩

def state01 : KState := ⟨⟨360607983936766916, 360608008977931080⟩, ⟨(-1586414947111490860), (-1585355824719024032)⟩, true⟩

def words00 : List Nat := [360582686403402630, 360582686526893522, 360582686905171072, 360582687283704190, 360582687544448270, 360582687689345028, 360582687690128338, 360582687676491072, 360582687848918528, 360582688254340673]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 62600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 62600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567361807527669, 360567386856960942⟩, ⟨957135261495282968, 958194901659219522⟩, true⟩

def words01 : List Nat := [360582688629855883, 360582689005530846, 360582689251549293, 360582689252428336, 360582689244175846, 360582689062846373, 360582688953849199, 360582688954728349, 360582688839500312, 360582688596048442]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 62610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 62600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575992262097682, 360576017319844066⟩, ⟨416696943498624160, 417757104269109558⟩, true⟩

def words02 : List Nat := [360582688352407818, 360582688223342492, 360582688301987018, 360582688380794587, 360582688381606231, 360582688240004487, 360582687899886877, 360582687814817036, 360582687729502891, 360582687559414067]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 62620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 62600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585002536973360, 360585027603098299⟩, ⟨(-147649031625787860), (-146588346065256654)⟩, true⟩

def words03 : List Nat := [360582687453704002, 360582687221009989, 360582687009339180, 360582687239983592, 360582687405656959, 360582687571483865, 360582687608918001, 360582687609797356, 360582687430531668, 360582687468903998]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 62630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 62600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360561571613180180, 360561596687599589⟩, ⟨1320110556398364251, 1321171761564892915⟩, true⟩

def words04 : List Nat := [360582687654844998, 360582687655724387, 360582687587777186, 360582687304398760, 360582687020893014, 360582686498634813, 360582686118617751, 360582685729486637, 360582685340278811, 360582684824256651]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 62640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 62600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk626
