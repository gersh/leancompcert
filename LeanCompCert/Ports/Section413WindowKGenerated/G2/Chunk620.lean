import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk620

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360594583905229038, 360594608441663272⟩, ⟨(-744175369211099132), (-743147694263999018)⟩, true⟩

def state01 : KState := ⟨⟨360607540337376305, 360607564882098095⟩, ⟨(-1547662144820962209), (-1546633956005275083)⟩, true⟩

def words00 : List Nat := [360582622438445198, 360582622439315710, 360582622533223832, 360582622710790786, 360582622821706381, 360582623018286123, 360582623019066083, 360582623019622967, 360582623194976799, 360582623598196767]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 62000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 62000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598846951255176, 360598871504178262⟩, ⟨(-1008505992268759089), (-1007477294849060663)⟩, true⟩

def words01 : List Nat := [360582624261053969, 360582624924056919, 360582625388057915, 360582625668717022, 360582625843283517, 360582626018079376, 360582626452533360, 360582626846892269, 360582627109601197, 360582627372434997]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 62010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 62000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599738068058544, 360599762629185258⟩, ⟨(-1063708009470986154), (-1062678803219817418)⟩, true⟩

def words02 : List Nat := [360582627840971816, 360582628438758486, 360582629101097173, 360582629763577840, 360582630201730506, 360582630381111959, 360582630553451578, 360582630726037463, 360582630937115548, 360582631214195659]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 62020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 62000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360581435916582499, 360581460485998273⟩, ⟨71627962271206752, 72657682732104170⟩, true⟩

def words03 : List Nat := [360582631292904221, 360582631371703057, 360582631422942549, 360582631676317602, 360582631809371360, 360582631942565406, 360582631943347979, 360582631924325015, 360582631646409220, 360582631628531028]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 62030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 62000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579842498340269, 360579867075958550⟩, ⟨170397170825067596, 171427400210415944⟩, true⟩

def words04 : List Nat := [360582631610369996, 360582631585536021, 360582631379702178, 360582631043280383, 360582630706727475, 360582630304088971, 360582630035967859, 360582630027690985, 360582630019308580, 360582629806018348]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 62040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 62000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360622787906056348, 360622812491882953⟩, ⟨(-2494643598179959567), (-2493612859427028827)⟩, true⟩

def words05 : List Nat := [360582629762203314, 360582629757462577, 360582630006366027, 360582630298779099, 360582630353355130, 360582630407975752, 360582630722001458, 360582631165095912, 360582631813259045, 360582632461599409]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 62050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 62000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360619406133153678, 360619430727281789⟩, ⟨(-2284759628600344167), (-2283728374615267093)⟩, true⟩

def words06 : List Nat := [360582632959411171, 360582633666015623, 360582634550030118, 360582635434280264, 360582636252008788, 360582636811368990, 360582637189135295, 360582637566982681, 360582637937910965, 360582638531657178]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 62060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 62000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360587148093160343, 360587172695487000⟩, ⟨(-282247785063441310), (-281216022153446968)⟩, true⟩

def words07 : List Nat := [360582639384541473, 360582640237565128, 360582640880144993, 360582641373202358, 360582641714765787, 360582642056561246, 360582642519190610, 360582642723575915, 360582642797321483, 360582642871190461]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 62070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 62000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360618440804594967, 360618465415154364⟩, ⟨(-2225072900801036447), (-2224040626762174251)⟩, true⟩

def words08 : List Nat := [360582643204216322, 360582643670133525, 360582644116375567, 360582644562765869, 360582644789913522, 360582644871427902, 360582645129857401, 360582645388538372, 360582645787457308, 360582646365263685]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 62080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 62000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360611915241649297, 360611939860505230⟩, ⟨(-1819878550443061109), (-1818845761232395473)⟩, true⟩

def words09 : List Nat := [360582646813406135, 360582647261624330, 360582647864308613, 360582648620455007, 360582649210388859, 360582649800440991, 360582650192162239, 360582650405482756, 360582650877836805, 360582651350477495]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 62090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 62000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 62000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk620
