import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk228

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360547351516151654, 360547354568694220⟩, ⟨751700827314210014, 751747915620455240⟩, true⟩

def state01 : KState := ⟨⟨360594960766016084, 360594963821340084⟩, ⟨(-334070513145901796), (-334023361408666966)⟩, true⟩

def words00 : List Nat := [360580324717637318, 360580324717934092, 360580324386639536, 360580322601362232, 360580320816193504, 360580318540198447, 360580318840859035, 360580319950109708, 360580320096290443, 360580320738555083]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 22800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 22800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360703586689896441, 360703589748014833⟩, ⟨(-2812406465915597320), (-2812359250424717952)⟩, true⟩

def words01 : List Nat := [360580323297679186, 360580325856665074, 360580328351907725, 360580331711108078, 360580333426488871, 360580335141739020, 360580338772777226, 360580343362853632, 360580348763899034, 360580354164542386]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 22810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 22800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360629905279458869, 360629908340390943⟩, ⟨(-1130988672202694074), (-1130941392489479416)⟩, true⟩

def words02 : List Nat := [360580358603219236, 360580361135302705, 360580364663244217, 360580368190965546, 360580370403049444, 360580371351980390, 360580371352248377, 360580370823747951, 360580370828337560, 360580372998422152]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 22820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 22800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578846492280737, 360578849555997126⟩, ⟨35034348921448591, 35081692214543121⟩, true⟩

def words03 : List Nat := [360580375506011895, 360580378013437739, 360580379236190381, 360580380629927758, 360580381535408669, 360580382440890360, 360580384403745907, 360580385598695757, 360580385598959758, 360580385532013525]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 22830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 22800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360564470367332129, 360564473433846791⟩, ⟨363390666785122677, 363438074004523265⟩, true⟩

def words04 : List Nat := [360580385465011796, 360580384701305971, 360580386111614874, 360580387521856674, 360580387522129553, 360580387295680319, 360580385167065044, 360580382603643354, 360580380040353466, 360580378820017668]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 22840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 22800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360594294038936312, 360594297108271790⟩, ⟨(-318305801428367932), (-318258329739288424)⟩, true⟩

def words05 : List Nat := [360580378124236219, 360580376457265558, 360580375032915470, 360580376480791810, 360580376622348528, 360580376763936800, 360580376764201286, 360580375736968165, 360580375046263015, 360580375655590837]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 22850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 22800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360621412329589450, 360621415401718772⟩, ⟨(-938126270736434946), (-938078735166174990)⟩, true⟩

def words06 : List Nat := [360580378173510791, 360580381533319862, 360580383933592495, 360580386333687453, 360580387548580507, 360580390070128797, 360580393150329507, 360580396230316236, 360580397529301733, 360580399323052944]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 22860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 22800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360717057375749368, 360717060450676348⟩, ⟨(-3126112504887190298), (-3126064905320925426)⟩, true⟩

def words07 : List Nat := [360580403023675677, 360580406724061217, 360580411765458267, 360580414908493291, 360580416358380881, 360580417808170294, 360580421163868095, 360580425767433899, 360580431739469397, 360580437711053040]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 22870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 22800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360653769339892273, 360653772417643234⟩, ⟨(-1678148429220938749), (-1678100765028011935)⟩, true⟩

def words08 : List Nat := [360580442475541716, 360580446622320289, 360580450701061986, 360580454779529475, 360580457848316278, 360580459020875765, 360580459226918481, 360580459432973090, 360580460894144341, 360580464097123030]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 22880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 22800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360497866780907689, 360497869861451519⟩, ⟨1891399887717742524, 1891447615853673186⟩, true⟩

def words09 : List Nat := [360580467569185801, 360580471041000325, 360580473266510277, 360580473597021997, 360580473597270941, 360580472988153788, 360580472379004161, 360580471704243675, 360580469433870183, 360580465827209322]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 22890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 22800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 22800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk228
