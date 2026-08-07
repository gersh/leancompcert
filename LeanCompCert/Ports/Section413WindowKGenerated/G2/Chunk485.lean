import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk485

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360590237632477830, 360590252352429016⟩, ⟨(-391185811237412294), (-390703395895414856)⟩, true⟩

def state01 : KState := ⟨⟨360541940677842776, 360541955404169903⟩, ⟨1951188880252577135, 1951671604855781001⟩, true⟩

def words00 : List Nat := [360582196779003536, 360582196650813524, 360582196097178715, 360582195291811883, 360582194486301035, 360582193514287489, 360582192246620352, 360582190638831802, 360582189030981529, 360582187760485215]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 48500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 48500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360497190105417043, 360497204838025562⟩, ⟨4122364547573985493, 4122847576919306003⟩, true⟩

def words01 : List Nat := [360582186931680117, 360582186433169278, 360582185934606057, 360582185180360887, 360582184121055826, 360582182878884517, 360582181636575003, 360582180241851987, 360582178715132963, 360582176964507824]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 48510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 48500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360542664915648475, 360542679654560033⟩, ⟨1915667061338535977, 1916150396538995835⟩, true⟩

def words02 : List Nat := [360582175213807192, 360582173512620316, 360582172026229288, 360582170963369564, 360582169900490616, 360582168480364677, 360582166882857910, 360582165708897901, 360582164534786212, 360582163487169533]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 48520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 48500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360555853802855378, 360555868548132235⟩, ⟨1275468320649367020, 1275951964790629304⟩, true⟩

def words03 : List Nat := [360582162674195206, 360582161532309138, 360582160390337670, 360582159671795478, 360582159167813764, 360582158404157630, 360582157640465434, 360582156661352711, 360582155697183786, 360582155156389150]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 48530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 48500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360560150010428969, 360560164761997770⟩, ⟨1066915648010218317, 1067399597592846735⟩, true⟩

def words04 : List Nat := [360582154615395228, 360582154497650359, 360582154260321954, 360582153697144222, 360582153133890957, 360582152233553874, 360582151607426175, 360582151253877802, 360582150900270762, 360582150335583617]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 48540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 48500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360586377399460101, 360586392157347076⟩, ⟨(-206537935837440196), (-206053679476503738)⟩, true⟩

def words05 : List Nat := [360582149883289572, 360582149719330509, 360582149587890758, 360582149588563717, 360582149562767469, 360582149176089174, 360582148789298762, 360582148788666082, 360582148876600048, 360582148964672368]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 48550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 48500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360577315142211667, 360577329906463110⟩, ⟨233413653840953216, 233898219292268416⟩, true⟩

def words06 : List Nat := [360582148965267817, 360582148842286135, 360582148295143477, 360582148170863466, 360582148046406856, 360582147642771361, 360582147253800459, 360582146653976238, 360582146054046967, 360582145599674810]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 48560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 48500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360543960827408230, 360543975597962545⟩, ⟨1853694879991882280, 1854179751605129550⟩, true⟩

def words07 : List Nat := [360582145824422097, 360582146148431666, 360582146149043703, 360582146138639157, 360582145835421041, 360582145309179281, 360582144782757643, 360582144510822582, 360582143936491570, 360582143151515554]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 48570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 48500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360553249416395604, 360553264193259533⟩, ⟨1402346341896034165, 1402831520061874025⟩, true⟩

def words08 : List Nat := [360582142366411326, 360582141514623593, 360582140875195807, 360582140421424060, 360582139967619105, 360582139125281954, 360582138150445317, 360582136952883577, 360582135755175085, 360582134979842408]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 48580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 48500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360572665794269996, 360572680577510355⟩, ⟨458808808668464591, 459294296695742179⟩, true⟩

def words09 : List Nat := [360582134386284661, 360582133577993648, 360582132769607771, 360582132383590150, 360582132349611667, 360582132210138968, 360582132070598915, 360582131662514206, 360582131271129542, 360582131077442367]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 48590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 48500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 48500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk485
