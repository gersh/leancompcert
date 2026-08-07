import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk040

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362090449074440462, 362090449258792914⟩, ⟨1552859240842011561, 1552859740884564619⟩, true⟩

def state01 : KState := ⟨⟨362395088449430147, 362395088634745585⟩, ⟨333934637321983682, 333935141221379632⟩, true⟩

def words00 : List Nat := [371278567164610902, 371278532413462338, 371278483049535321, 371278489470525033, 371278489470609293, 371278484536653426, 371278397056929478, 371278371691517871, 371278364230948863, 371278364231060144]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 4000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 4000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362545683621096309, 362545683807394607⟩, ⟨(-270934707725188668), (-270934199879486316)⟩, true⟩

def words01 : List Nat := [371278343469338271, 371278311501979724, 371278309539097645, 371278309539217269, 371278311898143606, 371278314549098107, 371278315538179521, 371278315538289258, 371278287240128548, 371278304001406175]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 4010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 4000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477711570539157, 362477711757800635⟩, ⟨2817741158924056, 2818252881628970⟩, true⟩

def words02 : List Nat := [371278382538363224, 371278382538471229, 371278379037803769, 371278372639531111, 371278366244397514, 371278355962158582, 371278356103392054, 371278386964662790, 371278411076020982, 371278411076133546]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 4020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 4000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362556898849540227, 362556899037785099⟩, ⟨(-316230250165582487), (-316229734474897467)⟩, true⟩

def words03 : List Nat := [371278453810812691, 371278496697758470, 371278584400609981, 371278590552915140, 371278590552999369, 371278586930115860, 371278609282942675, 371278609283062146, 371278624350911290, 371278643721161764]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 4030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 4000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362543212547850722, 362543212737078955⟩, ⟨(-261795521184576840), (-261795001516063270)⟩, true⟩

def words04 : List Nat := [371278663480043431, 371278663480152196, 371278620559492440, 371278616375213257, 371278625639765308, 371278625639876219, 371278599150027437, 371278569799399735, 371278571995838718, 371278587952700762]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 4040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 4000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362344089757982805, 362344089948192759⟩, ⟨546980288415033129, 546980812064593199⟩, true⟩

def words05 : List Nat := [371278664726024900, 371278741461507083, 371278807882781407, 371278807882890386, 371278796862334761, 371278800165485774, 371278864116232518, 371278864116341563, 371278847477526126, 371278814286139704]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 4050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 4000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362451791719726754, 362451791910915449⟩, ⟨109700808558146559, 109701336186467499⟩, true⟩

def words06 : List Nat := [371278795096910947, 371278795097031088, 371278798921608194, 371278818582795182, 371278829024024083, 371278829024133656, 371278780585085695, 371278756038702223, 371278745556056167, 371278745556170110]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 4060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 4000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362550620765686023, 362550620957874515⟩, ⟨(-292740506937531145), (-292739975234948093)⟩, true⟩

def words07 : List Nat := [371278738935361974, 371278724447961773, 371278755652290354, 371278779508726380, 371278818970384264, 371278858412724373, 371278895782441770, 371278895782551547, 371278870963807337, 371278888545418022]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 4070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 4000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362278497965906551, 362278498159076378⟩, ⟨818899665482249746, 818900201193828962⟩, true⟩

def words08 : List Nat := [371278911579573824, 371278911579684187, 371278879644619994, 371278846934277145, 371278814239908884, 371278793287793931, 371278743144978533, 371278736713765950, 371278730285659683, 371278718257167779]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 4080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 4000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362753060664876991, 362753060859043008⟩, ⟨(-1124121260131914267), (-1124120720340855093)⟩, true⟩

def words09 : List Nat := [371278680104473502, 371278690888166335, 371278761343883538, 371278771780375945, 371278773045240098, 371278774309519601, 371278810830165857, 371278818184938836, 371278885073471223, 371278951929430510]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 4090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 4000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 4000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk040
