import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk026

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362500810993940799, 362500811068355540⟩, ⟨(-63977366244301390), (-63977234931708816)⟩, true⟩

def state01 : KState := ⟨⟨362053214690188836, 362053214765209513⟩, ⟨1100312016788621198, 1100312149679758438⟩, true⟩

def words00 : List Nat := [371276213900035786, 371276205327686020, 371276002044654470, 371275899156634924, 371275796347574979, 371275737373073315, 371275484457166389, 371275204552567397, 371274924862509159, 371274790301485283]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 2600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 2600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361965019438384618, 361965019514011936⟩, ⟨1330875560869993955, 1330875695347648605⟩, true⟩

def words01 : List Nat := [371274628840200485, 371274525956327304, 371274423151180240, 371274309887741901, 371274003797677654, 371273741906662259, 371273480215758053, 371273362678732588, 371273181291465583, 371272987336663711]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 2610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 2600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362256050440793326, 362256050517027249⟩, ⟨568873795170645553, 568873931240705777⟩, true⟩

def words02 : List Nat := [371272793529833529, 371272743440836524, 371272652540865006, 371272659212366339, 371272659212419689, 371272629975147070, 371272467989785536, 371272406228737404, 371272352391953469, 371272352392023716]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 2620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 2600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362013240625696356, 362013240702551481⟩, ⟨1210563160099585262, 1210563297806549806⟩, true⟩

def words03 : List Nat := [371272270179275297, 371272187740588736, 371272165110087959, 371272165110162735, 371272153679075956, 371272151709409253, 371272150139270081, 371272150139338282, 371271961163931358, 371271787406266084]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 2630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 2600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361843397668643746, 361843397746106644⟩, ⟨1659843266497568742, 1659843405812242224⟩, true⟩

def words04 : List Nat := [371271613780146958, 371271540712665221, 371271278911272004, 371271016864836029, 371270755016519688, 371270511754297216, 371270216625237237, 371270062282917946, 371269908057104062, 371269753748299943]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 2640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 2600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362152442291634009, 362152442369716053⟩, ⟨838214608007214607, 838214748965764815⟩, true⟩

def words05 : List Nat := [371269517476750409, 371269350948446432, 371269184545648264, 371269075694584785, 371268780001680918, 371268452374735215, 371268124994375316, 371267937133496819, 371267679206406312, 371267560696394912]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 2650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 2600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨361879339012386602, 361879339091088782⟩, ⟨1565876662330397078, 1565876804941709526⟩, true⟩

def words06 : List Nat := [371267442275429120, 371267324084684720, 371267078975538248, 371266972882314510, 371266866868675948, 371266770155884379, 371266531719594964, 371266263541840066, 371265995565015524, 371265809804550097]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 2660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 2600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨361986879707157670, 361986879786482827⟩, ⟨1279607798598422208, 1279607942876319770⟩, true⟩

def words07 : List Nat := [371265590234880387, 371265509008752801, 371265427843377329, 371265319988556569, 371265100188993948, 371264918567417485, 371264737081496889, 371264693456592872, 371264523662058286, 371264345436809812]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 2670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 2600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362418220781554386, 362418220861502068⟩, ⟨121520885916266538, 121521031865700416⟩, true⟩

def words08 : List Nat := [371264167344485420, 371264044828874641, 371263854186517975, 371263800945668666, 371263747744455964, 371263672599681439, 371263466230430864, 371263397097185375, 371263395966212848, 371263395966284857]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 2680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 2600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362527448254648302, 362527448335230024⟩, ⟨(-172793142380337695), (-172792994722105863)⟩, true⟩

def words09 : List Nat := [371263379178859130, 371263351292925257, 371263432317098786, 371263473332871730, 371263497680808255, 371263522010715206, 371263540004555062, 371263540004625097, 371263450929691299, 371263474623744610]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 2690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 2600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 2600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk026
