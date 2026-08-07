import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk385

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360562717827081566, 360562726928869264⟩, ⟨748304620881621449, 748541479358128043⟩, true⟩

def state01 : KState := ⟨⟨360617564312385443, 360617573419078541⟩, ⟨(-1363460307453453607), (-1363223260094854513)⟩, true⟩

def words00 : List Nat := [360582169228066356, 360582169845569572, 360582170989347025, 360582172133164666, 360582172617815577, 360582172913146216, 360582173190180375, 360582173467345219, 360582174216771788, 360582175136507462]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 38500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 38500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587277058600460, 360587286170251873⟩, ⟨(-196902308459104256), (-196665070131545158)⟩, true⟩

def words01 : List Nat := [360582175539742224, 360582175943006068, 360582176636144782, 360582177860634195, 360582178915576503, 360582179970548969, 360582180572766100, 360582180573286578, 360582180638237547, 360582180771375117]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 38510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 38500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591975470071416, 360591984586628724⟩, ⟨(-377931256451203181), (-377693829123686707)⟩, true⟩

def words02 : List Nat := [360582180886497914, 360582181281512584, 360582181339100318, 360582181396742011, 360582181397178831, 360582181049469672, 360582181473342557, 360582181910032572, 360582181995144630, 360582182250091295]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 38520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 38500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360595932477718676, 360595941599189859⟩, ⟨(-530489860511376115), (-530252243828172361)⟩, true⟩

def words03 : List Nat := [360582182960224506, 360582183670477059, 360582184280878351, 360582184281399036, 360582184222629795, 360582183522136053, 360582182821579069, 360582182750208583, 360582183107632633, 360582183465155243]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 38530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 38500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574227638442798, 360574236764878694⟩, ⟨306054636455575433, 306292444503512393⟩, true⟩

def words04 : List Nat := [360582183465619561, 360582183403717861, 360582183981357566, 360582184606076950, 360582184843018349, 360582184843539281, 360582184411703605, 360582183644954220, 360582182878151502, 360582182094178397]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 38540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 38500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360544713537239201, 360544722668582457⟩, ⟨1443993191874043605, 1444231189124996761⟩, true⟩

def words05 : List Nat := [360582181972651947, 360582182057319251, 360582182057783392, 360582181751271833, 360582181076469314, 360582179961393996, 360582178846206727, 360582178401870207, 360582177767737777, 360582176796931135]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 38550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 38500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360629529952046038, 360629539088311574⟩, ⟨(-1827072304809601682), (-1826834117731139452)⟩, true⟩

def words06 : List Nat := [360582175826056994, 360582175560047552, 360582175563773001, 360582175567590985, 360582175568075794, 360582174993821106, 360582174316908379, 360582174310569889, 360582174967519402, 360582176196041964]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 38560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 38500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593694794222289, 360593703935449618⟩, ⟨(-444731362446388647), (-444492983966844151)⟩, true⟩

def words07 : List Nat := [360582176912472200, 360582177628919343, 360582178568542383, 360582179846586815, 360582180946043685, 360582182045528108, 360582182508438477, 360582182508959902, 360582182602974408, 360582182902195767]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 38570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 38500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605212724447985, 360605221870585587⟩, ⟨(-889241688750260762), (-889003120808032846)⟩, true⟩

def words08 : List Nat := [360582183590706381, 360582183825462800, 360582183825932018, 360582183711076755, 360582183596130861, 360582183435671256, 360582184002096330, 360582184568595221, 360582184732941277, 360582185330438713]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 38580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 38500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360613414457064085, 360613423608132466⟩, ⟨(-1205844817410330160), (-1205606059164911896)⟩, true⟩

def words09 : List Nat := [360582185691684196, 360582186053061520, 360582187083661771, 360582187813866726, 360582187999105435, 360582188184375021, 360582188569806898, 360582189480397451, 360582190289996891, 360582191099669864]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 38590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 38500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 38500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk385
