import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk473

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362498751473385074, 362498783655968276⟩, ⟨(-637213310253958201), (-636184849132616057)⟩, true⟩

def state01 : KState := ⟨⟨362504449670630544, 362504481867387163⟩, ⟨(-906850951272798908), (-905821819677233284)⟩, true⟩

def words00 : List Nat := [371285334230411086, 371285334231983571, 371285334192351215, 371285334396756226, 371285334737874627, 371285334784519462, 371285334823178029, 371285334862345055, 371285335346467612, 371285335752959710]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 47300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 47300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362480613314911937, 362480645525862665⟩, ⟨220974914148558416, 222004717339595830⟩, true⟩

def words01 : List Nat := [371285336205279318, 371285336658227060, 371285337025263030, 371285337026836545, 371285336876490874, 371285336864405462, 371285337283029386, 371285337284602695, 371285337185264259, 371285337087936621]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 47310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 47300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483020995127579, 362483053220156991⟩, ⟨107148126482627045, 108178595946892685⟩, true⟩

def words02 : List Nat := [371285337282073229, 371285337416883695, 371285337896052891, 371285338375825786, 371285338785071704, 371285338786644840, 371285338602118384, 371285338604627193, 371285338842782713, 371285338844411099]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 47320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 47300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482027480373805, 362482059719725138⟩, ⟨154180059920921999, 155211207314368209⟩, true⟩

def words03 : List Nat := [371285338797309624, 371285338753208117, 371285338782098039, 371285338783864443, 371285338792094790, 371285338866117662, 371285338946927143, 371285338948500590, 371285338435268388, 371285338367957381]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 47330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 47300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362460876535393817, 362460908788786200⟩, ⟨1155555842723007160, 1156587654891808260⟩, true⟩

def words04 : List Nat := [371285338417315295, 371285338418888806, 371285337943758456, 371285337444859503, 371285336945351405, 371285336472074591, 371285335833067979, 371285335602300972, 371285335371005602, 371285335138414327]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 47340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 47300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362477109123159849, 362477141390789795⟩, ⟨386917840691301956, 387950327080199028⟩, true⟩

def words05 : List Nat := [371285334623625610, 371285334554471581, 371285334858215103, 371285334859789012, 371285334641183332, 371285334217036163, 371285333792284805, 371285333548566517, 371285333080695201, 371285332909520374]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 47350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 47300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471598360960368, 362471630642797535⟩, ⟨647963945827697893, 648997105145151907⟩, true⟩

def words06 : List Nat := [371285332737738680, 371285332567660014, 371285332118290503, 371285332114306504, 371285332241027199, 371285332242612271, 371285331974868004, 371285331694235484, 371285331412979347, 371285331236108601]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 47360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 47300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362444248669563140, 362444280965577230⟩, ⟨1943783621966550694, 1944817452915590738⟩, true⟩

def words07 : List Nat := [371285331052278260, 371285331158295533, 371285331265177255, 371285331266752064, 371285330780512177, 371285330423549454, 371285330065722583, 371285329856409598, 371285329053753518, 371285328189150797]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 47370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 47300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480113354585418, 362480145664711321⟩, ⟨244340866727646692, 245375366366340240⟩, true⟩

def words08 : List Nat := [371285327323897559, 371285326903574278, 371285326282873544, 371285325839502376, 371285325395665285, 371285324910951038, 371285324101859233, 371285323737724490, 371285323450905605, 371285323452564589]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 47380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 47300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362477278821781546, 362477311146274400⟩, ⟨378748245329040551, 379783425889073129⟩, true⟩

def words09 : List Nat := [371285323344486169, 371285323238376336, 371285323417127069, 371285323484052727, 371285323687663365, 371285323891858679, 371285323969021996, 371285323970605253, 371285323621909798, 371285323454837461]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 47390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 47300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 47300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk473
