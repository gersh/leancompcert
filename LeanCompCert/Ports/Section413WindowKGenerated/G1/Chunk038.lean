import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk038

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362737317187837032, 362737317353385005⟩, ⟨(-997129033465292539), (-997128606780386375)⟩, true⟩

def state01 : KState := ⟨⟨362557909292024290, 362557909458489711⟩, ⟨(-315331640809278310), (-315331210633336494)⟩, true⟩

def words00 : List Nat := [371275040399757735, 371275040399859136, 371275038387047086, 371275071812496878, 371275125807607423, 371275125807709588, 371275121334041911, 371275114236018270, 371275145361095084, 371275167078370757]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 3800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 3800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362229781028122442, 362229781195503754⟩, ⟨937460833281439692, 937461266951685078⟩, true⟩

def words01 : List Nat := [371275236832497811, 371275306550077160, 371275372023909823, 371275372024011658, 371275346361404416, 371275324241151980, 371275312358251966, 371275312358354064, 371275254163955979, 371275189904129850]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 3810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 3800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362397382342087530, 362397382510385212⟩, ⟨298108815243913625, 298109252419329743⟩, true⟩

def words02 : List Nat := [371275129705545713, 371275129705660363, 371275169036946229, 371275222770719203, 371275258673642913, 371275258673745038, 371275203966348262, 371275199762708614, 371275217824227078, 371275217824332818]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 3820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 3800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362421679948555044, 362421680117787177⟩, ⟨205596350601879314, 205596791361013982⟩, true⟩

def words03 : List Nat := [371275197507178130, 371275176638644065, 371275202703153776, 371275217669392646, 371275239002308255, 371275260324143576, 371275281133931898, 371275281134034636, 371275234895299692, 371275220948870775]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 3830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 3800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362422609088119359, 362422609258268281⟩, ⟨201802379182489965, 201802823466856567⟩, true⟩

def words04 : List Nat := [371275237379374574, 371275237379477492, 371275203381908172, 371275153843654050, 371275104331129706, 371275074910357127, 371275016782237278, 371275021371708943, 371275025575943086, 371275025576051881]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 3840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 3800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362687448939854655, 362687449110932071⟩, ⟨(-818140206229519178), (-818139758365640320)⟩, true⟩

def words05 : List Nat := [371275065509195613, 371275119025690759, 371275239627826531, 371275291495349414, 371275332348058265, 371275373179616307, 371275423570012944, 371275440881059123, 371275495805541559, 371275550701616961]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 3850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 3800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362431281483211365, 362431281655220934⟩, ⟨171097323639802796, 171097775106523464⟩, true⟩

def words06 : List Nat := [371275594107508982, 371275594107612119, 371275569982383113, 371275591337835924, 371275632389395520, 371275632389498723, 371275584724678202, 371275536618782840, 371275492966499512, 371275492966617969]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 3860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 3800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362409399392872528, 362409399565816263⟩, ⟨256160984240228028, 256161439326908964⟩, true⟩

def words07 : List Nat := [371275496029330273, 371275510505765686, 371275524596505325, 371275524596609126, 371275477226159898, 371275447430562170, 371275454157242417, 371275454157347652, 371275437575322217, 371275420555333508]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 3870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 3800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362537297394275506, 362537297568148110⟩, ⟨(-240023469275185654), (-240023010579730842)⟩, true⟩

def words08 : List Nat := [371275452731043851, 371275469165185182, 371275517406007193, 371275565622035043, 371275593039654973, 371275593039758871, 371275555115537733, 371275546423840549, 371275594994626932, 371275610852501816]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 3880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 3800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362380937565520009, 362380937740341446⟩, ⟨369824332561542485, 369824794952813101⟩, true⟩

def words09 : List Nat := [371275626243525739, 371275641626678164, 371275694543724414, 371275725148691131, 371275763056439075, 371275800944772259, 371275838549715846, 371275838549820052, 371275788931532479, 371275764610842168]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 3890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 3800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 3800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk038
