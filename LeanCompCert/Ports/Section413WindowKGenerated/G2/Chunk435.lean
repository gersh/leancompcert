import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk435

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360609483300720017, 360609495036530284⟩, ⟨(-1144276847855185561), (-1143931849231299907)⟩, true⟩

def state01 : KState := ⟨⟨360592612773750782, 360592624515147077⟩, ⟨(-410432092812786301), (-410086851168260139)⟩, true⟩

def words00 : List Nat := [360583199271360417, 360583199659107405, 360583199674785327, 360583199690525964, 360583199691034916, 360583199227158674, 360583199238742914, 360583199451068192, 360583199451597224, 360583199614520379]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 43500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 43500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360605806103291951, 360605817850301983⟩, ⟨(-984583704723450281), (-984238218797286779)⟩, true⟩

def words01 : List Nat := [360583199983796951, 360583200353239956, 360583201076568969, 360583201273658255, 360583201274210893, 360583201016240810, 360583201027176165, 360583201561626156, 360583202081790493, 360583202602058669]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 43510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 43500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589352757876635, 360589364510543225⟩, ⟨(-268581208598681890), (-268235476471697116)⟩, true⟩

def words02 : List Nat := [360583202807915926, 360583202808510121, 360583202892021145, 360583203118082559, 360583203210126468, 360583203319073587, 360583203319606372, 360583203029231042, 360583202738756913, 360583202569019445]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 43520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 43500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360537239808735259, 360537251567004224⟩, ⟨2000240976948863359, 2000586952975661923⟩, true⟩

def words03 : List Nat := [360583203091582708, 360583203614235649, 360583203732009368, 360583203732603555, 360583203324536596, 360583202781550796, 360583202238419553, 360583201593429596, 360583200875112706, 360583199820402839]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 43530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 43500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360565687807307503, 360565699571183779⟩, ⟨761632773093300289, 761978993289871605⟩, true⟩

def words04 : List Nat := [360583198765596400, 360583198238025034, 360583198458144709, 360583198832035920, 360583198832583924, 360583198761784759, 360583198165379990, 360583197555182614, 360583196944841395, 360583196218561274]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 43540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 43500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360573488144117935, 360573499913659486⟩, ⟨421898735893204747, 422245202839258173⟩, true⟩

def words05 : List Nat := [360583195817345518, 360583195153034194, 360583194488639728, 360583194401211734, 360583194401709736, 360583194390607001, 360583194379439918, 360583194102811354, 360583193551549341, 360583193329702628]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 43550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 43500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360555810737937535, 360555822513081130⟩, ⟨1191937931228214778, 1192284642227978626⟩, true⟩

def words06 : List Nat := [360583193107666840, 360583192823598418, 360583192303026049, 360583191455514828, 360583190607945602, 360583189625545565, 360583188958717209, 360583188519777340, 360583188080787586, 360583187320109544]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 43560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 43500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360584891490790337, 360584903271546015⟩, ⟨(-75438645056390152), (-75091689510258578)⟩, true⟩

def words07 : List Nat := [360583186692544099, 360583185882891373, 360583185073101667, 360583184789707433, 360583183981540642, 360583182692488819, 360583181403379564, 360583180640682419, 360583180194071518, 360583180234224470]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 43570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 43500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584092476498375, 360584104262927433⟩, ⟨(-40633622181971643), (-40286419362129829)⟩, true⟩

def words08 : List Nat := [360583180234754465, 360583180034873234, 360583180380141817, 360583180725568595, 360583180785219318, 360583180909060139, 360583180909595548, 360583180695105214, 360583180480519929, 360583180071709931]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 43580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 43500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360557048648665799, 360557060440694334⟩, ⟨1138452580987340835, 1138800027916905315⟩, true⟩

def words09 : List Nat := [360583180619307477, 360583181166993807, 360583181317755167, 360583181318350359, 360583181118317052, 360583180783462412, 360583180638725925, 360583180639321084, 360583180305852441, 360583179707389676]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 43590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 43500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 43500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk435
