import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk080

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360812137370808983, 360812137711112498⟩, ⟨(-1841124796289099623), (-1841122950316465073)⟩, true⟩

def state01 : KState := ⟨⟨360647190445619385, 360647190786826817⟩, ⟨(-522076171436644804), (-522074318228264720)⟩, true⟩

def words00 : List Nat := [360582042461232385, 360582043390559309, 360582053406947162, 360582063420860002, 360582069411653294, 360582069411748034, 360582059987108484, 360582039153517069, 360582018325107677, 360582021105360301]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 8000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 8000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360478455926097938, 360478456268197540⟩, ⟨830841621553889949, 830843481913157825⟩, true⟩

def words01 : List Nat := [360582044703003866, 360582068294775556, 360582083979854009, 360582084270069458, 360582084270150292, 360582073295533872, 360582066798593572, 360582066798688663, 360582065631101424, 360582052712326363]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 8010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 8000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360543100537289733, 360543100880287175⟩, ⟨312447397073103703, 312449264637407799⟩, true⟩

def words02 : List Nat := [360582039796751729, 360582034463058500, 360582047540806788, 360582060615314081, 360582060615401641, 360582060516967939, 360582045068092374, 360582035946622619, 360582026827398118, 360582011124949368]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 8020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 8000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360510641637065304, 360510641980967304⟩, ⟨573245675088786109, 573247549921265375⟩, true⟩

def words03 : List Nat := [360582006280027858, 360581993583374046, 360581980889863433, 360581980955896162, 360581982186835613, 360581983417485811, 360581983417571483, 360581974517708656, 360581950296560282, 360581941427474925]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 8030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 8000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360342199594153739, 360342199938954212⟩, ⟨1927158518603777816, 1927160400664463394⟩, true⟩

def words04 : List Nat := [360581932560565298, 360581916274981090, 360581884677504784, 360581841063807352, 360581797460936963, 360581749916290685, 360581710930963028, 360581676128644645, 360581641334963485, 360581598746490171]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 8040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 8000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360518033652025478, 360518033997725879⟩, ⟨510477957369247765, 510479846678789627⟩, true⟩

def words05 : List Nat := [360581569011279009, 360581548351864280, 360581527697552298, 360581522337313310, 360581501700405619, 360581467967801578, 360581434243554072, 360581399956335198, 360581376825108872, 360581368966296449]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 8050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 8000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360495167959190688, 360495168305799311⟩, ⟨693669175003722294, 693671071638255540⟩, true⟩

def words06 : List Nat := [360581361109419722, 360581345492414212, 360581323223121506, 360581302952701611, 360581282687280975, 360581258523049350, 360581227141726252, 360581188034061827, 360581148936072641, 360581125068084102]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 8060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 8000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360309179166304664, 360309179513814677⟩, ⟨2195411363254821639, 2195413267168079981⟩, true⟩

def words07 : List Nat := [360581114418086979, 360581103232112135, 360581092048899356, 360581069611048375, 360581045590023832, 360581010547314540, 360580975513254901, 360580948648589353, 360580922708067545, 360580889076583004]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 8070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 8000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360685445496211530, 360685445844623929⟩, ⟨(-846758883146735405), (-846756971937721023)⟩, true⟩

def words08 : List Nat := [360580855453400687, 360580837007634592, 360580826404326018, 360580824361303481, 360580822318780740, 360580804370515712, 360580782809004221, 360580776399510632, 360580778728092607, 360580791664431404]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 8080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 8000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360533951501547717, 360533951850873986⟩, ⟨380324018758499760, 380325937365107636⟩, true⟩

def words09 : List Nat := [360580794721017286, 360580797776859271, 360580815963683671, 360580844231082880, 360580868647355214, 360580893057612907, 360580909811661424, 360580911467596004, 360580911467675289, 360580905670301778]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 8090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 8000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 8000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk080
