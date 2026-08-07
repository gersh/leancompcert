import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk791

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360581207227683764, 360581247945009634⟩, ⟨73395203784047539, 75570453860393303⟩, true⟩

def state01 : KState := ⟨⟨360566337790555996, 360566378518650596⟩, ⟨1249515318001765816, 1251691419937413594⟩, true⟩

def words00 : List Nat := [360582203312641600, 360582203154888464, 360582202837428775, 360582202679841968, 360582202521964124, 360582202275621492, 360582201937425877, 360582201476560393, 360582201015490190, 360582200682977956]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 79100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 79100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360573362700537172, 360573403439279403⟩, ⟨693783483120316692, 695960427442418356⟩, true⟩

def words01 : List Nat := [360582200483892288, 360582200444544201, 360582200405064541, 360582200285840117, 360582200170902950, 360582200016578966, 360582199861924683, 360582199820690953, 360582199813534516, 360582199703529181]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 79110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 79100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360579074141733029, 360579114891154931⟩, ⟨241804660935210661, 243982450285415091⟩, true⟩

def words02 : List Nat := [360582199593284366, 360582199446265244, 360582199378713671, 360582199336161759, 360582199293524456, 360582199112625543, 360582198772123343, 360582198545591540, 360582198318700405, 360582198202797613]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 79120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 79100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574818280785491, 360574859040969654⟩, ⟨578594376425580955, 580773017446260387⟩, true⟩

def words03 : List Nat := [360582198164845173, 360582198025631739, 360582197905274371, 360582198045503426, 360582198046471206, 360582198036995867, 360582198027408132, 360582197935771850, 360582197684563585, 360582197593123385]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 79130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 79100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576477387623135, 360576518158472354⟩, ⟨447283510727216292, 449462995833921084⟩, true⟩

def words04 : List Nat := [360582197501310756, 360582197497002502, 360582197497003512, 360582197373686127, 360582197250188615, 360582197021158591, 360582196881616157, 360582196892197791, 360582196893223027, 360582196781287691]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 79140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 79100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360609351199718607, 360609391981241068⟩, ⟨(-2154853727577449441), (-2152673397629781355)⟩, true⟩

def words05 : List Nat := [360582196798060452, 360582196886910473, 360582197134763902, 360582197314175939, 360582197359043437, 360582197404015211, 360582197496163012, 360582197681632883, 360582198026083120, 360582198370780996]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 79150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 79100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360581813602293859, 360581854394607542⟩, ⟨25039083595359957, 27220267826994489⟩, true⟩

def words06 : List Nat := [360582198635530071, 360582198741135131, 360582198802876172, 360582198864944095, 360582198865890911, 360582198856677281, 360582198773030735, 360582198568998678, 360582198364757742, 360582198215092916]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 79160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 79100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567408324123160, 360567449127079135⟩, ⟨1165600177414458346, 1167782204250522578⟩, true⟩

def words07 : List Nat := [360582198301773574, 360582198393010976, 360582198394030620, 360582198389878285, 360582198291506650, 360582198151417375, 360582198011015580, 360582197866865412, 360582197761331501, 360582197576236126]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 79170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 79100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360590344160974011, 360590384974607081⟩, ⟨(-650521519077206921), (-648338646775848525)⟩, true⟩

def words08 : List Nat := [360582197390888286, 360582197431183443, 360582197545607855, 360582197660261835, 360582197661305381, 360582197639435902, 360582197680746206, 360582197781790763, 360582197845682625, 360582197950238456]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 79180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 79100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360595973627472661, 360596014451910444⟩, ⟨(-1096371279028645886), (-1094187551049628058)⟩, true⟩

def words09 : List Nat := [360582197951274780, 360582197929815364, 360582198044732094, 360582198276608385, 360582198440059759, 360582198603696623, 360582198687499682, 360582198775859341, 360582198951215326, 360582199126964426]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 79190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 79100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 79100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk791
