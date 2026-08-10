import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk791A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk791A
