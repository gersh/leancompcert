import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk571A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360576523988679231, 360576544664042709⟩, ⟨305430947648434761, 306228557078063743⟩, true⟩

def state01 : KState := ⟨⟨360593026459446786, 360593047142322285⟩, ⟨(-636962125373070738), (-636164086969868184)⟩, true⟩

def words00 : List Nat := [360581907592784878, 360581907453189301, 360581907573061283, 360581907693080209, 360581907693821991, 360581907548453161, 360581907578071245, 360581907746718328, 360581907864892264, 360581908060762343]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 57100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 57100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360575727556608415, 360575748247075614⟩, ⟨351031685075894540, 351830157077950588⟩, true⟩

def words01 : List Nat := [360581908102026829, 360581908143382377, 360581908144037543, 360581908236844170, 360581908301674765, 360581908366633128, 360581908367342546, 360581908259201699, 360581907845531053, 360581907738621097]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 57110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 57100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360574176345243273, 360574197043202246⟩, ⟨439654479536894733, 440453379507161481⟩, true⟩

def words02 : List Nat := [360581907797197795, 360581907870722286, 360581907871443085, 360581907706833931, 360581907542101418, 360581907293664643, 360581907197672717, 360581907092962710, 360581906988169107, 360581906712019106]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 57120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 57100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360620609553555778, 360620630259034812⟩, ⟨(-2213338810446421569), (-2212539480819026887)⟩, true⟩

def words03 : List Nat := [360581906749117647, 360581906921401218, 360581907091975407, 360581907445807309, 360581907540267197, 360581907634782473, 360581907830615375, 360581908202913269, 360581908881227154, 360581909559697751]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 57130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 57100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360600484461793968, 360600505174874495⟩, ⟨(-1063470316640193818), (-1062670552626471088)⟩, true⟩

def words04 : List Nat := [360581909998669023, 360581910132529940, 360581910572464237, 360581911012616835, 360581911254746878, 360581911255543544, 360581911192562351, 360581910947825771, 360581910763586807, 360581911089860647]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 57140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 57100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk571A
