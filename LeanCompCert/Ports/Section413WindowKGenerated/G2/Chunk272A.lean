import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk272A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360653012051342514, 360653016463734094⟩, ⟨(-1910701597854243165), (-1910620418555707215)⟩, true⟩

def state01 : KState := ⟨⟨360615114292078382, 360615118707878408⟩, ⟨(-879717147637538187), (-879635875612037489)⟩, true⟩

def words00 : List Nat := [360582777552538756, 360582780042648710, 360582782737367102, 360582785431989904, 360582787780461382, 360582789308028742, 360582790159389433, 360582791010724355, 360582791038392996, 360582792226837211]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 27200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 27200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584881429632120, 360584885848799795⟩, ⟨(-56703937166817058), (-56622573490471774)⟩, true⟩

def words01 : List Nat := [360582794762014485, 360582797297073743, 360582799046869303, 360582800605872859, 360582801819449386, 360582803033041936, 360582804693971023, 360582805588972147, 360582805665715022, 360582805742503536]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 27210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 27200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360628444100058519, 360628448522608283⟩, ⟨(-1242746980696984476), (-1242665524943637654)⟩, true⟩

def words02 : List Nat := [360582806792055731, 360582808723166574, 360582810618189690, 360582812513137161, 360582813080071060, 360582813080428960, 360582812305183099, 360582812093665747, 360582812623408877, 360582814299665915]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 27220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 27200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360611044949382368, 360611049375340695⟩, ⟨(-768870135795038378), (-768788587209748056)⟩, true⟩

def words03 : List Nat := [360582815135304500, 360582815970921184, 360582817838247078, 360582820681718029, 360582822755945269, 360582824830079512, 360582825863848791, 360582825864206918, 360582826592729734, 360582827629178302]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 27230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 27200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360615650316922731, 360615654746253067⟩, ⟨(-894310715539319782), (-894229075083689140)⟩, true⟩

def words04 : List Nat := [360582830009311957, 360582831545451067, 360582832390272593, 360582833235074171, 360582833735427196, 360582835083376083, 360582836636560032, 360582838189698150, 360582839000007338, 360582840204581801]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 27240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 27200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk272A
