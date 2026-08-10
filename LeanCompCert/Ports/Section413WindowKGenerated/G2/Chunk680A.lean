import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk680A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360609644582518554, 360609674316013074⟩, ⟨(-1827610280023538349), (-1826244538029301089)⟩, true⟩

def state01 : KState := ⟨⟨360597555601431410, 360597585344071412⟩, ⟨(-1005610919118386040), (-1004244555185416762)⟩, true⟩

def words00 : List Nat := [360582818437707202, 360582818678202446, 360582818982041722, 360582819286160115, 360582819404345104, 360582819405306607, 360582819402112132, 360582819290824415, 360582819212183095, 360582819430392957]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 68000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 68000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360559627744220628, 360559657495927526⟩, ⟨1574118899688411255, 1575485880304936193⟩, true⟩

def words01 : List Nat := [360582819750421191, 360582820070639986, 360582820220290102, 360582820240548282, 360582820241352796, 360582820165862683, 360582820090089951, 360582820087512580, 360582819933077145, 360582819593550357]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 68010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 68000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360602854829668166, 360602884590444976⟩, ⟨(-1366365301484597805), (-1364997703886700435)⟩, true⟩

def words02 : List Nat := [360582819253813649, 360582819088206867, 360582819187456696, 360582819345581009, 360582819346468521, 360582819349899320, 360582819527259950, 360582819704897204, 360582819945853118, 360582820241782063]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 68020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 68000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583161092748201, 360583190862702226⟩, ⟨(-26486616839945912), (-25118394872745800)⟩, true⟩

def words03 : List Nat := [360582820429043066, 360582820616395474, 360582820798763909, 360582821174823748, 360582821410097204, 360582821645515331, 360582821772758955, 360582821773720471, 360582821690574668, 360582821697127459]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 68030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 68000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585257656701256, 360585287435703614⟩, ⟨(-169121579857230105), (-167752742195176821)⟩, true⟩

def words04 : List Nat := [360582821919046923, 360582822079379046, 360582822098585774, 360582822117896480, 360582822118701873, 360582822139948749, 360582822227764613, 360582822315748573, 360582822316613310, 360582822332439957]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 68040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 68000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk680A
