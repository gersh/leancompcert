import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk670A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360553378903560884, 360553407735059773⟩, ⟨1976145843219160825, 1977450699374235291⟩, true⟩

def state01 : KState := ⟨⟨360576782860621338, 360576811701038883⟩, ⟨407961661050323651, 409267114800703829⟩, true⟩

def words00 : List Nat := [360582921484868520, 360582921079751541, 360582920815803728, 360582920774388438, 360582920732892445, 360582920501843338, 360582920048306450, 360582919724534818, 360582919400495411, 360582919253863846]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 67000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 67000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360574156093963046, 360574184943401560⟩, ⟨583954726813084029, 585260785102985297⟩, true⟩

def words01 : List Nat := [360582919163578423, 360582918900596738, 360582918637437040, 360582918471577339, 360582918465036021, 360582918336618651, 360582918208102035, 360582917951595752, 360582917701467319, 360582917572245234]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 67010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 67000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360582639188637821, 360582668046977066⟩, ⟨15394912700163312, 16701567561921596⟩, true⟩

def words02 : List Nat := [360582917534622853, 360582917634061793, 360582917634918023, 360582917568171538, 360582917501287132, 360582917278829821, 360582917218773221, 360582917270790776, 360582917271633460, 360582917212538187]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 67020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 67000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360601041121121333, 360601069988401572⟩, ⟨(-1218156864166358441), (-1216849609946419977)⟩, true⟩

def words03 : List Nat := [360582917281718768, 360582917354920440, 360582917649923981, 360582917922144262, 360582917996986809, 360582918071900421, 360582918289001946, 360582918617889157, 360582918889421839, 360582919161147408]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 67030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 67000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360599445261088386, 360599474137387968⟩, ⟨(-1111327976464311616), (-1110020117544523486)⟩, true⟩

def words04 : List Nat := [360582919287367355, 360582919288313496, 360582919317756254, 360582919444159865, 360582919444958381, 360582919378558026, 360582919318503818, 360582919147512589, 360582919026416073, 360582919274409869]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 67040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 67000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk670A
