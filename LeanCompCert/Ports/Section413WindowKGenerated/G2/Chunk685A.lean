import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk685A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360572237741269520, 360572267931256878⟩, ⟨722907065095996435, 724303962840568009⟩, true⟩

def state01 : KState := ⟨⟨360608229855367860, 360608260054510983⟩, ⟨(-1742693543989969939), (-1741296019031280607)⟩, true⟩

def words00 : List Nat := [360582841616536579, 360582841845351894, 360582842225620711, 360582842606063793, 360582842805191650, 360582842806160045, 360582842990539270, 360582843189765383, 360582843384123101, 360582843756120487]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 68500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 68500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591527764857462, 360591557973214684⟩, ⟨(-598302224457204764), (-596904068194164578)⟩, true⟩

def words01 : List Nat := [360582843989990068, 360582844223958225, 360582844625778340, 360582845160369467, 360582845608391475, 360582846056575176, 360582846364428325, 360582846459650526, 360582846587577113, 360582846715816308]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 68510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 68500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360588042713796502, 360588072931292677⟩, ⟨(-359540703352344333), (-358141920844527775)⟩, true⟩

def words02 : List Nat := [360582847056340505, 360582847184334337, 360582847185216489, 360582847136776011, 360582847088179385, 360582847003256956, 360582847004042994, 360582847000693681, 360582846997239002, 360582846947127197]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 68520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 68500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603581584343846, 360603611810972316⟩, ⟨(-1424521000697638783), (-1423121592306796093)⟩, true⟩

def words03 : List Nat := [360582847236727487, 360582847526603605, 360582847909639673, 360582848080212777, 360582848081114583, 360582848069841179, 360582848058391570, 360582848133141630, 360582848436867414, 360582848740805456]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 68530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 68500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587616617583797, 360587646853440877⟩, ⟨(-330296738639472283), (-328896697673957577)⟩, true⟩

def words04 : List Nat := [360582848871288028, 360582848872257452, 360582849081802895, 360582849293518877, 360582849451260070, 360582849452229166, 360582849397465963, 360582849225479438, 360582849053316059, 360582849013910105]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 68540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 68500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk685A
