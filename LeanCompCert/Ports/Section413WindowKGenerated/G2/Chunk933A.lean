import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk933A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582974367106601, 360583031746654730⟩, ⟨(-95722685995129322), (-92107652820280530)⟩, true⟩

def state01 : KState := ⟨⟨360591904297169030, 360591961689450196⟩, ⟨(-928985210842153690), (-925368989610626460)⟩, true⟩

def words00 : List Nat := [360582044582808701, 360582044611041473, 360582044612277036, 360582044550816456, 360582044489136746, 360582044398892325, 360582044445944853, 360582044527679524, 360582044540993458, 360582044648698188]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 93300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 93300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360603090654170396, 360603148059195633⟩, ⟨(-1972887308837187467), (-1969269898392228551)⟩, true⟩

def words01 : List Nat := [360582044810356491, 360582044972421992, 360582045098197920, 360582045243208757, 360582045290613560, 360582045338123024, 360582045382776807, 360582045495615059, 360582045722838060, 360582045950362764]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 93310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 93300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360603959465433930, 360604016883339845⟩, ⟨(-2054059807686823826), (-2050441195156377496)⟩, true⟩

def words02 : List Nat := [360582046120661721, 360582046228917839, 360582046451688160, 360582046674886790, 360582046868509140, 360582046947827470, 360582046955066922, 360582046962450917, 360582047084338953, 360582047321295547]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 93320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 93300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360591564929609099, 360591622360249239⟩, ⟨(-897251471218506634), (-893631670138602672)⟩, true⟩

def words03 : List Nat := [360582047533268677, 360582047745477001, 360582047890354800, 360582047982363946, 360582048000319878, 360582048018626085, 360582048151289738, 360582048313871938, 360582048417659658, 360582048521634498]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 93330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 93300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360612153998078250, 360612211441465243⟩, ⟨(-2819123087987366981), (-2815502097053776157)⟩, true⟩

def words04 : List Nat := [360582048695197739, 360582048937492776, 360582049272066953, 360582049606893001, 360582049831910774, 360582050039093045, 360582050238306892, 360582050437921992, 360582050732008580, 360582051056498250]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 93340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 93300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk933A
