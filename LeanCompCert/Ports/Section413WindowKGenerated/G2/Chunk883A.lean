import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk883A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360556159670123294, 360556210844741017⟩, ⟨2288569093654512323, 2291620564777113699⟩, true⟩

def state01 : KState := ⟨⟨360579089185110060, 360579140371730456⟩, ⟨263819242037010689, 266871773056071367⟩, true⟩

def words00 : List Nat := [360582163219635799, 360582163055195960, 360582162957787554, 360582162961976127, 360582162963171028, 360582162843733104, 360582162633591693, 360582162529720384, 360582162425459857, 360582162359875129]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 88300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 88300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360556164899731254, 360556216098481384⟩, ⟨2288456069019461975, 2291509671275806869⟩, true⟩

def words01 : List Nat := [360582162326788825, 360582162229712336, 360582162132369379, 360582162194538142, 360582162195605837, 360582162193007436, 360582162190281956, 360582162122301041, 360582161926025503, 360582161633708692]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 88310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 88300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580824006312589, 360580875217046215⟩, ⟨110425186290778361, 113479846988492383⟩, true⟩

def words02 : List Nat := [360582161340973272, 360582161176489406, 360582161021453949, 360582160788968031, 360582160556280770, 360582160290900461, 360582160123816177, 360582160084961814, 360582160045969213, 360582159943039519]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 88320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 88300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360598041513478392, 360598092736234096⟩, ⟨(-1410555879596143217), (-1407500156928224283)⟩, true⟩

def words03 : List Nat := [360582159971400170, 360582160014679807, 360582160054659962, 360582160055933828, 360582160027730238, 360582159889046303, 360582159750121547, 360582159791937305, 360582159973325402, 360582160155021203]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 88330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 88300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574641634133309, 360574692869011925⟩, ⟨656612166583990815, 659668960248098817⟩, true⟩

def words04 : List Nat := [360582160238995672, 360582160240268496, 360582160198150716, 360582160201599030, 360582160202664144, 360582160173766288, 360582160047758684, 360582159820966039, 360582159593931282, 360582159410723845]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 88340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 88300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk883A
