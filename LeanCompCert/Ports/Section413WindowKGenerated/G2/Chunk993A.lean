import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk993A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578113000465711, 360578178311531839⟩, ⟨417553494068823075, 421932597027897365⟩, true⟩

def state01 : KState := ⟨⟨360584853606531265, 360584918931209709⟩, ⟨(-251782827087575064), (-247402372358068178)⟩, true⟩

def words00 : List Nat := [360582427384191850, 360582427464651953, 360582427487218096, 360582427509941397, 360582427511149433, 360582427556303370, 360582427635639673, 360582427715256527, 360582427716621076, 360582427743200747]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 99300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 99300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360605976422395407, 360606041760700172⟩, ⟨(-2349599814517959457), (-2345218006489907285)⟩, true⟩

def words01 : List Nat := [360582427838995276, 360582427935211728, 360582428075468962, 360582428233782120, 360582428305372128, 360582428377085845, 360582428549821611, 360582428773533931, 360582429012455429, 360582429251699157]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 99310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 99300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591352750300843, 360591418102372234⟩, ⟨(-897208694026641164), (-892825518633756270)⟩, true⟩

def words02 : List Nat := [360582429439975377, 360582429559290523, 360582429674757767, 360582429790642495, 360582429854226108, 360582429855670075, 360582429818275351, 360582429729601464, 360582429640652526, 360582429714873531]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 99320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 99300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360557529183951518, 360557594549605530⟩, ⟨2462701943765612375, 2467086468390314231⟩, true⟩

def words03 : List Nat := [360582429841182546, 360582429967766000, 360582430030828437, 360582430032272591, 360582429994193804, 360582429930844655, 360582429867094587, 360582429770296507, 360582429572304186, 360582429323799111]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 99330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 99300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580340504059531, 360580405883344381⟩, ⟨196471348304470913, 200857227084236201⟩, true⟩

def words04 : List Nat := [360582429074979134, 360582428839183230, 360582428654009786, 360582428530233616, 360582428406323009, 360582428187571497, 360582427938415708, 360582427790949595, 360582427643057711, 360582427596752376]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 99340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 99300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk993A
