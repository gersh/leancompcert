import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk715A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362477349104156191, 362477425099236969⟩, ⟨555390062103800167, 559059658329574019⟩, true⟩

def state01 : KState := ⟨⟨362487849325779217, 362487925342762357⟩, ⟨(-195373081836239883), (-191701919479530349)⟩, true⟩

def words00 : List Nat := [371285244069776292, 371285244072484805, 371285244237302211, 371285244419277708, 371285244541482598, 371285244543934038, 371285244405294938, 371285244407020727, 371285244569430595, 371285244609455880]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 71500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 71500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477253390193031, 362477329429573911⟩, ⟨562444684940458490, 566117449070795346⟩, true⟩

def words01 : List Nat := [371285244617758709, 371285244626945258, 371285244763985973, 371285244825064802, 371285244944318953, 371285245064492423, 371285245186124311, 371285245188576120, 371285245049607878, 371285244942004991]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 71510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 71500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483168895043540, 362483244956256234⟩, ⟨139353810885567709, 143028136541238199⟩, true⟩

def words02 : List Nat := [371285244874467412, 371285244876935947, 371285244744860017, 371285244613300821, 371285244480830380, 371285244410663215, 371285244359915665, 371285244434031530, 371285244508258114, 371285244510800359]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 71520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 71500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495787836327083, 362495863919719113⟩, ⟨(-763350430338887202), (-759674518083679584)⟩, true⟩

def words03 : List Nat := [371285244632600057, 371285244783620988, 371285244952892613, 371285244955345978, 371285244900748615, 371285244825579507, 371285244866737148, 371285244889027699, 371285245039134323, 371285245190345975]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 71530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 71500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480438069833039, 362480514175350428⟩, ⟨334795243576645104, 338472738792307300⟩, true⟩

def words04 : List Nat := [371285245340302739, 371285245342755554, 371285245266707109, 371285245304155530, 371285245365924535, 371285245368377713, 371285245195135013, 371285244982528746, 371285244768950560, 371285244751713703]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 71540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 71500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk715A
