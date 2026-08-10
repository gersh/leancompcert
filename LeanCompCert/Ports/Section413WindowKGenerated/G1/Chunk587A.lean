import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk587A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362502587417749590, 362502637850973650⟩, ⟨(-1035560242475294909), (-1033560484044322525)⟩, true⟩

def state01 : KState := ⟨⟨362483903340578361, 362483953791715688⟩, ⟨61281737938744353, 63282547969939235⟩, true⟩

def words00 : List Nat := [371285030915340255, 371285030945926541, 371285031219619967, 371285031494357526, 371285031829448799, 371285031831432235, 371285031809871819, 371285031725571694, 371285031673079523, 371285031675346585]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 58700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 58700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487751785590112, 362487802254611829⟩, ⟨(-164617331606939625), (-162615471493063427)⟩, true⟩

def words01 : List Nat := [371285031930372742, 371285032204573913, 371285032477136691, 371285032479122013, 371285032456660779, 371285032490584412, 371285032774108681, 371285032866657857, 371285032915306426, 371285032964724173]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 58710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 58700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487112544488979, 362487163031277513⟩, ⟨(-127042479966497335), (-125039576492288965)⟩, true⟩

def words02 : List Nat := [371285033204887457, 371285033301449429, 371285033516235844, 371285033731780846, 371285033895429153, 371285033897413346, 371285033739940736, 371285033808027041, 371285033971185287, 371285034009525929]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 58720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 58700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491843293062631, 362491893797902434⟩, ⟨(-404871629416296711), (-402867665698485003)⟩, true⟩

def words03 : List Nat := [371285034046349331, 371285034083823267, 371285034410659703, 371285034630616879, 371285034880166343, 371285035130489006, 371285035326710091, 371285035328695453, 371285035306078998, 371285035425288783]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 58730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 58700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487145206604689, 362487195729102351⟩, ⟨(-128840802982918851), (-126835801950154179)⟩, true⟩

def words04 : List Nat := [371285035833483633, 371285035930722528, 371285036005638020, 371285036081261984, 371285036229349724, 371285036233916619, 371285036429217051, 371285036625298338, 371285036819777236, 371285036858581847]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 58740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 58700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk587A
