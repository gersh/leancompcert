import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk532A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360573398116410410, 360573415961595366⟩, ⟨453738322802005041, 454379778343412953⟩, true⟩

def state01 : KState := ⟨⟨360596550801752821, 360596568653895990⟩, ⟨(-778017853297304852), (-777376027543699142)⟩, true⟩

def words00 : List Nat := [360581956966942858, 360581957337170565, 360581957976221096, 360581958615389126, 360581958953014809, 360581959092936543, 360581959093547443, 360581959050147663, 360581959067948067, 360581959343273305]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 53200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 53200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360611343046983317, 360611360906148519⟩, ⟨(-1565213643632754965), (-1564571444202563749)⟩, true⟩

def words01 : List Nat := [360581959441653855, 360581959540111563, 360581959908079131, 360581960545810797, 360581961016812291, 360581961487915999, 360581961769983383, 360581962166585521, 360581962719583592, 360581963272804491]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 53210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 53200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360597780125249970, 360597797991374973⟩, ⟨(-843311827010294972), (-842669257144015500)⟩, true⟩

def words02 : List Nat := [360581963817546979, 360581964435696325, 360581964857839769, 360581965280048024, 360581965609903768, 360581966116076281, 360581966589330011, 360581967062718070, 360581967270018339, 360581967568179016]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 53220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 53200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360651164807050025, 360651182680138626⟩, ⟨(-3685282811070604058), (-3684639870497508218)⟩, true⟩

def words03 : List Nat := [360581968218316214, 360581968868645469, 360581969870875606, 360581970655161551, 360581971116733741, 360581971578324753, 360581972318314198, 360581973267053715, 360581974567601931, 360581975868273757]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 53230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 53200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360636466196106589, 360636484076232671⟩, ⟨(-2902719355502481588), (-2902076040219820574)⟩, true⟩

def words04 : List Nat := [360581976992113580, 360581978125048774, 360581979457379031, 360581980789886659, 360581981934689827, 360581982834301497, 360581983557208448, 360581984280172493, 360581984994822123, 360581986019102856]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 53240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 53200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk532A
