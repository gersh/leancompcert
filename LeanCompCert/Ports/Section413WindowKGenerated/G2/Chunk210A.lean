import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk210A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360460713729112674, 360460716299897477⟩, ⟨2521605170202136481, 2521641701559347847⟩, true⟩

def state01 : KState := ⟨⟨360450931227250706, 360450933800579174⟩, ⟨2727020930877605369, 2727057515664674447⟩, true⟩

def words00 : List Nat := [360580788758644821, 360580785296613025, 360580779576020762, 360580772730101186, 360580765884789400, 360580758470165710, 360580752213400641, 360580745901480384, 360580739590130301, 360580731873671258]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 21000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 21000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360645971622152532, 360645974198030382⟩, ⟨(-1371812115909983792), (-1371775477547706450)⟩, true⟩

def words01 : List Nat := [360580725696265382, 360580721772113728, 360580717848256027, 360580716177201985, 360580715414857376, 360580712775871804, 360580710137085603, 360580710603757099, 360580713708809174, 360580716813626800]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 21010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 21000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585270043152971, 360585272621610107⟩, ⟨(-95863294296583021), (-95826601705054535)⟩, true⟩

def words02 : List Nat := [360580717782588421, 360580717782859307, 360580720030612058, 360580722279904109, 360580723540529076, 360580723540799611, 360580722546602110, 360580720103281998, 360580717660138637, 360580716176281542]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 21020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 21000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360536150900631420, 360536153481635087⟩, ⟨937576544011014226, 937613290169091424⟩, true⟩

def words03 : List Nat := [360580718642477786, 360580721108492970, 360580721977708688, 360580722248740256, 360580722248970654, 360580720921771544, 360580719963748444, 360580719964019203, 360580718968791153, 360580716850939702]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 21030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 21000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360562597122419878, 360562599705983339⟩, ⟨381253987498875177, 381290787527585309⟩, true⟩

def words04 : List Nat := [360580714733228619, 360580715234156018, 360580716712394333, 360580718190542451, 360580718190792357, 360580717530459929, 360580716171362559, 360580715479522601, 360580714787673379, 360580713282587975]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 21040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 21000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk210A
