import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk475A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360539355257117088, 360539369352153313⟩, ⟨2060779159042945069, 2061231577386769921⟩, true⟩

def state01 : KState := ⟨⟨360569379355414699, 360569393456623801⟩, ⟨634648617242148900, 635101328827210702⟩, true⟩

def words00 : List Nat := [360582762788132999, 360582762317028574, 360582762448795833, 360582762670703103, 360582762671305280, 360582762512209135, 360582761910732737, 360582761751034295, 360582761591163542, 360582761196653842]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 47500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 47500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360549526110715963, 360549540218153281⟩, ⟨1578043958880199355, 1578496966398811929⟩, true⟩

def words01 : List Nat := [360582760915880180, 360582760410389999, 360582759904796026, 360582759998834162, 360582759999385203, 360582759793411532, 360582759587364061, 360582759117355992, 360582758445186666, 360582757746907465]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 47510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 47500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360566154899066161, 360566169012660873⟩, ⟨787655956710661423, 788109256859744269⟩, true⟩

def words02 : List Nat := [360582757048428514, 360582756791474292, 360582756092563395, 360582755055082009, 360582754017538315, 360582752864423733, 360582751951872829, 360582751480754251, 360582751009586439, 360582750314088598]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 47520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 47500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360570866298436300, 360570880418195874⟩, ⟨563596531984640060, 564050125180400580⟩, true⟩

def words03 : List Nat := [360582749965768810, 360582749500767647, 360582749035592664, 360582749011751732, 360582748546139955, 360582747700527569, 360582746854834824, 360582745999122004, 360582745415209102, 360582745166306527]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 47530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 47500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360555277828379043, 360555291954365354⟩, ⟨1304643253785314975, 1305097143030508615⟩, true⟩

def words04 : List Nat := [360582744917323935, 360582744329913579, 360582743677816879, 360582743466938705, 360582743255884320, 360582742826427214, 360582741955421717, 360582740850574893, 360582739745650841, 360582738792283977]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 47540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 47500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk475A
