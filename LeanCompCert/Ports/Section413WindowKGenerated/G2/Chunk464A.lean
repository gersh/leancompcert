import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk464A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360605665074736713, 360605678498530475⟩, ⟨(-1050812697799003164), (-1050391795818071740)⟩, true⟩

def state01 : KState := ⟨⟨360557578063723439, 360557591493588843⟩, ⟨1180483629956108953, 1180904813690436097⟩, true⟩

def words00 : List Nat := [360583041488969326, 360583041489606011, 360583041282724474, 360583041055969635, 360583040829049624, 360583040485043882, 360583039677409636, 360583038609003646, 360583037540525298, 360583036544519471]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 46400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 46400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360512498208129131, 360512511643984757⟩, ⟨3273041783845767888, 3273463245617080602⟩, true⟩

def words01 : List Nat := [360583035996779601, 360583035912144604, 360583035827449227, 360583035498390152, 360583034961734725, 360583034308208702, 360583033654534235, 360583032830703448, 360583031543483047, 360583030024976078]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 46410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 46400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360535280833627872, 360535294275490309⟩, ⟨2215390798009876571, 2215812538647612657⟩, true⟩

def words02 : List Nat := [360583028506385981, 360583027312073265, 360583026353741881, 360583025532224351, 360583024710682110, 360583023494765663, 360583021940040799, 360583020543317852, 360583019146468614, 360583018000208113]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 46420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 46400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360543750815217883, 360543764263162599⟩, ⟨1821964917202972084, 1822386940268924504⟩, true⟩

def words03 : List Nat := [360583016972952819, 360583015482430800, 360583013991851092, 360583012808525479, 360583011893954135, 360583010748724986, 360583009603471794, 360583008165857367, 360583006858958752, 360583006014675712]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 46430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 46400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360559898292854954, 360559911746796380⟩, ⟨1072020356613533643, 1072442658197272221⟩, true⟩

def words04 : List Nat := [360583005170210129, 360583004788227752, 360583004339255203, 360583003636214367, 360583002933107341, 360583001913776842, 360583001126650334, 360583000801930118, 360583000477162190, 360582999855691908]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 46440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 46400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk464A
