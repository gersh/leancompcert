import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk956A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360604463811260126, 360604524168539703⟩, ⟨(-2138510310483817627), (-2134614015916433979)⟩, true⟩

def state01 : KState := ⟨⟨360612611534181925, 360612671904657169⟩, ⟨(-2917558225456352810), (-2913660669316943194)⟩, true⟩

def words00 : List Nat := [360582195956491107, 360582196077142666, 360582196306967070, 360582196537195107, 360582196739112952, 360582196943885737, 360582197093240983, 360582197242739249, 360582197468714392, 360582197789029083]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 95600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 95600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360586870432777965, 360586930816323165⟩, ⟨(-456301858128907247), (-452403052304940379)⟩, true⟩

def words01 : List Nat := [360582198160605552, 360582198532448838, 360582198807057603, 360582198972724684, 360582199078080879, 360582199183811596, 360582199398530326, 360582199504450274, 360582199555165331, 360582199606104647]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 95610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 95600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360597486427305394, 360597546823927408⟩, ⟨(-1471446098309497316), (-1467546042015841252)⟩, true⟩

def words02 : List Nat := [360582199766106588, 360582199980970429, 360582200211911018, 360582200443105025, 360582200568851684, 360582200611340071, 360582200617036855, 360582200623126093, 360582200738187800, 360582200900095013]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 95620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 95600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360598228486888710, 360598288896707657⟩, ⟨(-1542392455397884385), (-1538491137020229821)⟩, true⟩

def words03 : List Nat := [360582200999699410, 360582201099453729, 360582201308321526, 360582201620882751, 360582201887815592, 360582202154968338, 360582202358388152, 360582202452940136, 360582202622258746, 360582202792034764]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 95630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 95600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593323396452862, 360593383819347516⟩, ⟨(-1073282609899285067), (-1069380040895920787)⟩, true⟩

def words04 : List Nat := [360582202917064026, 360582203062367556, 360582203153064792, 360582203243899990, 360582203245069074, 360582203302431568, 360582203447023089, 360582203591902353, 360582203681570543, 360582203799892457]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 95640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 95600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk956A
