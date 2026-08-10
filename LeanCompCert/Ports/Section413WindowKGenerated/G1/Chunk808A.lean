import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk808A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362481362667838864, 362481460640421499⟩, ⟨292913718727922380, 298259131037044648⟩, true⟩

def state01 : KState := ⟨⟨362489409360659345, 362489507358306546⟩, ⟨(-357307354375645035), (-351959916724771563)⟩, true⟩

def words00 : List Nat := [371285151922551575, 371285151890228706, 371285151834727836, 371285151885578242, 371285151910281835, 371285151913096340, 371285151800346551, 371285151802504205, 371285151954883727, 371285152011673975]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 80800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 80800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492196963844209, 362492294986928692⟩, ⟨(-582584552205844242), (-577235058837636340)⟩, true⟩

def words01 : List Nat := [371285152057181805, 371285152103584967, 371285152288742574, 371285152398511689, 371285152514026491, 371285152630612067, 371285152724677079, 371285152727480673, 371285152753090133, 371285152844925530]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 80810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 80800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490744092409661, 362490842140424226⟩, ⟨(-465125072118806536), (-459773563772136098)⟩, true⟩

def words02 : List Nat := [371285153036656692, 371285153127392929, 371285153204109145, 371285153281791004, 371285153389681070, 371285153441903164, 371285153631824830, 371285153822875198, 371285153982588920, 371285154055855532]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 80820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 80800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362511718231734462, 362511816305064337⟩, ⟨(-2160538288348067101), (-2155184733639396331)⟩, true⟩

def words03 : List Nat := [371285154281100945, 371285154507832577, 371285154886042634, 371285155118765953, 371285155312467036, 371285155507055404, 371285155835314092, 371285156089768521, 371285156421468199, 371285156754419994]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 80830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 80800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362496145880557089, 362496243979156777⟩, ⟨(-901652984624046109), (-896297386978125331)⟩, true⟩

def words04 : List Nat := [371285157086351279, 371285157234813102, 371285157445746295, 371285157658060914, 371285157867568852, 371285157874037020, 371285157880328880, 371285157887574739, 371285158046545678, 371285158186934317]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 80840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 80800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk808A
