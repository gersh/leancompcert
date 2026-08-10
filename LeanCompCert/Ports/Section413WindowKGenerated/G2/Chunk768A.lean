import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk768A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360576648235376460, 360576686530369323⟩, ⟨419036292786034962, 421022707578196270⟩, true⟩

def state01 : KState := ⟨⟨360594073848016858, 360594112153323000⟩, ⟨(-919325110320599857), (-917337903415773519)⟩, true⟩

def words00 : List Nat := [360582168624254298, 360582168698340164, 360582168699316170, 360582168688663610, 360582168677808464, 360582168693116716, 360582168891326600, 360582169089740960, 360582169203309887, 360582169359928620]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 76800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 76800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360595602106023030, 360595640421684123⟩, ⟨(-1036806520342718469), (-1034818518024189679)⟩, true⟩

def words01 : List Nat := [360582169512394248, 360582169665162520, 360582169844409384, 360582169887011794, 360582169888032634, 360582169782582183, 360582169676930971, 360582169552845567, 360582169729087579, 360582169905574932]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 76810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 76800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581427575327601, 360581465901419799⟩, ⟨52017654910114502, 54006458597307600⟩, true⟩

def words02 : List Nat := [360582169977520203, 360582169978615913, 360582169945803335, 360582169959006608, 360582169959940695, 360582169855683290, 360582169621887328, 360582169303538770, 360582168984988754, 360582168835932325]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 76820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 76800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360564799659548049, 360564837995968639⟩, ⟨1329696937540453404, 1331686534809590160⟩, true⟩

def words03 : List Nat := [360582168987631263, 360582169148704364, 360582169224083305, 360582169225179463, 360582169202474638, 360582169064267911, 360582168955420199, 360582168956515987, 360582168862422018, 360582168638014574]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 76830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 76800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594838034084372, 360594876380850647⟩, ⟨(-978623711761066502), (-976633319479647150)⟩, true⟩

def words04 : List Nat := [360582168413361856, 360582168298254885, 360582168271317234, 360582168219765241, 360582168168129974, 360582167975214390, 360582167933607308, 360582167998092782, 360582168073669538, 360582168240169594]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 76840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 76800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk768A
