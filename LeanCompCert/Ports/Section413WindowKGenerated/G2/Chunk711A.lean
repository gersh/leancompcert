import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk711A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360550985273103178, 360551017894889861⟩, ⟨2227530992097866573, 2229097650494139235⟩, true⟩

def state01 : KState := ⟨⟨360562534717581645, 360562567348859912⟩, ⟨1406255812403208179, 1407823145699579243⟩, true⟩

def words00 : List Nat := [360582369039155941, 360582368742889598, 360582368302285296, 360582367750074478, 360582367197708123, 360582366595712376, 360582366144938567, 360582365853446999, 360582365561861426, 360582365171187287]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 71100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 71100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360570730531056840, 360570763171867489⟩, ⟨823315778187016466, 824883789377245270⟩, true⟩

def words01 : List Nat := [360582364893597877, 360582364611593966, 360582364329316493, 360582364043039653, 360582363703624801, 360582363168469299, 360582362633136228, 360582362171930090, 360582361812369221, 360582361650345797]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 71110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 71100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360571876534821279, 360571909185231843⟩, ⟨741657154425347669, 743225848409519415⟩, true⟩

def words02 : List Nat := [360582361488163671, 360582361209143492, 360582360807533874, 360582360464696017, 360582360121601737, 360582359721598541, 360582359360534393, 360582358849034981, 360582358337354245, 360582358023252503]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 71120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 71100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360541790533227524, 360541823193137214⟩, ⟨2881936955091011937, 2883506324796553839⟩, true⟩

def words03 : List Nat := [360582357881776521, 360582357887389055, 360582357888287976, 360582357784653441, 360582357686295417, 360582357489362496, 360582357292127454, 360582357046318416, 360582356603088286, 360582356034362918]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 71130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 71100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360558326815204083, 360558359484652863⟩, ⟨1705467360900274777, 1707037409261523801⟩, true⟩

def words04 : List Nat := [360582355465439338, 360582354892651867, 360582354439301965, 360582354183322780, 360582353927285400, 360582353487039338, 360582352849318160, 360582352409086392, 360582351968547746, 360582351577544803]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 71140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 71100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk711A
