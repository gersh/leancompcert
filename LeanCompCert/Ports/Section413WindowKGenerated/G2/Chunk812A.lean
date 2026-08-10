import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk812A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360596356424582661, 360596399420204013⟩, ⟨(-1155629267475672380), (-1153271400999167392)⟩, true⟩

def state01 : KState := ⟨⟨360595179348846204, 360595222355526551⟩, ⟨(-1060093708368096571), (-1057734943845004223)⟩, true⟩

def words00 : List Nat := [360582196845471115, 360582196922674665, 360582197151144942, 360582197379951177, 360582197551364960, 360582197656946784, 360582197658010389, 360582197646274644, 360582197665814273, 360582197827521170]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 81200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 81200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360574394089662490, 360574437107288299⟩, ⟨628015743582510394, 630375397041747792⟩, true⟩

def words01 : List Nat := [360582198033866535, 360582198240425235, 360582198318075206, 360582198399715353, 360582198409210998, 360582198419027777, 360582198551396649, 360582198552559321, 360582198533792044, 360582198439436068]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 81210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 81200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360592683268758854, 360592726297379753⟩, ⟨(-857549572845529613), (-855189026311831805)⟩, true⟩

def words02 : List Nat := [360582198344834642, 360582198205644251, 360582198228836073, 360582198316849567, 360582198317935633, 360582198280723596, 360582198199974923, 360582198209191736, 360582198301268834, 360582198432078184]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 81220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 81200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360588795250013171, 360588838289698996⟩, ⟨(-541706721479315457), (-539345276085923051)⟩, true⟩

def words03 : List Nat := [360582198486992612, 360582198542032537, 360582198748229900, 360582199030976823, 360582199173153908, 360582199315495229, 360582199361389682, 360582199362552716, 360582199375569695, 360582199458615111]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 81230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 81200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360602658557396900, 360602701608055463⟩, ⟨(-1668034131150635908), (-1665671794279430424)⟩, true⟩

def words04 : List Nat := [360582199659349109, 360582199867194753, 360582199958595283, 360582200050109056, 360582200103648917, 360582200272988028, 360582200565972941, 360582200859173451, 360582201030914569, 360582201284437546]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 81240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 81200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk812A
