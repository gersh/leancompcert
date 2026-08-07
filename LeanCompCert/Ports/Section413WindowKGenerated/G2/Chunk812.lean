import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk812

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

def state06 : KState := ⟨⟨360609224748241147, 360609267809875349⟩, ⟨(-2201576025098262487), (-2199212796402220935)⟩, true⟩

def words05 : List Nat := [360582201628883542, 360582201973674763, 360582202442025551, 360582202759506391, 360582202947310625, 360582203135220910, 360582203307607649, 360582203571193299, 360582203905192479, 360582204239449164]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 81250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 81200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590218603819341, 360590261676560789⟩, ⟨(-657182038432600676), (-654817907110435896)⟩, true⟩

def words06 : List Nat := [360582204497362984, 360582204667578646, 360582204735687552, 360582204804113021, 360582204834485847, 360582204835649395, 360582204750823978, 360582204579209829, 360582204407369207, 360582204461722650]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 81260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 81200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360550412771003852, 360550455854695367⟩, ⟨2578131374071161937, 2580496395361830067⟩, true⟩

def words07 : List Nat := [360582204669027462, 360582204876549937, 360582205008296012, 360582205009459640, 360582204990135638, 360582204931259392, 360582204872056013, 360582204750235081, 360582204477309424, 360582204087906020]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 81270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 81200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579506982957394, 360579550077634848⟩, ⟨213262245872215831, 215628160153921963⟩, true⟩

def words08 : List Nat := [360582203698248357, 360582203460129573, 360582203349225653, 360582203370077623, 360582203371150980, 360582203262553508, 360582203048652529, 360582202918335550, 360582202787673154, 360582202656797770]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 81280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 81200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592178780235697, 360592221885999614⟩, ⟨(-816934946850119674), (-814568131295219338)⟩, true⟩

def words09 : List Nat := [360582202625222534, 360582202476824944, 360582202329797592, 360582202439515957, 360582202484496361, 360582202529665408, 360582202530713086, 360582202500170362, 360582202596462536, 360582202721028763]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 81290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 81200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 81200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk812
