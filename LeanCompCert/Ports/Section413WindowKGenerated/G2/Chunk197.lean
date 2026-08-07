import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk197

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360627111003327985, 360627113252927304⟩, ⟨(-863273089372417040), (-863243096522416766)⟩, true⟩

def state01 : KState := ⟨⟨360529508985649556, 360529511237652376⟩, ⟨1059311313854029334, 1059341354064820142⟩, true⟩

def words00 : List Nat := [360583296349080997, 360583296349333258, 360583294095876444, 360583291223667138, 360583288351686488, 360583283649324709, 360583277468877600, 360583270000913707, 360583262533658350, 360583257628015888]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 19700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 19700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360423858128617652, 360423860382999962⟩, ⟨3142414911747695627, 3142444998870428075⟩, true⟩

def words01 : List Nat := [360583254901499802, 360583253321091867, 360583251740810831, 360583248874103614, 360583243438909723, 360583237355919366, 360583231273472249, 360583227749980003, 360583221658607368, 360583213577668848]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 19710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 19700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360505234772832533, 360505237029597634⟩, ⟨1536980322315879076, 1537010456439105736⟩, true⟩

def words02 : List Nat := [360583205497493285, 360583196752861529, 360583189577189756, 360583182514813863, 360583175453134543, 360583166177267346, 360583157037284125, 360583150454491045, 360583143872289196, 360583139232154102]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 19720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 19700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360492346675752937, 360492348934927362⟩, ⟨1791236990716720328, 1791267172387461950⟩, true⟩

def words03 : List Nat := [360583135284165540, 360583130053421354, 360583124823162603, 360583119532215376, 360583116542729065, 360583112908537516, 360583109274689552, 360583103699738317, 360583096549629764, 360583091952778804]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 19730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 19700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360386346166355427, 360386348427908609⟩, ⟨3884176465439736579, 3884206694079213127⟩, true⟩

def words04 : List Nat := [360583087356305840, 360583083860959965, 360583077804791007, 360583070468741694, 360583063133395700, 360583054063519286, 360583046264759164, 360583037113870873, 360583027963881904, 360583017121279709]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 19740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 19700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360573949551415606, 360573951815355644⟩, ⟨178049514527968554, 178079790319694422⟩, true⟩

def words05 : List Nat := [360583007164079979, 360582999757510307, 360582992351616874, 360582987495817859, 360582983825768751, 360582977971274643, 360582972117323556, 360582967410289353, 360582964406332649, 360582963950493281]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 19750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 19700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360517235004252629, 360517237270603472⟩, ⟨1298663364913638882, 1298693688354860438⟩, true⟩

def words06 : List Nat := [360582963494665793, 360582961038807851, 360582957250760754, 360582956010325934, 360582954769947190, 360582952203452880, 360582947081445955, 360582939963641801, 360582932846505224, 360582927391410496]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 19760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 19700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360451711588919663, 360451713857654036⟩, ⟨2594317703199268254, 2594348073774745178⟩, true⟩

def words07 : List Nat := [360582924069066647, 360582921577081372, 360582919085323606, 360582914986277241, 360582908333089098, 360582899926340241, 360582891520367717, 360582885658990996, 360582880654184882, 360582874023163376]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 19770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 19700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360524248811388583, 360524251082517026⟩, ⟨1159497076754991955, 1159527494696882587⟩, true⟩

def words08 : List Nat := [360582867392754814, 360582862557467696, 360582859800607790, 360582858807044124, 360582857813561034, 360582854642789001, 360582850780330042, 360582848548701985, 360582846317229730, 360582842668908986]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 19780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 19700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360518267651071097, 360518269924614799⟩, ⟨1277970823176476623, 1278001288928193545⟩, true⟩

def words09 : List Nat := [360582839708620272, 360582835450918409, 360582831193598396, 360582829476415743, 360582829070250943, 360582827369498778, 360582825668886374, 360582822692028394, 360582818704003500, 360582815444257638]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 19790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 19700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 19700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk197
