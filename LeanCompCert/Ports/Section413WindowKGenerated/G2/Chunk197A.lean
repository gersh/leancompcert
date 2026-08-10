import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk197A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk197A
