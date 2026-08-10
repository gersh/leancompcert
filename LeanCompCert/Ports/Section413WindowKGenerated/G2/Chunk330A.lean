import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk330A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571107841004119, 360571114443814654⟩, ⟨333184080772169759, 333331411167925127⟩, true⟩

def state01 : KState := ⟨⟨360545319872834288, 360545326479786251⟩, ⟨1184302618064251817, 1184450085148348915⟩, true⟩

def words00 : List Nat := [360581215401394333, 360581215401835042, 360581215256117720, 360581214544698542, 360581213833257537, 360581212235924906, 360581211101596332, 360581210231956155, 360581209362320637, 360581208033410861]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 33000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 33000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360574191273122044, 360574197884238291⟩, ⟨231126163662058749, 231273768229536623⟩, true⟩

def words01 : List Nat := [360581206946811994, 360581206000059226, 360581205053222118, 360581205021722823, 360581204700000778, 360581203602376517, 360581202504734546, 360581202146666774, 360581202147029449, 360581201935365776]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 33010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 33000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360632577929774222, 360632584545088958⟩, ⟨(-1697283703450365418), (-1697135960228200890)⟩, true⟩

def words02 : List Nat := [360581201723653380, 360581201045453037, 360581201210854969, 360581201751169657, 360581202054453344, 360581202430925704, 360581202431318406, 360581202280486511, 360581202892743466, 360581204448808852]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 33020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 33000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360553629923270129, 360553636542741011⟩, ⟨910753573073279933, 910901453593837173⟩, true⟩

def words03 : List Nat := [360581205838649169, 360581207228488352, 360581207753390794, 360581207753831683, 360581207612180206, 360581207238864931, 360581207405723705, 360581207406164587, 360581207033320615, 360581206199326781]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 33030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 33000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360606969004640348, 360606975628273694⟩, ⟨(-851919146857570416), (-851771128789023530)⟩, true⟩

def words04 : List Nat := [360581205365276986, 360581204452886589, 360581204247563972, 360581204494056067, 360581204494462620, 360581203956895960, 360581203616226012, 360581203249959134, 360581203430273989, 360581204210501493]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 33040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 33000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk330A
