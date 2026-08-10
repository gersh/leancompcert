import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk476A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589708618745412, 360589722775657005⟩, ⟨(-333487266527267170), (-333031906013820138)⟩, true⟩

def state01 : KState := ⟨⟨360583856715558331, 360583870878707575⟩, ⟨(-55138743952432377), (-54683086496002865)⟩, true⟩

def words00 : List Nat := [360582726454614475, 360582726293958146, 360582725692767990, 360582725445177404, 360582725197424001, 360582724839866754, 360582724355716355, 360582723529088929, 360582722702366541, 360582722339788082]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 47600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 47600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360560928393404434, 360560942562720297⟩, ⟨1036726334986114482, 1037182286066042714⟩, true⟩

def words01 : List Nat := [360582722660297529, 360582722980918707, 360582723026536254, 360582723233572025, 360582723258878455, 360582723284357625, 360582723460814828, 360582723461470411, 360582723411830590, 360582722955119836]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 47610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 47600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360602825901424739, 360602840076929398⟩, ⟨(-958734035826903617), (-958277790006008593)⟩, true⟩

def words02 : List Nat := [360582722498289181, 360582722031409525, 360582721978418009, 360582722172058140, 360582722172662862, 360582721985130095, 360582721357538591, 360582721048893186, 360582720870074135, 360582721293154000]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 47620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 47600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360577689208820771, 360577703390557163⟩, ⟨238627758837752095, 239084301507590075⟩, true⟩

def words03 : List Nat := [360582721496687047, 360582721700286198, 360582721879315135, 360582722358904512, 360582722531882304, 360582722704950233, 360582722705539510, 360582722601395835, 360582722057320078, 360582721952721471]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 47630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 47600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360559226983970776, 360559241171886476⟩, ⟨1118269643867949602, 1118726480950845662⟩, true⟩

def words04 : List Nat := [360582721847913803, 360582721653198072, 360582721614217582, 360582721356038116, 360582721097765002, 360582720594174889, 360582720314523130, 360582720045972252, 360582719777371219, 360582719167289432]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 47640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 47600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk476A
