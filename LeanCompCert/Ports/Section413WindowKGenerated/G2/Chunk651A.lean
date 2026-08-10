import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk651A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360595479136945509, 360595506294047230⟩, ⟨(-818380259706706182), (-817186005533370766)⟩, true⟩

def state01 : KState := ⟨⟨360587868390277550, 360587895556010652⟩, ⟨(-322865189469426861), (-321670373349416533)⟩, true⟩

def words00 : List Nat := [360582954135487949, 360582954418167481, 360582954582606867, 360582954747145627, 360582954803260415, 360582954978195404, 360582955092639910, 360582955207243876, 360582955208066457, 360582955217613924]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 65100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 65100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360616747868057219, 360616775042444492⟩, ⟨(-2203387098733874651), (-2202191719097189591)⟩, true⟩

def words01 : List Nat := [360582955529664459, 360582955841974409, 360582956135369515, 360582956435394897, 360582956532416621, 360582956629499065, 360582956796072038, 360582957081025212, 360582957601084406, 360582958121342280]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 65110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 65100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360603158598725621, 360603185781856063⟩, ⟨(-1318540280324770185), (-1317344331290175847)⟩, true⟩

def words02 : List Nat := [360582958458677710, 360582958560975823, 360582958898457266, 360582959236207965, 360582959508960779, 360582959546755749, 360582959547575203, 360582959419545835, 360582959397705183, 360582959709305509]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 65120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 65100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360561835310291956, 360561862502052536⟩, ⟨1373074156260650156, 1374270667420386490⟩, true⟩

def words03 : List Nat := [360582959984842133, 360582960260542396, 360582960417932079, 360582960448681259, 360582960449462400, 360582960317595952, 360582960214637862, 360582960215555369, 360582960010542990, 360582959687613181]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 65130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 65100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580633912727039, 360580661113164005⟩, ⟨148538313636963150, 149735390017534744⟩, true⟩

def words04 : List Nat := [360582959364485480, 360582959408664087, 360582959610820826, 360582959813146030, 360582959813992559, 360582959800755222, 360582959552382138, 360582959539489693, 360582959526341532, 360582959430739102]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 65140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 65100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk651A
