import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk531A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360593954403104841, 360593972178574605⟩, ⟨(-639695573106182858), (-639057822925881958)⟩, true⟩

def state01 : KState := ⟨⟨360601837909873885, 360601855692288818⟩, ⟨(-1058304330053031102), (-1057666211050188124)⟩, true⟩

def words00 : List Nat := [360581937999068801, 360581938589572153, 360581938976695570, 360581939363884364, 360581939488896300, 360581939824784543, 360581940325436946, 360581940826217707, 360581941057539327, 360581941433264319]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 53100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 53100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360634490430481923, 360634508219844035⟩, ⟨(-2792649352099910767), (-2792010864097155263)⟩, true⟩

def words01 : List Nat := [360581942090421446, 360581942747769747, 360581943758574901, 360581944416011101, 360581944771160614, 360581945126367214, 360581945835072374, 360581946783513552, 360581947773597902, 360581948763807870]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 53110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 53100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360611197317049024, 360611215113434407⟩, ⟨(-1555440867226903057), (-1554802006115029981)⟩, true⟩

def words02 : List Nat := [360581949576359100, 360581950035568039, 360581950486352413, 360581950937327160, 360581951183204923, 360581951183941526, 360581951183454282, 360581951006606665, 360581951005550403, 360581951557203299]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 53120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 53100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360558372323455579, 360558390126768841⟩, ⟨1251465199637576816, 1252104428863250190⟩, true⟩

def words03 : List Nat := [360581952085002951, 360581952612921281, 360581952951160400, 360581953083445711, 360581953126855758, 360581953170468046, 360581953205664309, 360581953206401133, 360581952941054706, 360581952498407217]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 53130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 53100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590382211076515, 360590400021343566⟩, ⟨(-449750952949080026), (-449111354164509822)⟩, true⟩

def words04 : List Nat := [360581952055613455, 360581951666963475, 360581951545193656, 360581951563153754, 360581951563839398, 360581951278350500, 360581950639651892, 360581950354429786, 360581950136211849, 360581950295954307]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 53140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 53100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk531A
