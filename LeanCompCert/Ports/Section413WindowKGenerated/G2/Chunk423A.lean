import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk423A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360597981536911301, 360597992608682772⟩, ⟨(-652645942972519059), (-652329433607309305)⟩, true⟩

def state01 : KState := ⟨⟨360605198723862278, 360605209801060976⟩, ⟨(-958069597371781254), (-957752858407076604)⟩, true⟩

def words00 : List Nat := [360582571823514670, 360582572007488195, 360582572008001242, 360582571842334791, 360582571676582308, 360582571487982264, 360582572166266034, 360582572844637884, 360582573240351341, 360582573775951500]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 42300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 42300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360602335776703389, 360602346859339229⟩, ⟨(-837016140973194412), (-836699171936546666)⟩, true⟩

def words01 : List Nat := [360582574606524672, 360582575437227361, 360582576174458695, 360582576356346216, 360582576356889394, 360582576059024807, 360582575761067128, 360582575616707552, 360582576084357906, 360582576552117365]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 42310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 42300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594697568137881, 360594708656267250⟩, ⟨(-513788202018822441), (-513471000468750741)⟩, true⟩

def words02 : List Nat := [360582576739753388, 360582576941230399, 360582577700168637, 360582578459239741, 360582579075646091, 360582579137007980, 360582579137526120, 360582578918326949, 360582578699029093, 360582578751458275]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 42320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 42300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360565124532623379, 360565135626178097⟩, ⟨738332475154023098, 738649906386433932⟩, true⟩

def words03 : List Nat := [360582579595849972, 360582580440313308, 360582580955903676, 360582581109480133, 360582581120308499, 360582581131306464, 360582581699366831, 360582581712746341, 360582581713263301, 360582581301813110]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 42330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 42300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360584516375318606, 360584527474322883⟩, ⟨(-82953971164718738), (-82636309171388454)⟩, true⟩

def words04 : List Nat := [360582580890253537, 360582580665580105, 360582580666055040, 360582580497010010, 360582580327932774, 360582579680104934, 360582578701104910, 360582577682999526, 360582576664773407, 360582576249814102]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 42340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 42300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk423A
