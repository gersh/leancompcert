import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk083

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360865323419226258, 360865323786924327⟩, ⟨(-2372792244481163549), (-2372790175217113259)⟩, true⟩

def state01 : KState := ⟨⟨360629654294544828, 360629654663181993⟩, ⟨(-415976530563650407), (-415974453500377631)⟩, true⟩

def words00 : List Nat := [360579507094334387, 360579535267132209, 360579563919807347, 360579592565610558, 360579611061052839, 360579615189166957, 360579615189255963, 360579609489542507, 360579603791183586, 360579603591890888]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 8300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 8300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360430052443996034, 360430052813562711⟩, ⟨1244328341919187480, 1244330426711390620⟩, true⟩

def words01 : List Nat := [360579623964636891, 360579644332500191, 360579653909239151, 360579653909337838, 360579649137205304, 360579640703186683, 360579638174544394, 360579638174643118, 360579629736973949, 360579611759080907]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 8310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 8300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595075871802676, 360595076242303461⟩, ⟨(-130111198101424102), (-130109105532909122)⟩, true⟩

def words02 : List Nat := [360579593785486502, 360579584266834457, 360579583671559628, 360579575577850940, 360579567486079841, 360579545866313387, 360579518631508615, 360579493284076935, 360579467942703293, 360579458776749157]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 8320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 8300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360554603391825457, 360554603763267735⟩, ⟨207081920504692650, 207084020920623160⟩, true⟩

def words03 : List Nat := [360579458776837277, 360579453470427515, 360579448165272983, 360579452488853273, 360579454618821517, 360579456748294837, 360579456748384502, 360579447597778914, 360579436959092425, 360579433981603542]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 8330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 8300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360504820627048370, 360504820999423977⟩, ⟨622482964595268034, 622485072799852810⟩, true⟩

def words04 : List Nat := [360579433807756374, 360579433807855499, 360579430219779434, 360579418738829755, 360579407260614001, 360579392186472525, 360579386284708354, 360579384874619216, 360579383464857729, 360579370109938930]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 8340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 8300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360587500627019600, 360587501000332889⟩, ⟨(-68745608317839291), (-68743492278888489)⟩, true⟩

def words05 : List Nat := [360579361183052560, 360579351735092210, 360579347039653385, 360579347039752576, 360579337575615069, 360579315565040963, 360579293559715693, 360579280029063057, 360579278094454395, 360579279078041431]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 8350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 8300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360597507535635887, 360597507909894343⟩, ⟨(-153418822354171832), (-153416698408977676)⟩, true⟩

def words06 : List Nat := [360579279078130658, 360579272696777490, 360579260569723956, 360579261587073868, 360579261587158503, 360579252301853867, 360579235662490596, 360579211907067962, 360579188157303530, 360579180744871171]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 8360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 8300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360416647921077783, 360416648296273846⟩, ⟨1361477253569453545, 1361479385367112923⟩, true⟩

def words07 : List Nat := [360579184869061218, 360579188992286700, 360579188992375279, 360579186014765093, 360579175694615316, 360579160220868001, 360579144750786389, 360579143397154989, 360579135393123755, 360579116003358228]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 8370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 8300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360755567935332919, 360755568311468500⟩, ⟨(-1480826228619156690), (-1480824088943645462)⟩, true⟩

def words08 : List Nat := [360579096618197862, 360579077177701157, 360579068923675015, 360579069128827124, 360579069128919243, 360579057231171688, 360579049345656094, 360579052442168819, 360579069611848948, 360579090646238654]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 8380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 8300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360668925394576352, 360668925771662947⟩, ⟨(-754034368844060856), (-754032221184872586)⟩, true⟩

def words09 : List Nat := [360579104618879998, 360579118588202674, 360579124699063397, 360579138158925878, 360579143087942984, 360579148015802166, 360579148015891901, 360579149343179348, 360579160030930328, 360579170716171355]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 8390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 8300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 8300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk083
