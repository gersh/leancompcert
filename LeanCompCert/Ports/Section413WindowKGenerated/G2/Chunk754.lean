import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk754

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360539583648482717, 360539620506499186⟩, ⟨3209770787383876977, 3211647845039761675⟩, true⟩

def state01 : KState := ⟨⟨360580983274160252, 360581020142304774⟩, ⟨88061576107053841, 89939397469122195⟩, true⟩

def words00 : List Nat := [360582214741463059, 360582214353455095, 360582214082481447, 360582213987427131, 360582213892280091, 360582213624626061, 360582213257184852, 360582213065739707, 360582212873984726, 360582212814330621]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 75400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 75400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360578687614614106, 360578724493015156⟩, ⟨261139585024379933, 263018179880695839⟩, true⟩

def words01 : List Nat := [360582212799501215, 360582212644159669, 360582212488617946, 360582212385598237, 360582212370615817, 360582212311359102, 360582212251981151, 360582212082210242, 360582211917757106, 360582211872753697]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 75410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 75400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360571222896917571, 360571259785432449⟩, ⟨824167582925987343, 826046940617747179⟩, true⟩

def words02 : List Nat := [360582211929376853, 360582211930451453, 360582211924267416, 360582211818443677, 360582211712464462, 360582211482690027, 360582211365504874, 360582211275808802, 360582211186010488, 360582210957918433]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 75420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 75400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360588617011236111, 360588653909908534⟩, ⟨(-487931690393961890), (-486051566469753224)⟩, true⟩

def words03 : List Nat := [360582210843972881, 360582210875543580, 360582211051333660, 360582211052408003, 360582211052697575, 360582210901474325, 360582210773273711, 360582210933231509, 360582211019524981, 360582211106042338]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 75430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 75400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581766990517068, 360581803899416173⟩, ⟨28793959883042922, 30674855358861240⟩, true⟩

def words04 : List Nat := [360582211106999832, 360582211105537579, 360582210984637802, 360582210965616570, 360582210946311390, 360582210857830193, 360582210844979117, 360582210728374972, 360582210611576026, 360582210458135310]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 75440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 75400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360567143713319867, 360567180632354974⟩, ⟨1132237489639304567, 1134119149926880207⟩, true⟩

def words05 : List Nat := [360582210594821448, 360582210737103007, 360582210743832887, 360582210744908399, 360582210648016820, 360582210507054564, 360582210365769885, 360582210349028081, 360582210238683090, 360582210040649791]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 75450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 75400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360574063342731961, 360574100271903219⟩, ⟨610049689449721117, 611932114661449097⟩, true⟩

def words06 : List Nat := [360582209842351149, 360582209768614664, 360582209769487407, 360582209755272171, 360582209740989294, 360582209577341166, 360582209289510817, 360582208997907905, 360582208705994946, 360582208554858850]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 75460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 75400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360582938597596994, 360582975537007164⟩, ⟨(-59848773002191787), (-57965575009749637)⟩, true⟩

def words07 : List Nat := [360582208448387446, 360582208208310678, 360582207968034330, 360582207879613831, 360582207880514718, 360582207861594237, 360582207842557295, 360582207730472061, 360582207576383647, 360582207587788027]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 75470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 75400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360574058693366582, 360574095642911021⟩, ⟨610426745914266022, 612310708891981248⟩, true⟩

def words08 : List Nat := [360582207588672883, 360582207542285692, 360582207524786005, 360582207418903836, 360582207312849967, 360582207134190245, 360582207070612189, 360582207007338263, 360582206943930235, 360582206792849980]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 75480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 75400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360575539166855027, 360575576126546845⟩, ⟨498594811399428734, 500479540453897614⟩, true⟩

def words09 : List Nat := [360582206686278344, 360582206632158707, 360582206577718730, 360582206550743734, 360582206348399352, 360582205979959273, 360582205611325543, 360582205302438441, 360582205081318437, 360582204994632328]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 75490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 75400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 75400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk754
