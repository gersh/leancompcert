import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk354

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586840905569420, 360586848547985034⟩, ⟨(-172660984033961793), (-172478083442734033)⟩, true⟩

def state01 : KState := ⟨⟨360601837146110616, 360601844792996837⟩, ⟨(-703575081327528988), (-703392022454256500)⟩, true⟩

def words00 : List Nat := [360581977358215089, 360581977840920262, 360581977920379666, 360581977999886624, 360581978000284311, 360581978008247989, 360581979111990618, 360581980215761791, 360581980572723839, 360581981134177424]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 35400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 35400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360621307338987044, 360621314990365841⟩, ⟨(-1393301826269833484), (-1393118608292377868)⟩, true⟩

def words01 : List Nat := [360581981957130518, 360581982780177597, 360581983581275728, 360581983588416807, 360581983588858960, 360581982911745687, 360581982234578831, 360581982467150338, 360581983577995588, 360581984688898001]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 35410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 35400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593211096493168, 360593218752393556⟩, ⟨(-398181486791240353), (-397998108636430733)⟩, true⟩

def words02 : List Nat := [360581985397235768, 360581985533970106, 360581986466401591, 360581987398925025, 360581987895219822, 360581987895695177, 360581987598600411, 360581986675777536, 360581985752914679, 360581985704818370]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 35420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 35400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360587025674136572, 360587033334511893⟩, ⟨(-179032535889847823), (-178848999165465527)⟩, true⟩

def words03 : List Nat := [360581986138093824, 360581986571433424, 360581986571861187, 360581986534885656, 360581986523502915, 360581986123197587, 360581986117154139, 360581986661873969, 360581986804698007, 360581986947582477]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 35430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 35400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360629714823425083, 360629722488295333⟩, ⟨(-1692290352510492922), (-1692106656463864508)⟩, true⟩

def words04 : List Nat := [360581986947973809, 360581987430031436, 360581988185411704, 360581988940839721, 360581988941279327, 360581988927320486, 360581988810248695, 360581989149415429, 360581990283106787, 360581991630027193]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 35440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 35400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360584417255701451, 360584424925102624⟩, ⟨(-86271983120836910), (-86088126430770032)⟩, true⟩

def words05 : List Nat := [360581992430605720, 360581993231184703, 360581994126984704, 360581995518423654, 360581996356813585, 360581997195226996, 360581997544920017, 360581997545395838, 360581997171412937, 360581997240422814]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 35450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 35400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360616413871932040, 360616421545821514⟩, ⟨(-1220901862796470882), (-1220717846928895388)⟩, true⟩

def words06 : List Nat := [360581998103486956, 360581999356138975, 360582000207379441, 360582001058629637, 360582001511637184, 360582002487224533, 360582003882140142, 360582005277067830, 360582006043583016, 360582007014318910]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 35460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 35400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360624986680616562, 360624994358999165⟩, ⟨(-1525043473255760087), (-1524859297995243245)⟩, true⟩

def words07 : List Nat := [360582008561863294, 360582010109459711, 360582011997149085, 360582013093300281, 360582013384595021, 360582013675915335, 360582014200719241, 360582015150758487, 360582016362508890, 360582017574297628]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 35470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 35400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588884117709299, 360588891800631257⟩, ⟨(-244228915931917582), (-244044579593098008)⟩, true⟩

def words08 : List Nat := [360582018385432518, 360582018623313919, 360582018623705845, 360582018594065832, 360582018564301789, 360582018185133147, 360582017687678829, 360582016793901079, 360582015900083193, 360582015562159727]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 35480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 35400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360505057996393125, 360505065683797235⟩, ⟨2731405455125728225, 2731589950558868609⟩, true⟩

def words09 : List Nat := [360582016548995337, 360582017535867434, 360582018122361288, 360582018122837572, 360582017918723400, 360582017354692626, 360582016790556904, 360582015813834162, 360582014046653517, 360582011879587626]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 35490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 35400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 35400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk354
