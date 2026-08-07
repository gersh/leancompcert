import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk515

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360579690335540157, 360579707014283315⟩, ⟨112507843566009794, 113088230171913138⟩, true⟩

def state01 : KState := ⟨⟨360604457854623923, 360604474540150568⟩, ⟨(-1163265232097269120), (-1162684496108721980)⟩, true⟩

def words00 : List Nat := [360581902860244669, 360581902629591887, 360581902435247471, 360581902526655435, 360581902527251666, 360581902677117018, 360581902677757760, 360581902571814405, 360581902524268779, 360581902963281381]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 51500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 51500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360576172670890702, 360576189363137261⟩, ⟨293941912446559581, 294522994611119579⟩, true⟩

def words01 : List Nat := [360581903778070462, 360581904592964676, 360581905040093135, 360581905261075581, 360581905388192397, 360581905515501337, 360581906018526302, 360581906145742364, 360581906146380243, 360581906036169310]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 51510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 51500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360596991765162776, 360597008464131260⟩, ⟨(-778681243440962703), (-778099814929571077)⟩, true⟩

def words02 : List Nat := [360581906190738230, 360581906667223574, 360581907408475712, 360581908149840333, 360581908558983862, 360581908592300691, 360581908592888530, 360581908460838991, 360581908525203466, 360581908818967581]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 51520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 51500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360592342454305242, 360592359160060003⟩, ⟨(-539098551345995662), (-538516773103907684)⟩, true⟩

def words03 : List Nat := [360581908901182279, 360581908983475006, 360581909270028910, 360581909851219217, 360581910183542475, 360581910515965215, 360581910607161342, 360581910607874470, 360581910638232160, 360581910841767694]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 51530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 51500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360562479629234657, 360562496341715400⟩, ⟨1000055861989610245, 1000637986921758229⟩, true⟩

def words04 : List Nat := [360581910938737946, 360581910939451049, 360581910660871009, 360581910137217824, 360581909613469661, 360581908857599302, 360581908406310144, 360581908120324547, 360581907834259671, 360581907359890410]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 51540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 51500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360583419171938449, 360583435891146929⟩, ⟨(-79478118042130256), (-78895646261325320)⟩, true⟩

def words05 : List Nat := [360581906983926897, 360581906983694521, 360581907210438650, 360581907211151865, 360581907166859584, 360581906770624511, 360581906374272397, 360581905915653209, 360581905718836419, 360581905749251673]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 51550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 51500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360596725454916617, 360596742180932968⟩, ⟨(-765659211089976895), (-765076388262539837)⟩, true⟩

def words06 : List Nat := [360581905749894773, 360581905510610109, 360581905689917906, 360581905967718813, 360581906151764903, 360581906401615850, 360581906463194207, 360581906524852917, 360581906525439899, 360581906781420403]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 51560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 51500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360582421289732588, 360582438022466353⟩, ⟨(-27926344915206510), (-27343175636549828)⟩, true⟩

def words07 : List Nat := [360581907181127817, 360581907580953673, 360581907792592122, 360581907793305728, 360581907726186752, 360581907559112240, 360581907599052574, 360581907898829894, 360581907909753437, 360581907920769284]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 51570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 51500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360618250483504401, 360618267222984301⟩, ⟨(-1876208819854713965), (-1875625302576885785)⟩, true⟩

def words08 : List Nat := [360581908306671787, 360581908882847234, 360581909449084107, 360581910015429672, 360581910278839218, 360581910279552961, 360581910336424734, 360581910505775269, 360581910848849501, 360581911554309981]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 51580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 51500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360607528829366024, 360607545575636256⟩, ⟨(-1323014382994687157), (-1322430515370140241)⟩, true⟩

def words09 : List Nat := [360581912019609137, 360581912484967728, 360581913325021281, 360581914355161954, 360581915157129596, 360581915959181110, 360581916456581817, 360581916579197911, 360581917076461071, 360581917573943070]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 51590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 51500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 51500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk515
