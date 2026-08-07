import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk434

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360613069030092076, 360613080709767971⟩, ⟨(-1298979397743499089), (-1298636838156877381)⟩, true⟩

def state01 : KState := ⟨⟨360601614872200473, 360601626557512078⟩, ⟨(-802044135044471118), (-801701330839864658)⟩, true⟩

def words00 : List Nat := [360583159108137283, 360583159108729475, 360583159014237650, 360583159232651835, 360583159314364419, 360583159322498191, 360583159323042508, 360583158892769028, 360583158462402106, 360583158857370643]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 43400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 43400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360582155402780673, 360582167093670659⟩, ⟨42927217911963619, 43270264302072185⟩, true⟩

def words01 : List Nat := [360583159813539613, 360583160769777919, 360583161399474367, 360583162055676318, 360583162460372253, 360583162865212030, 360583163350870541, 360583163666936502, 360583163667464486, 360583163645128561]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 43410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 43400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360621095927404807, 360621107623892196⟩, ⟨(-1648150186951700262), (-1647806897495186534)⟩, true⟩

def words02 : List Nat := [360583163622665015, 360583163813988594, 360583164455095948, 360583165096288121, 360583165289693579, 360583165290286096, 360583165149798499, 360583165344935024, 360583165949378258, 360583166823599889]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 43420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 43400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585481128113766, 360585492830241909⟩, ⟨(-101194740998399201), (-100851206536181449)⟩, true⟩

def words03 : List Nat := [360583167411888383, 360583168000214284, 360583168712849740, 360583169764508000, 360583170317064045, 360583170869681386, 360583171155232066, 360583171155825109, 360583171208789645, 360583171262908372]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 43430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 43400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360623756585259862, 360623768292977769⟩, ⟨(-1764024728527953742), (-1763680951218394240)⟩, true⟩

def words04 : List Nat := [360583171846375141, 360583172623945202, 360583173136002955, 360583173648096498, 360583174023898613, 360583174747105314, 360583175716264712, 360583176685492326, 360583177246301363, 360583178181099599]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 43440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 43400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360655511222269543, 360655522935579610⟩, ⟨(-3143940823675326191), (-3143596803358263647)⟩, true⟩

def words05 : List Nat := [360583179645015630, 360583181109045804, 360583182801340355, 360583183965946316, 360583184684454984, 360583185402987184, 360583186650532745, 360583188163703009, 360583189828583562, 360583191493519873]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 43450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 43400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360620181884120203, 360620193603088967⟩, ⟨(-1608568833169102313), (-1608224566898309249)⟩, true⟩

def words06 : List Nat := [360583192752348082, 360583193702326587, 360583194631554372, 360583195560904678, 360583196354043536, 360583196773371570, 360583196926033211, 360583197078752621, 360583197408077775, 360583198259827982]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 43460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 43400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360547477161221346, 360547488885772378⟩, ⟨1552383181544582284, 1552727690504956980⟩, true⟩

def words07 : List Nat := [360583199394159392, 360583200528559766, 360583201340913702, 360583201626140023, 360583201626637465, 360583201612849952, 360583201598897684, 360583201570498292, 360583201014933847, 360583200194201655]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 43470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 43400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595037080700178, 360595048810849061⟩, ⟨(-515783236515917246), (-515438484132536306)⟩, true⟩

def words08 : List Nat := [360583199373372995, 360583199081255212, 360583199054051740, 360583198905040058, 360583198755981359, 360583198126808913, 360583197327625681, 360583197057044466, 360583196925108845, 360583197198236509]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 43480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 43400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360609483300720017, 360609495036530284⟩, ⟨(-1144276847855185561), (-1143931849231299907)⟩, true⟩

def words09 : List Nat := [360583197198775497, 360583197053900428, 360583196908919555, 360583197006813105, 360583197118997895, 360583197231274323, 360583197231808600, 360583197146932676, 360583197751961876, 360583198357161275]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 43490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 43400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 43400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk434
