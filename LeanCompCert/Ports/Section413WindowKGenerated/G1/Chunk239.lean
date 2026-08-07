import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk239

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362538469882293790, 362538477647424732⟩, ⟨(-1279783924345906224), (-1279658440519802058)⟩, true⟩

def state01 : KState := ⟨⟨362498261389310766, 362498269161227642⟩, ⟨(-318722641738593879), (-318596995694579059)⟩, true⟩

def words00 : List Nat := [371284939937832086, 371284940950224423, 371284942438403285, 371284943926860837, 371284945535884757, 371284945536637055, 371284944814038620, 371284944064956516, 371284944317388434, 371284944875514181]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 23900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 23900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362485660205915044, 362485667984624990⟩, ⟨(-17090536723652000), (-16964728223049692)⟩, true⟩

def words01 : List Nat := [371284947184555085, 371284949493728614, 371284951784433835, 371284952521851954, 371284953779976448, 371284955038357775, 371284958046797168, 371284958725770808, 371284958755996725, 371284958786505219]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 23910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 23900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362532729807754234, 362532737593198024⟩, ⟨(-1143172261472900049), (-1143046291863835375)⟩, true⟩

def words02 : List Nat := [371284960084029507, 371284960514721304, 371284962406891428, 371284964299201272, 371284965636771369, 371284965637537258, 371284966889260459, 371284968243365567, 371284971345370600, 371284973342148598]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 23920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 23900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362508395816787956, 362508403609106481⟩, ⟨(-560699324426950693), (-560573190272043185)⟩, true⟩

def words03 : List Nat := [371284975322270426, 371284977302468439, 371284979691586134, 371284981210827198, 371284983249643022, 371284985288593942, 371284987243904299, 371284987244657615, 371284987852506722, 371284988831516905]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 23930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 23900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362459439376826937, 362459447175848194⟩, ⟨611664677354222210, 611790972007897356⟩, true⟩

def words04 : List Nat := [371284991285967658, 371284991416033121, 371284991416597774, 371284991367148186, 371284991787662443, 371284991788496182, 371284991635104650, 371284991658448096, 371284991683293230, 371284991684073994]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 23940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 23900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362528094445163041, 362528102251007415⟩, ⟨(-1032912593776752699), (-1032786135675102183)⟩, true⟩

def words05 : List Nat := [371284990936141063, 371284991255111777, 371284992639639168, 371284992925639609, 371284992939713310, 371284992954012890, 371284994712022518, 371284995853892990, 371284997653507179, 371284999453308025]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 23950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 23900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478862865122113, 362478870677775974⟩, ⟨146778553242347483, 146905174534004705⟩, true⟩

def words06 : List Nat := [371285000836519713, 371285000837273748, 371285000397220931, 371285000895650319, 371285001914140834, 371285001914896066, 371285001074123509, 371285000218712438, 371284999386740016, 371284999387602174]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 23960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 23900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362461905049238863, 362461912868677553⟩, ⟨553492673863748814, 553619457822193576⟩, true⟩

def words07 : List Nat := [371285000618695025, 371285002105638140, 371285003475992548, 371285003476747190, 371285002528714990, 371285001607366200, 371285001504761848, 371285001505518140, 371285000546960678, 371284999585017095]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 23970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 23900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362471486624040334, 362471494450240035⟩, ⟨323955793452100942, 324082739574568022⟩, true⟩

def words08 : List Nat := [371284999400925601, 371284999543464486, 371285000958705658, 371285002374143763, 371285003518785475, 371285003519540659, 371285002821103554, 371285002987254602, 371285003525722616, 371285003526504086]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 23980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 23900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497746293434640, 362497754126524678⟩, ⟨(-306138470077691766), (-306011358622049424)⟩, true⟩

def words09 : List Nat := [371285002963983675, 371285002068000560, 371285002014449529, 371285002151496249, 371285002807282242, 371285003463308686, 371285004056379781, 371285004057138848, 371285003652302403, 371285004184496344]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 23990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 23900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 23900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk239
