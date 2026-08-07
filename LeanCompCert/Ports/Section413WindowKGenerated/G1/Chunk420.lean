import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk420

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362514110871702871, 362514136002212952⟩, ⟨(-1217848814815091219), (-1217135629926125649)⟩, true⟩

def state01 : KState := ⟨⟨362478320860070200, 362478346002876236⟩, ⟨285596332928800191, 286310034313190151⟩, true⟩

def words00 : List Nat := [371285158432259532, 371285158837347953, 371285159227401177, 371285159617875092, 371285160153317369, 371285160406354489, 371285160745819643, 371285161085824079, 371285161284337398, 371285161285768719]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 42000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 42000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362535858876535086, 362535884031830366⟩, ⟨(-2131871333954284912), (-2131157107834012938)⟩, true⟩

def words01 : List Nat := [371285161423762463, 371285161724684587, 371285162591553928, 371285162988913475, 371285163302211588, 371285163615951483, 371285164495718179, 371285165137700709, 371285166345657411, 371285167554168388]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 42010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 42000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362498321763029898, 362498346930826713⟩, ⟨(-554433507172931171), (-553718755675418897)⟩, true⟩

def words02 : List Nat := [371285168595834869, 371285168883286545, 371285169736771106, 371285170590947139, 371285171535783355, 371285171726626020, 371285171915862630, 371285172105573419, 371285172559601815, 371285172874637819]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 42020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 42000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362468722315577329, 362468747495821663⟩, ⟨689850559438186034, 690565834169352746⟩, true⟩

def words03 : List Nat := [371285173479353288, 371285174084614663, 371285174688161779, 371285174689545361, 371285174538973940, 371285174418519218, 371285174666665436, 371285174668049212, 371285174284477943, 371285173895302381]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 42030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 42000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483285064623736, 362483310257286580⟩, ⟨77671351860986933, 78387148726970883⟩, true⟩

def words04 : List Nat := [371285173505520678, 371285173474543577, 371285173770713238, 371285174202728186, 371285174551261273, 371285174552645202, 371285174152045114, 371285174158370420, 371285174397319134, 371285174398754523]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 42040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 42000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362485753924728759, 362485779129973525⟩, ⟨(-26156564912429051), (-25440238911030597)⟩, true⟩

def words05 : List Nat := [371285174355458838, 371285174295956406, 371285174465344996, 371285174466870252, 371285174544401378, 371285174641192551, 371285174738015062, 371285174739403105, 371285174272381412, 371285174288459747]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 42050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 42000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469005557971616, 362469030775573654⟩, ⟨678399947537311166, 679116793348085018⟩, true⟩

def words06 : List Nat := [371285174869116654, 371285174870501133, 371285174698217572, 371285174413941769, 371285174129122219, 371285173977281957, 371285173627562770, 371285173544404025, 371285173460788227, 371285173318795620]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 42060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 42000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493867597019356, 362493892827135646⟩, ⟨(-367610466372389920), (-366893094023502350)⟩, true⟩

def words07 : List Nat := [371285173117506743, 371285173300635271, 371285174048148239, 371285174121295789, 371285174122388950, 371285173964943659, 371285173881129250, 371285173882654846, 371285173883211932, 371285174091981456]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 42070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 42000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362492974275279166, 362492999517889455⟩, ⟨(-330101517454494521), (-329383619294972321)⟩, true⟩

def words08 : List Nat := [371285174292922648, 371285174294308142, 371285173939995909, 371285174046500487, 371285174293078050, 371285174294472609, 371285174035560275, 371285173775648323, 371285173818533742, 371285174006039061]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 42080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 42000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478720125112471, 362478745380201725⟩, ⟨269975336010702417, 270693759474394313⟩, true⟩

def words09 : List Nat := [371285174422470027, 371285174839419145, 371285175254393162, 371285175255785448, 371285175180833415, 371285175228887764, 371285175460712136, 371285175462123138, 371285175311896741, 371285175160711806]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 42090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 42000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 42000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk420
