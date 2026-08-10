import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk466A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk466B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk466A

def state06 : KState := ⟨⟨360527891804868689, 360527905385771213⟩, ⟨2567921986973675507, 2568350199234811791⟩, true⟩

def words05 : List Nat := [360582952676437255, 360582953163304463, 360582953420860343, 360582953421500673, 360582953220507905, 360582952643004186, 360582952065333119, 360582951411880504, 360582950503932836, 360582949324888976]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 46650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 46600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360555545411331327, 360555558998290836⟩, ⟨1277580881254360545, 1278009376163453199⟩, true⟩

def words06 : List Nat := [360582948145751125, 360582947215571658, 360582946733289094, 360582946709222355, 360582946685112439, 360582946202639278, 360582945261810060, 360582944533264813, 360582943804572143, 360582942957497253]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 46660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 46600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360540696111177466, 360540709704231525⟩, ⟨1970638293378475299, 1971067072751517407⟩, true⟩

def words07 : List Nat := [360582942371323524, 360582941511891792, 360582940652377692, 360582939864781952, 360582939310355656, 360582938635665051, 360582937960922348, 360582937057214371, 360582935695333511, 360582934791479844]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 46670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 46600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360574631743389847, 360574645342489372⟩, ⟨386273097257673453, 386702158861846031⟩, true⟩

def words08 : List Nat := [360582933887452480, 360582933441325088, 360582932847983860, 360582931879223295, 360582930910395427, 360582929825967179, 360582929007605860, 360582928647024799, 360582928286389274, 360582927676155293]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 46680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 46600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586551895274765, 360586565500422240⟩, ⟨(-170258787072862075), (-169829443059803967)⟩, true⟩

def words09 : List Nat := [360582927779487079, 360582928060387396, 360582928652774634, 360582928990526266, 360582928991121178, 360582928890129494, 360582928789025456, 360582928816588132, 360582928894981448, 360582928973515754]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 46690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 46600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 46600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk466B
