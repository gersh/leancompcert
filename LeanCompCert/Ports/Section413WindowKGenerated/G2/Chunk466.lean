import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk466

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360536740272942771, 360536753817514646⟩, ⟨2152602193776476020, 2153028711941213850⟩, true⟩

def state01 : KState := ⟨⟨360583377743621767, 360583391294229056⟩, ⟨(-20902946432863093), (-20476146987781257)⟩, true⟩

def words00 : List Nat := [360582955159460917, 360582954628040396, 360582954329089910, 360582954279062800, 360582954228990620, 360582953781154810, 360582953349474384, 360582952777524311, 360582952205411370, 360582951995630275]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 46600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 46600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360597520452105993, 360597534008820812⟩, ⟨(-680278021922674384), (-679850937776414704)⟩, true⟩

def words01 : List Nat := [360582951996205457, 360582951773616999, 360582951550924326, 360582951403876675, 360582951404412113, 360582951376019545, 360582951347558576, 360582951023628656, 360582951190873397, 360582951504417723]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 46610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 46600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360570207201757883, 360570220764492638⟩, ⟨593184986236037322, 593612351062568040⟩, true⟩

def words02 : List Nat := [360582952029808062, 360582952096155768, 360582952096725800, 360582951933597183, 360582951770371120, 360582951477272691, 360582951466271971, 360582951444013522, 360582951421695786, 360582951031510922]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 46620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 46600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360618042763276047, 360618056332050730⟩, ⟨(-1637752695975974848), (-1637325049477458442)⟩, true⟩

def words03 : List Nat := [360582950759032130, 360582950387540598, 360582950102305088, 360582950205462190, 360582950206052268, 360582949915989158, 360582949686096244, 360582949981041289, 360582950734267900, 360582951487611772]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 46630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 46600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360602284759088526, 360602298333965419⟩, ⟨(-902944908734584834), (-902516977599696248)⟩, true⟩

def words04 : List Nat := [360582951884062799, 360582951884703006, 360582952217876827, 360582952614120045, 360582952790955025, 360582952791595360, 360582952630294103, 360582952192396741, 360582951774229291, 360582952189668412]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 46640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 46600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk466
