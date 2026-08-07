import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk442

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362477754195159325, 362477782143081421⟩, ⟨343403128920686811, 344237773270950055⟩, true⟩

def state01 : KState := ⟨⟨362505878410760448, 362505906371750741⟩, ⟨(-899722035642045030), (-898886813610122942)⟩, true⟩

def words00 : List Nat := [371285570488302595, 371285570595531323, 371285571213807044, 371285571832635805, 371285572321456730, 371285572332752790, 371285572855163600, 371285573378342517, 371285574164546752, 371285574625949694]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 44200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 44200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484924122801372, 362484952097101710⟩, ⟨26838563380297824, 27674373917203080⟩, true⟩

def words01 : List Nat := [371285575086299951, 371285575547136217, 371285576239854392, 371285576678234277, 371285577195609765, 371285577713532977, 371285578168545551, 371285578170007356, 371285577943323773, 371285577930975912]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 44210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 44200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476887489097448, 362476915476418137⟩, ⟨382305780387275523, 383142166750853249⟩, true⟩

def words02 : List Nat := [371285578414940330, 371285578416402396, 371285578233140249, 371285578049803412, 371285577865897440, 371285577751213999, 371285577668195202, 371285577839960531, 371285577970196331, 371285577971709814]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 44220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 44200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486489078423102, 362486517078992908⟩, ⟨(-42430788046427843), (-41593815608451799)⟩, true⟩

def words03 : List Nat := [371285577844843060, 371285577914586163, 371285578128332541, 371285578129798864, 371285577823840075, 371285577433915843, 371285577070434926, 371285577072046232, 371285576891596724, 371285576914538930]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 44230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 44200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475231058859625, 362475259072603879⟩, ⟨455638522079342792, 456476077423486036⟩, true⟩

def words04 : List Nat := [371285576936376806, 371285576937849323, 371285576527953811, 371285576555588282, 371285576737305300, 371285576738768090, 371285576239901612, 371285575628617375, 371285575016753791, 371285574916161472]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 44240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 44200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362461831985937537, 362461860012844066⟩, ⟨1048669516925509105, 1049507654766932167⟩, true⟩

def words05 : List Nat := [371285574684037937, 371285574653320018, 371285574622131617, 371285574466233032, 371285573991257627, 371285573627579644, 371285573408155818, 371285573409618990, 371285572875372758, 371285572341239162]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 44250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 44200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483288966782224, 362483317006805927⟩, ⟨98874871549856550, 99713590023404230⟩, true⟩

def words06 : List Nat := [371285571806510743, 371285571485681248, 371285570911214256, 371285570847654308, 371285570783624084, 371285570643566910, 371285569822961165, 371285569513334924, 371285569401719215, 371285569403237448]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 44260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 44200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493790473616217, 362493818526991749⟩, ⟨(-366073611202529685), (-365234301577659671)⟩, true⟩

def words07 : List Nat := [371285569353464422, 371285569300854799, 371285569703483084, 371285569948503124, 371285570088797384, 371285570229604405, 371285570369594557, 371285570371065562, 371285570234687056, 371285570422803098]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 44270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 44200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491787444068081, 362491815510498424⟩, ⟨(-277285384388671078), (-276445496629627772)⟩, true⟩

def words08 : List Nat := [371285571119953822, 371285571394036334, 371285571634058117, 371285571874548789, 371285572158332411, 371285572273582867, 371285572826523842, 371285573380055485, 371285573795353145, 371285573937794498]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 44280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 44200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362516587478788868, 362516615558432262⟩, ⟨(-1375799439841853666), (-1374958966809119496)⟩, true⟩

def words09 : List Nat := [371285574412663238, 371285574888247420, 371285575872701376, 371285576178282133, 371285576405227944, 371285576632660185, 371285577122411463, 371285577406708988, 371285578108338960, 371285578810575349]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 44290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 44200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 44200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk442
