import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk679

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360555260476140209, 360555290118812386⟩, ⟨1868557816666263826, 1869917387284762540⟩, true⟩

def state01 : KState := ⟨⟨360571217328335791, 360571246980051638⟩, ⟨785047193675635721, 786407378405894441⟩, true⟩

def words00 : List Nat := [360582828998062326, 360582828810199125, 360582828731220146, 360582828685745778, 360582828640207113, 360582828410447169, 360582828086191057, 360582827716034989, 360582827345608554, 360582827121097227]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 67900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 67900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360571378607398400, 360571408268253557⟩, ⟨774111338353688709, 775472143778998691⟩, true⟩

def words01 : List Nat := [360582826951432623, 360582826673342252, 360582826395071787, 360582826387492276, 360582826388297714, 360582826341460243, 360582826294519437, 360582826139188590, 360582825869653067, 360582825702643708]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 67910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 67900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360550816755344175, 360550846425244350⟩, ⟨2170674761955860128, 2172036181765059854⟩, true⟩

def words02 : List Nat := [360582825535334914, 360582825313517613, 360582824875083728, 360582824327793604, 360582823780375013, 360582823038754869, 360582822405897795, 360582821989724933, 360582821573442907, 360582821048853434]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 67920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 67900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585559813522583, 360585589492481738⟩, ⟨(-189629409763089036), (-188267374533800540)⟩, true⟩

def words03 : List Nat := [360582820578936641, 360582820325770665, 360582820072316369, 360582820035488181, 360582819782159301, 360582819325811201, 360582818869286590, 360582818542600517, 360582818408553756, 360582818450334378]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 67930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 67900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360575851528602524, 360575881216722355⟩, ⟨470011963020760614, 471374620670080760⟩, true⟩

def words04 : List Nat := [360582818451197464, 360582818390620352, 360582818614305448, 360582818838267841, 360582818978780795, 360582818979740969, 360582818975077599, 360582818780915147, 360582818586590259, 360582818297232585]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 67940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 67900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360564237144816624, 360564266841973751⟩, ⟨1259266752263027019, 1260630024043071253⟩, true⟩

def words05 : List Nat := [360582818195923060, 360582818158363150, 360582818120698841, 360582817974776581, 360582817683904246, 360582817338566599, 360582816992939173, 360582816863793950, 360582816702279240, 360582816430320471]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 67950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 67900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585096422591430, 360585126128827361⟩, ⟨(-158425354599014697), (-157061465778519293)⟩, true⟩

def words06 : List Nat := [360582816158152154, 360582816172617905, 360582816173409748, 360582816155244370, 360582816137001516, 360582815921340740, 360582815635399857, 360582815565986121, 360582815496288404, 360582815415938357]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 67960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 67900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585782066580323, 360585811781956243⟩, ⟨(-205046707274105086), (-203682197164005678)⟩, true⟩

def words07 : List Nat := [360582815416793982, 360582815326876071, 360582815309201540, 360582815491530068, 360582815618775120, 360582815746173029, 360582815747055949, 360582815700425664, 360582815573187040, 360582815618364004]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 67970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 67900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360597876638712277, 360597906363130675⟩, ⟨(-1027336785370966064), (-1025971660508066334)⟩, true⟩

def words08 : List Nat := [360582815834854845, 360582815957107496, 360582815957966543, 360582815911375562, 360582815864612593, 360582815771491043, 360582815996428830, 360582816221545368, 360582816324471477, 360582816547412300]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 67980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 67900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360609644582518554, 360609674316013074⟩, ⟨(-1827610280023538349), (-1826244538029301089)⟩, true⟩

def words09 : List Nat := [360582816656902976, 360582816766653417, 360582817092197568, 360582817201886467, 360582817202780723, 360582817128062678, 360582817134731802, 360582817381958802, 360582817777690692, 360582818173632384]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 67990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 67900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 67900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk679
