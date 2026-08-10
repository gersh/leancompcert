import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk617A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk617B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk617A

def state06 : KState := ⟨⟨362512368784874878, 362512424838665188⟩, ⟨(-1672817240606082311), (-1670478876783473921)⟩, true⟩

def words05 : List Nat := [371285375456969935, 371285375508139306, 371285375763910153, 371285375875307215, 371285375922078158, 371285375969478486, 371285376278508169, 371285376487627388, 371285376927007310, 371285377367335652]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 61750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 61700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486911322063907, 362486967394762591⟩, ⟨(-100515103558623120), (-98175571856712748)⟩, true⟩

def words06 : List Nat := [371285377727519532, 371285377738717299, 371285377921829098, 371285378105990757, 371285378304365620, 371285378306460761, 371285378186654046, 371285378068602862, 371285378019344091, 371285378047466017]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 61760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 61700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482656152789104, 362482712244342559⟩, ⟨162390403287162502, 164731099740303020⟩, true⟩

def words07 : List Nat := [371285378304564315, 371285378562487583, 371285378795522458, 371285378797618208, 371285378720495392, 371285378650885107, 371285378738398652, 371285378740503165, 371285378699862194, 371285378659035669]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 61770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 61700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480411450023953, 362480467560344153⟩, ⟨301197413609442449, 303539269569358627⟩, true⟩

def words08 : List Nat := [371285378836372618, 371285378961615616, 371285379302618597, 371285379644480545, 371285379940432163, 371285379942528056, 371285379909045510, 371285379931498234, 371285379991731672, 371285379993902486]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 61780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 61700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485887903269573, 362485944032705668⟩, ⟨(-37211942180502133), (-34868904953260511)⟩, true⟩

def words09 : List Nat := [371285379915969224, 371285379833969027, 371285379886999357, 371285379894334160, 371285379923070999, 371285379952625868, 371285379980545258, 371285379982656308, 371285379808324323, 371285379820072325]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 61790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 61700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 61700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk617B
