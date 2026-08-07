import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk617

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362513214906814460, 362513270847440634⟩, ⟨(-1723640632524369968), (-1721309254329466064)⟩, true⟩

def state01 : KState := ⟨⟨362491748942182898, 362491804901670373⟩, ⟨(-399131638503474596), (-396799096470258894)⟩, true⟩

def words00 : List Nat := [371285373699140545, 371285373792075103, 371285374147261683, 371285374503563235, 371285374825210432, 371285374827303428, 371285374798901816, 371285374750867767, 371285374837739439, 371285374944345581]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 61700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 61700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476317818737940, 362476373797100026⟩, ⟨553254065984617592, 555587772865370420⟩, true⟩

def words01 : List Nat := [371285375171389990, 371285375399345529, 371285375627439883, 371285375629533482, 371285375542262143, 371285375535057567, 371285375779913148, 371285375782006508, 371285375686738046, 371285375543257923]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 61710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 61700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362491756295160861, 362491812292266379⟩, ⟨(-399670290943795050), (-397335427122955276)⟩, true⟩

def words02 : List Nat := [371285375398842942, 371285375367155246, 371285375316472203, 371285375424070620, 371285375485829428, 371285375487959473, 371285375340317979, 371285375351118709, 371285375623533253, 371285375729969917]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 61720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 61700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487363698371725, 362487419714571419⟩, ⟨(-128483279384461293), (-126147236785750791)⟩, true⟩

def words03 : List Nat := [371285375828201160, 371285375927117964, 371285376133112675, 371285376209241755, 371285376363549476, 371285376518672665, 371285376672108706, 371285376674202662, 371285376510818122, 371285376546550400]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 61730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 61700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362472111870197166, 362472167905040671⟩, ⟨813239253849061990, 815576447612883440⟩, true⟩

def words04 : List Nat := [371285376775241812, 371285376777335847, 371285376656472827, 371285376487231824, 371285376317161251, 371285376207555991, 371285375979967852, 371285375861128657, 371285375741620552, 371285375620791487]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 61740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 61700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk617
