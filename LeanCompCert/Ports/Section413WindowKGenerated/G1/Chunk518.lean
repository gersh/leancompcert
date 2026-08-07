import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk518

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496973450920948, 362497012333149110⟩, ⟨(-622736888280606936), (-621376214284330898)⟩, true⟩

def state01 : KState := ⟨⟨362481234582809072, 362481273480669161⟩, ⟨192561489360049988, 193922973171328130⟩, true⟩

def words00 : List Nat := [371285017113025730, 371285017114759813, 371285017051705443, 371285017207782289, 371285017428602539, 371285017430336379, 371285017154910797, 371285016808523601, 371285016461421488, 371285016444829967]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 51800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 51800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362485232694795292, 362485271608239938⟩, ⟨(-14526456969919713), (-13164165642081375)⟩, true⟩

def words01 : List Nat := [371285016647361943, 371285016922814631, 371285017168015617, 371285017169779976, 371285017122063810, 371285017140113969, 371285017529306774, 371285017563718928, 371285017569920286, 371285017576753821]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 51810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 51800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492648138649166, 362492687067633381⟩, ⟨(-398862669505125749), (-397499572837313777)⟩, true⟩

def words02 : List Nat := [371285017630412813, 371285017632341671, 371285017645456032, 371285017792688464, 371285017887319205, 371285017889053830, 371285017487554321, 371285017458924152, 371285017770586708, 371285017920350147]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 51820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 51800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489255186733974, 362489294131557212⟩, ⟨(-222970938763947020), (-221607021084758616)⟩, true⟩

def words03 : List Nat := [371285018070002636, 371285018220249387, 371285018605024058, 371285018826696687, 371285019062430305, 371285019298781390, 371285019506514989, 371285019508250173, 371285019302564646, 371285019387221942]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 51830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 51800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490075290000913, 362490114250295859⟩, ⟨(-265437611439252907), (-264072891626024293)⟩, true⟩

def words04 : List Nat := [371285019787634079, 371285019935005657, 371285020010369974, 371285020086300669, 371285020276343601, 371285020281476800, 371285020623463330, 371285020966156804, 371285021232260348, 371285021332287990]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 51840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 51800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362527122216793158, 362527161192760060⟩, ⟨(-2186507076223112052), (-2185141543739083264)⟩, true⟩

def words05 : List Nat := [371285021706542152, 371285022081660427, 371285022827439215, 371285023241190561, 371285023591844611, 371285023943080140, 371285024539981330, 371285024982939980, 371285025796617130, 371285026611017728]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 51850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 51800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492372057511786, 362492411049159330⟩, ⟨(-384297136737896810), (-382930790977299064)⟩, true⟩

def words06 : List Nat := [371285027403704119, 371285027701498628, 371285028118220054, 371285028535817521, 371285028880344601, 371285028882080599, 371285028731455792, 371285028543759102, 371285028537183611, 371285028681536241]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 51860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 51800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477413836470390, 362477452843755306⟩, ⟨391775895860383662, 393143052812219788⟩, true⟩

def words07 : List Nat := [371285029196367973, 371285029711909503, 371285030226884680, 371285030317018918, 371285030514002845, 371285030711849106, 371285031061869554, 371285031063606315, 371285030918714720, 371285030774611363]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 51870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 51800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475040588535763, 362475079611370351⟩, ⟨514979949997608808, 516347913745195606⟩, true⟩

def words08 : List Nat := [371285030762190110, 371285030764103792, 371285030893250527, 371285031076020593, 371285031202766494, 371285031204503488, 371285030836245417, 371285030609214599, 371285030426950328, 371285030428748366]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 51880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 51800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493411606626057, 362493450645286653⟩, ⟨(-438416007267526989), (-437047222228006077)⟩, true⟩

def words09 : List Nat := [371285030238306558, 371285029968490949, 371285029797322707, 371285029799257783, 371285029735982084, 371285029737510007, 371285029738428155, 371285029739975785, 371285029694747616, 371285029859131705]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 51890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 51800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 51800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk518
