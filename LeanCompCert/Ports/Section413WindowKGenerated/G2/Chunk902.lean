import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk902

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360606897928597604, 360606951417280685⟩, ⟨(-2255479292354204155), (-2252221282675307103)⟩, true⟩

def state01 : KState := ⟨⟨360616548267745892, 360616601768834562⟩, ⟨(-3126008751469686850), (-3122749622747770152)⟩, true⟩

def words00 : List Nat := [360581982712408472, 360581982978647963, 360581983367419761, 360581983756565540, 360581984114420860, 360581984477820405, 360581984762052630, 360581985046403059, 360581985321025579, 360581985706239671]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 90200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 90200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360593117710073257, 360593171223424912⟩, ⟨(-1012206833450572809), (-1008946598424597839)⟩, true⟩

def words01 : List Nat := [360581986073056196, 360581986440109731, 360581986745303409, 360581986972909430, 360581987169381095, 360581987366232680, 360581987685433131, 360581987915854849, 360581988040975136, 360581988166282733]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 90210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 90200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360615749123213196, 360615802648864421⟩, ⟨(-3054140318391811659), (-3050878973637820881)⟩, true⟩

def words02 : List Nat := [360581988386831268, 360581988701840120, 360581989013505354, 360581989325395058, 360581989533089202, 360581989643688347, 360581989876778457, 360581990110246423, 360581990401303804, 360581990777405191]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 90220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 90200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360600149965591965, 360600203503640490⟩, ⟨(-1646573538880982073), (-1643311075455455011)⟩, true⟩

def words03 : List Nat := [360581991079233243, 360581991381194321, 360581991643551800, 360581991971551874, 360581992268295030, 360581992565247838, 360581992768159349, 360581992848551546, 360581993051406629, 360581993254690950]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 90230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 90200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360596811071114997, 360596864621428242⟩, ⟨(-1345328239095028812), (-1342064668842001670)⟩, true⟩

def words04 : List Nat := [360581993468545608, 360581993560012568, 360581993570323254, 360581993580796050, 360581993581885864, 360581993621102598, 360581993804359973, 360581993987864245, 360581994097428839, 360581994263550302]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 90240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 90200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360593583826370288, 360593637388997710⟩, ⟨(-1054098216092255587), (-1050833534424505911)⟩, true⟩

def words05 : List Nat := [360581994426421688, 360581994589669530, 360581994794015230, 360581994875999125, 360581994877208599, 360581994835514622, 360581994829403107, 360581994962739170, 360581995092785085, 360581995223118488]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 90250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 90200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589684021764780, 360589737596800712⟩, ⟨(-702180394221764237), (-698914592500950403)⟩, true⟩

def words06 : List Nat := [360581995290690371, 360581995291993119, 360581995303317284, 360581995371212906, 360581995372322052, 360581995355549279, 360581995325955047, 360581995234874762, 360581995143549016, 360581995192346337]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 90260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 90200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360556016657144863, 360556070244465526⟩, ⟨2337233955665575828, 2340500866390706630⟩, true⟩

def words07 : List Nat := [360581995401795423, 360581995611519724, 360581995759454575, 360581995784967569, 360581995786060683, 360581995741455305, 360581995696476221, 360581995629663892, 360581995440186921, 360581995154372380]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 90270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 90200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588271201162111, 360588324800784925⟩, ⟨(-574844680657526375), (-571576659233317295)⟩, true⟩

def words08 : List Nat := [360581994868267533, 360581994705156982, 360581994632828963, 360581994647013704, 360581994648221186, 360581994558521874, 360581994471623053, 360581994389442197, 360581994345795011, 360581994417255744]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 90280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 90200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583569322316901, 360583622934365086⟩, ⟨(-150304951415405698), (-147035808044776816)⟩, true⟩

def words09 : List Nat := [360581994426952849, 360581994436791937, 360581994443442029, 360581994526206800, 360581994577813445, 360581994629631687, 360581994630803840, 360581994610801240, 360581994629327896, 360581994648874950]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 90290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 90200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 90200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk902
