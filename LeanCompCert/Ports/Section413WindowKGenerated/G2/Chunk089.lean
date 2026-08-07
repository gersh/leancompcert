import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk089

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360772090858934244, 360772091284772509⟩, ⟨(-1743568182822626073), (-1743565613329145757)⟩, true⟩

def state01 : KState := ⟨⟨360627736820261438, 360627737247115020⟩, ⟨(-459268063889367848), (-459265485354745956)⟩, true⟩

def words00 : List Nat := [360576220292143693, 360576221056549121, 360576227888145928, 360576234718241019, 360576234718330710, 360576233890744470, 360576226412239964, 360576212660913395, 360576198912653505, 360576198083681652]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 8900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 8900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360426302685145324, 360426303113003808⟩, ⟨1336074973945420203, 1336077561438848121⟩, true⟩

def words01 : List Nat := [360576198203377464, 360576198323064986, 360576198323160027, 360576192185555440, 360576173603493348, 360576151821342986, 360576130044047513, 360576114710643308, 360576104386740223, 360576087592985742]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 8910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 8900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360628123039678435, 360628123468544187⟩, ⟨(-465511229055813550), (-465508632572566276)⟩, true⟩

def words02 : List Nat := [360576070802973085, 360576055637392689, 360576050566380135, 360576054256361642, 360576054256461984, 360576044883907416, 360576023099642072, 360576009532870508, 360575995969105927, 360576000679094790]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 8920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 8900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574213113376442, 360574213543260609⟩, ⟨16453050355946492, 16455655938758604⟩, true⟩

def words03 : List Nat := [360576000679190411, 360575998110016159, 360576005400753365, 360576021631996245, 360576034674459997, 360576047714022287, 360576054116178849, 360576054426364431, 360576054426452571, 360576054220658681]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 8930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 8900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360639869464624685, 360639869895516928⟩, ⟨(-570727188375955329), (-570724573775915685)⟩, true⟩

def words04 : List Nat := [360576066212339003, 360576075024139517, 360576075024235438, 360576074143431965, 360576073262807651, 360576075367972310, 360576086885646968, 360576098400767703, 360576101786604327, 360576108910847516]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 8940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 8900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360741632498218781, 360741632930123221⟩, ⟨(-1481784079377690875), (-1481781455713341169)⟩, true⟩

def words05 : List Nat := [360576128410751407, 360576147906330085, 360576166898791753, 360576187440353501, 360576197708434537, 360576207974230383, 360576219374147185, 360576237075953911, 360576255535399779, 360576273990751127]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 8950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 8900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360603850409153348, 360603850842078441⟩, ⟨(-247640658955595353), (-247638026141223293)⟩, true⟩

def words06 : List Nat := [360576284256334745, 360576284256441922, 360576292519492893, 360576302822273784, 360576304386322646, 360576304386429884, 360576293650369792, 360576272811080840, 360576251976418376, 360576246558705214]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 8960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 8900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360541590207563862, 360541590641498968⟩, ⟨311882701903255237, 311885343782647705⟩, true⟩

def words07 : List Nat := [360576261967645397, 360576277373171391, 360576286389605584, 360576296009294606, 360576302027086155, 360576308043565950, 360576321428136356, 360576325616655050, 360576325616750756, 360576321748824430]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 8970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 8900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360501461477531300, 360501461912482091⟩, ⟨672279462899176677, 672282113904499205⟩, true⟩

def words08 : List Nat := [360576317881736998, 360576315516707433, 360576320927719886, 360576326337547839, 360576326337646838, 360576320965364326, 360576303351547377, 360576280778539447, 360576258210520988, 360576243015252336]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 8980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 8900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360443434726127061, 360443435162102894⟩, ⟨1193697301101456035, 1193699961327021143⟩, true⟩

def words09 : List Nat := [360576234698020413, 360576218498484302, 360576202302530890, 360576185377643358, 360576174706141892, 360576155270069835, 360576135838306157, 360576110228202807, 360576083229689904, 360576068491139230]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 8990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 8900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 8900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk089
