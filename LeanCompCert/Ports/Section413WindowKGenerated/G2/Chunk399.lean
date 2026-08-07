import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk399

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360616966407269879, 360616976211517956⟩, ⟨(-1373076421446836082), (-1372812023416297016)⟩, true⟩

def state01 : KState := ⟨⟨360608258768177822, 360608268577512489⟩, ⟨(-1025601624611489507), (-1025337023600677095)⟩, true⟩

def words00 : List Nat := [360582572246890103, 360582573308535725, 360582574014884312, 360582574721257063, 360582575074458332, 360582575747341099, 360582576403798605, 360582577060322728, 360582577346091004, 360582577990366072]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 39900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 39900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360650241729857831, 360650251544290362⟩, ⟨(-2701283215772167565), (-2701018411279621275)⟩, true⟩

def words01 : List Nat := [360582579115011001, 360582580239757896, 360582581843703366, 360582583462179880, 360582584548684760, 360582585635174251, 360582587193443358, 360582589066492260, 360582590761885123, 360582592457311589]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 39910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 39900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360608483255152299, 360608493074741134⟩, ⟨(-1034408037201074589), (-1034143026843623575)⟩, true⟩

def words02 : List Nat := [360582593667951218, 360582594254205651, 360582594761401410, 360582595268733347, 360582595612463076, 360582595613003849, 360582595332431951, 360582594738296830, 360582594175376668, 360582594824588531]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 39920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 39900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360575778502676047, 360575788327352796⟩, ⟨271706100492274953, 271971314035950663⟩, true⟩

def words03 : List Nat := [360582595920973812, 360582597017407732, 360582597619796780, 360582597864555827, 360582597865016432, 360582597651850016, 360582597850465342, 360582597993905170, 360582597994386996, 360582597824449340]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 39930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 39900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590949142129209, 360590958971919011⟩, ⟨(-334225827442122084), (-333960409658095878)⟩, true⟩

def words04 : List Nat := [360582597654400750, 360582597987197921, 360582598815553884, 360582599643971824, 360582599935542805, 360582599936083778, 360582599661418057, 360582599719480195, 360582599719927354, 360582599721595913]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 39940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 39900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360575944732432317, 360575954567376640⟩, ⟨265319013040231196, 265584636772381266⟩, true⟩

def words05 : List Nat := [360582599722083085, 360582599528441114, 360582599765671951, 360582600511088666, 360582600978983649, 360582601446952669, 360582601532496974, 360582601533038133, 360582600995261711, 360582600829558132]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 39950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 39900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595791754458167, 360595801594506236⟩, ⟨(-527892302817854087), (-527626475114307753)⟩, true⟩

def words06 : List Nat := [360582600960601814, 360582601381308187, 360582601381802005, 360582601221380725, 360582601060879207, 360582600742041553, 360582600939745138, 360582601143374831, 360582601143861624, 360582601362460145]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 39960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 39900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360660165347000157, 360660175192156752⟩, ⟨(-3101221295432971644), (-3100955263516224590)⟩, true⟩

def words07 : List Nat := [360582602317652921, 360582603272956467, 360582604658801962, 360582606243512327, 360582607258244265, 360582608272965720, 360582609271642294, 360582610588153989, 360582612528676982, 360582614469225455]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 39970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 39900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360639785925213113, 360639795775525385⟩, ⟨(-2286580833554045529), (-2286314595488094503)⟩, true⟩

def words08 : List Nat := [360582616096957229, 360582617101972719, 360582618730958484, 360582620360033380, 360582621576630253, 360582622170619582, 360582622444753866, 360582622718931176, 360582623616980644, 360582625047224315]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 39980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 39900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360566362327230767, 360566372182649880⟩, ⟨649972773397480568, 650239215711725324⟩, true⟩

def words09 : List Nat := [360582626271457146, 360582627495724490, 360582628407426709, 360582628696734066, 360582628697188416, 360582628681243892, 360582628665133001, 360582628609753668, 360582628568890893, 360582628163042674]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 39990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 39900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 39900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk399
