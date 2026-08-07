import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk057

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362481509539872013, 362481509927515340⟩, ⟨(-6290466506201832), (-6288969494685772)⟩, true⟩

def state01 : KState := ⟨⟨362308217816256282, 362308218205307765⟩, ⟨982886907880147055, 982888412925605391⟩, true⟩

def words00 : List Nat := [371280437570975063, 371280437571133312, 371280427526516688, 371280417499424332, 371280407475787222, 371280397740074994, 371280372962694817, 371280368272178114, 371280363583253661, 371280352778499640]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 5700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 5700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471426971968339, 362471427362456993⟩, ⟨50643053304391011, 50644566563173501⟩, true⟩

def words01 : List Nat := [371280322991389241, 371280323345123211, 371280346256222025, 371280346256380577, 371280328520572330, 371280305680664316, 371280290437902316, 371280290438076746, 371280282855642230, 371280281307660346]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 5710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 5700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362312108406304236, 362312108798224284⟩, ⟨962253711713398078, 962255233167169658⟩, true⟩

def words02 : List Nat := [371280279760157181, 371280278232135395, 371280236171651609, 371280215279173241, 371280194393915891, 371280181303611761, 371280143518846758, 371280103512192428, 371280063519438543, 371280041648689759]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 5720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 5700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362214919875230805, 362214920268583902⟩, ⟨1519911474828756731, 1519913004501298597⟩, true⟩

def words03 : List Nat := [371280012346259848, 371279998231376095, 371279984121368173, 371279965332483919, 371279914475165186, 371279868167522000, 371279821875939508, 371279805806154583, 371279759614021589, 371279713474943014]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 5730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 5700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362507141544429567, 362507141939209661⟩, ⟨(-158256040012812271), (-158254502141974653)⟩, true⟩

def words04 : List Nat := [371279667351866268, 371279651417762609, 371279632866925620, 371279638675038861, 371279639378614562, 371279639378775172, 371279617815983574, 371279608310629475, 371279619416932598, 371279624202791304]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 5740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 5700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362449760116301589, 362449760512538934⟩, ⟨172325762412269989, 172327308669601465⟩, true⟩

def words05 : List Nat := [371279628084652026, 371279631965217046, 371279650972495042, 371279659154790667, 371279676495819702, 371279693830883820, 371279708755472025, 371279708755631853, 371279683642858526, 371279678448071851]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 5750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 5700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362326974302929542, 362326974700592879⟩, ⟨880212393074537464, 880213947553114770⟩, true⟩

def words06 : List Nat := [371279680179423754, 371279680179583753, 371279654918284928, 371279626618227801, 371279598327928062, 371279579233178238, 371279546877667445, 371279539581447538, 371279532287700156, 371279524778158411]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 5760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 5700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362510975391589348, 362510975790700118⟩, ⟨(-182592819497586482), (-182591256660106254)⟩, true⟩

def words07 : List Nat := [371279498344360471, 371279494332719811, 371279506728062054, 371279506728222378, 371279483351091715, 371279448898401704, 371279414457572187, 371279404412359846, 371279385607708162, 371279391072371091]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 5770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 5700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362426875446102577, 362426875846661255⟩, ⟨303872715033118878, 303874286247060594⟩, true⟩

def words08 : List Nat := [371279392928549187, 371279392928712369, 371279380132478536, 371279388588130819, 371279401007459578, 371279401007621126, 371279387377032788, 371279373695091793, 371279360017816158, 371279358452230696]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 5780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 5700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362275089976700941, 362275090378710302⟩, ⟨1184337250045438665, 1184338829666102927⟩, true⟩

def words09 : List Nat := [371279369964841646, 371279390533204180, 371279411044298692, 371279411044459475, 371279392032337143, 371279378363963965, 371279364700221781, 371279357133849110, 371279321940808814, 371279286728652734]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 5790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 5700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 5700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk057
