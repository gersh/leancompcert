import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk117

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362446962433291500, 362446964181221270⟩, ⟨455795981740232900, 455809823021882204⟩, true⟩

def state01 : KState := ⟨⟨362404742524314871, 362404744275328113⟩, ⟨950165675435642322, 950179552810201706⟩, true⟩

def words00 : List Nat := [371285922890321950, 371285922890668212, 371285917126794195, 371285911081666069, 371285905037426612, 371285901205395573, 371285893732813001, 371285891448866550, 371285889165199716, 371285886850290556]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 11700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 11700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362468463679501423, 362468465433657271⟩, ⟨203318161998311119, 203332076188288091⟩, true⟩

def words01 : List Nat := [371285879921781887, 371285875707852599, 371285871494461843, 371285869748660094, 371285858325841942, 371285844730748849, 371285831137839315, 371285824790228556, 371285816066953173, 371285814586915658]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 11710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 11700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362419973385274951, 362419975142560125⟩, ⟨771518877309705728, 771532828191452244⟩, true⟩

def words02 : List Nat := [371285813106998573, 371285811643302996, 371285800515144200, 371285794661987702, 371285788809668093, 371285782973743619, 371285773229623695, 371285763457182956, 371285753686264324, 371285749467214128]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 11720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 11700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362325121528967663, 362325123289381177⟩, ⟨1885155954000594618, 1885169941594035990⟩, true⟩

def words03 : List Nat := [371285745478316554, 371285747096167890, 371285748730523966, 371285748730871400, 371285740721463323, 371285734923905745, 371285729127152644, 371285726193429415, 371285713623911875, 371285699945394298]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 11730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 11700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362440584097132720, 362440585860660338⟩, ⟨529316667852479853, 529330692021432083⟩, true⟩

def words04 : List Nat := [371285686269056893, 371285678562443240, 371285668184215906, 371285665011926322, 371285661840067713, 371285657386205835, 371285646917281182, 371285641062617434, 371285635280897361, 371285635281257907]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 11740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 11700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362374717550763509, 362374719317470536⟩, ⟨1303736052141369281, 1303750113684115605⟩, true⟩

def words05 : List Nat := [371285631447851593, 371285627644234797, 371285623841124505, 371285621611317171, 371285615794088423, 371285612189969451, 371285608586350136, 371285605017956272, 371285591849870027, 371285582422375648]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 11750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 11700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362292543813917192, 362292545583724687⟩, ⟨2270565849705889463, 2270579947726505985⟩, true⟩

def words06 : List Nat := [371285572996279897, 371285568855124083, 371285555122452892, 371285541355171741, 371285527590101956, 371285515142371023, 371285499573384852, 371285485722851158, 371285471874551494, 371285458068663218]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 11760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 11700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498534224193507, 362498535997150363⟩, ⟨(-155016913928628668), (-155002778824373924)⟩, true⟩

def words07 : List Nat := [371285441680107299, 371285431270718555, 371285420862919000, 371285416498596663, 371285407249128132, 371285396708003734, 371285386168523451, 371285382783726703, 371285377866131052, 371285378983414316]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 11770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 11700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362445256079806435, 362445257855916915⟩, ⟨472462701366252813, 472476873636498885⟩, true⟩

def words08 : List Nat := [371285378983684980, 371285377001998106, 371285366921606405, 371285363991243145, 371285361061203330, 371285360344501823, 371285351496335187, 371285342692547547, 371285333890109346, 371285332230271156]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 11780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 11700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362365147643717791, 362365149422975527⟩, ⟨1417603706508185355, 1417617915900698647⟩, true⟩

def words09 : List Nat := [371285330132267645, 371285331432916109, 371285332778012197, 371285332778361456, 371285324584033798, 371285316511070480, 371285308439300370, 371285306209475425, 371285296716071065, 371285286534492536]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 11790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 11700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 11700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk117
