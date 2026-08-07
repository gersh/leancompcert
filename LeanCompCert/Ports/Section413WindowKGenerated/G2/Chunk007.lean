import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk007

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360037005650955589, 360037005652891774⟩, ⟨299719003253000405, 299719004179886277⟩, true⟩

def state01 : KState := ⟨⟨361590559566463017, 361590559568459416⟩, ⟨(-793276227230032945), (-793276226260692811)⟩, true⟩

def words00 : List Nat := [360465901169386647, 360468507306983951, 360471353521025990, 360474191660703166, 360475282926537194, 360475282926543589, 360474529418166581, 360473472752883399, 360473269108930688, 360474840544182774]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360472177209138965, 360472177211197281⟩, ⟨5055586016223801, 5055587029839399⟩, true⟩

def words01 : List Nat := [360475330211749759, 360475818505775836, 360476644715340238, 360479221275005178, 360480185169426564, 360481146375161613, 360481146375167444, 360481072073853695, 360479208625695859, 360479198859849836]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360476524637615564, 360476524639736144⟩, ⟨(-5462997967232897), (-5462996908469521)⟩, true⟩

def words02 : List Nat := [360479189121091536, 360478917933302274, 360477786196822389, 360475657036874737, 360473533750470744, 360470586191562682, 360469380139317920, 360469680797375979, 360469680797381933, 360469051319751918]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨361448784874255923, 361448784876439327⟩, ⟨(-725887856668411130), (-725887855563465166)⟩, true⟩

def words03 : List Nat := [360469219442682748, 360469387106889840, 360471330199424400, 360471553824540981, 360471553824547189, 360470028433748743, 360468507182408536, 360466949416121197, 360467855341887208, 360469179133438700]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360636026902354993, 360636026904602892⟩, ⟨(-123237529844452019), (-123237528691453825)⟩, true⟩

def words04 : List Nat := [360469238605056740, 360469622572667904, 360471742545384925, 360473856826901923, 360475364284187365, 360475364284194144, 360475206758300445, 360474103614846002, 360473003417033773, 360471928996891236]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨359749434318034280, 359749434320346808⟩, ⟨555380112429566949, 555380113631367617⟩, true⟩

def words05 : List Nat := [360473844193060424, 360475754302388460, 360476722693323013, 360477717502896266, 360478149713613618, 360478580782428753, 360480678276349330, 360481160425249621, 360481160425255825, 360480197627756503]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨361655179659113336, 361655179661491742⟩, ⟨(-905483811445611253), (-905483810193409051)⟩, true⟩

def words06 : List Nat := [360479937237204983, 360481563907497167, 360483020493869022, 360484473272173133, 360484473272179613, 360484278268246965, 360482505082855029, 360480868052641244, 360479235279981362, 360480751892109889]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360322427810042530, 360322427812488221⟩, ⟨133032981479738014, 133032982784092614⟩, true⟩

def words07 : List Nat := [360481387615320421, 360482021693710996, 360484258436075219, 360487463083501070, 360489999905385869, 360492530197485728, 360493639791824551, 360493639791831649, 360493201859699782, 360492982918621674]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360867621626779295, 360867621629292573⟩, ⟨(-299014680318787827), (-299014678961367757)⟩, true⟩

def words08 : List Nat := [360492764538209952, 360492516747862241, 360492366359360689, 360491222811221927, 360490082176580387, 360488426910462468, 360488425594973021, 360489195769695670, 360489195769702106, 360489600543374283]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨361000403249862782, 361000403252445137⟩, ⟨(-411933333358337970), (-411933331945999998)⟩, true⟩

def words09 : List Nat := [360489938273008860, 360490275150868355, 360490790573137056, 360490790573144328, 360489833396813131, 360487513534316992, 360485199493306348, 360484842136103605, 360485486587505038, 360486129429790955]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk007
