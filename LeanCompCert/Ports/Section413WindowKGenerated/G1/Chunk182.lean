import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk182

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362551287098501811, 362551291496694679⟩, ⟨(-1193444283760364979), (-1193390141126913651)⟩, true⟩

def state01 : KState := ⟨⟨362488792066289280, 362488796469532287⟩, ⟨(-55813678276976700), (-55759443704839350)⟩, true⟩

def words00 : List Nat := [371285727807631064, 371285728329656978, 371285731459684519, 371285734589651532, 371285737776740266, 371285737777301001, 371285736947849087, 371285735235758933, 371285734445625955, 371285734614405999]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 18200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 18200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362497308716147498, 362497313124434520⟩, ⟨(-210659234465312709), (-210604908015955503)⟩, true⟩

def words01 : List Nat := [371285737796235940, 371285740977939213, 371285744187071754, 371285744914055570, 371285746555879481, 371285748197815328, 371285752851085041, 371285753492894085, 371285754127761032, 371285754762763045]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 18210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 18200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362526449381184247, 362526453794502374⟩, ⟨(-741715752697016207), (-741661334555406205)⟩, true⟩

def words02 : List Nat := [371285756144908960, 371285756145526769, 371285758919836232, 371285761812175296, 371285764226158857, 371285764226722866, 371285764951953226, 371285766087972767, 371285770231960130, 371285772464100564]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 18220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 18200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362522860120970608, 362522864539407139⟩, ⟨(-676138341018228996), (-676083829542986274)⟩, true⟩

def words03 : List Nat := [371285774411156843, 371285776358193716, 371285781312606344, 371285784781585276, 371285788387365493, 371285791992952958, 371285795589914410, 371285796506653960, 371285798539276577, 371285800571996198]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 18230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 18200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362468511124361157, 362468515547803351⟩, ⟨315544468914284372, 315599071719238306⟩, true⟩

def words04 : List Nat := [371285803438359795, 371285803833614332, 371285804214912696, 371285804596349519, 371285805281070655, 371285805281689217, 371285806174250203, 371285807877018020, 371285808647041250, 371285808647623584]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 18240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 18200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362564650313325021, 362564654741846615⟩, ⟨(-1439405523458783123), (-1439350827929352287)⟩, true⟩

def words05 : List Nat := [371285809756177079, 371285811812313697, 371285816870700853, 371285817932103096, 371285818514792141, 371285819097609668, 371285822681886274, 371285825077219428, 371285829394670769, 371285833711895936]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 18250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 18200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362512993341073466, 362512997774674759⟩, ⟨(-496124858998162450), (-496070070687448376)⟩, true⟩

def words06 : List Nat := [371285838017718893, 371285839157143850, 371285841511396029, 371285843865678411, 371285846813918378, 371285846814481049, 371285845770726889, 371285844717452749, 371285845608133285, 371285847094871385]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 18260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 18200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362453550460354677, 362453554899023628⟩, ⟨590280349445876128, 590335230369059650⟩, true⟩

def words07 : List Nat := [371285849928164521, 371285852761380553, 371285855585361314, 371285855585924093, 371285854421480546, 371285853389270083, 371285852517570219, 371285852518137227, 371285850714918045, 371285848948824999]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 18270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 18200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362532277596093605, 362532282039803203⟩, ⟨(-849153949879771677), (-849098976788176431)⟩, true⟩

def words08 : List Nat := [371285847899435917, 371285847900059828, 371285849798558548, 371285851980425973, 371285853472525788, 371285853473089371, 371285852655523171, 371285853742579221, 371285857819603092, 371285860358277416]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 18280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 18200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362530226830026995, 362530231278868132⟩, ⟨(-811675696684808740), (-811620629710795616)⟩, true⟩

def words09 : List Nat := [371285862228477494, 371285864098650031, 371285867503695740, 371285869420529956, 371285872241214812, 371285875061811195, 371285877759942820, 371285878000034487, 371285880424094294, 371285882848197087]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 18290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 18200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 18200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk182
