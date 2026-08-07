import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk471

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482950309399787, 362482982209421720⟩, ⟨111264651870108729, 112279776049928507⟩, true⟩

def state01 : KState := ⟨⟨362465925615941754, 362465957529930865⟩, ⟨913225296556897185, 914241078662780437⟩, true⟩

def words00 : List Nat := [371285366174750440, 371285366176326529, 371285365927903228, 371285365587504763, 371285365246497676, 371285365044397019, 371285364618123759, 371285364443386283, 371285364268143399, 371285364048263763]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 47100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 47100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482803558779209, 362482835486926328⟩, ⟨118033519415139674, 119049968575686024⟩, true⟩

def words01 : List Nat := [371285363674942301, 371285363714383504, 371285363986420688, 371285363987986604, 371285363660557126, 371285363252306144, 371285362843469595, 371285362568010959, 371285362066108640, 371285362014273011]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 47110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 47100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362464820449675036, 362464852391956495⟩, ⟨965419170294332021, 966436285534218565⟩, true⟩

def words02 : List Nat := [371285361961826504, 371285361920251357, 371285361278735806, 371285361087376165, 371285360895209012, 371285360752043399, 371285360009140627, 371285359239218399, 371285358468678500, 371285358148067979]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 47120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 47100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362455214254684809, 362455246211070836⟩, ⟨1418208306338403956, 1419226086399595630⟩, true⟩

def words03 : List Nat := [371285357714069704, 371285357468963487, 371285357223365024, 371285356977017551, 371285356131064760, 371285355300868918, 371285354469875577, 371285354088474314, 371285353468419808, 371285352831486611]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 47130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 47100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483135828389428, 362483167798785832⟩, ⟨101830642245156116, 102849082826846538⟩, true⟩

def words04 : List Nat := [371285352193903059, 371285351734457326, 371285351055842993, 371285350826861085, 371285350597409153, 371285350265438881, 371285349528688353, 371285349241659989, 371285349113868085, 371285349115494779]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 47140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 47100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362489321755634995, 362489353740359483⟩, ⟨(-189820235845767470), (-188801119624249418)⟩, true⟩

def words05 : List Nat := [371285349070421825, 371285349033284412, 371285349336809256, 371285349507187821, 371285349814889852, 371285350123163614, 371285350337627684, 371285350339202726, 371285350321940451, 371285350408801114]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 47150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 47100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489037841623189, 362489069840310275⟩, ⟨(-176401508169263942), (-175381733399702040)⟩, true⟩

def words06 : List Nat := [371285350943360243, 371285350944927589, 371285350881064846, 371285350833982404, 371285350875526278, 371285350877283139, 371285351122928881, 371285351441294690, 371285351760811366, 371285351841255778]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 47160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 47100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489714391701880, 362489746404560924⟩, ⟨(-208293285641840971), (-207272842307904499)⟩, true⟩

def words07 : List Nat := [371285352296742299, 371285352753002935, 371285353330044593, 371285353361102578, 371285353362321744, 371285353245057084, 371285353210879745, 371285353212623249, 371285353167466638, 371285353262357328]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 47170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 47100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475242341506417, 362475274368505527⟩, ⟨474491942497116566, 475513053031173086⟩, true⟩

def words08 : List Nat := [371285353357599940, 371285353359169307, 371285352950039517, 371285352881168563, 371285352878751401, 371285352880319654, 371285352350916203, 371285351728903321, 371285351106293699, 371285350932460416]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 47180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 47100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471540561361680, 362471572602493152⟩, ⟨649289500247686452, 650311277758514780⟩, true⟩

def words09 : List Nat := [371285350848529920, 371285350978775975, 371285351109511253, 371285351111106861, 371285350868359465, 371285350764461030, 371285350964228419, 371285350965796924, 371285350673923751, 371285350383801596]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 47190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 47100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 47100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk471
