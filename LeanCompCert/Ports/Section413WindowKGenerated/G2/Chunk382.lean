import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk382

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360577043393220309, 360577052347985645⟩, ⟨185132680631385384, 185363900775474862⟩, true⟩

def state01 : KState := ⟨⟨360613424253634914, 360613433213266185⟩, ⟨(-1204763413712543871), (-1204532007664911221)⟩, true⟩

def words00 : List Nat := [360581905236177388, 360581906134044301, 360581906839498599, 360581907545011338, 360581907684253331, 360581907840674340, 360581908200532114, 360581908560520117, 360581909213578512, 360581910039110447]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 38200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 38200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360599177765096550, 360599186729649226⟩, ⟨(-660414980638094721), (-660183386520402595)⟩, true⟩

def words01 : List Nat := [360581910463443436, 360581910887810777, 360581911117408331, 360581911869525261, 360581912448389682, 360581913027309404, 360581913263233196, 360581913263749330, 360581913485026097, 360581913937557957]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 38210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 38200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360569177970180786, 360569186939588685⟩, ⟨486333408327311333, 486565188036097839⟩, true⟩

def words02 : List Nat := [360581914782215680, 360581915265827987, 360581915343801689, 360581915421823184, 360581915422258518, 360581915080066846, 360581915080491616, 360581914918811149, 360581914757081619, 360581914252903781]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 38220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 38200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360633010592475658, 360633019566755051⟩, ⟨(-1954409098538662759), (-1954177132567954137)⟩, true⟩

def words03 : List Nat := [360581914270140487, 360581914620421480, 360581914820286953, 360581915036680959, 360581915037156822, 360581914669578768, 360581914616346336, 360581915270906072, 360581916607733011, 360581917944606887]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 38230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 38200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360606916396977529, 360606925376186966⟩, ⟨(-956679262706916201), (-956447108187978875)⟩, true⟩

def words04 : List Nat := [360581918744607615, 360581918865308721, 360581919501863624, 360581920138536387, 360581920602356133, 360581920874193505, 360581920874657631, 360581920550954528, 360581920227161245, 360581920876744129]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 38240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 38200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360581096260333363, 360581105244404030⟩, ⟨31082009681913889, 31314350167240955⟩, true⟩

def words05 : List Nat := [360581921897631026, 360581922918563141, 360581923504574040, 360581923694528202, 360581923694968034, 360581923417342256, 360581923328889588, 360581923726639292, 360581923727106375, 360581923706248443]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 38250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 38200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360624649170962603, 360624658159915740⟩, ⟨(-1635277012962867915), (-1635044485650078161)⟩, true⟩

def words06 : List Nat := [360581924345448157, 360581925540461152, 360581927251470992, 360581928962490297, 360581930090767625, 360581931063438246, 360581932261617456, 360581933459889443, 360581934237623388, 360581935354510863]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 38260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 38200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360623501534773899, 360623510528646516⟩, ⟨(-1591309702587086738), (-1591076986980947676)⟩, true⟩

def words07 : List Nat := [360581936129500056, 360581936904508461, 360581938360473213, 360581940155468549, 360581941770748596, 360581943386037001, 360581944660662717, 360581945257200014, 360581946343440139, 360581947429799022]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 38270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 38200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360629073132565074, 360629082131310659⟩, ⟨(-1804738388715674586), (-1804505486547722206)⟩, true⟩

def words08 : List Nat := [360581949196740358, 360581950285684613, 360581950848892371, 360581951412120732, 360581951472242204, 360581951879288231, 360581952966790912, 360581954054335757, 360581954800221856, 360581956031534009]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 38280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 38200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360647444943150271, 360647453946772905⟩, ⟨(-2508421962385351499), (-2508188873450607927)⟩, true⟩

def words09 : List Nat := [360581957220343448, 360581958409239260, 360581960106096629, 360581961408514147, 360581962027107584, 360581962645703921, 360581963245375411, 360581964275763460, 360581965986094736, 360581967696454360]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 38290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 38200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 38200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk382
