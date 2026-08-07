import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk387

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362501302022564131, 362501323218098469⟩, ⟨(-627443000479781645), (-626888688021044769)⟩, true⟩

def state01 : KState := ⟨⟨362481957686118730, 362481978892941849⟩, ⟨121282553706587312, 121837303099285298⟩, true⟩

def words00 : List Nat := [371285125780644935, 371285125830595009, 371285125831559929, 371285125693085106, 371285125617900860, 371285125619294978, 371285125748059648, 371285126146873838, 371285126329043329, 371285126330376602]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 38700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 38700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362523153361271729, 362523174579546375⟩, ⟨(-1473547030229149150), (-1472991837490405234)⟩, true⟩

def words01 : List Nat := [371285126835551264, 371285127422667058, 371285128675975961, 371285129291340547, 371285129775991942, 371285130260999562, 371285131021144758, 371285131450154353, 371285132433533331, 371285133417451120]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 38710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 38700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362524701715479709, 362524722945165556⟩, ⟨(-1533581247943615453), (-1533025613304140163)⟩, true⟩

def words02 : List Nat := [371285134399991233, 371285134696598045, 371285135659292316, 371285136622603462, 371285137784046339, 371285138325036866, 371285138848761752, 371285139372884835, 371285140562795003, 371285141586220418]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 38720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 38700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362503550945544243, 362503572186638553⟩, ⟨(-714300978932872833), (-713744902385541133)⟩, true⟩

def words03 : List Nat := [371285142689071953, 371285143792350593, 371285144894475035, 371285145196754184, 371285145635284132, 371285146074446950, 371285147179038513, 371285147730818722, 371285148207359043, 371285148684344200]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 38730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 38700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362518917519968766, 362518938772391181⟩, ⟨(-1309658698332054545), (-1309102182876139785)⟩, true⟩

def words04 : List Nat := [371285149646776899, 371285150376455944, 371285151388815986, 371285152401647890, 371285153195961243, 371285153197228415, 371285153676559032, 371285154250184883, 371285155488938314, 371285156362056580]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 38740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 38700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362491738106588811, 362491759370587581⟩, ⟨(-256257843825760864), (-255700879728898326)⟩, true⟩

def words05 : List Nat := [371285157234037977, 371285158106443400, 371285159166467539, 371285159893862245, 371285160684149669, 371285161474868088, 371285162264517097, 371285162265784524, 371285162339079418, 371285162510864435]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 38750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 38700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489887223260665, 362489908498547812⟩, ⟨(-184483337210051360), (-183925935516648370)⟩, true⟩

def words06 : List Nat := [371285163287858824, 371285163289126304, 371285163179934973, 371285163033831147, 371285162942558261, 371285162943985448, 371285163373952150, 371285163922434521, 371285164470010509, 371285164593682923]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 38760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 38700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493567099561289, 362493588386313744⟩, ⟨(-327146255522881713), (-326588409261901339)⟩, true⟩

def words07 : List Nat := [371285165316063463, 371285166039063761, 371285166911200876, 371285166912468909, 371285166898997174, 371285166683409827, 371285166666802433, 371285166668201116, 371285166816819912, 371285167035413512]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 38770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 38700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486964438705884, 362486985736900872⟩, ⟨(-71143594192117239), (-70585304131343867)⟩, true⟩

def words08 : List Nat := [371285167267311114, 371285167268579477, 371285166625243893, 371285166636964697, 371285166850570406, 371285166851848418, 371285166602725873, 371285166223357007, 371285166057582935, 371285166105952164]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 38780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 38700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489943262810211, 362489964572440451⟩, ⟨(-186570920931608527), (-186012187239750983)⟩, true⟩

def words09 : List Nat := [371285166817955581, 371285167530455288, 371285168205545811, 371285168468238246, 371285168933103278, 371285169398557036, 371285170199790589, 371285170317937761, 371285170442459693, 371285170567460174]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 38790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 38700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 38700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk387
