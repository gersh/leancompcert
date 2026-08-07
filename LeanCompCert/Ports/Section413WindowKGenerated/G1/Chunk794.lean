import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk794

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362506027306692088, 362506121786961786⟩, ⟨(-1666362228626192458), (-1661296558462953552)⟩, true⟩

def state01 : KState := ⟨⟨362492661935675044, 362492756440727094⟩, ⟨(-605096767810509338), (-600029129801380342)⟩, true⟩

def words00 : List Nat := [371285199161021369, 371285199251592556, 371285199491168906, 371285199732147550, 371285200020506129, 371285200098392230, 371285200153905233, 371285200210405195, 371285200347309076, 371285200445590383]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 79400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 79400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477643835789496, 362477738365501029⟩, ⟨587641288354785092, 592710884700326320⟩, true⟩

def words01 : List Nat := [371285200701021499, 371285200957538177, 371285201206776722, 371285201265875621, 371285201330779962, 371285201397061723, 371285201527252958, 371285201529996604, 371285201449142919, 371285201358257266]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 79410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 79400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492099946654539, 362492194500949548⟩, ⟨(-560489410407038629), (-555417861519279253)⟩, true⟩

def words02 : List Nat := [371285201303302171, 371285201306381524, 371285201441996070, 371285201591089120, 371285201711415926, 371285201714160085, 371285201719314503, 371285201803403442, 371285201952940890, 371285202043829290]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 79420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 79400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489039313661931, 362489133892976383⟩, ⟨(-317339508788447892), (-312265972478476978)⟩, true⟩

def words03 : List Nat := [371285202095539560, 371285202148184053, 371285202358041263, 371285202489743341, 371285202669003887, 371285202849337898, 371285203028709240, 371285203031453597, 371285203048997999, 371285203101917881]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 79430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 79400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487867109534132, 362487961713317059⟩, ⟨(-224202023089540618), (-219126542875892618)⟩, true⟩

def words04 : List Nat := [371285203253798565, 371285203297233165, 371285203303180609, 371285203309964330, 371285203364426013, 371285203367450659, 371285203451770152, 371285203563904583, 371285203667088734, 371285203704696955]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 79440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 79400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362500023392263130, 362500118020829314⟩, ⟨(-1190084437309483256), (-1185006987942296252)⟩, true⟩

def words05 : List Nat := [371285203899545516, 371285204095813228, 371285204354062238, 371285204402136752, 371285204424003066, 371285204446776935, 371285204534090338, 371285204576422204, 371285204765969058, 371285204956710536]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 79450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 79400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486072633272597, 362486167286628207⟩, ⟨(-81512535544065059), (-76433116285528439)⟩, true⟩

def words06 : List Nat := [371285205147167412, 371285205149913192, 371285205289169306, 371285205430160578, 371285205591111677, 371285205593857149, 371285205543956427, 371285205494934648, 371285205497682262, 371285205512946166]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 79460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 79400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362470010607993146, 362470105286109124⟩, ⟨1195036920253821158, 1200118307346698508⟩, true⟩

def words07 : List Nat := [371285205592634245, 371285205673441620, 371285205742791205, 371285205745537176, 371285205624048095, 371285205484012874, 371285205342590183, 371285205287038536, 371285205099394828, 371285204912522646]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 79470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 79400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486377624147267, 362486472326850933⟩, ⟨(-105847647110933345), (-100764305667359937)⟩, true⟩

def words08 : List Nat := [371285204724407129, 371285204695629137, 371285204649863071, 371285204696316507, 371285204703171717, 371285204705936558, 371285204570515400, 371285204571940898, 371285204689013919, 371285204707803905]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 79480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 79400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479074039350292, 362479168767068144⟩, ⟨474810591107119546, 479895921054845388⟩, true⟩

def words09 : List Nat := [371285204725783903, 371285204744726009, 371285204920611547, 371285205018543372, 371285205144570207, 371285205271668074, 371285205373105073, 371285205375851664, 371285205266302007, 371285205193748080]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 79490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 79400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 79400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk794
