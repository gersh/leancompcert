import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk534

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483425985174963, 362483467407986059⟩, ⟨82764395568695521, 84258715601960711⟩, true⟩

def state01 : KState := ⟨⟨362477250319532282, 362477291758331998⟩, ⟨412578103193722286, 414073277100593400⟩, true⟩

def words00 : List Nat := [371285045578946562, 371285045580738312, 371285045435729803, 371285045222088568, 371285045007785536, 371285044807857573, 371285044479059894, 371285044491135064, 371285044492477898, 371285044487729126]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 53400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 53400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362505089152964110, 362505130607922615⟩, ⟨(-1074407687762386689), (-1072911650730247543)⟩, true⟩

def words01 : List Nat := [371285044548830014, 371285044755983466, 371285045256671928, 371285045400635440, 371285045489692764, 371285045579319925, 371285045744656232, 371285045772521169, 371285046149717084, 371285046527678325]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 53410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 53400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479438744630397, 362479480215773234⟩, ⟨295922309136706310, 297419210815979736⟩, true⟩

def words02 : List Nat := [371285046904934685, 371285046906727025, 371285046992039650, 371285047169223365, 371285047450484733, 371285047452277138, 371285047266925365, 371285047018819163, 371285046770007003, 371285046736656932]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 53420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 53400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362470683010135087, 362470724497446589⟩, ⟨763770439224753212, 765268204878531220⟩, true⟩

def words03 : List Nat := [371285046633716628, 371285046594712049, 371285046555102667, 371285046513061379, 371285046003923315, 371285045602967750, 371285045201118151, 371285045149737942, 371285044901942760, 371285044636010933]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 53430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 53400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362466240995606768, 362466282498960087⟩, ⟨1001284666223675740, 1002783289234145182⟩, true⟩

def words04 : List Nat := [371285044451112366, 371285044453106495, 371285044500581124, 371285044642071301, 371285044699568842, 371285044701362174, 371285044292306988, 371285044033243838, 371285043773249401, 371285043645624898]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 53440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 53400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362464165105063105, 362464206624780823⟩, ⟨1112324194865356913, 1113823692632959085⟩, true⟩

def words05 : List Nat := [371285043295981421, 371285042946956006, 371285042597194843, 371285042597855865, 371285042435226302, 371285042380651225, 371285042325441004, 371285042258119181, 371285041724071493, 371285041336577175]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 53450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 53400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362455333241375306, 362455374777054293⟩, ⟨1584543922867637781, 1586044274007694883⟩, true⟩

def words06 : List Nat := [371285040948076541, 371285040886685396, 371285040358749298, 371285039815408200, 371285039271388911, 371285038724335411, 371285038086169594, 371285037757013861, 371285037427300919, 371285037097495806]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 53460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 53400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362469323036661567, 362469364588595633⟩, ⟨836389019650356515, 837890240031274613⟩, true⟩

def words07 : List Nat := [371285036543985101, 371285036168929408, 371285035792954369, 371285035562546734, 371285034865878936, 371285034104575541, 371285033342586552, 371285032877279345, 371285032236261370, 371285031945365104]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 53470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 53400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362468028025193757, 362468069593307925⟩, ⟨905647352435121852, 907149438211952386⟩, true⟩

def words08 : List Nat := [371285031653755166, 371285031362598845, 371285030908831294, 371285030774311396, 371285030638932792, 371285030574937508, 371285030109216571, 371285029581901554, 371285029053853927, 371285028827523890]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 53480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 53400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362462066803404923, 362462108387659942⟩, ⟨1224622295536364723, 1226125244770299317⟩, true⟩

def words09 : List Nat := [371285028511693554, 371285028499550209, 371285028486826939, 371285028411771876, 371285028045921311, 371285027742300563, 371285027437726551, 371285027428147587, 371285027042918818, 371285026616534154]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 53490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 53400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 53400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk534
