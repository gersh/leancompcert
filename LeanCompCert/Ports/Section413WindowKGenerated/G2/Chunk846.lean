import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk846

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360585072418673343, 360585119239243852⟩, ⟨(-228452154826838604), (-225777152629589088)⟩, true⟩

def state01 : KState := ⟨⟨360579153180457939, 360579200012485117⟩, ⟨272358224008269781, 275034195497557863⟩, true⟩

def words00 : List Nat := [360582450564361780, 360582450622635820, 360582450623718272, 360582450611984835, 360582450600047760, 360582450592534355, 360582450643760613, 360582450695216091, 360582450696330991, 360582450623470788]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 84600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 84600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360588207077598527, 360588253921093029⟩, ⟨(-493733702366195513), (-491056760568879757)⟩, true⟩

def words01 : List Nat := [360582450663780120, 360582450742871779, 360582450936611604, 360582450991066701, 360582450992187457, 360582450927562189, 360582450862690624, 360582450781063283, 360582450838287273, 360582450908122622]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 84610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 84600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360582885866256090, 360582932721345572⟩, ⟨(-43576616183400183), (-40898693165375223)⟩, true⟩

def words02 : List Nat := [360582450909205537, 360582450893778898, 360582450804360053, 360582450634066084, 360582450463454113, 360582450257502030, 360582450074743102, 360582449822204033, 360582449569438087, 360582449462336871]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 84620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 84600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360567055516093912, 360567102382615771⟩, ⟨1296313105920656861, 1298991996519460595⟩, true⟩

def words03 : List Nat := [360582449608538727, 360582449754970313, 360582449831302886, 360582449886684052, 360582449906706750, 360582449927063917, 360582449928063697, 360582449924675555, 360582449821619737, 360582449641553856]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 84630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 84600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360578976115012929, 360579022993008137⟩, ⟨287272434972146757, 289952296731649967⟩, true⟩

def words04 : List Nat := [360582449461214895, 360582449378215637, 360582449364873953, 360582449325158776, 360582449285350645, 360582449114637169, 360582448804295702, 360582448590090154, 360582448375532649, 360582448300707271]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 84640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 84600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360589953010178234, 360589999899769437⟩, ⟨(-642024363903794178), (-639343520486316738)⟩, true⟩

def words05 : List Nat := [360582448261346379, 360582448104043183, 360582447946510721, 360582447979858211, 360582447996820537, 360582448013995572, 360582448015078769, 360582447962344980, 360582448002317959, 360582448092910479]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 84650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 84600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360567149423609773, 360567196324644036⟩, ⟨1288631154045753004, 1291312966289778362⟩, true⟩

def words06 : List Nat := [360582448268184413, 360582448304338997, 360582448305434000, 360582448251929337, 360582448198243420, 360582448014439722, 360582447912483470, 360582447789646500, 360582447666684784, 360582447452154250]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 84660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 84600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360578916027162247, 360578962939691017⟩, ⟨292309947042820773, 294992732583463291⟩, true⟩

def words07 : List Nat := [360582447273015071, 360582447206115797, 360582447209916739, 360582447211132831, 360582447144033544, 360582446960005859, 360582446775752177, 360582446633492829, 360582446597101554, 360582446557222707]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 84670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 84600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580914395639115, 360580961319756249⟩, ⟨122998866564565270, 125682633465678888⟩, true⟩

def words08 : List Nat := [360582446517178279, 360582446394275421, 360582446230940024, 360582446129369046, 360582446027477985, 360582445890758043, 360582445802768152, 360582445645070966, 360582445487150781, 360582445351323916]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 84680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 84600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571078760333902, 360571125695924299⟩, ⟨956090668101596902, 958775406729232364⟩, true⟩

def words09 : List Nat := [360582445456558951, 360582445579548055, 360582445583853981, 360582445598106920, 360582445599129712, 360582445537373792, 360582445551449912, 360582445552666345, 360582445490695737, 360582445358341410]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 84690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 84600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 84600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk846
