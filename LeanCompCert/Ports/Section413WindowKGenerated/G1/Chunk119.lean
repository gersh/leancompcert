import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk119

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362453192984180065, 362453194795059977⟩, ⟨374114990638545977, 374129574759092433⟩, true⟩

def state01 : KState := ⟨⟨362423370579740630, 362423372393801386⟩, ⟨729009845312648544, 729024467301426994⟩, true⟩

def words00 : List Nat := [371284631613638461, 371284629006090607, 371284620151989999, 371284618316350429, 371284616806264364, 371284616806617092, 371284607765091187, 371284597344028703, 371284586924575466, 371284583516160868]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 11900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 11900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362397721527158894, 362397723344401834⟩, ⟨1035025552729527877, 1035040212634521375⟩, true⟩

def words01 : List Nat := [371284578938679555, 371284579500290801, 371284579500557475, 371284578682906462, 371284573648455521, 371284570782294166, 371284569477012407, 371284569477365669, 371284562861799099, 371284555577005402]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 11910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 11900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362450067151658971, 362450068972068753⟩, ⟨410829490875277566, 410844188545202636⟩, true⟩

def words02 : List Nat := [371284548293278866, 371284542512071257, 371284533216970592, 371284530916205861, 371284528615721459, 371284525229030400, 371284513922125692, 371284509607198744, 371284506875185414, 371284506875551168]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 11920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 11900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362470658435156287, 362470660258785653⟩, ⟨165110476451175294, 165125212546955854⟩, true⟩

def words03 : List Nat := [371284503989393973, 371284499881929960, 371284498652937827, 371284499311235739, 371284499459202566, 371284499607277838, 371284499607543269, 371284499137861615, 371284490998996396, 371284489841076018]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 11930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 11900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362465329790265460, 362465331617052338⟩, ⟨229139309580328073, 229154083393460219⟩, true⟩

def words04 : List Nat := [371284494503418109, 371284494512510391, 371284494512778038, 371284494494331535, 371284496610969248, 371284496611361536, 371284500652556312, 371284504951009505, 371284507690609458, 371284507690976477]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 11940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 11900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362548855255493742, 362548857085490659⟩, ⟨(-769532581038776525), (-769517768849837323)⟩, true⟩

def words05 : List Nat := [371284506506588590, 371284506926877699, 371284514312177220, 371284514312531828, 371284513805119947, 371284512118877070, 371284512334345123, 371284512334735305, 371284516134514692, 371284521514146304]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 11950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 11900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477511222151046, 362477513055356733⟩, ⟨83663899203059397, 83678749785165055⟩, true⟩

def words06 : List Nat := [371284526942411107, 371284526942765766, 371284523085692852, 371284522165711267, 371284522476354726, 371284522476709782, 371284516049233183, 371284509636517083, 371284503760854923, 371284503761270281]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 11960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 11900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362375818542505362, 362375820378899942⟩, ⟨1301971942461598461, 1301986831231451771⟩, true⟩

def words07 : List Nat := [371284509539614145, 371284515901005577, 371284522134010497, 371284522134365473, 371284519100319662, 371284518153747906, 371284517227938086, 371284517228293261, 371284509487047524, 371284500414895890]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 11970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 11900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490469113686701, 362490470953265010⟩, ⟨(-71973959685304835), (-71959032758342473)⟩, true⟩

def words08 : List Nat := [371284491344105436, 371284489212251198, 371284483614330875, 371284482884973043, 371284482155616910, 371284479664661754, 371284470632054007, 371284468532143551, 371284469365508784, 371284469866386657]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 11980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 11900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502978673996245, 362502980516820427⟩, ⟨(-221991502132770907), (-221976536271390487)⟩, true⟩

def words09 : List Nat := [371284469866657639, 371284468841726083, 371284472440533574, 371284473603671205, 371284476910338493, 371284480216586499, 371284483447864647, 371284483448226475, 371284482471686062, 371284484013506421]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 11990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 11900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 11900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk119
