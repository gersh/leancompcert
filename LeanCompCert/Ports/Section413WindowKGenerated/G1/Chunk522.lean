import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk522

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487421369439410, 362487460879144533⟩, ⟨(-127252103162261086), (-125858800114001054)⟩, true⟩

def state01 : KState := ⟨⟨362483418105108682, 362483457630392711⟩, ⟨81783980127231521, 83178096474388109⟩, true⟩

def words00 : List Nat := [371285050251256233, 371285050253005043, 371285050242367788, 371285050232478528, 371285050305997634, 371285050307970663, 371285050461789134, 371285050618500049, 371285050773503929, 371285050775316565]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 52200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 52200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362493051350854072, 362493090891936968⟩, ⟨(-421209160459520374), (-419814219173571068)⟩, true⟩

def words01 : List Nat := [371285051053871579, 371285051363818543, 371285051823625395, 371285051825374311, 371285051796671867, 371285051685359773, 371285051574927148, 371285051576873802, 371285051552169917, 371285051708099555]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 52210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 52200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362472049430096997, 362472088986954404⟩, ⟨675574919049820250, 676970684160784930⟩, true⟩

def words02 : List Nat := [371285051853528584, 371285051855277689, 371285051534075447, 371285051558187477, 371285051690500173, 371285051692249319, 371285051336247703, 371285050907953225, 371285050478968956, 371285050324962461]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 52220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 52200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362469054265674092, 362469093838299323⟩, ⟨832122975562621246, 833519564308327858⟩, true⟩

def words03 : List Nat := [371285050100837999, 371285050125590170, 371285050126900329, 371285050123662285, 371285049927902098, 371285049816152704, 371285049955820253, 371285049957569770, 371285049722991863, 371285049419545654]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 52230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 52200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479393566628030, 362479433154937754⟩, ⟨291912540007601661, 293309948189757421⟩, true⟩

def words04 : List Nat := [371285049115334501, 371285048877289523, 371285048455613817, 371285048346993337, 371285048237862768, 371285048072973444, 371285047465826634, 371285047103116067, 371285046740633370, 371285046742462917]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 52240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 52200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362494754497094059, 362494794101316396⟩, ⟨(-510778739878513069), (-509380500181963439)⟩, true⟩

def words05 : List Nat := [371285046636336545, 371285046530913826, 371285046683449281, 371285046761491913, 371285046855839886, 371285046950859393, 371285047045428618, 371285047047185411, 371285047055527374, 371285047244191926]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 52250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 52200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489492279330993, 362489531899144817⟩, ⟨(-235711841926165064), (-234312787336216558)⟩, true⟩

def words06 : List Nat := [371285047619197414, 371285047691730658, 371285047762705921, 371285047834272451, 371285048017573801, 371285048047238615, 371285048441906544, 371285048837255002, 371285049157953722, 371285049245525483]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 52260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 52200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362510256889577994, 362510296525246475⟩, ⟨(-1321169608355694043), (-1319769724965096267)⟩, true⟩

def words07 : List Nat := [371285049659603880, 371285050074631915, 371285050732086585, 371285050952047350, 371285051050856486, 371285051150217035, 371285051557501133, 371285051782791382, 371285052266857128, 371285052751696522]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 52270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 52200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483835638236832, 362483875289741594⟩, ⟨60144105953199592, 61544817343664550⟩, true⟩

def words08 : List Nat := [371285053192442694, 371285053194193795, 371285053147468063, 371285053105841561, 371285053132033018, 371285053133792545, 371285052853876809, 371285052540954492, 371285052277886692, 371285052279937496]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 52280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 52200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362474034392186965, 362474074059427643⟩, ⟨572819202281495769, 574220736585171037⟩, true⟩

def words09 : List Nat := [371285052601507628, 371285052946273821, 371285053290680429, 371285053308517106, 371285053438170362, 371285053568698705, 371285053819644145, 371285053821395893, 371285053631397651, 371285053423415888]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 52290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 52200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 52200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk522
