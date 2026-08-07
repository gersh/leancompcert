import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk747

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578042974251826, 360578079124455717⟩, ⟨313496222002932310, 315320157942385668⟩, true⟩

def state01 : KState := ⟨⟨360577203428807552, 360577239589018272⟩, ⟨376146257382807636, 377970940882817726⟩, true⟩

def words00 : List Nat := [360582300222199950, 360582300194619558, 360582300063536090, 360582299818583200, 360582299573442736, 360582299249905850, 360582299016356834, 360582298961910695, 360582298907357669, 360582298763705501]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 74700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 74700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360596187164985332, 360596223335248700⟩, ⟨(-1042345838449284034), (-1040520403865542696)⟩, true⟩

def words01 : List Nat := [360582298696867826, 360582298554232379, 360582298446344236, 360582298447407590, 360582298304478798, 360582297991754383, 360582297678834794, 360582297552644952, 360582297739877719, 360582297927346430]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 74710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 74700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360570693506793745, 360570729687179443⟩, ⟨862524002651707802, 864350193625520996⟩, true⟩

def words02 : List Nat := [360582298025087969, 360582298026151461, 360582297944862601, 360582297891763740, 360582297838396013, 360582297652996190, 360582297288561447, 360582296797825156, 360582296306898441, 360582295995136429]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 74720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 74700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360555580412931791, 360555616603350845⟩, ⟨1992113554470717279, 1993940495286852715⟩, true⟩

def words03 : List Nat := [360582295865248344, 360582295890357278, 360582295891305824, 360582295805686976, 360582295758431703, 360582295666399833, 360582295574050420, 360582295535244206, 360582295317448455, 360582294961596589]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 74730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 74700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360597394992025897, 360597431192488427⟩, ⟨(-1133348396136140729), (-1131520704622415219)⟩, true⟩

def words04 : List Nat := [360582294605513271, 360582294359130152, 360582294202616372, 360582294152754519, 360582294102827300, 360582293872973804, 360582293711467433, 360582293720813565, 360582293790648325, 360582293994262017]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 74740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 74700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360583989838439378, 360584026049041462⟩, ⟨(-131273575823275532), (-129445126326695792)⟩, true⟩

def words05 : List Nat := [360582294108200747, 360582294222252507, 360582294291635665, 360582294450641517, 360582294564334749, 360582294678205598, 360582294702470847, 360582294703534830, 360582294572066640, 360582294596461552]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 74750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 74700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360573849494549412, 360573885715166879⟩, ⟨626896793833066768, 628725992130247438⟩, true⟩

def words06 : List Nat := [360582294799122496, 360582294907347819, 360582294908310442, 360582294895200043, 360582294881918505, 360582294808181665, 360582294809062993, 360582294741010305, 360582294672843520, 360582294515382611]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 74760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 74700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360608219459200397, 360608255689864305⟩, ⟨(-1943138344106324770), (-1941308394588779754)⟩, true⟩

def words07 : List Nat := [360582294469926769, 360582294537254128, 360582294687246558, 360582294854745113, 360582294868765540, 360582294882872182, 360582294908936046, 360582295078712536, 360582295426732857, 360582295774985008]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 74770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 74700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360574023519400287, 360574059760225442⟩, ⟨614119639891814131, 615950349315930835⟩, true⟩

def words08 : List Nat := [360582295985366281, 360582296059978867, 360582296136168679, 360582296212669102, 360582296243902554, 360582296244967099, 360582296154577580, 360582295953227172, 360582295751669869, 360582295491597497]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 74780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 74700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360547992077682452, 360548028328524632⟩, ⟨2561170941756755004, 2563002400405023102⟩, true⟩

def words09 : List Nat := [360582295382342342, 360582295369534411, 360582295356610980, 360582295244217417, 360582294953054920, 360582294539540944, 360582294125724096, 360582293890619969, 360582293523475111, 360582293066497962]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 74790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 74700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 74700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk747
