import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk002

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨374836077610435986, 374836077610561726⟩, ⟨(-2916971798814639084), (-2916971798797252816)⟩, true⟩

def state01 : KState := ⟨⟨360875542324368321, 360875542324508539⟩, ⟨(-89903995625430279), (-89903995605074935)⟩, true⟩

def words00 : List Nat := [360381049762311575, 360418539035026496, 360448583293424064, 360478334437105957, 360497105369739601, 360497105369741130, 360496761577314368, 360481773789284420, 360466929425063126, 360449457037280696]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨349292608477142091, 349292608477297582⟩, ⟨2431573397260972919, 2431573397284616251⟩, true⟩

def words01 : List Nat := [360471438955378660, 360493214470490093, 360502208803636201, 360502208803637809, 360492935157917058, 360475096521499047, 360457422296476179, 360435406491818371, 360395683350741583, 360345214828591293]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨357744244855898447, 357744244856070135⟩, ⟨513111641349662333, 513111641376952573⟩, true⟩

def words02 : List Nat := [360295203035147915, 360242612414835474, 360203368901540247, 360181810323353621, 360160443376972951, 360122555540620339, 360068239681654162, 360031302165920296, 359994687248576667, 359975165035969929]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨361807443816894056, 361807443817083042⟩, ⟨(-462965476219782462), (-462965476188424476)⟩, true⟩

def words03 : List Nat := [359965507372855074, 359938554707894121, 359911833396280159, 359903279683989837, 359903279683991366, 359897999967489880, 359892764805557844, 359877904614893908, 359878420999629200, 359886425243687090]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361079035111675618, 361079035111882286⟩, ⟨(-273953380078619283), (-273953380042925925)⟩, true⟩

def words04 : List Nat := [359909811968667333, 359930290123143017, 359942167583037861, 359953948084076634, 359954329026782732, 359964868302281579, 359973888777174007, 359982836798453211, 359983221591708606, 359987587382627602]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361594115812472866, 361594115812698223⟩, ⟨(-405613744833332095), (-405613744792870133)⟩, true⟩

def words05 : List Nat := [360006086727639420, 360024439832770293, 360039698968997546, 360041903202533842, 360041903202535648, 360029332844754190, 360018084400860804, 360028039577972932, 360034062948108162, 360040040162150828]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨363725397247612912, 363725397247857954⟩, ⟨(-1008743832299843651), (-1008743832254163495)⟩, true⟩

def words06 : List Nat := [360040040162152651, 360037052611967216, 360021868165838372, 360019803093371093, 360017753606355904, 360010478065891275, 360007717937253896, 359997380153957565, 359989308980247571, 360003095283820451]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨356923631657962282, 356923631658227688⟩, ⟨876646292602437122, 876646292653721102⟩, true⟩

def words07 : List Nat := [360029073321489667, 360054861043865001, 360069620746568420, 360073064285122577, 360073064285124417, 360068007047297614, 360069921785651289, 360069921785653465, 360065733065586420, 360054511274848121]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨365404735986110531, 365404735986397084⟩, ⟨(-1526156442358158462), (-1526156442300843552)⟩, true⟩

def words08 : List Nat := [360043980580396100, 360051674407157084, 360070911951843672, 360090014496217083, 360098848469984181, 360111255393135767, 360120224351782095, 360129131241511078, 360142127564667683, 360160212129693155]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362110168845939316, 362110168846248088⟩, ⟨(-538778626190320698), (-538778626126448086)⟩, true⟩

def words09 : List Nat := [360171169335009789, 360182051747116340, 360203682866325234, 360234031048856670, 360259448506355913, 360284694802525580, 360301232506407818, 360308233641807208, 360314240092490607, 360320206633203410]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk002
