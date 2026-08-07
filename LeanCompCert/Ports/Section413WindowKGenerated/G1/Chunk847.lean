import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk847

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476491654433562, 362476599704390321⟩, ⟨731939357912069460, 738118840358895440⟩, true⟩

def state01 : KState := ⟨⟨362481891580487263, 362481999656750468⟩, ⟨274607216136544638, 280788926873982708⟩, true⟩

def words00 : List Nat := [371285314148084239, 371285314151332831, 371285314242182134, 371285314350850610, 371285314435757693, 371285314438700656, 371285314361729693, 371285314343826530, 371285314361847607, 371285314364894418]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 84700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 84700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362485198092709429, 362485306195781978⟩, ⟨(-5502342956518628), 681638938689338⟩, true⟩

def words01 : List Nat := [371285314327984959, 371285314246649245, 371285314218817477, 371285314225847607, 371285314274288370, 371285314323828586, 371285314372390397, 371285314375332643, 371285314237975913, 371285314241567374]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 84710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 84700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478341639124104, 362478449768445424⟩, ⟨575401960962888838, 581588166787860582⟩, true⟩

def words02 : List Nat := [371285314265002211, 371285314267964519, 371285314166620180, 371285314067066775, 371285313966416947, 371285313908135575, 371285313780579006, 371285313785149994, 371285313787349831, 371285313785520697]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 84720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 84700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362499249783176813, 362499357939053595⟩, ⟨(-1196253912141156822), (-1190065456138421074)⟩, true⟩

def words03 : List Nat := [371285313764718695, 371285313826424041, 371285313958380335, 371285313961337247, 371285313960398123, 371285313925694270, 371285313991014466, 371285314040686588, 371285314208411758, 371285314377422998]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 84730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 84700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485838529518034, 362485946711980860⟩, ⟨(-59718851221543387), (-53528142184259665)⟩, true⟩

def words04 : List Nat := [371285314537148237, 371285314582173023, 371285314752368239, 371285314924169774, 371285315105647052, 371285315108590354, 371285315104628599, 371285315088053995, 371285315108120935, 371285315118935536]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 84740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 84700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362477477990965871, 362477586199959387⟩, ⟨648937237035465377, 655130194684666047⟩, true⟩

def words05 : List Nat := [371285315267534860, 371285315417367687, 371285315564891129, 371285315567836926, 371285315557788553, 371285315533170296, 371285315606476576, 371285315609420332, 371285315525584982, 371285315437744719]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 84750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 84700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488509269722077, 362488617505101854⟩, ⟨(-286107346363610081), (-279912152079050293)⟩, true⟩

def words06 : List Nat := [371285315396484067, 371285315399767648, 371285315446470387, 371285315500733275, 371285315531418803, 371285315534382763, 371285315439850175, 371285315415141557, 371285315482982868, 371285315525036985]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 84760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 84700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488373858299607, 362488482120475748⟩, ⟨(-274613192641757890), (-268415726693375180)⟩, true⟩

def words07 : List Nat := [371285315566293148, 371285315608495441, 371285315741851570, 371285315813014133, 371285315924159779, 371285316036454760, 371285316098445525, 371285316101400789, 371285316090323378, 371285316131319058]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 84770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 84700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485593723296713, 362485702011697844⟩, ⟨(-38895541261184780), (-32695851822446484)⟩, true⟩

def words08 : List Nat := [371285316290750715, 371285316293695246, 371285316267919944, 371285316234536862, 371285316199933045, 371285316199277826, 371285316227810659, 371285316313782010, 371285316398885232, 371285316406482404]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 84780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 84700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492268349137722, 362492376664238711⟩, ⟨(-604862757336256370), (-598660803884396710)⟩, true⟩

def words09 : List Nat := [371285316470577606, 371285316536190061, 371285316739249760, 371285316757891428, 371285316760170435, 371285316756439306, 371285316847256949, 371285316896317532, 371285316981590122, 371285317068197575]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 84790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 84700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 84700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk847
