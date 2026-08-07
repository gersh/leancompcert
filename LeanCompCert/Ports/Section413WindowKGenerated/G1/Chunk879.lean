import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk879

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362495354317603752, 362495471019641582⟩, ⟨(-910472492459704642), (-903546242632509604)⟩, true⟩

def state01 : KState := ⟨⟨362485775951155804, 362485892680462463⟩, ⟨(-68496275071859965), (-61567628175197767)⟩, true⟩

def words00 : List Nat := [371285192050915797, 371285192053977298, 371285192047981513, 371285192043353949, 371285192069155047, 371285192073315840, 371285192158019460, 371285192243934545, 371285192328888268, 371285192340025258]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 87900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 87900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362497990591281680, 362498107348346936⟩, ⟨(-1142346607480915450), (-1135415520191663700)⟩, true⟩

def words01 : List Nat := [371285192479352281, 371285192620357313, 371285192796381023, 371285192816454448, 371285192818823551, 371285192818390573, 371285192942281421, 371285193006565587, 371285193155539145, 371285193305965803]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 87910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 87900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480485069037616, 362480601853710575⟩, ⟨396790590925860246, 403724105627994192⟩, true⟩

def words02 : List Nat := [371285193455495962, 371285193458558037, 371285193476883062, 371285193521914240, 371285193603866782, 371285193606929004, 371285193516701625, 371285193407170034, 371285193296366604, 371285193279909006]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 87920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 87900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482383980747500, 362482500792968999⟩, ⟨229873221171052346, 236809158357383764⟩, true⟩

def words03 : List Nat := [371285193306779487, 371285193387107103, 371285193466443119, 371285193474290632, 371285193510360943, 371285193547991130, 371285193693188383, 371285193696251078, 371285193669375124, 371285193642165695]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 87930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 87900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482824600821765, 362482941440489534⟩, ⟨191130260555528606, 198068611507591398⟩, true⟩

def words04 : List Nat := [371285193613663366, 371285193608408036, 371285193593204477, 371285193652510651, 371285193672925615, 371285193675988705, 371285193523804669, 371285193482936776, 371285193496569922, 371285193499744879]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 87940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 87900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490497410726069, 362490614278320126⟩, ⟨(-483739044294413446), (-476798237083873744)⟩, true⟩

def words05 : List Nat := [371285193476433337, 371285193449800996, 371285193512945085, 371285193547558318, 371285193585031982, 371285193623635254, 371285193649511046, 371285193652597694, 371285193648790337, 371285193714239638]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 87950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 87900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488213382507683, 362488330277416869⟩, ⟨(-282772973902357962), (-275829763910583822)⟩, true⟩

def words06 : List Nat := [371285193907074427, 371285194006959379, 371285194105312286, 371285194204670374, 371285194336457832, 371285194406920188, 371285194540814198, 371285194675981863, 371285194776182770, 371285194815004136]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 87960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 87900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362503538614991520, 362503655537557449⟩, ⟨(-1631035301183403278), (-1624089658088320038)⟩, true⟩

def words07 : List Nat := [371285194912085524, 371285195010710603, 371285195236880704, 371285195291858171, 371285195303693022, 371285195316532812, 371285195457131529, 371285195562547363, 371285195774445510, 371285195987676358]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 87970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 87900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488388680622389, 362488505630887097⟩, ⟨(-298100043572277487), (-291151963401566743)⟩, true⟩

def words08 : List Nat := [371285196199813663, 371285196240579189, 371285196334077370, 371285196429222505, 371285196562316756, 371285196588971869, 371285196613857052, 371285196639749499, 371285196706276857, 371285196747439909]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 87980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 87900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478325413197498, 362478442391074593⟩, ⟨587476342578676914, 594426852503106088⟩, true⟩

def words09 : List Nat := [371285196916170459, 371285197086181902, 371285197253807329, 371285197256872612, 371285197285005700, 371285197321410588, 371285197386350259, 371285197389420156, 371285197314914132, 371285197241671220]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 87990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 87900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 87900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk879
