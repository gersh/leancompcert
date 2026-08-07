import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk517

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360569873160686327, 360569889974548127⟩, ⟨623081370266510131, 623668728994363061⟩, true⟩

def state01 : KState := ⟨⟨360577172853288722, 360577189673907000⟩, ⟨245698294174447865, 246286002245632955⟩, true⟩

def words00 : List Nat := [360581952966734958, 360581952678940621, 360581952959435875, 360581953240541364, 360581953241207691, 360581953201132245, 360581952896318994, 360581952794466839, 360581952692418371, 360581952505124282]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 51700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 51700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360592822284432874, 360592839111864176⟩, ⟨(-563651477348832311), (-563063416942270181)⟩, true⟩

def words01 : List Nat := [360581952413661129, 360581952038047652, 360581951662311640, 360581951935479250, 360581952118707614, 360581952302058038, 360581952302695479, 360581952298884645, 360581952347379595, 360581952558685733]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 51710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 51700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360600579049669396, 360600595883847902⟩, ⟨(-964859700531494822), (-964271291125784844)⟩, true⟩

def words02 : List Nat := [360581953142805962, 360581953672266253, 360581953908712267, 360581954145210373, 360581954282600258, 360581954665790654, 360581954990215381, 360581955314761408, 360581955417385335, 360581955778473450]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 51720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 51700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360587427125462822, 360587443966395292⟩, ⟨(-284501958073366532), (-283913199251140118)⟩, true⟩

def words03 : List Nat := [360581956234566935, 360581956690859168, 360581957203900470, 360581957344239881, 360581957344899845, 360581957164570447, 360581956984121588, 360581956674611880, 360581956659905733, 360581956766703537]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 51730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 51700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577943149473283, 360577959997228742⟩, ⟨206074494368082577, 206663606244154791⟩, true⟩

def words04 : List Nat := [360581956767347194, 360581956686844003, 360581956392918139, 360581956346652158, 360581956300179263, 360581956094848273, 360581955516825779, 360581954719253483, 360581953921572984, 360581953496866311]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 51740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 51700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360541798833861665, 360541815688366872⟩, ⟨2076696661061390751, 2077286122271125091⟩, true⟩

def words05 : List Nat := [360581953420287667, 360581953333927732, 360581953247496012, 360581952926663992, 360581952326729082, 360581951480661542, 360581950634415148, 360581950063224933, 360581949502464967, 360581948727823424]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 51750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 51700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360610866124079673, 360610882985345029⟩, ⟨(-1498625324821001924), (-1498035513672953208)⟩, true⟩

def words06 : List Nat := [360581947953049627, 360581947472518739, 360581947180438953, 360581947098577723, 360581947016677716, 360581946538428934, 360581946207183768, 360581946228286271, 360581946621580404, 360581947181252527]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 51760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 51700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360568206597868194, 360568223465963346⟩, ⟨710180735434031155, 710770900195033057⟩, true⟩

def words07 : List Nat := [360581947553878460, 360581947926580909, 360581948471698296, 360581949205507878, 360581949758867490, 360581950312320652, 360581950579955857, 360581950580672427, 360581950476100381, 360581950211814931]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 51770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 51700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586218432270753, 360586235307112232⟩, ⟨(-222586984110993269), (-221996469991439889)⟩, true⟩

def words08 : List Nat := [360581949947302137, 360581949937269706, 360581949805385117, 360581949436499980, 360581949067512211, 360581948605975633, 360581948640988935, 360581948844991256, 360581948845629895, 360581948916233674]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 51780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 51700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360607984691492624, 360608001573111622⟩, ⟨(-1349968478258348386), (-1349377613099077978)⟩, true⟩

def words09 : List Nat := [360581949261982682, 360581949607932220, 360581949912207415, 360581950248750007, 360581950268646808, 360581950288593611, 360581950680405345, 360581951307999038, 360581951811484929, 360581952315122412]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 51790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 51700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 51700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk517
