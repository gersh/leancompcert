import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk517A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk517A
