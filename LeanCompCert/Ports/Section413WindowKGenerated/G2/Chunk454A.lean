import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk454A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360566056232555487, 360566069060896403⟩, ⟨780468484008892345, 780862053573138365⟩, true⟩

def state01 : KState := ⟨⟨360597797916720195, 360597810750939842⟩, ⟨(-660616109085506555), (-660222272598624501)⟩, true⟩

def words00 : List Nat := [360583268287265913, 360583268656894858, 360583269529022634, 360583270401231004, 360583270857128473, 360583270976169528, 360583271255292912, 360583271534589682, 360583271611942118, 360583271932754852]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 45400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 45400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360583514575096584, 360583527415232857⟩, ⟨(-11850761612356074), (-11456656421384176)⟩, true⟩

def words01 : List Nat := [360583272009977084, 360583272087263818, 360583272648603790, 360583273505825320, 360583274164512866, 360583274823283173, 360583275238559942, 360583275239181924, 360583275176381521, 360583275182643936]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 45410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 45400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604827547296212, 360604840393300992⟩, ⟨(-980100275228992618), (-979705903462419448)⟩, true⟩

def words02 : List Nat := [360583275516250065, 360583275708703620, 360583275709272747, 360583275515907058, 360583275322448198, 360583274840669969, 360583274935936368, 360583275225861577, 360583275226416941, 360583275692910017]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 45420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 45400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360635655403595142, 360635668255463848⟩, ⟨(-2380792399650508986), (-2380397761455744880)⟩, true⟩

def words03 : List Nat := [360583276551964369, 360583277411169557, 360583278753895187, 360583279613450339, 360583280052042752, 360583280490662115, 360583280917343194, 360583281587324311, 360583282740703127, 360583283894172157]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 45430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 45400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360606386382252188, 360606399240056094⟩, ⟨(-1050905266195829062), (-1050510358278107070)⟩, true⟩

def words04 : List Nat := [360583284612543259, 360583284847868727, 360583285342104920, 360583285836513067, 360583286115419244, 360583286116042132, 360583286113943193, 360583285868919839, 360583285700103038, 360583286209357582]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 45440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 45400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk454A
