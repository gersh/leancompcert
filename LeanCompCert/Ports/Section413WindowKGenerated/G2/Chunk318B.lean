import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk318A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk318B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk318A

def state06 : KState := ⟨⟨360535576116702215, 360535582253184763⟩, ⟨1489936784079749281, 1490068989779984079⟩, true⟩

def words05 : List Nat := [360582365538286021, 360582363705906254, 360582361873560656, 360582360693962049, 360582360012972547, 360582358796548719, 360582357580159172, 360582355440860964, 360582352992198074, 360582351524678172]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 31850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 31800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360522566634382351, 360522572774857810⟩, ⟨1904464015430831923, 1904596348365456963⟩, true⟩

def words06 : List Nat := [360582350057105300, 360582349330744867, 360582347932155499, 360582345831264449, 360582343730428924, 360582341385151840, 360582339595479724, 360582337959807775, 360582336324195449, 360582334191499337]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 31860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 31800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360555093618868853, 360555099763357565⟩, ⟨867427456655534180, 867559917511362856⟩, true⟩

def words07 : List Nat := [360582332316745551, 360582330071142912, 360582327825557095, 360582326560080508, 360582324311915254, 360582321115778876, 360582317919760030, 360582315452250040, 360582313913848848, 360582313060644622]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 31870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 31800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360512843159873277, 360512849308400219⟩, ⟨2214514138332923731, 2214646727948159489⟩, true⟩

def words08 : List Nat := [360582312207433008, 360582310864207225, 360582309115596159, 360582308346385306, 360582307577116690, 360582306121892395, 360582303997156204, 360582301372613055, 360582298748157353, 360582295740759836]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 31880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 31800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360486270012567769, 360486276165098816⟩, ⟨3062241796811480445, 3062374514137382131⟩, true⟩

def words09 : List Nat := [360582293563484792, 360582292365269960, 360582291167075557, 360582289479276300, 360582287266680317, 360582284810137398, 360582282353620099, 360582280636834570, 360582278375199450, 360582275366168954]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 31890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 31800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 31800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk318B
