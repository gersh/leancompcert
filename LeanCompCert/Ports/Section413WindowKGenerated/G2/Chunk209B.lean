import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk209A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk209B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk209A

def state06 : KState := ⟨⟨360556681981450452, 360556684541998703⟩, ⟨507843374793959702, 507879691388506560⟩, true⟩

def words05 : List Nat := [360580948429000827, 360580945750685016, 360580943072543669, 360580941418247194, 360580937494459368, 360580931341016072, 360580925188107591, 360580920019485450, 360580916599135996, 360580915443305407]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 20950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 20900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360527117846177759, 360527120409294866⟩, ⟨1127335413855828315, 1127371784306331731⟩, true⟩

def words06 : List Nat := [360580914287549141, 360580911494210128, 360580907387524482, 360580905544794127, 360580903702172364, 360580900244711270, 360580896494622081, 360580891300849881, 360580886107522606, 360580881581650915]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 20960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 20900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360426476039435490, 360426478605096882⟩, ⟨3238522554633747192, 3238558978450420536⟩, true⟩

def words07 : List Nat := [360580879018273289, 360580877974446775, 360580876930685678, 360580874757564918, 360580870319406190, 360580865262693473, 360580860206384678, 360580855486481933, 360580850070495242, 360580842712744662]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 20970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 20900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587411133953047, 360587413702161854⟩, ⟨(-138581470052705354), (-138544992778526540)⟩, true⟩

def words08 : List Nat := [360580835355634670, 360580830258665092, 360580826623583774, 360580825248045490, 360580823872616974, 360580820529662848, 360580817270057492, 360580815361828824, 360580813453698625, 360580813492892238]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 20980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 20900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360460713729112674, 360460716299897477⟩, ⟨2521605170202136481, 2521641701559347847⟩, true⟩

def words09 : List Nat := [360580813493132792, 360580812680515403, 360580811867927502, 360580811279733082, 360580811279961388, 360580809652664612, 360580808025495250, 360580805239349323, 360580800194129650, 360580794476162208]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 20990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 20900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 20900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk209B
