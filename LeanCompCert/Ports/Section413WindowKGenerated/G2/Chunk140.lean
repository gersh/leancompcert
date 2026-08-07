import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk140

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360591474315346963, 360591475416358724⟩, ⟨(-130415021159269315), (-130404582446534655)⟩, true⟩

def state01 : KState := ⟨⟨360457701402826209, 360457702505494973⟩, ⟨1742214233420917917, 1742224695339930963⟩, true⟩

def words00 : List Nat := [360582161468764588, 360582158843154646, 360582151136034359, 360582141634792042, 360582132134859208, 360582121353032536, 360582107756174958, 360582089577219338, 360582071400825580, 360582058301022449]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 14000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 14000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360502997317086154, 360502998421394950⟩, ⟨1107811597743872095, 1107822082648006447⟩, true⟩

def words01 : List Nat := [360582049425580424, 360582045624655981, 360582041824256589, 360582035364768353, 360582032710613927, 360582028778224021, 360582024846344729, 360582024403453342, 360582021324606452, 360582015688345593]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 14010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 14000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360565617588116669, 360565618694073832⟩, ⟨229330076843630369, 229340584865750513⟩, true⟩

def words02 : List Nat := [360582010052852121, 360582004225577257, 360582002462845206, 360582002934594556, 360582002934756875, 360581997914467383, 360581987830847113, 360581978578800313, 360581969328018795, 360581965136330835]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 14020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 14000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360527236595512492, 360527237703130672⟩, ⟨768140037227096928, 768150568561599944⟩, true⟩

def words03 : List Nat := [360581963971464339, 360581960245613768, 360581957850874680, 360581961773339802, 360581962164540762, 360581962555713137, 360581962555868628, 360581960395727001, 360581953179000424, 360581949282088051]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 14030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 14000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360533965576662284, 360533966685925775⟩, ⟨673863987973072306, 673874542416035974⟩, true⟩

def words04 : List Nat := [360581945385671111, 360581944545924136, 360581944546079820, 360581942525950507, 360581940506080603, 360581936613682687, 360581935306846929, 360581934678711096, 360581934050649804, 360581929286809479]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 14040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 14000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360605414327771538, 360605415438683826⟩, ⟨(-330575149957495852), (-330564572340745336)⟩, true⟩

def words05 : List Nat := [360581927502310574, 360581929131095786, 360581929477642859, 360581929477817480, 360581924777448303, 360581915730509798, 360581906684822428, 360581902772286355, 360581904444737378, 360581906116989726]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 14050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 14000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360488144131933993, 360488145244512535⟩, ⟨1318198097848352689, 1318208698900814327⟩, true⟩

def words06 : List Nat := [360581906117145584, 360581904815056870, 360581900548943560, 360581894882716748, 360581889217249982, 360581880724334599, 360581870971415694, 360581858606040832, 360581846242391570, 360581834562131641]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 14060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 14000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360344091681677466, 360344092795903207⟩, ⟨3346326664109032859, 3346337288345984737⟩, true⟩

def words07 : List Nat := [360581827903946423, 360581826276494515, 360581824649254930, 360581820481672748, 360581813766101313, 360581805594338551, 360581797423685951, 360581789062979412, 360581775677200353, 360581758796495962]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 14070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 14000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360528294637977984, 360528295753852298⟩, ⟨752000523997962794, 752011171455392974⟩, true⟩

def words08 : List Nat := [360581741918148895, 360581730064415036, 360581720772937479, 360581716504270522, 360581712236194553, 360581703660240883, 360581690064578221, 360581681490215769, 360581672917019746, 360581667731954172]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 14080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 14000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360520813217432490, 360520814334977908⟩, ⟨857142603509728197, 857153274520919493⟩, true⟩

def words09 : List Nat := [360581663944449561, 360581655257518888, 360581646571787368, 360581639470722032, 360581635440806363, 360581630138440142, 360581624836807314, 360581616153121027, 360581609658880757, 360581605347355279]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 14090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 14000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 14000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk140
