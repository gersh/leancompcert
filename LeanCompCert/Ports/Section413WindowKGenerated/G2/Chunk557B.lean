import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk557A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk557B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk557A

def state06 : KState := ⟨⟨360592652727533818, 360592672406309954⟩, ⟨(-606324742431002389), (-605583373157404389)⟩, true⟩

def words05 : List Nat := [360581810118939730, 360581810412994249, 360581810957721805, 360581811284272879, 360581811293520501, 360581811302808517, 360581811408726881, 360581811676144032, 360581811871552367, 360581812067127418]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 55750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 55700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360577365737189882, 360577385423366911⟩, ⟨246129776240834921, 246871558223812231⟩, true⟩

def words06 : List Nat := [360581812102317576, 360581812157327095, 360581812532962070, 360581812908819080, 360581813125482212, 360581813126258321, 360581813022339824, 360581812718569657, 360581812414673232, 360581812024733664]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 55760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 55700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360536153405056845, 360536173098534450⟩, ⟨2544834881090883196, 2545577070264445764⟩, true⟩

def words07 : List Nat := [360581812071105468, 360581812196992283, 360581812197690253, 360581812161316159, 360581811897727923, 360581811433592325, 360581810969232638, 360581810590932250, 360581809933641721, 360581809116287488]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 55770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 55700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360548979572368991, 360548999273182871⟩, ⟨1829218467344878537, 1829961065772966573⟩, true⟩

def words08 : List Nat := [360581808298791040, 360581807521274400, 360581806904994845, 360581806150774627, 360581805396519388, 360581804368159046, 360581803019301450, 360581801991268918, 360581800963045873, 360581800152655411]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 55780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 55700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360562055757204341, 360562075465419155⟩, ⟨1099625436041320581, 1100368447403238129⟩, true⟩

def words09 : List Nat := [360581799565429336, 360581798816255409, 360581798066954507, 360581797638390820, 360581797440723488, 360581797162431300, 360581796884071646, 360581796355807695, 360581795682581532, 360581795330067959]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 55790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 55700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 55700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk557B
