import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk557

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360574073628161445, 360574093262899587⟩, ⟨429778498818542786, 430517413858254434⟩, true⟩

def state01 : KState := ⟨⟨360559102849638282, 360559122491767371⟩, ⟨1263604230678899395, 1264343557430496429⟩, true⟩

def words00 : List Nat := [360581822342318586, 360581822040450373, 360581821417060681, 360581821016988241, 360581820616722224, 360581820035750383, 360581819569652407, 360581818916828841, 360581818263880915, 360581817583446253]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 55700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 55700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360539243287706880, 360539262937144554⟩, ⟨2370136782396381291, 2370876516346293089⟩, true⟩

def words01 : List Nat := [360581817176701344, 360581817091523841, 360581817006276987, 360581816669985344, 360581816101696157, 360581815321696422, 360581814541497344, 360581814082833919, 360581813529776311, 360581812766942586]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 55710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 55700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580802603663849, 360580822260418313⟩, ⟨54327096497452830, 55067238174641828⟩, true⟩

def words02 : List Nat := [360581812003946699, 360581811562526993, 360581811347894575, 360581811361184749, 360581811361900649, 360581811102341987, 360581810968388240, 360581810717696516, 360581810466778171, 360581810368047501]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 55720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 55700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360589240376735297, 360589260040872073⟩, ⟨(-415966283599542846), (-415225730468834446)⟩, true⟩

def words03 : List Nat := [360581810351011776, 360581810125162132, 360581809993752277, 360581810336128686, 360581810539421819, 360581810742834145, 360581810743536297, 360581810697854713, 360581810708619199, 360581810843145645]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 55730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 55700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583061972751926, 360583081644206513⟩, ⟨(-71646147874996924), (-70905186813259058)⟩, true⟩

def words04 : List Nat := [360581810970030445, 360581810970806471, 360581810891326760, 360581810589194639, 360581810286943056, 360581809903986316, 360581809806941778, 360581809884459603, 360581809885150805, 360581809825103479]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 55740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 55700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk557
