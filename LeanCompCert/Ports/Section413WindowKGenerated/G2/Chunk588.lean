import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk588

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360596741125764911, 360596763102254725⟩, ⟨(-865462389458360863), (-864589374026853057)⟩, true⟩

def state01 : KState := ⟨⟨360577607175296018, 360577629159515835⟩, ⟨259697165213881696, 260570635207934080⟩, true⟩

def words00 : List Nat := [360582059930064562, 360582060120384769, 360582060121118396, 360582060111701674, 360582060102152514, 360582060029100861, 360582060029777035, 360582060028129237, 360582060026391744, 360582059879379939]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 58800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 58800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360608530399250797, 360608552391223363⟩, ⟨(-1559078982877915015), (-1558205056906030607)⟩, true⟩

def words01 : List Nat := [360582059863944014, 360582059924089539, 360582060200150574, 360582060483737212, 360582060521225968, 360582060558770565, 360582060639099072, 360582060863891422, 360582061314938638, 360582061766159083]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 58810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 58800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589004698990027, 360589026698799055⟩, ⟨(-410663228192442426), (-409788841242367620)⟩, true⟩

def words02 : List Nat := [360582061996915432, 360582061997737175, 360582062073425541, 360582062207619851, 360582062208311555, 360582062178870775, 360582061951658575, 360582061579317554, 360582061206811899, 360582061173119697]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 58820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 58800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360570126963683379, 360570148971227245⟩, ⟨700085568382807821, 700960410412595715⟩, true⟩

def words03 : List Nat := [360582061581089081, 360582061989202148, 360582062251085205, 360582062382290112, 360582062382990054, 360582062273216912, 360582062163208174, 360582062163446483, 360582062164183493, 360582061962566685]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 58830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 58800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590021755943656, 360590043771254741⟩, ⟨(-470602345039666085), (-469727045948865561)⟩, true⟩

def words04 : List Nat := [360582061760770978, 360582061882266180, 360582062145252182, 360582062408385649, 360582062427226864, 360582062428048925, 360582062158781407, 360582062110628380, 360582062062247554, 360582062138895922]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 58840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 58800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360581782972830712, 360581804995971273⟩, ⟨14311073930918268, 15186833824486192⟩, true⟩

def words05 : List Nat := [360582062139638462, 360582062093116104, 360582062226088390, 360582062612998590, 360582062878270431, 360582063143681730, 360582063223237178, 360582063224059409, 360582063015612627, 360582063012176243]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 58850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 58800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360574617464567694, 360574639495461523⟩, ⟨436023196522293152, 436899412811791500⟩, true⟩

def words06 : List Nat := [360582063047022413, 360582063047846447, 360582062963335950, 360582062659121751, 360582062354779899, 360582061934700453, 360582061658315372, 360582061468298485, 360582061278205574, 360582060922551923]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 58860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 58800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360575778722128843, 360575800760782364⟩, ⟨367626052894764226, 368502726036214720⟩, true⟩

def words07 : List Nat := [360582060797155981, 360582060767501287, 360582060938243453, 360582060939065887, 360582060852700663, 360582060512997222, 360582060173162179, 360582059715328415, 360582059404370739, 360582059298928360]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 58870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 58800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360553254871431309, 360553276917917076⟩, ⟨1693755763486393437, 1694632897829314581⟩, true⟩

def words08 : List Nat := [360582059193371251, 360582058914327550, 360582058446968271, 360582057930955362, 360582057414726329, 360582056824527042, 360582055946621657, 360582054921628667, 360582053896510653, 360582053160026591]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 58880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 58800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360540262928510503, 360540284982751693⟩, ⟨2458881633899792371, 2459759224998259815⟩, true⟩

def words09 : List Nat := [360582052672067773, 360582052118191307, 360582051564243866, 360582050839958671, 360582050073803331, 360582049233831419, 360582048393638220, 360582047841906237, 360582047307657570, 360582046599474924]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 58890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 58800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 58800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk588
