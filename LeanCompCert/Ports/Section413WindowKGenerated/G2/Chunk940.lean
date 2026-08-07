import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk940

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360576642725977074, 360576701003564991⟩, ⟨500223152995349140, 503922287962423732⟩, true⟩

def state01 : KState := ⟨⟨360598624290822776, 360598682581275383⟩, ⟨(-1566255708203216858), (-1562555363891367544)⟩, true⟩

def words00 : List Nat := [360582061823041007, 360582061783397794, 360582061784522592, 360582061747178062, 360582061709739995, 360582061575706941, 360582061423535570, 360582061384845403, 360582061418643048, 360582061596881096]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 94000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 94000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360594336492189658, 360594394795601908⟩, ⟨(-1163138145210375082), (-1159436582498220452)⟩, true⟩

def words01 : List Nat := [360582061718157131, 360582061839582263, 360582062028091887, 360582062273491089, 360582062490036498, 360582062706806159, 360582062811186989, 360582062853845688, 360582062986108993, 360582063118822272]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 94010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 94000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591646412000005, 360591704728230042⟩, ⟨(-910203828088470564), (-906501060182571990)⟩, true⟩

def words02 : List Nat := [360582063342086676, 360582063487985990, 360582063568108995, 360582063648392616, 360582063699663064, 360582063807562719, 360582063953622962, 360582064099947468, 360582064175292484, 360582064279227239]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 94020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 94000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360593921560344563, 360593979889436024⟩, ⟨(-1124193772089023461), (-1120489794758095307)⟩, true⟩

def words03 : List Nat := [360582064334634154, 360582064390431989, 360582064558823278, 360582064614758429, 360582064616014013, 360582064575851530, 360582064586106026, 360582064726242689, 360582064854054020, 360582064982164110]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 94030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 94000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590983578953965, 360591041921029558⟩, ⟨(-847978717513973792), (-844273519097750110)⟩, true⟩

def words04 : List Nat := [360582065044046170, 360582065072635729, 360582065190654722, 360582065309075395, 360582065349447952, 360582065350810007, 360582065316616872, 360582065194355134, 360582065071834863, 360582065158218980]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 94040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 94000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360582342956234706, 360582401311139515⟩, ⟨(-35227316099105518), (-31520911029320022)⟩, true⟩

def words05 : List Nat := [360582065344131439, 360582065530324867, 360582065656201311, 360582065785451256, 360582065851739298, 360582065918381868, 360582066097579035, 360582066189983028, 360582066194791900, 360582066199764670]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 94050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 94000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360606451525746375, 360606509893509950⟩, ⟨(-2303038736582884089), (-2299331121954128371)⟩, true⟩

def words06 : List Nat := [360582066200876083, 360582066207742021, 360582066358916223, 360582066510348447, 360582066565687727, 360582066623772307, 360582066774103893, 360582066924855421, 360582067124775966, 360582067386021414]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 94060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 94000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360600614360386151, 360600672741135405⟩, ⟨(-1753950466128304856), (-1750241629871243562)⟩, true⟩

def words07 : List Nat := [360582067590404046, 360582067794940416, 360582067973594646, 360582068208844504, 360582068389821763, 360582068571017040, 360582068695678930, 360582068781885607, 360582068980732827, 360582069180056428]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 94070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 94000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583934948622869, 360583993342192470⟩, ⟨(-184705570632978248), (-180995528171513156)⟩, true⟩

def words08 : List Nat := [360582069412543209, 360582069532688898, 360582069567964103, 360582069603379692, 360582069604520581, 360582069635635958, 360582069677547478, 360582069719703101, 360582069720916936, 360582069720080138]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 94080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 94000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360616615269647464, 360616673676079173⟩, ⟨(-3259792566513886572), (-3256081313794381350)⟩, true⟩

def words09 : List Nat := [360582069807196564, 360582069894710892, 360582070035351573, 360582070266670721, 360582070382179029, 360582070497774030, 360582070697568441, 360582070953942646, 360582071322766820, 360582071691894155]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 94090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 94000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 94000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk940
