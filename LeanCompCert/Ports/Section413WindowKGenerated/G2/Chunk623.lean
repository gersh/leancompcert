import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk623

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360614505655248514, 360614530439219868⟩, ⟨(-1984654328210278634), (-1983611268815670752)⟩, true⟩

def state01 : KState := ⟨⟨360584209682514381, 360584234474809311⟩, ⟨(-97162785831629439), (-96119207837903803)⟩, true⟩

def words00 : List Nat := [360582691640755873, 360582691741982518, 360582692100509999, 360582692459289060, 360582692665181017, 360582692666055334, 360582692615458598, 360582692344467165, 360582692073319901, 360582691902745986]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 62300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 62300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360568815190741568, 360568839991264230⟩, ⟨862249359257596565, 863293449963310893⟩, true⟩

def words01 : List Nat := [360582692185620982, 360582692468654433, 360582692622060626, 360582692782180016, 360582692782916773, 360582692757012790, 360582692894470366, 360582692895344819, 360582692803302468, 360582692581924746]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 62310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 62300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360613060502989353, 360613085311781387⟩, ⟨(-1895417610668659959), (-1894373004576366589)⟩, true⟩

def words02 : List Nat := [360582692360366635, 360582692051591649, 360582692082106312, 360582692226535953, 360582692227350756, 360582692154089754, 360582692184187471, 360582692328502544, 360582692674831537, 360582693163338777]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 62320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 62300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585167382096374, 360585192199213082⟩, ⟨(-156638098292171196), (-155592973280789440)⟩, true⟩

def words03 : List Nat := [360582693505819128, 360582693848384027, 360582694388131736, 360582695059431029, 360582695506253207, 360582695953187550, 360582696206040176, 360582696280449859, 360582696321197739, 360582696362231308]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 62330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 62300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360604099456082083, 360604124281449299⟩, ⟨(-1336959382529143359), (-1335913743140864109)⟩, true⟩

def words04 : List Nat := [360582696556457925, 360582696825091984, 360582696963310140, 360582697101611517, 360582697111579441, 360582697249622216, 360582697644526355, 360582698039595598, 360582698238149380, 360582698582693211]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 62340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 62300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360623360798034613, 360623385631657422⟩, ⟨(-2538003245821762819), (-2536957091655506341)⟩, true⟩

def words05 : List Nat := [360582699184128613, 360582699785810395, 360582700507436291, 360582700973069379, 360582701221337146, 360582701469682909, 360582701920976574, 360582702535511508, 360582703188614664, 360582703841890493]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 62350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 62300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590948527459474, 360590973369436008⟩, ⟨(-516810433615727928), (-515763758473142136)⟩, true⟩

def words06 : List Nat := [360582704311117816, 360582704524315562, 360582704665308769, 360582704806541724, 360582704882022690, 360582704882897956, 360582704702341235, 360582704392553288, 360582704082607847, 360582704081490118]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 62360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 62300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360548807431616282, 360548832281828321⟩, ⟨2111862627702189489, 2112909816534597169⟩, true⟩

def words07 : List Nat := [360582704400853895, 360582704720375757, 360582704860531463, 360582704924626216, 360582704925359659, 360582704919548758, 360582704913494096, 360582704792000141, 360582704414437262, 360582703872346670]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 62370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 62300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360570347116054633, 360570371974526988⟩, ⟨768073779595406709, 769121483747923423⟩, true⟩

def words08 : List Nat := [360582703330080100, 360582702757550110, 360582702350912886, 360582702201291850, 360582702051592123, 360582701684963064, 360582701062233465, 360582700515283688, 360582699968085764, 360582699614914036]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 62380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 62300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571894237682848, 360571919104505809⟩, ⟨671504733655765455, 672552958845108183⟩, true⟩

def words09 : List Nat := [360582699418120712, 360582699025448902, 360582698632616348, 360582698401373869, 360582698297659320, 360582698128666702, 360582697959589950, 360582697660818454, 360582697368519132, 360582697196794994]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 62390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 62300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 62300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk623
