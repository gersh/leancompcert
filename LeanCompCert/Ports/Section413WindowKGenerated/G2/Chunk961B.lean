import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk961A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk961B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk961A

def state06 : KState := ⟨⟨360580894674713632, 360580955768770260⟩, ⟨122614060273538215, 126580997182028767⟩, true⟩

def words05 : List Nat := [360582271197691128, 360582271438563039, 360582271624808987, 360582271727838467, 360582271803080244, 360582271878704857, 360582272062072413, 360582272137872384, 360582272139139340, 360582272126894034]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 96150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 96100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360602534669958543, 360602595777181115⟩, ⟨(-1958421411864045966), (-1954453208853592290)⟩, true⟩

def words06 : List Nat := [360582272128273253, 360582272228091987, 360582272333580045, 360582272439332417, 360582272452599476, 360582272468480008, 360582272592217450, 360582272716362202, 360582272876611544, 360582273089376542]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 96160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 96100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360596885291848700, 360596946412376661⟩, ⟨(-1415136048827420435), (-1411166566172535741)⟩, true⟩

def words07 : List Nat := [360582273247529904, 360582273405832410, 360582273508145602, 360582273682870776, 360582273829876095, 360582273977104745, 360582274069784800, 360582274115613592, 360582274269291563, 360582274423458138]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 96170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 96100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360590732688507602, 360590793822165378⟩, ⟨(-823340598041967946), (-819369852495488796)⟩, true⟩

def words08 : List Nat := [360582274685248183, 360582274839525891, 360582274939715722, 360582275040053705, 360582275112608599, 360582275279952633, 360582275397025104, 360582275514337236, 360582275577114555, 360582275667114537]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 96180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 96100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360605467825201280, 360605528972029832⟩, ⟨(-2240818042941351066), (-2236846030433565320)⟩, true⟩

def words09 : List Nat := [360582275825665189, 360582275984636566, 360582276157214704, 360582276332536833, 360582276403162159, 360582276473885574, 360582276554832391, 360582276690002007, 360582276932837465, 360582277175994099]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 96190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 96100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 96100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk961B
